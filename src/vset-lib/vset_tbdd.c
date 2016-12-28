#include <hre/config.h>

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>
#include <alloca.h>

#include <hre/user.h>
#include <hre-io/user.h>
#include <vset-lib/vdom_object.h>
#include <sylvan.h>

// No support for action labels

struct vector_domain
{
    struct vector_domain_shared shared;

    TBDD vars;                  // the variable domain of full state vectors
};

struct vector_set
{
    vdom_t dom;
    size_t vector_size;         // size of state vectors in this set
    TBDD dd;                    // the set
    TBDD vars;                  // the variable domain of the set
};

struct vector_relation
{
    vdom_t dom;
    expand_cb expand;           // compatibility with generic vector_relation
    void *expand_ctx;           // compatibility with generic vector_relation

    TBDD dd;                    // the relation
    TBDD vars;                  // the variable domain of the relation

    /* the following are for rel_add_cpy */
    int r_k, w_k;               // number of read/write in this relation
    int *r_proj;                // in case we want to store this
    int *w_proj;                // easier for rel_add_cpy
    TBDD cur_is_next;           // helper BDD for read-only (copy) variables
    TBDD state_vars;            // set of READ state variables in this relation
    TBDD ro_vars;               // set of READ-ONLY (state+prime) variables
    TBDD rw_vars;               // set of READ-WRITE (state+prime) variables
    TBDD srw_vars;              // set of state_vars + rw_vars
};

/**
 * This means: create a new BDD set in the domain dom
 * dom = my domain (just copy)
 * k is the number of integers in proj
 * proj is a list of indices of the state vector in the projection
 */
static vset_t
set_create(vdom_t dom, int k, int* proj) 
{
    vset_t set = (vset_t)RTmalloc(sizeof(struct vector_set));

    LACE_ME;

    set->dom = dom;
    set->dd = tbdd_false; // Initialize with an empty BDD

    if (k>=0 && k<dom->shared.size) {
        // We are creating a projection
        set->vector_size = k;

        uint32_t vars[16*k];
        for (int i=0; i<k; i++) {
            for (int j=0; j<16; j++) {
                vars[i*16+j] = 2*(proj[i]*16+j);
            }
        }
        set->vars = tbdd_from_array(vars, 16*k);
    } else {
        // Use all variables
        set->vector_size = dom->shared.size;
        set->vars = dom->vars;
    }

    tbdd_protect(&set->dd);
    tbdd_protect(&set->vars);

    return set;
}

/**
 * Destroy a set.
 * The set must be created first with set_create
 */
static void
set_destroy(vset_t set) 
{
    tbdd_unprotect(&set->dd);
    tbdd_unprotect(&set->vars);
    RTfree(set);
}

/**
 * Create a transition relation
 * There are r_k 'read' variables and w_k 'write' variables
 */
static vrel_t
rel_create_rw(vdom_t dom, int r_k, int *r_proj, int w_k, int *w_proj)
{
    LACE_ME;

    vrel_t rel = (vrel_t)RTmalloc(sizeof(struct vector_relation));

    rel->dom = dom;
    rel->dd = tbdd_false; // Initially, empty.

    rel->r_k = r_k;
    rel->w_k = w_k;
    rel->r_proj = (int*)RTmalloc(sizeof(int)*r_k);
    memcpy(rel->r_proj, r_proj, sizeof(int)*r_k);
    rel->w_proj = (int*)RTmalloc(sizeof(int)*w_k);
    memcpy(rel->w_proj, w_proj, sizeof(int)*w_k);

    tbdd_protect(&rel->dd);
    tbdd_protect(&rel->vars);
    tbdd_protect(&rel->cur_is_next);
    tbdd_protect(&rel->state_vars);
    tbdd_protect(&rel->ro_vars);
    tbdd_protect(&rel->rw_vars);
    tbdd_protect(&rel->srw_vars);

    /* Compute a_proj the union of r_proj and w_proj, and a_k the length of a_proj */
    int a_proj[r_k+w_k];
    int r_i = 0, w_i = 0, a_i = 0;
    for (;r_i < r_k || w_i < w_k;) {
        if (r_i < r_k && w_i < w_k) {
            if (r_proj[r_i] < w_proj[w_i]) {
                a_proj[a_i++] = r_proj[r_i++];
            } else if (r_proj[r_i] > w_proj[w_i]) {
                a_proj[a_i++] = w_proj[w_i++];
            } else /* r_proj[r_i] == w_proj[w_i] */ {
                a_proj[a_i++] = w_proj[w_i++];
                r_i++;
            }
        } else if (r_i < r_k) {
            a_proj[a_i++] = r_proj[r_i++];
        } else if (w_i < w_k) {
            a_proj[a_i++] = w_proj[w_i++];
        }
    }
    const int a_k = a_i;

    /* Compute ro_proj: a_proj \ w_proj */
    int ro_proj[r_k];
    int ro_i = 0;
    for (a_i = w_i = 0; a_i < a_k; a_i++) {
        if (w_i < w_k) {
            if (a_proj[a_i] < w_proj[w_i]) {
                ro_proj[ro_i++] = a_proj[a_i];
            } else /* a_proj[a_i] == w_proj[w_i] */ {
                w_i++;
            }
        } else {
            ro_proj[ro_i++] = a_proj[a_i];
        }
    }
    const int ro_k = ro_i;

    /* Compute all_variables, which are all variables the transition relation is defined on */
    BDDVAR all_vars[16 * a_k * 2];
    for (int i=0; i<a_k; i++) {
        for (int j=0; j<16; j++) {
            all_vars[2*(i*16+j)]   = 2*(a_proj[i]*16+j);
            all_vars[2*(i*16+j)+1] = 2*(a_proj[i]*16+j)+1;
        }
    }
    rel->vars = tbdd_from_array(all_vars, 16 * a_k * 2);

    /* Create set of (read) state variables */
    BDDVAR state_vars[16 * r_k];
    for (int i=0; i<r_k; i++) {
        for (int j=0; j<16; j++) {
            state_vars[i*16+j] = 2*(r_proj[i]*16+j);
        }
    }
    rel->state_vars = tbdd_from_array(state_vars, 16 * r_k);

    /* Create set of read-write state+prime variables */
    BDDVAR rw_vars[16 * w_k * 2];
    for (int i=0; i<w_k; i++) {
        for (int j=0; j<16; j++) {
            rw_vars[2*(i*16+j)] = 2*(w_proj[i]*16+j);
            rw_vars[2*(i*16+j)+1] = 2*(w_proj[i]*16+j)+1;
        }
    }
    rel->rw_vars = tbdd_from_array(rw_vars, 16 * w_k * 2);

    /* Create merged domains of state_vars and rw_vars */
    rel->srw_vars = tbdd_merge_domains(rel->state_vars, rel->rw_vars);

    /* Create set of read-only state+prime variables */
    BDDVAR ro_vars[16 * ro_k * 2];
    for (int i=0; i<ro_k; i++) {
        for (int j=0; j<16; j++) {
            ro_vars[2*(i*16+j)] = 2*(ro_proj[i]*16+j);
            ro_vars[2*(i*16+j)+1] = 2*(ro_proj[i]*16+j)+1;
        }
    }
    rel->ro_vars = tbdd_from_array(ro_vars, 16 * ro_k * 2);

    /* Compute cur_is_next for variables in ro_proj */
    TBDD cur_is_next = tbdd_true;
    uint32_t last = 0xfffff;
    for (int i=ro_k-1; i>=0; i--) {
        for (int j=16-1; j>=0; j--) {
            tbdd_refs_push(cur_is_next);
            TBDD low = tbdd_makenode(2*(ro_proj[i]*16+j)+1, cur_is_next, tbdd_false, last);
            tbdd_refs_push(low);
            TBDD high = tbdd_makenode(2*(ro_proj[i]*16+j)+1, tbdd_false, cur_is_next, last);
            tbdd_refs_pop(2);
            cur_is_next = tbdd_makenode(2*(ro_proj[i]*16+j), low, high, 2*(ro_proj[i]*16+j)+1);
            last = 2*(ro_proj[i]*16+j);
        }
    }
    rel->cur_is_next = cur_is_next;

    return rel;
}

static vrel_t
rel_create(vdom_t dom, int k, int *proj)
{
    return rel_create_rw(dom, k, proj, k, proj);
}

/**
 * Destroy a relation.
 */
static void
rel_destroy(vrel_t rel)
{
    tbdd_unprotect(&rel->dd);
    tbdd_unprotect(&rel->vars);
    tbdd_unprotect(&rel->cur_is_next);
    tbdd_unprotect(&rel->state_vars);
    tbdd_unprotect(&rel->ro_vars);
    tbdd_unprotect(&rel->rw_vars);
    tbdd_unprotect(&rel->srw_vars);
    RTfree(rel);
}

/**
 * Bit smash state to cube
 * Make sure size(arr) is 16*state_length
 */
static void
state_to_cube(const int* state, size_t state_length, uint8_t *arr)
{
    for (size_t i=0; i<state_length; i++) {
        for (int j=0; j<16; j++) {
            *arr = (*state & (1LL<<(16-j-1))) ? 1 : 0;
            arr++;
        }
        state++;
    }
}

/**
 * Adds e to set
 */
static void
set_add(vset_t set, const int* e)
{
    // e is a full state vector

    // create cube
    uint8_t cube[set->dom->shared.size * 16];
    state_to_cube(e, set->dom->shared.size, cube);

    // get Lace infrastructure
    LACE_ME;

    // cube it
    TBDD dd = tbdd_cube(set->dom->vars, cube);

    // existential quantification
    tbdd_refs_push(dd);
    dd = tbdd_exists_dom(dd, set->vars);
    tbdd_refs_pop(1);

    // add to set
    tbdd_refs_push(dd);
    set->dd = tbdd_or(set->dd, dd, set->vars);
    tbdd_refs_pop(1);
}

/**
 * Returns 1 if e is a member of set, 0 otherwise
 */
static int
set_member(vset_t set, const int* e)
{
    // e is a full state vector

    // create cube
    uint8_t cube[set->dom->shared.size * 16];
    state_to_cube(e, set->dom->shared.size, cube);

    // get Lace infrastructure
    LACE_ME;

    // cube it
    TBDD dd = tbdd_cube(set->dom->vars, cube);

    // existential quantification
    tbdd_refs_push(dd);
    dd = tbdd_exists_dom(dd, set->vars);
    tbdd_refs_pop(1);

    // check if in set
    tbdd_refs_push(dd);
    int res = tbdd_and(set->dd, dd, set->vars) != tbdd_false ? 1 : 0;
    tbdd_refs_pop(1);
    return res;
}

/**
 * Returns 1 if the set is empty, 0 otherwise
 */
static int
set_is_empty(vset_t set)
{
    return set->dd == tbdd_false ? 1 : 0;
}

/**
 * Returns 1 if the two sets are equal, 0 otherwise.
 * Assumption: projections are equal.
 */
static int
set_equal(vset_t set1, vset_t set2)
{
    assert(set1->vars == set2->vars);
    return set1->dd == set2->dd;
}

/** 
 * Clear a set.
 */
static void
set_clear(vset_t set) 
{
    set->dd = tbdd_false;
}

/**
 * Copy a set from src to dst.
 * Assumption: projections are equal.
 */
static void
set_copy(vset_t dst, vset_t src)
{
    assert(dst->vars == src->vars);
    dst->dd = src->dd;
}

struct enum_ctx
{
    vset_element_cb cb;
    void* ctx;
};

static void
state_from_arr(uint8_t *arr, size_t arr_len, int* vec, size_t vec_len)
{
    assert(vec_len*16 == arr_len);
    for (size_t i=0; i<vec_len; i++) {
        vec[i] = 0;
        for (int j=0; j<16; j++) {
            vec[i]<<=1;
            if (*arr++) vec[i] |= 1;
        }
    }
}

VOID_TASK_3(enum_cb, void*, ctx, uint8_t*, arr, size_t, arr_len)
{
    int vec[arr_len/16];
    state_from_arr(arr, arr_len, vec, arr_len/16);
    struct enum_ctx *ectx = (struct enum_ctx*)ctx;
    ectx->cb(ectx->ctx, vec);
}

/**
 * Enumerate all elements of the set. Calls cb(context, const int* ELEMENT) 
 * for every found element. Elements are projected, meaning not the full 
 * state vector is returned, but only the selected bytes.
 */
static void
set_enum(vset_t set, vset_element_cb cb, void* context)
{
    LACE_ME;
    struct enum_ctx ctx = (struct enum_ctx){cb, context};
    tbdd_enum_seq(set->dd, set->vars, TASK(enum_cb), &ctx);
}

/**
 * Context struct for set_update
 */
struct set_update_context
{
    vset_t set;
    vset_update_cb cb;
    void* context;
};

/**
 * Callback implementation for set_update
 */
TASK_3(TBDD, tbdd_set_updater, void*, _ctx, uint8_t*, arr, size_t, arr_len)
{
    struct set_update_context *ctx = (struct set_update_context*)_ctx;
    int vec[arr_len/16];
    state_from_arr(arr, arr_len, vec, arr_len/16);
    struct vector_set dummyset;
    dummyset.dom = ctx->set->dom;
    dummyset.vector_size = ctx->set->vector_size;
    dummyset.vars = ctx->set->vars;
    dummyset.dd = tbdd_false;
    tbdd_protect(&dummyset.dd);
    ctx->cb(&dummyset, ctx->context, (int*)vec);
    tbdd_unprotect(&dummyset.dd);
    return dummyset.dd;
}

/**
 * Combination of enumeration and set union of the result
 */
static void
set_update(vset_t dst, vset_t src, vset_update_cb cb, void* context)
{
    LACE_ME;
    struct set_update_context ctx = (struct set_update_context){dst, cb, context};
    TBDD result = tbdd_collect(src->dd, src->vars, dst->vars, TASK(tbdd_set_updater), &ctx);
    tbdd_refs_push(result);
    dst->dd = tbdd_or(dst->dd, result, dst->vars);
    tbdd_refs_pop(1);
}

/**
 * Generate one possible state
 */
static void
set_example(vset_t set, int *e)
{
    assert(0);
    (void)set;
    (void)e;
    /*
    assert(set->bdd != sylvan_false);

    memset(e, 0, sizeof(int)*set->vector_size);

    uint8_t* cube = (uint8_t*)alloca(set->vector_size*16*sizeof(uint8_t));
    sylvan_sat_one(set->bdd, set->state_variables, cube);

    size_t i;
    int j;
    for (i=0;i<set->vector_size;i++) {
        for (j=0;j<16;j++) {
            if (cube[i*16+j]==1) e[i] |= 1<<(16-j-1);
        }
    }
    */
}

/**
 * Enumerate all states that match partial state <match>
 * <match> is p_len long
 * <proj> is an ordered list of integers, containing indices of each match integer
 */
static void
set_enum_match(vset_t set, int p_len, int* proj, int* match, vset_element_cb cb, void* context) 
{
    (void)set;
    (void)p_len;
    (void)proj;
    (void)match;
    (void)cb;
    (void)context;
    /* create bdd of 'match' */
    /*
    BDD match_bdd = sylvan_true;
    for (int i=p_len-1; i>=0; i--) {
        uint32_t b = match[i];
        for (int j=16-1; j>=0; j--) {
            if (b & 1) match_bdd = sylvan_makenode(2*(proj[i]*16+j), sylvan_false, match_bdd);
            else match_bdd = sylvan_makenode(2*(proj[i]*16+j), match_bdd, sylvan_false);
            b >>= 1;
        }
    }

    LACE_ME;

    bdd_refs_push(match_bdd);
    match_bdd = sylvan_and(match_bdd, set->bdd);
    bdd_refs_pop(1);

    int vec[set->vector_size];
    memset(vec, 0, sizeof(int)*set->vector_size);

    bdd_refs_push(match_bdd);
    set_enum_do(match_bdd, set->state_variables, vec, 0, cb, context);
    bdd_refs_pop(1);
    */
}

static void
set_copy_match(vset_t dst, vset_t src, int p_len, int* proj, int*match)
{
    (void)dst;
    (void)src;
    (void)p_len;
    (void)proj;
    (void)match;
    /* create bdd of 'match' */
    /*
    BDD match_bdd = sylvan_true;
    for (int i=p_len-1; i>=0; i--) {
        uint32_t b = match[i];
        for (int j=16-1; j>=0; j--) {
            if (b & 1) match_bdd = sylvan_makenode(2*(proj[i]*16+j), sylvan_false, match_bdd);
            else match_bdd = sylvan_makenode(2*(proj[i]*16+j), match_bdd, sylvan_false);
            b >>= 1;
        }
    }

    LACE_ME;

    bdd_refs_push(match_bdd);
    dst->bdd = sylvan_and(match_bdd, src->bdd);
    bdd_refs_pop(1);
    */
}

static void
set_count(vset_t set, long *nodes, double *elements)
{
    LACE_ME;
    if (nodes != NULL) *nodes = tbdd_nodecount(set->dd);
    if (elements != NULL) *elements = tbdd_satcount(set->dd, set->vars);
}

static void
rel_count(vrel_t rel, long *nodes, double *elements)
{
    LACE_ME;
    if (nodes != NULL) *nodes = tbdd_nodecount(rel->dd);
    if (elements != NULL) *elements = tbdd_satcount(rel->dd, rel->vars);
}

/**
 * Calculate dst = dst + src
 */
static void
set_union(vset_t dst, vset_t src)
{
    assert(dst->vars == src->vars);

    LACE_ME;

    if (dst != src) {
        dst->dd = tbdd_or(dst->dd, src->dd, dst->vars);
    }
}

/**
 * Calculate dst = dst /\ src
 */
static void
set_intersect(vset_t dst, vset_t src)
{
    LACE_ME;

    assert(dst->vars == src->vars);
    if (dst != src) dst->dd = tbdd_and(dst->dd, src->dd, dst->vars);
}

/**
 * Calculate dst = dst /\ src, but with two sets of possibly different projections
 */
static void
set_join(vset_t dst, vset_t left, vset_t right)
{
    LACE_ME;

    // assumption: dst->vars == tbdd_merge_domains(left->vars, right->vars)
    dst->dd = tbdd_and_dom(left->dd, left->vars, right->dd, right->vars);
}

/**
 * Calculate dst = dst - src
 */
static void
set_minus(vset_t dst, vset_t src)
{
    LACE_ME;

    assert(dst->vars == src->vars);
    dst->dd = dst == src ? tbdd_false : tbdd_diff(dst->dd, src->dd, dst->vars);
}

/**
 * Calculate dst = next(src, rel)
 */
static void
set_next(vset_t dst, vset_t src, vrel_t rel)
{
    LACE_ME;

    assert(dst->vars == src->vars);
    dst->dd = tbdd_relnext(src->dd, rel->dd, rel->vars, src->vars);
} 

/**
 * Calculate dst = prev(src, rel) intersected with univ
 */
static void
set_prev(vset_t dst, vset_t src, vrel_t rel, vset_t univ)
{
    // TODO implement relprev and then implement vset code
    (void)dst;
    (void)src;
    (void)rel;
    (void)univ;
    /*
    assert(dst->vars == src->vars);

    LACE_ME;

    if (dst == univ) {
        BDD tmp = sylvan_relprev(rel->bdd, src->bdd, rel->all_variables);
        bdd_refs_push(tmp);
        dst->bdd = sylvan_and(tmp, univ->bdd);
        bdd_refs_pop(1);
    } else {
        dst->bdd = sylvan_relprev(rel->bdd, src->bdd, rel->all_variables);
        dst->bdd = sylvan_and(dst->bdd, univ->bdd);
    }
    */
}

/**
 * Calculate projection of src onto dst
 */
static void
set_project(vset_t dst, vset_t src)
{
    if (dst->vars != src->vars) {
        LACE_ME;
        dst->dd = tbdd_exists_dom(src->dd, dst->vars);
    } else {
        dst->dd = src->dd;
    }
}

/**
 * Add all elements of src to dst and remove all elements that were in dst already from src
 * in other words: newDst = dst + src
 *                 newSrc = src - dst
 */
static void
set_zip(vset_t dst, vset_t src)
{
    assert(dst->vars == src->vars);

    LACE_ME;

    if (src == dst) {
        Abort("Do not call set_zip with dst == src");
    }

    BDD tmp1 = dst->dd;
    BDD tmp2 = src->dd;
    tbdd_refs_push(tmp1);
    tbdd_refs_push(tmp2);
    dst->dd = tbdd_or(tmp1, tmp2, dst->vars);
    src->dd = tbdd_diff(tmp2, tmp1, dst->vars);
    tbdd_refs_pop(2);
}

/**
 * Add (src, dst) to the relation
 */
static void
rel_add_cpy(vrel_t rel, const int *src, const int *dst, const int *cpy)
{
    LACE_ME;

    // make cube of src on domain state_vars
    uint8_t src_cube[rel->r_k * 16];
    state_to_cube(src, (size_t)rel->r_k, src_cube);
    TBDD src_dd = tbdd_cube(rel->state_vars, src_cube);
    tbdd_refs_push(src_dd);

    // create the BDD representing the dst+cpy structure on domain rw_vars
    TBDD dst_dd = tbdd_true;
    uint32_t last = 0xfffff;
    for (int i=rel->w_k-1; i>=0; i--) {
        int k = rel->w_proj[i];
        if (cpy && cpy[i]) {
            // take copy of read
            for (int j=16-1; j>=0; j--) {
                tbdd_refs_push(dst_dd);
                TBDD low = tbdd_makenode(2*(k*16+j)+1, dst_dd, tbdd_false, last);
                tbdd_refs_push(low);
                TBDD high = tbdd_makenode(2*(k*16+j)+1, tbdd_false, dst_dd, last);
                tbdd_refs_pop(2);
                dst_dd = tbdd_makenode(2*(k*16+j), low, high, 2*(k*16+j)+1);
                last = 2*(k*16+j);
            }
        } else {
            // actually write
            for (int j=16-1; j>=0; j--) {
                if (dst[i] & (1LL<<(16-j-1))) dst_dd = tbdd_makenode(2*(k*16+j)+1, tbdd_false, dst_dd, last);
                else dst_dd = tbdd_makenode(2*(k*16+j)+1, dst_dd, tbdd_false, last);
                dst_dd = tbdd_makenode(2*(k*16+j), dst_dd, dst_dd, 2*(k*16+j)+1);
                last = 2*(k*16+j);
            }
        }
    }
    tbdd_refs_push(dst_dd);

    TBDD to_add;

    if (1) {
        // intersect src and dst
        TBDD src_and_dst = tbdd_and_dom(src_dd, rel->state_vars, dst_dd, rel->rw_vars);
        tbdd_refs_pop(2);
        tbdd_refs_push(src_and_dst);
        // intersect src_and_dst with cur_is_next
        to_add = tbdd_and_dom(src_and_dst, rel->srw_vars, rel->cur_is_next, rel->ro_vars);
        tbdd_refs_pop(1); // src_and_dst
        tbdd_refs_push(to_add);
        // assert(rel->vars == tbdd_merge_domains(rel->srw_vars, rel->ro_vars));
    } else {
        src_dd = tbdd_extend_domain(src_dd, rel->state_vars, rel->vars);
        tbdd_refs_push(src_dd);
        dst_dd = tbdd_extend_domain(dst_dd, rel->rw_vars, rel->vars);
        tbdd_refs_push(dst_dd);
        TBDD cin = tbdd_extend_domain(rel->cur_is_next, rel->ro_vars, rel->vars);
        tbdd_refs_pop(4);
        tbdd_refs_push(src_dd);
        tbdd_refs_push(dst_dd);
        tbdd_refs_push(cin);
        to_add = tbdd_and(src_dd, dst_dd, rel->vars);
        tbdd_refs_push(to_add);
        to_add = tbdd_and(to_add, cin, rel->vars);
        tbdd_refs_pop(4);
        tbdd_refs_push(to_add);
    }

    // add result to relation
    rel->dd = tbdd_or(rel->dd, to_add, rel->vars);
    tbdd_refs_pop(1);
}

/**
 * Add (src, dst) to the relation
 */
static void
rel_add(vrel_t rel, const int *src, const int *dst)
{
    return rel_add_cpy(rel, src, dst, 0);
}

/**
 * Context struct for rel_update
 */
struct rel_update_context
{
    vrel_t rel;
    vrel_update_cb cb;
    void* context;
};

/**
 * Callback implementation for rel_update
 */
TASK_3(TBDD, tbdd_rel_updater, void*, _ctx, uint8_t*, arr, size_t, arr_len)
{
    struct rel_update_context *ctx = (struct rel_update_context*)_ctx;
    int vec[arr_len/16];
    state_from_arr(arr, arr_len, vec, arr_len/16);
    struct vector_relation dummyrel;
    memcpy(&dummyrel, ctx->rel, sizeof(struct vector_relation));
    dummyrel.dd = tbdd_false;
    tbdd_protect(&dummyrel.dd);
    ctx->cb(&dummyrel, ctx->context, (int*)vec);
    tbdd_unprotect(&dummyrel.dd);
    return dummyrel.dd;
}

/**
 * Combination of enumeration and rel union of the result
 */
static void
rel_update(vrel_t dst, vset_t src, vrel_update_cb cb, void* context)
{
    LACE_ME;
    struct rel_update_context ctx = (struct rel_update_context){dst, cb, context};
    TBDD result = tbdd_collect(src->dd, src->vars, dst->vars, TASK(tbdd_rel_updater), &ctx);
    tbdd_refs_push(result);
    dst->dd = tbdd_or(dst->dd, result, dst->vars);
    tbdd_refs_pop(1);
}

static void
set_reorder()
{
    // ignore
}

static void
set_dot(FILE* fp, vset_t src)
{
    sylvan_fprintdot(fp, src->dd);
}

static void
rel_dot(FILE* fp, vrel_t rel)
{
    sylvan_fprintdot(fp, rel->dd);
}

/* SAVING */
static void
set_save(FILE* f, vset_t set)
{
    LACE_ME;
    TBDD sets[2];
    sets[0] = set->dd;
    sets[1] = set->vars;
    tbdd_writer_tobinary(f, sets, 2);
    fwrite(&set->vector_size, sizeof(size_t), 1, f);
}

static void
rel_save_proj(FILE* f, vrel_t rel)
{
    fwrite(&rel->r_k, sizeof(int), 1, f);
    fwrite(&rel->w_k, sizeof(int), 1, f);
    fwrite(rel->r_proj, sizeof(int), rel->r_k, f);
    fwrite(rel->w_proj, sizeof(int), rel->w_k, f);
}

static void
rel_save(FILE* f, vrel_t rel)
{
    LACE_ME;
    tbdd_writer_tobinary(f, &rel->dd, 1);
}

static vset_t
set_load(FILE* f, vdom_t dom)
{
    LACE_ME;
    TBDD sets[2];
    if (tbdd_reader_frombinary(f, sets, 2) != 0) Abort("Invalid file format.");

    vset_t set = (vset_t)RTmalloc(sizeof(struct vector_set));
    set->dom = dom;
    set->dd = sets[0];
    set->vars = sets[1];
    if (fread(&set->vector_size, sizeof(size_t), 1, f) != 1) Abort("invalid file format.");

    tbdd_protect(&set->dd);
    tbdd_protect(&set->vars);

    return set;
}

static vrel_t 
rel_load_proj(FILE* f, vdom_t dom)
{
    int r_k, w_k;
    if (fread(&r_k, sizeof(int), 1, f) != 1) Abort("Invalid file format.");
    if (fread(&w_k, sizeof(int), 1, f) != 1) Abort("Invalid file format.");
    int r_proj[r_k], w_proj[w_k];
    if (fread(r_proj, sizeof(int), r_k, f) != (size_t)r_k) Abort("Invalid file format.");
    if (fread(w_proj, sizeof(int), w_k, f) != (size_t)w_k) Abort("Invalid file format.");
    return rel_create_rw(dom, r_k, r_proj, w_k, w_proj);
}

static void
rel_load(FILE* f, vrel_t rel)
{
    LACE_ME;
    if (tbdd_reader_frombinary(f, &rel->dd, 1) != 1) Abort("Invalid file format.");
}

static void
dom_save(FILE* f, vdom_t dom)
{
    int vector_size = dom->shared.size;
    fwrite(&vector_size, sizeof(int), 1, f);
}

static int
separates_rw()
{
    return 1;
}

static void
dom_set_function_pointers(vdom_t dom)
{
    // Set function pointers
    dom->shared.set_create = set_create;
    dom->shared.set_destroy = set_destroy;
    dom->shared.set_add = set_add;
    dom->shared.set_update = set_update;
    // set_update_seq has a good default
    dom->shared.set_member = set_member;
    dom->shared.set_equal = set_equal;
    dom->shared.set_is_empty = set_is_empty;
    dom->shared.set_clear = set_clear;
    dom->shared.set_enum = set_enum;
    dom->shared.set_enum_match = set_enum_match;
    dom->shared.set_copy = set_copy;
    dom->shared.set_copy_match = set_copy_match;
    // copy_match_proj
    // proj_create (default is returning -1)
    dom->shared.set_example = set_example;
    // set_example_match (has inefficient default)
    // set_random (has fallback and warning message)
    dom->shared.set_project = set_project;
    // set_project_minus (has reasonable default)
    dom->shared.set_union = set_union;
    dom->shared.set_intersect = set_intersect;
    dom->shared.set_minus = set_minus;
    dom->shared.set_zip = set_zip;
    dom->shared.set_count = set_count;
    // set_ccount
    // visit_seq
    // visit_par (has terrible default: visit_seq)
    dom->shared.set_join = set_join;
    // set_universe (seems unused)
    dom->shared.rel_create = rel_create;
    dom->shared.rel_create_rw = rel_create_rw;
    dom->shared.rel_destroy = rel_destroy;
    dom->shared.rel_add = rel_add;
    dom->shared.rel_add_cpy = rel_add_cpy;
    // rel_add_act
    dom->shared.rel_update = rel_update;
    // rel_update_seq has a good default
    dom->shared.rel_count = rel_count;
    dom->shared.set_next = set_next;
    // set_next_union (has reasonable default)
    dom->shared.set_prev = set_prev;
    // set_least_fixpoint
    dom->shared.dom_save = dom_save;
    dom->shared.set_save = set_save;
    dom->shared.set_load = set_load;
    dom->shared.rel_save_proj = rel_save_proj;
    dom->shared.rel_save = rel_save;
    dom->shared.rel_load_proj = rel_load_proj;
    dom->shared.rel_load = rel_load;
    // pre_save not needed
    // pre_load not needed
    // post_save not needed
    // post_load not needed
    dom->shared.set_dot = set_dot;
    dom->shared.rel_dot = rel_dot;
    dom->shared.reorder = set_reorder;
    dom->shared.separates_rw = separates_rw;
    // supports_precise_counting
    // dom_clear_cache
    // dom_next_cache_op
}

void ltsmin_initialize_sylvan(); // defined in vset_sylvan.c

/**
 * Create a domain with object size n
 */
vdom_t
vdom_create_tbdd(int n)
{
    Warning(info, "Creating a Sylvan domain.");

    ltsmin_initialize_sylvan();
    sylvan_init_tbdd();

    // Create data structure of domain
    vdom_t dom = (vdom_t)RTmalloc(sizeof(struct vector_domain));
    vdom_init_shared(dom, n);
    dom_set_function_pointers(dom);

    LACE_ME;

    // Create domain variables
    uint32_t vars[16*n];
    for (int i=0;i<16*n;i++) vars[i] = 2*i;
    dom->vars = tbdd_from_array(vars, 16*n);
    tbdd_protect(&dom->vars);

    return dom;
}

vdom_t
vdom_create_tbdd_from_file(FILE *f)
{
    int vector_size;
    if ((fread(&vector_size, sizeof(int), 1, f) != 1)) Abort("invalid file format");
    return vdom_create_tbdd(vector_size);
}
