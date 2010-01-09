#include <config.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <strings.h>
#include <ltsmin-syntax.h>

#include "archive.h"
#include <runtime.h>
#include "treedbs.h"
#include <stringindex.h>
#include "vector_set.h"
#include "scctimer.h"
#include "dm/dm.h"

#include <lts_enum.h>
#include <lts_io.h>

#if defined(MCRL)
#include "mcrl-greybox.h"
#endif
#if defined(MCRL2)
#include "mcrl2-greybox.h"
#endif
#if defined(NIPS)
#include "nips-greybox.h"
#endif
#if defined(ETF)
#include "etf-greybox.h"
#endif
#if defined(DIVINE)
#include "dve-greybox.h"
#endif

static char* etf_output=NULL;
static char* trc_output=NULL;
static int dlk_detect=0;

static lts_enum_cb_t trace_handle=NULL;
static lts_output_t trace_output=NULL;

static enum { BFS , BFS2 , Chain } strategy = BFS;

static char* order="bfs";
static si_map_entry strategies[]={
	{"bfs",BFS},
	{"bfs2",BFS2},
	{"chain",Chain},
	{NULL,0}
};

static void reach_popt(poptContext con,
 		enum poptCallbackReason reason,
                            const struct poptOption * opt,
                             const char * arg, void * data){
	(void)con;(void)opt;(void)arg;(void)data;
	switch(reason){
	case POPT_CALLBACK_REASON_PRE:
		Fatal(1,error,"unexpected call to vset_popt");
	case POPT_CALLBACK_REASON_POST: {
		int res=linear_search(strategies,order);
		if (res<0) {
			Warning(error,"unknown exploration order %s",order);
			RTexitUsage(EXIT_FAILURE);
		} else {
			Warning(info,"Exploration order is %s",order);
		}
		strategy = res;

                if (trc_output)
                    dlk_detect = 1;
		return;
	}
	case POPT_CALLBACK_REASON_OPTION:
		Fatal(1,error,"unexpected call to reach_popt");
	}
}


static  struct poptOption options[] = {
	{ NULL, 0 , POPT_ARG_CALLBACK|POPT_CBFLAG_POST|POPT_CBFLAG_SKIPOPTION , (void*)reach_popt , 0 , NULL , NULL },
	{ "order" , 0 , POPT_ARG_STRING|POPT_ARGFLAG_SHOW_DEFAULT , &order , 0 , "select the exploration strategy to a specific order" ,"<bfs|bfs2|chain>" },
	{ "deadlock" , 'd' , POPT_ARG_VAL , &dlk_detect , 1 , "detect deadlocks" , NULL },
	{ "trace" , 0 , POPT_ARG_STRING , &trc_output , 0 , "file to write trace to" , "<lts-file>.gcf" },
#if defined(MCRL)
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, mcrl_options , 0 , "mCRL options",NULL},
#endif
#if defined(MCRL2)
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, mcrl2_options , 0 , "mCRL2 options",NULL},
#endif
#if defined(NIPS)
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, nips_options , 0 , "NIPS options",NULL},
#endif
#if defined(ETF)
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, etf_options , 0 , "ETF options",NULL},
#endif
#if defined(DIVINE)
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, dve_options , 0 , "DiVinE options", NULL },
#endif
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, greybox_options , 0 , "Greybox options",NULL},
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, vset_options , 0 , "Vector set options",NULL},
	{ NULL, 0 , POPT_ARG_INCLUDE_TABLE, lts_io_options , 0 , NULL , NULL },
	POPT_TABLEEND
};

static lts_type_t ltstype;
static int N;
static int eLbls;
static int sLbls;
static int nGrps;
static vdom_t domain;
static vset_t visited;
static long max_lev_count=0;
static long max_vis_count=0;
static long max_grp_count=0;
static long max_trans_count=0;
static model_t model;
static vrel_t *group_next;
static vset_t *group_explored;
static vset_t *group_tmp;
static int explored;

static void *new_string_index(void* context){
	(void)context;
	Warning(info,"creating a new string index");
	return SIcreate();
}

struct group_add_info {
	int group;
	int *src;
};

static void group_add(void*context,int*labels,int*dst){
	(void)labels;
	struct group_add_info* ctx=(struct group_add_info*)context;
	vrel_add(group_next[ctx->group],ctx->src,dst);
}

static void explore_cb(void*context,int *src){
	struct group_add_info* ctx=(struct group_add_info*)context;
	ctx->src=src;
	GBgetTransitionsShort(model,ctx->group,src,group_add,context);
	explored++;
	if (explored%1000 ==0 && RTverbosity >=2) {
		Warning(info,"explored %d short vectors for group %d",explored,ctx->group);
	}
}

static inline void expand_group_next(int group,vset_t set){
	struct group_add_info ctx;
	explored=0;
	ctx.group=group;
	vset_project(group_tmp[group],set);
	vset_zip(group_explored[group],group_tmp[group]);
	vset_enum(group_tmp[group],explore_cb,&ctx);
	vset_clear(group_tmp[group]);
}

static void write_trace_state(int src_no, int*state){
	Warning(debug,"dumping state %d",src_no);
    int labels[sLbls];
	if (sLbls) GBgetStateLabelsAll(model,state,labels);
    enum_state(trace_handle,0,state,labels);
}

struct write_trace_step_s {
    int src_no;
    int dst_no;
    int* dst;
    int found;
};

static void write_trace_next(void*arg,int*lbl,int*dst){
	struct write_trace_step_s*ctx=(struct write_trace_step_s*)arg;
	if(ctx->found) return;
	for(int i=0;i<N;i++){
	    if (ctx->dst[i]!=dst[i]) return;
	}
	ctx->found=1;
	enum_seg_seg(trace_handle,0,ctx->src_no,0,ctx->dst_no,lbl);
}

static void write_trace_step(int src_no,int*src,int dst_no,int*dst){
    Warning(debug,"finding edge for state %d",src_no);
    struct write_trace_step_s ctx;
    ctx.src_no=src_no;
    ctx.dst_no=dst_no;
    ctx.dst=dst;
    ctx.found=0;
    GBgetTransitionsAll(model,src,write_trace_next,&ctx);
    if (ctx.found==0) Fatal(1,error,"no matching transition found");
}

static int same_state(int*s1,int*s2){
	for(int i=0;i<N;i++) if (s1[i]!=s2[i]) return 0;
	return 1;
}

static int find_trace_to(int step,int *src,int *dst){
	if(same_state(src,dst))return step;
	vset_t src_reach=vset_create(domain,0,NULL);
	vset_t current=vset_create(domain,0,NULL);
	vset_t dst_reach=vset_create(domain,0,NULL);
	vset_t temp=vset_create(domain,0,NULL);
	vset_add(src_reach,src);
	vset_add(dst_reach,dst);
	int middle[N];
	int distance=0;
	//long long e_count;
	//long n_count;
	for(;;){
		//Warning(info,"from src forward");
		distance++;
		vset_copy(current,src_reach);
		//vset_count(current,&n_count,&e_count);
		//fprintf(stderr,"current set has %lld states (%ld nodes)\n",e_count,n_count);
		for(int i=0;i<nGrps;i++){
			vset_next(temp,current,group_next[i]);
			vset_union(src_reach,temp);
		}
		vset_clear(temp);
		vset_copy(current,src_reach);
		//Warning(info,"checking overlap");
		vset_minus(current,dst_reach);
		if (!vset_equal(src_reach,current)){
			vset_minus(src_reach,current);
			vset_example(src_reach,middle);
			//Warning(info,"middle found");
			break;
		}
		//Warning(info,"from dst backward");
		distance++;
		vset_copy(current,dst_reach);
		//vset_count(current,&n_count,&e_count);
		//fprintf(stderr,"current set has %lld states (%ld nodes)\n",e_count,n_count);
		for(int i=0;i<nGrps;i++){
			vset_prev(temp,current,group_next[i]);
			vset_union(dst_reach,temp);
		}
		vset_clear(temp);
		vset_copy(current,dst_reach);
		//Warning(info,"checking overlap");
		vset_minus(current,src_reach);
		if (!vset_equal(dst_reach,current)){
			vset_minus(dst_reach,current);
			vset_example(dst_reach,middle);
			//Warning(info,"middle found");
			break;
		}
	}
	vset_clear(src_reach);
	vset_clear(current);
	vset_clear(dst_reach);
	vset_clear(temp);
	switch(distance){
	case 1:
		write_trace_state(step,src);
		write_trace_step(step,src,step+1,dst);
		return step+1;
	case 2:
		write_trace_state(step,src);
		write_trace_step(step,src,step+1,middle);
		write_trace_state(step+1,middle);
		write_trace_step(step+1,middle,step+2,dst);
		return step+2;
	default:
		step=find_trace_to(step,src,middle);
		return find_trace_to(step,middle,dst);
	}
}

static void find_trace(int *src,int *dst){
	eLbls=lts_type_get_edge_label_count(ltstype);
	sLbls=lts_type_get_state_label_count(ltstype);
	mytimer_t timer=SCCcreateTimer();
	SCCstartTimer(timer);
	int len=find_trace_to(0,src,dst);
	write_trace_state(len,dst);
	SCCstopTimer(timer);
	SCCreportTimer(timer,"constructing the trace took");
}

static void deadlock_check(vset_t deadlocks){
    if (vset_is_empty(deadlocks)) return;
    Warning(info,"deadlock found");
    if (trc_output){
        int init_state[N];
        GBgetInitialState(model,init_state);
        int dlk_state[N];
        vset_example(deadlocks,dlk_state);
        trace_output=lts_output_open(trc_output,model,1,0,1,"vsi",NULL);
        lts_output_set_root_vec(trace_output,(uint32_t*)init_state);
        lts_output_set_root_idx(trace_output,0,0);
        trace_handle=lts_output_begin(trace_output,0,0,0);	
        find_trace(init_state,dlk_state);
        lts_output_end(trace_output,trace_handle);
        lts_output_close(&trace_output);
    }
    Fatal(1,info,"exiting now");
}

static void stats_and_progress_report(vset_t current, vset_t visited, int level) {
  bn_int_t e_count;
  long n_count;
  char string[1024];
  int size;
  
  if (current) {
    vset_count(current,&n_count,&e_count);
    if (n_count>max_lev_count) max_lev_count=n_count;
    size = bn_int2string(string,sizeof string,&e_count);
    if(size >= (ssize_t)sizeof string) Fatal(1,error,"Error converting number to string");
    Warning(info,"level %d has %s states ( %ld nodes )",level,string,n_count);
    bn_clear(&e_count);
  }
  
  vset_count(visited,&n_count,&e_count);
  if (n_count>max_vis_count) max_vis_count=n_count;
  size = bn_int2string(string,sizeof string,&e_count);
  if(size >= (ssize_t)sizeof string) Fatal(1,error,"Error converting number to string");
  Warning(info,"visited %d has %s states ( %ld nodes )",level,string,n_count);
  bn_clear(&e_count);
  if (RTverbosity >= 2) {
    int i;
    fprintf(stderr,"transition caches (grp,nds,elts): ");
    for (i=0;i<nGrps;i++) {
      vrel_count(group_next[i],&n_count,&e_count);
      size = bn_int2string(string,sizeof string,&e_count);
      if(size >= (ssize_t)sizeof string) Fatal(1,error,"Error converting number to string");
      fprintf(stderr,"( %d %ld %s ) ",i,n_count,string);
      bn_clear(&e_count);
      if (n_count>max_trans_count) max_trans_count=n_count;
    }
    fprintf(stderr,"\ngroup explored    (grp,nds,elts): ");
    for (i=0;i<nGrps;i++) {
      vset_count(group_explored[i],&n_count,&e_count);
      size = bn_int2string(string,sizeof string,&e_count);
      if(size >= (ssize_t)sizeof string) Fatal(1,error,"Error converting number to string");
      fprintf(stderr,"( %d %ld %s ) ",i,n_count,string);
      bn_clear(&e_count);
      if (n_count>max_grp_count) max_grp_count=n_count;
    }
    fprintf(stderr,"\n");
  }
}

static void final_stat_reporting(vset_t visited) {
  bn_int_t e_count;
  long n_count;
  char string[1024];
  int size;

  vset_count(visited,&n_count,&e_count);
  size = bn_int2string(string,sizeof string,&e_count);
  if(size >= (ssize_t)sizeof string) Fatal(1,error,"Error converting number to string");
  fprintf(stderr,"state space has %s states\n",string);
  bn_clear(&e_count);
  if (max_lev_count==0)
    fprintf(stderr,"( %ld final BDD nodes; %ld peak nodes )\n",
	    n_count,max_vis_count);
  else
    fprintf(stderr,"( %ld final BDD nodes; %ld peak nodes; %ld peak nodes per level )\n",
	    n_count,max_vis_count,max_lev_count);
  if (RTverbosity >=2)
    fprintf(stderr,"( peak transition cache: %ld nodes; peak group explored: %ld nodes )\n",
	    max_trans_count,max_grp_count);
}

static void reach_bfs(){
	int level,i;
	long eg_count=0;
	long next_count=0;

	level=0;
	vset_t current_level=vset_create(domain,0,NULL);
	vset_t next_level=vset_create(domain,0,NULL);
	vset_t temp=vset_create(domain,0,NULL);
	vset_t deadlocks=dlk_detect?vset_create(domain,0,NULL):NULL;
	vset_t dlk_temp=dlk_detect?vset_create(domain,0,NULL):NULL;

	vset_t *levels = NULL;
	int max_levels = 0;

	vset_copy(current_level,visited);
	for(;;){
		if(vset_is_empty(current_level)) break;
          if (trc_output) {
	    if (level == max_levels) {
	      max_levels += 1024;
	      levels = RTrealloc(levels, max_levels * sizeof(vset_t));
	      for(int i=level;i<max_levels;i++)
		levels[i] = vset_create(domain,0,NULL);
	    }
	    vset_copy(levels[level],current_level);
	  }
	        stats_and_progress_report(current_level,visited,level);
		level++;
		for(i=0;i<nGrps;i++){
			if (RTverbosity >= 2) fprintf(stderr,"\rexploring group %4d/%d",i+1,nGrps);
			expand_group_next(i,current_level);
			eg_count++;
		}
		if (RTverbosity >= 2) fprintf(stderr,"\rexploration complete             \n");
		vset_clear(next_level);
		if (dlk_detect) vset_copy(deadlocks,current_level);
		for(i=0;i<nGrps;i++){
			if (RTverbosity >= 2) fprintf(stderr,"\rlocal next %4d/%d",i+1,nGrps);
			next_count++;
			vset_next(temp,current_level,group_next[i]);
			if (dlk_detect) {
				vset_prev(dlk_temp,temp,group_next[i]);
				vset_minus(deadlocks,dlk_temp);
				vset_clear(dlk_temp);
			}
			vset_minus(temp,visited);
			vset_union(next_level,temp);
			vset_clear(temp);
		}
		if (RTverbosity >= 2) fprintf(stderr,"\rlocal next complete       \n");
		if (dlk_detect) deadlock_check(deadlocks);
		vset_union(visited,next_level);
		vset_copy(current_level,next_level);
	}
	Warning(info,"Exploration took %ld group checks and %ld next state calls",eg_count,next_count);
	if (dlk_detect)
	  Warning(info,"No deadlocks found");
}

void reach_bfs2(){
	int level,i;
	long eg_count=0;
	long next_count=0;

	level=0;
	vset_t old_vis=vset_create(domain,0,NULL);
	vset_t temp=vset_create(domain,0,NULL);
	vset_t deadlocks=dlk_detect?vset_create(domain,0,NULL):NULL;
	vset_t dlk_temp=dlk_detect?vset_create(domain,0,NULL):NULL;

	vset_t *levels = NULL;
	int max_levels = 0;

	for(;;){
          if (trc_output) {
	    if (level == max_levels) {
	      max_levels += 1024;
	      levels = RTrealloc(levels, max_levels * sizeof(vset_t));
	      for(int i=level;i<max_levels;i++)
		levels[i] = vset_create(domain,0,NULL);
	    }
	    vset_copy(levels[level],visited);
	    if (level != 0) vset_minus(levels[level],levels[level - 1]);
	  }
		vset_copy(old_vis,visited);
		stats_and_progress_report(NULL,visited,level);
		level++;
		for(i=0;i<nGrps;i++){
			if (RTverbosity >= 2) fprintf(stderr,"\rexploring group %4d/%d",i+1,nGrps);
			expand_group_next(i,visited);
			eg_count++;
		}
		if (RTverbosity >= 2) fprintf(stderr,"\rexploration complete             \n");
		if (dlk_detect) vset_copy(deadlocks,visited);
		for(i=0;i<nGrps;i++){
			if (RTverbosity >= 2) fprintf(stderr,"\rlocal next %4d/%d",i+1,nGrps);
			next_count++;
			vset_next(temp,old_vis,group_next[i]);
			vset_union(visited,temp);
			if (dlk_detect) {
				vset_prev(dlk_temp,temp,group_next[i]);
				vset_minus(deadlocks,dlk_temp);
				vset_clear(dlk_temp);
			}
		}
		if (RTverbosity >= 2) fprintf(stderr,"\rlocal next complete       \n");
		if (dlk_detect) deadlock_check(deadlocks);
		if (vset_equal(visited,old_vis)) break;
	}
	Warning(info,"Exploration took %ld group checks and %ld next state calls",eg_count,next_count);
	if (dlk_detect)
	  Warning(info,"No deadlocks found");
}

void reach_sat(){
	Fatal(1,error,"Saturation not implemented yet");
}

void reach_chain(){
	int level,i;
	long eg_count=0;
	long next_count=0;

	level=0;
	vset_t old_vis=vset_create(domain,0,NULL);
	vset_t temp=vset_create(domain,0,NULL);
	vset_t deadlocks=dlk_detect?vset_create(domain,0,NULL):NULL;
	vset_t dlk_temp=dlk_detect?vset_create(domain,0,NULL):NULL;

	vset_t *levels = NULL;
        int max_levels = 0;

	for(;;){
          if (trc_output) {
	    if (level == max_levels) {
	      max_levels += 1024;
	      levels = RTrealloc(levels, max_levels * sizeof(vset_t));
	      for(int i=level;i<max_levels;i++)
		levels[i] = vset_create(domain,0,NULL);
	    }
	    vset_copy(levels[level],visited);
	    if (level != 0) vset_minus(levels[level],levels[level - 1]);
	  }
		vset_copy(old_vis,visited);
		stats_and_progress_report(NULL,visited,level);
		level++;
		if (dlk_detect) vset_copy(deadlocks,visited);
		for(i=0;i<nGrps;i++){
			if (RTverbosity >= 2) fprintf(stderr,"\rgroup %4d/%d",i+1,nGrps);
			expand_group_next(i,visited);
			eg_count++;
			next_count++;
			vset_next(temp,visited,group_next[i]);
			vset_union(visited,temp);
			if (dlk_detect) {
				vset_prev(dlk_temp,temp,group_next[i]);
				vset_minus(deadlocks,dlk_temp);
				vset_clear(dlk_temp);
			}
		}
		if (RTverbosity >= 2) fprintf(stderr,"\rround %d complete       \n",level);
		if (dlk_detect) deadlock_check(deadlocks); // no deadlocks in old_vis.
		if (vset_equal(visited,old_vis)) break;
	}
	Warning(info,"Exploration took %ld group checks and %ld next state calls",eg_count,next_count);
	if (dlk_detect)
	  Warning(info,"No deadlocks found");
}

static FILE* table_file;

static int table_count=0;

typedef struct {
	model_t model;
	int group;
	int *src;
} output_context;

static void etf_edge(void*context,int*labels,int*dst){
	output_context* ctx=(output_context*)context;
	table_count++;
	int k=0;
	for(int i=0;i<N;i++) {
		if (dm_is_set(GBgetDMInfo(ctx->model), ctx->group, i)) {
			fprintf(table_file," %d/%d",ctx->src[k],dst[k]);
			k++;
		} else {
			fprintf(table_file," *");
		}
	}
	for(int i=0;i<eLbls;i++) {
		fprintf(table_file," %d",labels[i]);
	}
	fprintf(table_file,"\n");
}

static void enum_edges(void*context,int *src){
	output_context* ctx=(output_context*)context;
	ctx->src=src;
	GBgetTransitionsShort(model,ctx->group,ctx->src,etf_edge,context);
}

typedef struct {
	int mapno;
	int len;
	int*used;
} map_context;


static void enum_map(void*context,int *src){
	map_context*ctx=(map_context*)context;
	int val=GBgetStateLabelShort(model,ctx->mapno,src);
	int k=0;
	for(int i=0;i<N;i++){
		if (k<ctx->len && ctx->used[k]==i){
			fprintf(table_file,"%d ",src[k]);
			k++;
		} else {
			fprintf(table_file,"* ");
		}
	}
	fprintf(table_file,"%d\n",val);
}


void do_output(){
	eLbls=lts_type_get_edge_label_count(ltstype);
	int state[N];
	GBgetInitialState(model,state);
	table_file=fopen(etf_output,"w");
	if(!table_file){
	    FatalCall(1,error,"could not open %s",etf_output);
	}
	fprintf(table_file,"begin state\n");
	for(int i=0;i<N;i++){
                fprint_ltsmin_ident(table_file,lts_type_get_state_name(ltstype,i));
                fprintf(table_file,":");
                fprint_ltsmin_ident(table_file,lts_type_get_state_type(ltstype,i));
		fprintf(table_file,(i==(N-1))?"\n":" ");
	}
	fprintf(table_file,"end state\n");
	fprintf(table_file,"begin edge\n");
	for(int i=0;i<eLbls;i++){
            fprint_ltsmin_ident(table_file,lts_type_get_edge_label_name(ltstype,i));
            fprintf(table_file,":");
            fprint_ltsmin_ident(table_file,lts_type_get_edge_label_type(ltstype,i));
            fprintf(table_file,(i==(eLbls-1))?"\n":" ");
	}
	fprintf(table_file,"end edge\n");
	fprintf(table_file,"begin init\n");
	for(int i=0;i<N;i++) {
		fprintf(table_file,"%d%s",state[i],(i==(N-1))?"\n":" ");
	}
	fprintf(table_file,"end init\n");
	for(int g=0;g<nGrps;g++){
		output_context ctx;
		ctx.model = model;
		ctx.group=g;
		fprintf(table_file,"begin trans\n");
		vset_enum(group_explored[g],enum_edges,&ctx);
		fprintf(table_file,"end trans\n");
	}
	Warning(info,"Symbolic tables have %d reachable transitions",table_count);
	matrix_t *sl_info = GBgetStateLabelInfo(model);
	sLbls = dm_nrows(sl_info);
	if (dm_nrows(sl_info) != lts_type_get_state_label_count(ltstype))
		Warning(error,"State label count mismatch!");
	for(int i=0;i<sLbls;i++){
		int len = dm_ones_in_row(sl_info, i);
		int used[len];
		// get projection
		for (int pi = 0, pk = 0; pi < dm_ncols (sl_info); pi++) {
			if (dm_is_set (sl_info, i, pi)) {
				used[pk++] = pi;
			}
		}

		vset_t patterns=vset_create(domain,len,used);
		vset_project(patterns,visited);
		map_context ctx;
		ctx.mapno=i;
		ctx.len=len;
		ctx.used=used;
		fprintf(table_file,"begin map ");
                fprint_ltsmin_ident(table_file,lts_type_get_state_label_name(ltstype,i));
                fprintf(table_file,":");
                fprint_ltsmin_ident(table_file,lts_type_get_state_label_type(ltstype,i));
                fprintf(table_file,"\n");
		vset_enum(patterns,enum_map,&ctx);
		fprintf(table_file,"end map\n");
		vset_clear(patterns); // Should be vset_destroy, which doesn't exist.
	}
	int type_count=lts_type_get_type_count(ltstype);
	for(int i=0;i<type_count;i++){
		Warning(info,"dumping type %s",lts_type_get_type(ltstype,i));
		fprintf(table_file,"begin sort ");
                fprint_ltsmin_ident(table_file,lts_type_get_type(ltstype,i));
                fprintf(table_file,"\n");
		int values=GBchunkCount(model,i);
		for(int j=0;j<values;j++){
			chunk c=GBchunkGet(model,i,j);
			size_t len=c.len*2+3;
			char str[len];
			chunk2string(c,len,str);
			fprintf(table_file,"%s\n",str);
		}
		fprintf(table_file,"end sort\n");
	}
	fclose(table_file);
}

int main(int argc, char *argv[]){
	char* files[2];
	RTinitPopt(&argc,&argv,options,1,2,files,NULL,"<model> [<etf>]",
		"Perform a symbolic reachability analysis of <model>\n"
		"The optional output of this analysis is an ETF representation of the input\n"
		"\nOptions");
	etf_output=files[1];
	Warning(info,"opening %s",files[0]);
	model=GBcreateBase();
	GBsetChunkMethods(model,new_string_index,NULL,
		(int2chunk_t)SIgetC,(chunk2int_t)SIputC,(get_count_t)SIgetCount);

	GBloadFile(model,files[0],&model);

	if (RTverbosity >=2) {
	  fprintf(stderr,"Dependency Matrix:\n");
	  GBprintDependencyMatrix(stderr,model);
	}

	ltstype=GBgetLTStype(model);
	N=lts_type_get_state_length(ltstype);
	nGrps=dm_nrows(GBgetDMInfo(model));
	domain=vdom_create_default(N);
	visited=vset_create(domain,0,NULL);
	group_next=(vrel_t*)RTmalloc(nGrps*sizeof(vrel_t));
	group_explored=(vset_t*)RTmalloc(nGrps*sizeof(vset_t));
	group_tmp=(vset_t*)RTmalloc(nGrps*sizeof(vset_t));
	for(int i=0;i<nGrps;i++){
		int len = dm_ones_in_row(GBgetDMInfo(model), i);
		// get indices
		int tmp[len];
		// temporary replacement for e_info->indices[i]
		for(int j=0, k=0; j < dm_ncols(GBgetDMInfo(model)); j++) {
			if (dm_is_set(GBgetDMInfo(model), i,j))
				tmp[k++] = j;
		}

		group_next[i]=vrel_create(domain,len,tmp);
		group_explored[i]=vset_create(domain,len,tmp);
		group_tmp[i]=vset_create(domain,len,tmp);
	}
	Warning(info,"length is %d, there are %d groups",N,nGrps);
	int src[N];
	GBgetInitialState(model,src);
	vset_add(visited,src);
	Warning(info,"got initial state");
	mytimer_t timer=SCCcreateTimer();
	SCCstartTimer(timer);
	switch(strategy){
	case BFS:
		reach_bfs();
		break;
	case BFS2:
		reach_bfs2();
		break;
	case Chain:
		reach_chain();
		break;
	}
	SCCstopTimer(timer);
	SCCreportTimer(timer,"reachability took");
	final_stat_reporting(visited);
	if (etf_output) {
		SCCresetTimer(timer);
		SCCstartTimer(timer);
		do_output();
		SCCstopTimer(timer);
		SCCreportTimer(timer,"writing output took");
	}
	return 0;
}
