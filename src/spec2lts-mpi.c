#include "config.h"
#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <mpi.h>

#include "fast_hash.h"
#include "chunk-table.h"
#ifdef MCRL
#include "mcrl-greybox.h"
#endif
#ifdef MCRL2
#include "mcrl2-greybox.h"
#endif
#include "treedbs.h"
#include "stream.h"
#include "options.h"
#include "runtime.h"
#include "archive.h"
#include "mpi_io_stream.h"
#include "mpi_ram_raf.h"
#include "stringindex.h"
#include "dynamic-array.h"
#include "mpi-event-loop.h"

/********************************************************************************************/

typedef struct mpi_index_pool {
	MPI_Comm comm;
	event_queue_t queue;
	int me;
	int nodes;
	int next_tag;
	int max_chunk;
} *mpi_index_pool_t;

typedef struct mpi_index {
	mpi_index_pool_t pool;
	int tag;
	int owner;
	string_index_t index;
	char *recv_buf;
	void *wanted;
	int w_len;
	int looking;
} *mpi_index_t;

static void mpi_index_handler(void* context,MPI_Status *status){
	mpi_index_t index=(mpi_index_t)context;
	int len;
	MPI_Get_count(status,MPI_CHAR,&len);
	if (index->pool->me==index->owner) {
		int res=SIlookupC(index->index,index->recv_buf,len);
		if (res==SI_INDEX_FAILED) {
			res=SIputC(index->index,index->recv_buf,len);
			int todo=index->pool->nodes-1;
			for(int i=0;i<index->pool->nodes;i++) if (i!=index->owner) {
				event_Isend(index->pool->queue,index->recv_buf,len,MPI_CHAR,
					i,index->tag,index->pool->comm,event_decr,&todo);
			}
			event_while(index->pool->queue,&todo);
		}
	} else {
		int res=SIputC(index->index,index->recv_buf,len);
		if (index->wanted) {
			if (len==index->w_len && memcmp(index->recv_buf,index->wanted,len)==0){
				index->looking=0;
			}
		} else {
			if (index->looking==res+1){
				index->looking=0;
			}
		}
	}
	event_Irecv(index->pool->queue,index->recv_buf,index->pool->max_chunk,MPI_CHAR,
		MPI_ANY_SOURCE,index->tag,index->pool->comm,mpi_index_handler,context);
}

mpi_index_pool_t mpi_index_pool_create(MPI_Comm comm,event_queue_t queue,int max_chunk){
	mpi_index_pool_t pool=(mpi_index_pool_t)RTmalloc(sizeof(struct mpi_index_pool));
	MPI_Comm_dup(comm,&pool->comm);
	pool->queue=queue;
	MPI_Comm_size(pool->comm,&pool->nodes);
        MPI_Comm_rank(pool->comm,&pool->me);
	pool->next_tag=1;
	pool->max_chunk=max_chunk;
	return pool;
}

void* mpi_newmap(void*newmap_context){
	mpi_index_pool_t pool=(mpi_index_pool_t)newmap_context;
	mpi_index_t index=(mpi_index_t)RTmalloc(sizeof(struct mpi_index));
	index->pool=pool;
	index->tag=pool->next_tag;
	pool->next_tag++;
	index->owner=(index->tag)%(pool->nodes);
	index->index=SIcreate();
	index->wanted=NULL;
	index->looking=0;
	index->recv_buf=RTmalloc(pool->max_chunk);
	event_Irecv(index->pool->queue,index->recv_buf,index->pool->max_chunk,MPI_CHAR,
		MPI_ANY_SOURCE,index->tag,index->pool->comm,mpi_index_handler,index);
	return index;
}

int mpi_chunk2int(void*map,void*chunk,int len){
	mpi_index_t index=(mpi_index_t)map;
	int res=SIlookupC(index->index,chunk,len);
	if (res==SI_INDEX_FAILED) {
		if (index->pool->me==index->owner) {
			res=SIputC(index->index,chunk,len);
			int todo=index->pool->nodes-1;
			for(int i=0;i<index->pool->nodes;i++) if (i!=index->owner) {
				event_Isend(index->pool->queue,chunk,len,MPI_CHAR,
					i,index->tag,index->pool->comm,event_decr,&todo);
			}
			event_while(index->pool->queue,&todo);
		} else {
			index->wanted=chunk;
			index->w_len=len;
			index->looking=1;
			event_Isend(index->pool->queue,chunk,len,MPI_CHAR,
				index->owner,index->tag,index->pool->comm,NULL,NULL);
			event_while(index->pool->queue,&index->looking);
			res=SIlookupC(index->index,chunk,len);
		}
	}
	return res;
}

void* mpi_int2chunk(void*map,int idx,int*len){
	mpi_index_t index=(mpi_index_t)map;
	if (index->pool->me!=index->owner && SIgetCount(index->index)<=idx){
		index->looking=idx+1;
		event_while(index->pool->queue,&index->looking);
	}
	return SIgetC(index->index,idx,len);
}

int mpi_get_count(void*map){
	mpi_index_t index=(mpi_index_t)map;
	return SIgetCount(index->index);
}

/********************************************************************************************/

#define MAX_PARAMETERS 256
#define MAX_TERM_LEN 5000

static mpi_index_pool_t index_pool;
static archive_t arch;
static int verbosity=1;
static char *outputarch=NULL;
static int write_lts=1;
static int nice_value=0;
static int plain=0;
static int find_dlk=0;


static event_queue_t mpi_queue;
static event_barrier_t barrier;

struct option options[]={
	{"",OPT_NORMAL,NULL,NULL,NULL,
		"usage: mpirun <nodespec> inst-mpi options file ...",NULL,NULL,NULL},
	{"-v",OPT_NORMAL,inc_int,&verbosity,NULL,"increase the level of verbosity",NULL,NULL,NULL},
	{"-q",OPT_NORMAL,reset_int,&verbosity,NULL,"be silent",NULL,NULL,NULL},
	{"-help",OPT_NORMAL,usage,NULL,NULL,
		"print this help message",NULL,NULL,NULL},
/* Deadlocks can be found, but traces cannot be printed yet.
	{"-dlk",OPT_NORMAL,set_int,&find_dlk,NULL,
		"If a deadlock is found, a trace to the deadlock will be",
		"printed and the exploration will be aborted.",
		"using this option implies -nolts",NULL},
*/
	{"-out",OPT_REQ_ARG,assign_string,&outputarch,"-out <archive>",
		"Specifiy the name of the output archive.",
		"This will be a pattern archive if <archive> contains %s",
		"and a GCF archive otherwise",NULL},
	{"-nolts",OPT_NORMAL,reset_int,&write_lts,NULL,
		"disable writing of the LTS",NULL,NULL,NULL},
	{"-nice",OPT_REQ_ARG,parse_int,&nice_value,"-nice <val>",
		"all workers will set nice to <val>",
		"useful when running on other people's workstations",NULL,NULL},
	{"-plain",OPT_NORMAL,set_int,&plain,NULL,
		"disable compression of the output",NULL,NULL,NULL},
	{0,0,0,0,0,0,0,0,0}
};

static char who[24];
static int mpi_nodes,mpi_me;

static stream_t *output_src=NULL;
static stream_t *output_label=NULL;
static stream_t *output_dest=NULL;

static int *tcount;
static int *src;
static int size;

static uint32_t chk_base=0;

static inline void adjust_owner(int32_t *state){
	chk_base=SuperFastHash((char*)state,size*4,0);
	//Warning(info,"chkbase=%x",chk_base);
	//for (int i=0;i<size;i++) fprintf(stderr,"%3d",state[i]);
	//fprintf(stderr,"\n");
}

static inline int owner(int32_t *state){
	uint32_t hash=chk_base^SuperFastHash((char*)state,size*4,0);
	return (hash%mpi_nodes);
}

#define POOL_SIZE 16

struct work_msg {
	int src_worker;
	int src_number;
	int label;
	int dest[MAX_PARAMETERS];
} work_send_buf[POOL_SIZE],work_recv_buf[POOL_SIZE];
static int work_send_used[POOL_SIZE];
static int work_send_next=0;

#define BARRIER_TAG 12
#define EXPLORE_IDLE_TAG 11

#define STATE_FOUND_TAG 10

#define LEAF_CHUNK_TAG 9
#define LEAF_INT_TAG 8

#define ACT_CHUNK_TAG 5
#define ACT_INT_TAG 4

#define WORK_TAG 3
#define WORK_SIZE (sizeof(struct work_msg)-(MAX_PARAMETERS-size)*sizeof(int))
//define WORK_SIZE sizeof(struct work_msg)

static idle_detect_t work_counter;

static struct state_found_msg {
	int reason; // -1: deadlock n>=0: action n is enabled and matches a wanted action.
	int segment;
	int offset;
} state_found_buf;

static int deadlock_count=0;

static void state_found_handler(void* context,MPI_Status *status){
	(void)context;(void)status;
	deadlock_count++;
	if (state_found_buf.reason==-1) {
		Warning(info,"deadlock %d found: segment %d, offset %d",
			deadlock_count,state_found_buf.segment,state_found_buf.offset);
	}
	event_idle_recv(work_counter);
	event_Irecv(mpi_queue,&state_found_buf,sizeof(struct state_found_msg),MPI_CHAR,
		MPI_ANY_SOURCE,STATE_FOUND_TAG,MPI_COMM_WORLD,state_found_handler,NULL);
}

static void state_found_init(){
	event_Irecv(mpi_queue,&state_found_buf,sizeof(struct state_found_msg),MPI_CHAR,
		MPI_ANY_SOURCE,STATE_FOUND_TAG,MPI_COMM_WORLD,state_found_handler,NULL);
}

static void deadlock_found(int segment,int offset){
	struct state_found_msg msg;
	msg.reason=-1;
	msg.segment=segment;
	msg.offset=offset;
	event_Send(mpi_queue,&msg,sizeof(struct state_found_msg),MPI_CHAR,
		0,STATE_FOUND_TAG,MPI_COMM_WORLD);
	event_idle_send(work_counter);
}

/*
static string_index_t act_db;
static int next_act=0;
static int int_buf_act[1];
static char chunk_buf_act[MAX_TERM_LEN+1];

static string_index_t leaf_db;
static int next_leaf=0;
static int int_buf_leaf[1];
static char chunk_buf_leaf[MAX_TERM_LEN+1];

static int chunk2int(string_index_t term_db,int chunk_tag,int int_tag,size_t len,void* chunk){
	//struct timeval tv1,tv2;
	//gettimeofday(&tv1,NULL);
	if (mpi_me==0) {
		((char*)chunk)[len]=0;
		return SIput(term_db,chunk);
	} else {
		int idx;
		((char*)chunk)[len]=0;
		//Warning(info,"requesting chunk %s",chunk);
		MPI_Status status;
		event_Send(mpi_queue,chunk,len,MPI_CHAR,0,chunk_tag,MPI_COMM_WORLD);
		event_Recv(mpi_queue,&idx,1,MPI_INT,0,int_tag,MPI_COMM_WORLD,&status);
		//Warning(info,"got chunk %s: %d",chunk,idx);
		return idx;
	}
	//gettimeofday(&tv2,NULL);
	//long long int usec=(tv2.tv_sec-tv1.tv_sec)*1000000LL + tv2.tv_usec - tv1.tv_usec;
	//Warning(info,"chunk2int took %lld us",usec);
}

static void chunk_call(string_index_t term_db,int chunk_tag,int int_tag,int next_cb,chunk_add_t cb,void* context){
	//struct timeval tv1,tv2;
	//gettimeofday(&tv1,NULL);
	if (mpi_me==0) {
		char*s=SIget(term_db,next_cb);
		int len=strlen(s);
		cb(context,len,s);
	} else {
		MPI_Status status;
		char chunk[MAX_TERM_LEN+1];
		//Warning(info,"requesting int %d",next_cb);
		event_Send(mpi_queue,&next_cb,1,MPI_INT,0,int_tag,MPI_COMM_WORLD);
		event_Recv(mpi_queue,&chunk,MAX_TERM_LEN,MPI_CHAR,0,chunk_tag,MPI_COMM_WORLD,&status);
		int len;
		MPI_Get_count(&status,MPI_CHAR,&len);
		chunk[len]=0;
		//Warning(info,"got int %d; %s",next_cb,chunk);
		cb(context,len,chunk);
	}
	//gettimeofday(&tv2,NULL);
	//long long int usec=(tv2.tv_sec-tv1.tv_sec)*1000000LL + tv2.tv_usec - tv1.tv_usec;
	//Warning(info,"cunk_call took %lld us",usec);
}


chunk_table_t CTcreate(char *name){
	if (!strcmp(name,"action")) {
		return (void*)1;
	}
	if (!strcmp(name,"leaf")) {
		return (void*)2;
	}
	Fatal(1,error,"CT support incomplete cannot deal with table %s",name);
	return NULL;
}

void CTsubmitChunk(chunk_table_t table,size_t len,void* chunk,chunk_add_t cb,void* context){
	//struct timeval tv1,tv2;
	//gettimeofday(&tv1,NULL);
	if(table==(void*)1){
		int res=chunk2int(act_db,ACT_CHUNK_TAG,ACT_INT_TAG,len,chunk);
		while(next_act<=res){
			chunk_call(act_db,ACT_CHUNK_TAG,ACT_INT_TAG,next_act,cb,context);
			next_act++;
		}
	} else {
		int res=chunk2int(leaf_db,LEAF_CHUNK_TAG,LEAF_INT_TAG,len,chunk);
		while(next_leaf<=res){
			chunk_call(leaf_db,LEAF_CHUNK_TAG,LEAF_INT_TAG,next_leaf,cb,context);
			next_leaf++;
		}
	}
	//gettimeofday(&tv2,NULL);
	//long long int usec=(tv2.tv_sec-tv1.tv_sec)*1000000LL + tv2.tv_usec - tv1.tv_usec;
	//static long long int max=0;
	//Warning(info,"CTsubmitChunk took %lld us",usec);
	//if (usec>max) {
	//	max=usec;
	//}
}

void CTupdateTable(chunk_table_t table,uint32_t wanted,chunk_add_t cb,void* context){
	//struct timeval tv1,tv2;
	//gettimeofday(&tv1,NULL);
	if(table==(void*)1){
		while(next_act<=(int)wanted){
			chunk_call(act_db,ACT_CHUNK_TAG,ACT_INT_TAG,next_act,cb,context);
			next_act++;
		}
	} else {
		while(next_leaf<=(int)wanted){
			chunk_call(leaf_db,LEAF_CHUNK_TAG,LEAF_INT_TAG,next_leaf,cb,context);
			next_leaf++;
		}
	}
	//gettimeofday(&tv2,NULL);
	//long long int usec=(tv2.tv_sec-tv1.tv_sec)*1000000LL + tv2.tv_usec - tv1.tv_usec;
	//static long long int max=0;
	//Warning(info,"CTupdateTable took %lld us",usec);
	//if (usec>max) {
	//	max=usec;
	//}
}

static void int_handler(void *context,MPI_Status *status){
	//Warning(info,"int request");
	int chunk_tag,int_tag;
	string_index_t term_db;
	int *int_buf;
	if (context==act_db){
		chunk_tag=ACT_CHUNK_TAG;
		int_tag=ACT_INT_TAG;
		term_db=act_db;
		int_buf=int_buf_act;
	} else {
		chunk_tag=LEAF_CHUNK_TAG;
		int_tag=LEAF_INT_TAG;
		term_db=leaf_db;
		int_buf=int_buf_leaf;
	}
	char *s=SIget(term_db,int_buf[0]);
	int len=strlen(s);
	event_Send(mpi_queue,s,len,MPI_CHAR,status->MPI_SOURCE,chunk_tag,MPI_COMM_WORLD);
	event_Irecv(mpi_queue,int_buf,1,MPI_INT,MPI_ANY_SOURCE,
				int_tag,MPI_COMM_WORLD,int_handler,context);
}

static void chunk_handler(void* context,MPI_Status *status){
	//Warning(info,"chunk request");
	int chunk_tag,int_tag;
	string_index_t term_db;
	char* chunk_buf;
	if (context==act_db){
		//Warning(info,"action");
		chunk_tag=ACT_CHUNK_TAG;
		int_tag=ACT_INT_TAG;
		term_db=act_db;
		chunk_buf=chunk_buf_act;
	} else {
		//Warning(info,"leaf");
		chunk_tag=LEAF_CHUNK_TAG;
		int_tag=LEAF_INT_TAG;
		term_db=leaf_db;
		chunk_buf=chunk_buf_leaf;
	}
	int len;
	MPI_Get_count(status,MPI_CHAR,&len);
	chunk_buf[len]=0;
	//Warning(info,"chunk request %s",chunk_buf);
	int ii=SIput(term_db,chunk_buf);
	event_Send(mpi_queue,&ii,1,MPI_INT,status->MPI_SOURCE,int_tag,MPI_COMM_WORLD);
	event_Irecv(mpi_queue,chunk_buf,MAX_TERM_LEN,MPI_CHAR,MPI_ANY_SOURCE,
				chunk_tag,MPI_COMM_WORLD,chunk_handler,context);	
}

static void map_server_init(){
	if (mpi_me==0) {
		act_db=SIcreate();
		event_Irecv(mpi_queue,chunk_buf_act,MAX_TERM_LEN,MPI_CHAR,MPI_ANY_SOURCE,
				ACT_CHUNK_TAG,MPI_COMM_WORLD,chunk_handler,act_db);	
		event_Irecv(mpi_queue,int_buf_act,1,MPI_INT,MPI_ANY_SOURCE,
				ACT_INT_TAG,MPI_COMM_WORLD,int_handler,act_db);
		leaf_db=SIcreate();
		event_Irecv(mpi_queue,chunk_buf_leaf,MAX_TERM_LEN,MPI_CHAR,MPI_ANY_SOURCE,
				LEAF_CHUNK_TAG,MPI_COMM_WORLD,chunk_handler,leaf_db);	
		
		event_Irecv(mpi_queue,int_buf_leaf,1,MPI_INT,MPI_ANY_SOURCE,
				LEAF_INT_TAG,MPI_COMM_WORLD,int_handler,leaf_db);
	}
}
*/

/********************************************************/

struct src_info {
	int seg;
	int ofs;
};

static void callback(void*context,int*labels,int*dst){
	(void)context;
	int i,who;

	//struct timeval tv1,tv2;
	//gettimeofday(&tv1,NULL);
	event_while(mpi_queue,&work_send_used[work_send_next]);
	work_send_used[work_send_next]=1;
	work_send_buf[work_send_next].src_worker=((struct src_info*)context)->seg;
	work_send_buf[work_send_next].src_number=((struct src_info*)context)->ofs;
	work_send_buf[work_send_next].label=labels[0];
	for(i=0;i<size;i++){
		work_send_buf[work_send_next].dest[i]=dst[i];
	}
	who=owner(work_send_buf[work_send_next].dest);
	event_Isend(mpi_queue,&work_send_buf[work_send_next],WORK_SIZE,MPI_CHAR,who,
			WORK_TAG,MPI_COMM_WORLD,event_decr,&work_send_used[work_send_next]);
	event_idle_send(work_counter);
	work_send_next=(work_send_next+1)%POOL_SIZE;
	//gettimeofday(&tv2,NULL);
	//long long int usec=(tv2.tv_sec-tv1.tv_sec)*1000000LL + tv2.tv_usec - tv1.tv_usec;
	//static long long int max=0;
	//if (usec>max) {
	//	Warning(info,"callback took %lld us",usec);
	//	max=usec;
	//}
}


static char name[100];

static array_manager_t state_man=NULL;
static uint32_t *parent_ofs=NULL;
static uint16_t *parent_seg=NULL;
static long long int explored,visited,transitions;

static void in_trans_handler(void*context,MPI_Status *status){
#define work_recv ((struct work_msg*)context)
	(void)status;
	int temp[2*MAX_PARAMETERS];
	event_idle_recv(work_counter);
	for(int i=0;i<size;i++){
		temp[size+i]=work_recv->dest[i];
	}
	int who=owner(work_recv->dest);
	if (who != mpi_me) {
		Fatal(1,error,"state does not belong to me");
	}
	Fold(temp);
	if (temp[1]>=visited) {
		visited=temp[1]+1;
		if(find_dlk){
			ensure_access(state_man,temp[1]);
			parent_seg[temp[1]]=work_recv->src_worker;
			parent_ofs[temp[1]]=work_recv->src_number;
		}
	}
	if (write_lts){
		DSwriteU32(output_src[work_recv->src_worker],work_recv->src_number);
		DSwriteU32(output_label[work_recv->src_worker],work_recv->label);
		DSwriteU32(output_dest[work_recv->src_worker],temp[1]);
	}
	tcount[work_recv->src_worker]++;
	transitions++;
	//if (transitions%1000==0) {
	//	Warning(info,"%lld transitions %lld explored",transitions,explored);
	//}
	event_Irecv(mpi_queue,work_recv,WORK_SIZE,MPI_CHAR,MPI_ANY_SOURCE,
			WORK_TAG,MPI_COMM_WORLD,in_trans_handler,work_recv);
#undef work_recv
}

static void io_trans_init(){
	for(int i=0;i<POOL_SIZE;i++){
		event_Irecv(mpi_queue,&work_recv_buf[i],WORK_SIZE,MPI_CHAR,MPI_ANY_SOURCE,
			WORK_TAG,MPI_COMM_WORLD,in_trans_handler,&work_recv_buf[i]);
		work_send_used[i]=0;
	}
}

/*
void *new_string_index(void* context){
	(void)context;
	Warning(info,"creating a new string index");
	return SIcreate();
}
*/

int main(int argc, char*argv[]){
	int temp[2*MAX_PARAMETERS];
	long long int global_visited,global_explored,global_transitions;
	void *bottom=(void*)&argc;

        MPI_Init(&argc, &argv);
	MPI_Errhandler_set(MPI_COMM_WORLD,MPI_ERRORS_ARE_FATAL);
        MPI_Comm_size(MPI_COMM_WORLD, &mpi_nodes);
        MPI_Comm_rank(MPI_COMM_WORLD, &mpi_me);
	sprintf(who,"inst-mpi(%2d)",mpi_me);
	RTinit(argc,&argv);
	set_label(who);
	mpi_queue=event_queue();
	state_found_init();
	work_counter=event_idle_create(mpi_queue,MPI_COMM_WORLD,EXPLORE_IDLE_TAG);
	barrier=event_barrier_create(mpi_queue,MPI_COMM_WORLD,BARRIER_TAG);

	tcount=(int*)malloc(mpi_nodes*sizeof(int));

	Warning(info,"initializing grey box module");
#ifdef MCRL
	MCRLinitGreybox(argc,argv,bottom);
#endif
#ifdef MCRL2
	MCRL2initGreybox(argc,argv,bottom);
#endif
	if (mpi_me!=0) MPI_Barrier(MPI_COMM_WORLD);
	parse_options(options,argc,argv);
	if (mpi_me==0) MPI_Barrier(MPI_COMM_WORLD);
	Warning(info,"creating model for %s",argv[argc-1]);
	model_t model=GBcreateBase();
	GBsetChunkMethods(model,mpi_newmap,mpi_index_pool_create(MPI_COMM_WORLD,mpi_queue,MAX_TERM_LEN),
		 mpi_int2chunk,mpi_chunk2int,mpi_get_count);
//	GBsetChunkMethods(model,new_string_index,NULL,
//		(int2chunk_t)SIgetC,(chunk2int_t)SIputC,(get_count_t)SIgetCount);
#ifdef MCRL
	MCRLloadGreyboxModel(model,argv[argc-1]);
#endif
#ifdef MCRL2
	MCRL2loadGreyboxModel(model,argv[argc-1]);
#endif
	event_barrier_wait(barrier);
	Warning(info,"model created");
	lts_struct_t ltstype=GBgetLTStype(model);

	/* Initializing according to the options just parsed.
	 */
	if (nice_value) {
		if (mpi_me==0) Warning(info,"setting nice to %d\n",nice_value);
		nice(nice_value);
	}
	/***************************************************/
	if (find_dlk) {
		write_lts=0;
		state_man=create_manager(65536);
		add_array(state_man,&parent_ofs,4);
		add_array(state_man,&parent_seg,2);
	}
	/***************************************************/
	if (mpi_me==0){
		if (write_lts && !outputarch) Fatal(1,error,"please specify the output archive with -out");
	}
	MPI_Barrier(MPI_COMM_WORLD);
	if (write_lts){
		if (strstr(outputarch,"%s")) {
			arch=arch_fmt(outputarch,mpi_io_read,mpi_io_write,prop_get_U32("bs",65536));
		} else {
			uint32_t bs=prop_get_U32("bs",65536);
			uint32_t bc=prop_get_U32("bc",128);
			arch=arch_gcf_create(MPI_Create_raf(outputarch,MPI_COMM_WORLD),bs,bs*bc,mpi_me,mpi_nodes);
		}
	}
	/***************************************************/
	if (write_lts) {
		output_src=(stream_t*)malloc(mpi_nodes*sizeof(FILE*));
		output_label=(stream_t*)malloc(mpi_nodes*sizeof(FILE*));
		output_dest=(stream_t*)malloc(mpi_nodes*sizeof(FILE*));
		for(int i=0;i<mpi_nodes;i++){
			sprintf(name,"src-%d-%d",i,mpi_me);
			output_src[i]=arch_write(arch,name,plain?NULL:"diff32|gzip",1);
			sprintf(name,"label-%d-%d",i,mpi_me);
			output_label[i]=arch_write(arch,name,plain?NULL:"gzip",1);
			sprintf(name,"dest-%d-%d",i,mpi_me);
			output_dest[i]=arch_write(arch,name,plain?NULL:"diff32|gzip",1);
			tcount[i]=0;
		}
	}
	/***************************************************/
	size=ltstype->state_length;
	if (size<2) Fatal(1,error,"there must be at least 2 parameters");
	if (size>MAX_PARAMETERS) Fatal(1,error,"please make src and dest dynamic");
	TreeDBSinit(size,1);
	io_trans_init();
	/***************************************************/
	event_barrier_wait(barrier);
	/***************************************************/
	GBgetInitialState(model,temp+size);
	Warning(info,"initial state computed at %d",mpi_me);
	adjust_owner(temp+size);
	Warning(info,"initial state translated at %d",mpi_me);
	explored=0;
	transitions=0;
	if(mpi_me==0){
		Warning(info,"folding initial state at %d",mpi_me);
		Fold(temp);
		if (temp[1]) Fatal(1,error,"Initial state wasn't assigned state no 0");
		visited=1;
	} else {
		visited=0;
	}
	/***************************************************/
	int level=0;
	for(;;){
		long long int limit=visited;
		level++;
		int lvl_scount=0;
		int lvl_tcount=0;
		//if (mpi_me==0) Warning(info,"exploring level %d",level);
		event_barrier_wait(barrier);
		Warning(info,"exploring level %d",level);
		while(explored<limit){
			temp[1]=explored;
			Unfold(temp);
			src=temp+size;
			struct src_info ctx;
			ctx.seg=mpi_me;
			ctx.ofs=explored;
			explored++;
			int count=GBgetTransitionsAll(model,src,callback,&ctx);;
			if (count<0) Fatal(1,error,"error in GBgetTransitionsAll");
			if (count==0 && find_dlk){
				Warning(info,"deadlock found: %d.%d",ctx.seg,ctx.ofs);
				deadlock_found(ctx.seg,ctx.ofs);
			}
			lvl_scount++;
			lvl_tcount+=count;
			if ((lvl_scount%1000)==0) {
				Warning(info,"generated %d transitions from %d states",
					lvl_tcount,lvl_scount);
			}
			event_yield(mpi_queue);
		}
		Warning(info,"explored %d states and %d transitions",lvl_scount,lvl_tcount);
		event_idle_detect(work_counter);
		MPI_Allreduce(&visited,&global_visited,1,MPI_LONG_LONG,MPI_SUM,MPI_COMM_WORLD);
		MPI_Allreduce(&explored,&global_explored,1,MPI_LONG_LONG,MPI_SUM,MPI_COMM_WORLD);
		MPI_Allreduce(&transitions,&global_transitions,1,MPI_LONG_LONG,MPI_SUM,MPI_COMM_WORLD);
		event_statistics(mpi_queue);
		if (global_visited==global_explored) break;
		if (mpi_me==0) {
			Warning(info,"level %d: %lld explored %lld transitions %lld visited",
				level,global_explored,global_transitions,global_visited);
		}
	}
	if (mpi_me==0) {
		Warning(info,"State space has %d levels %lld states %lld transitions",
			level,global_explored,global_transitions);
	}
	event_barrier_wait(barrier);
	/* State space was succesfully generated. */
	Warning(info,"My share is %lld states and %lld transitions",explored,transitions);
	if (write_lts){
		for(int i=0;i<mpi_nodes;i++){
			DSclose(&output_src[i]);
			DSclose(&output_label[i]);
			DSclose(&output_dest[i]);
		}
	}
	Warning(info,"transition files closed");
	{
	int *temp=NULL;
	int tau;
	stream_t info_s=NULL;
		if (write_lts && mpi_me==0){
			/* It would be better if we didn't create tau if it is non-existent. */
/*
			stream_t ds=arch_write(arch,"TermDB",plain?NULL:"gzip",1);
			int act_count=0;
			for(;;){
				char*s=SIget(act_db,act_count);
				if (s==NULL) break;
				act_count++;
				DSwrite(ds,s,strlen(s));
				DSwrite(ds,"\n",1);
			}
			DSclose(&ds);
			tau=SIlookup(act_db,"tau");
			Warning(info,"%d actions, tau has index %d",act_count,tau);
*/
			/* Start writing the info file. */
			info_s=arch_write(arch,"info",plain?NULL:"",1);
			DSwriteU32(info_s,31);
			DSwriteS(info_s,"generated by instantiator-mpi");
			DSwriteU32(info_s,mpi_nodes);
			DSwriteU32(info_s,0);
			DSwriteU32(info_s,0);
//			DSwriteU32(info_s,act_count);
			DSwriteU32(info_s,tau);
			DSwriteU32(info_s,size-1);
		}
		if (mpi_me==0) temp=(int*)malloc(mpi_nodes*mpi_nodes*sizeof(int));
		MPI_Gather(&explored,1,MPI_INT,temp,1,MPI_INT,0,MPI_COMM_WORLD);
		if (write_lts && mpi_me==0){
			for(int i=0;i<mpi_nodes;i++){
				DSwriteU32(info_s,temp[i]);
			}
		}
		MPI_Gather(tcount,mpi_nodes,MPI_INT,temp,mpi_nodes,MPI_INT,0,MPI_COMM_WORLD);
		if (write_lts && mpi_me==0){
			for(int i=0;i<mpi_nodes;i++){
				for(int j=0;j<mpi_nodes;j++){
					//Warning(info,"%d -> %d : %d",i,j,temp[i+mpi_nodes*j]);
					DSwriteU32(info_s,temp[i+mpi_nodes*j]);
				}
			}
			DSclose(&info_s);
		}
	}
	if (write_lts) arch_close(&arch);
	char dir[16];
	sprintf(dir,"gmon-%d",mpi_me);
	chdir(dir);
	MPI_Finalize();
	return 0;
}


