/* H3/T1 phase-two profiling adaptation of H5 prototype at 6e85c306db71d4080850edfc4ef5436544cc2997.
 * No phase-three search or exclusion claim. See run_prototype.py for bounded commands. */
/* C prototype of the H3 phase-two traversal (sizing only; NOT a proof).
 *
 * Vertices follow threeHighRepresentativeMasks 1: highs 0..2, triple supports,
 * uncovered pair supports, singleton supports grouped by colour, empties.
 *
 * usage: h3_phase2_profile 1 [key=val ...]
 *   mrv=0|1      phase-1 clause choice: first open (0) or fewest candidates (1)
 *   fc=0|1       phase-1 forward check: reject when an open clause has no candidate
 *   p1only=0|1   stop at phase-1 leaves (count only)
 *   maxleaf=N    stop after N phase-1 leaves (0 = no limit)
 *   secs=N       wall limit
 *   pre=K        split point: the state when the clauses of the first K core vertices are closed
 *   mod=M res=R  with pre=K: report per-part node counts (res=-1), or run only part R
 *   verbose=0|1
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;
#define NV 49
#define NH 3
static int MASK[NV], CAP[NV], ncore, nlow0; /* core = [NH, NH+ncore) ; empties after */
static u64 FIBM[NH];
static int FIB[NH][NV], FIBN[NH];
static int E0; /* first empty */

typedef struct { u64 rows[NV]; unsigned char deg[NV]; } St;

static int opt_mrv = 1, opt_fc = 1, opt_p1only = 0, opt_verbose = 0, opt_mod = 1, opt_res = -1;
static int opt_early_gate = 0;
static unsigned long long gate_hits;
static unsigned long long opt_nodes = 2000000;
static long opt_maxleaf = 0; static double opt_secs = 1e18;
static unsigned long long n1, leaf1, n2, leaf2, n3, found, leafrun;
static double T0;
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+ts.tv_nsec*1e-9; }
static int stop = 0;
static int budget(void){
  unsigned long long n=n1+n2+n3;
  if(stop) return 1;
  if((opt_nodes && n>=opt_nodes) || ((n&4095)==0 && now()-T0>=opt_secs)){ stop=1; return 1; }
  return 0;
}

static void setup(int t){
  int n = 0, i, j;
  int tri[2][3] = {{0,1,2},{0,3,4}};
  for(i=0;i<NH;i++) MASK[n++] = 0;
  for(i=0;i<t;i++) MASK[n++] = (1<<tri[i][0])|(1<<tri[i][1])|(1<<tri[i][2]);
  for(i=0;i<NH;i++) for(j=i+1;j<NH;j++){
    int cov = 0, k; int pm = (1<<i)|(1<<j);
    for(k=0;k<t;k++){ int tm=(1<<tri[k][0])|(1<<tri[k][1])|(1<<tri[k][2]); if((tm&pm)==pm) cov=1; }
    if(!cov) MASK[n++] = pm;
  }
  for(i=0;i<NH;i++){
    int c = 9-NH, k;
    for(k=0;k<t;k++) if(tri[k][0]==i||tri[k][1]==i||tri[k][2]==i) c++;
    for(k=0;k<c;k++) MASK[n++] = 1<<i;
  }
  E0 = n; ncore = n - NH;
  while(n<NV) MASK[n++] = 0;
  for(i=0;i<NV;i++) CAP[i] = i<NH ? 8 : 7;
  for(i=0;i<NH;i++){ FIBM[i]=0; FIBN[i]=0; for(j=0;j<NV;j++) if(MASK[j]>>i&1){ FIBM[i]|=1ULL<<j; FIB[i][FIBN[i]++]=j; } }
}
static void init(St *s){
  int v,w; memset(s,0,sizeof *s);
  for(v=NH;v<NV;v++) for(w=0;w<NH;w++) if(MASK[v]>>w&1){
    s->rows[v]|=1ULL<<w; s->rows[w]|=1ULL<<v; s->deg[v]++; s->deg[w]++; }
}
static inline int allowed(const St *s,int u,int x){
  if(s->deg[u]>=CAP[u]||s->deg[x]>=CAP[x]) return 0;
  u64 r = s->rows[u], rx = s->rows[x];
  while(r){ int y=__builtin_ctzll(r); r&=r-1; if(s->rows[y]&rx) return 0; }
  return 1;
}
static int degree_dead(const St *s){
  for(int u=E0;u<NV;u++){
    int possible=s->deg[u];
    if(possible>=7) continue;
    for(int x=0;x<NV && possible<7;x++)
      if(x!=u && !(s->rows[u]>>x&1) && allowed(s,u,x)) possible++;
    if(possible<7) return 1;
  }
  return 0;
}

/* returns 0 = impossible, 1 = ok (edge present after call) */
static inline int try_add(St *s,int u,int x){
  if(u==x) return 0;
  if(s->rows[u]>>x&1) return 1;
  if(!allowed(s,u,x)) return 0;
  s->rows[u]|=1ULL<<x; s->rows[x]|=1ULL<<u; s->deg[u]++; s->deg[x]++;
  return 1;
}
static inline int twin_skip(const St *s,int u,int w,int x){
  int i; for(i=0;i<FIBN[w];i++){ int y=FIB[w][i];
    if(y<x && y!=u && s->rows[y]==s->rows[x] && MASK[y]==MASK[x]) return 1; }
  return 0;
}
static u64 st_key(const St *s){ u64 a=0; int i; for(i=0;i<NV;i++) a=(a*31+s->rows[i]%1000003)%1000003; return a; }

/* ---------- patterns: transversals of the three fibres, as vertex sets ---------- */
typedef struct { u64 set; unsigned char v[NH]; unsigned char k; } Pat;
static Pat *ALLP; static int NALLP;
static void gen_pats(void){
  int idx[NH]={0}, w, cnt=0, cap=1<<16; ALLP=malloc(sizeof(Pat)*cap);
  for(;;){
    int t[NH], ok=1, w2;
    for(w=0;w<NH;w++) t[w]=FIB[w][idx[w]];
    for(w=0;w<NH&&ok;w++) for(w2=0;w2<NH;w2++) if((MASK[t[w]]>>w2&1) && t[w2]!=t[w]) { ok=0; break; }
    if(ok){ Pat p; p.set=0; p.k=0; for(w=0;w<NH;w++) if(!(p.set>>t[w]&1)){ p.set|=1ULL<<t[w]; p.v[p.k++]=t[w]; }
      if(cnt==cap){cap*=2; ALLP=realloc(ALLP,sizeof(Pat)*cap);} ALLP[cnt++]=p; }
    for(w=NH-1;w>=0;w--){ if(++idx[w]<FIBN[w]) break; idx[w]=0; }
    if(w<0) break;
  }
  NALLP=cnt;
}
static inline int insertable(const St *s,const Pat *p){
  int i,j;
  for(i=0;i<p->k;i++) if(s->deg[p->v[i]]>=7) return 0;
  for(i=0;i<p->k;i++) for(j=i+1;j<p->k;j++) if(s->rows[p->v[i]]&s->rows[p->v[j]]) return 0;
  return 1;
}

/* Phase three is deliberately omitted from this profiling program. */

/* ---------- phase 2 ---------- */
static int state_ok(const St *s){
  int v,w;
  for(v=0;v<NH;v++) if(s->deg[v]!=8) return 0;
  for(v=NH;v<E0;v++) for(w=0;w<NH;w++) if(!(s->rows[v]&FIBM[w])) return 0;
  for(v=E0;v<NV;v++) if(s->rows[v]) for(w=0;w<NH;w++) if(!(s->rows[v]&FIBM[w])) return 0;
  return 1;
}
static int dfs2(const St *s,const Pat **avail0,int na0){
  n2++; if(budget()) return 1;
  if(!state_ok(s)){ fprintf(stderr,"state_ok failed\n"); exit(2); }
  if(opt_early_gate && degree_dead(s)){ gate_hits++; return 1; }
  const Pat **avail = malloc(sizeof(Pat*)*(na0+1)); int na=0, i, v;
  int cnt[NV]; memset(cnt,0,sizeof cnt);
  for(i=0;i<na0;i++) if(insertable(s,avail0[i])){ avail[na++]=avail0[i]; for(int j=0;j<avail0[i]->k;j++) cnt[avail0[i]->v[j]]++; }
  int best=-1;
  for(v=NH;v<E0;v++){ if(s->deg[v]>=7) continue; if(best<0||cnt[v]<cnt[best]) best=v; }
  int r=1;
  if(best<0){ leaf2++; free(avail); return 1; }
  v=best;
  int n=-1; for(i=E0;i<NV;i++) if(!s->rows[i]){ n=i; break; }
  if(n<0){ free(avail); return 1; }
  /* gate: total deficiency of core must be coverable; (heuristic prune not mirrored unless proved) */
  const Pat **child = malloc(sizeof(Pat*)*(na+1)); int npre=0, ncs=0;
  const Pat **cs = malloc(sizeof(Pat*)*(na+1));
  for(i=0;i<na;i++){ if(avail[i]->set>>v&1) cs[ncs++]=avail[i]; else child[npre++]=avail[i]; }
  for(i=0;i<ncs && r && !stop;i++){
    St t=*s; int ok=1, j;
    for(j=0;j<cs[i]->k;j++) if(!try_add(&t,n,cs[i]->v[j])){ ok=0; break; }
    if(!ok) continue;
    memcpy(child+npre, cs+i, sizeof(Pat*)*(ncs-i));
    if(!dfs2(&t,child,npre+ncs-i)) r=0;
  }
  free(avail); free(child); free(cs);
  return r;
}

/* ---------- phase 1 ---------- */
static const Pat **ROOTP;
static int opt_pre = 0; static unsigned long long npre, preleaf, partn[4096];
static int dfs1(const St *s,int inpre){
  n1++; if(budget()) return 1;
  int u,w,bu=-1,bw=-1,bn=99;
  for(u=NH;u<E0;u++) for(w=0;w<NH;w++){
    if(s->rows[u]&FIBM[w]) continue;
    if(!opt_mrv && !opt_fc){ if(bu<0){bu=u;bw=w;} continue; }
    int c=0,i; for(i=0;i<FIBN[w];i++){ int x=FIB[w][i]; if(x!=u && allowed(s,u,x)) c++; }
    if(c==0 && opt_fc) return 1;
    if(opt_mrv){ if(c<bn){bn=c;bu=u;bw=w;} } else if(bu<0){bu=u;bw=w;}
  }
  if(inpre && (bu<0 || bu>=NH+opt_pre)){
    /* prefix leaf: attribute the subtree to part key %% mod (sizing report only) */
    unsigned long long b=n1; int part=(int)(st_key(s)%(u64)opt_mod); preleaf++;
    if(opt_res>=0 && part!=opt_res) return 1;
    n1--; int r=dfs1(s,0); partn[part]+=n1-b+1; return r;
  }
  if(inpre) npre++;
  if(bu<0){
    leaf1++;
    if(opt_maxleaf && (long)leaf1>opt_maxleaf){ stop=1; return 1; }
    if(opt_p1only) return 1;
    unsigned long long b2=n2,b3=n3,bl=leaf2; double t1=now();
    int r=dfs2(s,ROOTP,NALLP); leafrun++;
    if(opt_verbose) printf("leaf %llu n1 %llu n2 %llu leaf2 %llu n3 %llu secs %.3f r %d\n",leaf1,n1,n2-b2,leaf2-bl,n3-b3,now()-t1,r);
    return r;
  }
  u=bu; w=bw; int i;
  for(i=0;i<FIBN[w];i++){ int x=FIB[w][i];
    if(x==u || twin_skip(s,u,w,x)) continue;
    St t=*s; if(!try_add(&t,u,x)) continue;
    if(!dfs1(&t,inpre)) return 0;
    if(stop) return 1;
  }
  return 1;
}

int main(int argc,char **argv){
  int t = argc>1 ? atoi(argv[1]) : 2, i;
  for(i=2;i<argc;i++){
    char *e=strchr(argv[i],'='); if(!e) continue; *e=0; const char *k=argv[i], *v=e+1;
    if(!strcmp(k,"mrv")) opt_mrv=atoi(v); else if(!strcmp(k,"fc")) opt_fc=atoi(v);
    else if(!strcmp(k,"p1only")) opt_p1only=atoi(v); else if(!strcmp(k,"maxleaf")) opt_maxleaf=atol(v);
    else if(!strcmp(k,"secs")) opt_secs=atof(v); else if(!strcmp(k,"mod")) opt_mod=atoi(v);
    else if(!strcmp(k,"earlygate")) opt_early_gate=atoi(v);
    else if(!strcmp(k,"nodes")) opt_nodes=strtoull(v,0,10);
    else if(!strcmp(k,"res")) opt_res=atoi(v); else if(!strcmp(k,"pre")) opt_pre=atoi(v); else if(!strcmp(k,"verbose")) opt_verbose=atoi(v);
  }
  if(t!=1 || opt_mod<1 || opt_mod>4096 || opt_res>=opt_mod || opt_pre<0 || opt_pre>22) return 2;
  setup(t); gen_pats();
  ROOTP=malloc(sizeof(Pat*)*NALLP); for(i=0;i<NALLP;i++) ROOTP[i]=&ALLP[i];
  printf("T%d core=%d E0=%d patterns=%d masks:",t,ncore,E0,NALLP); for(i=0;i<NV;i++) printf(" %d",MASK[i]); printf("\n");
  St s; init(&s); T0=now();
  int r=dfs1(&s,opt_pre>0);
  printf("PROFILE T%d traversal_return=%d stopped=%d n1=%llu leaf1=%llu leafrun=%llu n2=%llu leaf2=%llu n3=%llu found=%llu secs=%.1f mrv=%d fc=%d\n",
    t,r,stop,n1,leaf1,leafrun,n2,leaf2,n3,found,now()-T0,opt_mrv,opt_fc);
  if(opt_pre>0){ unsigned long long mn=~0ULL,mx=0,sum=0; for(i=0;i<opt_mod;i++){ if(partn[i]<mn)mn=partn[i]; if(partn[i]>mx)mx=partn[i]; sum+=partn[i]; }
    printf("SPLIT pre=%d mod=%d prefix_nodes=%llu prefix_leaves=%llu part_min=%llu part_max=%llu part_sum=%llu\n",opt_pre,opt_mod,npre,preleaf,mn,mx,sum);
    if(opt_verbose){ for(i=0;i<opt_mod;i++) printf(" %llu",partn[i]); printf("\n"); } }
  printf("GATE enabled=%d hits=%llu node_cap=%llu\n",opt_early_gate,gate_hits,opt_nodes);
  return stop ? 124 : 0;
}
