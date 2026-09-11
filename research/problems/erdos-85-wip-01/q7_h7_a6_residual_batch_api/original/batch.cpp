#include "filter.cpp"
extern "C" const char* batch_hosts(const U*base,const int*E,const U*records,int count,int cap,double deadline){
 static thread_local std::string result;std::ostringstream out;
 bool sane=count>=0&&cap>=0;U seen=0;
 for(int u=0;u<49;u++){
  if((base[u]>>49)||(base[u]>>u&1)){sane=false;continue;}
  for(int v:bits(base[u]))if(!(base[v]>>u&1))sane=false;
 }
 for(int i=0;i<7;i++){
  if(E[i]<7||E[i]>=49){sane=false;continue;}
  if((seen>>E[i]&1)||(base[E[i]]&127))sane=false;
  seen|=U(1)<<E[i];
 }
 for(int u=7;u<49;u++)if(pc(base[u]&127)==2 && base[u]!=(base[u]&127))sane=false;
 if(!sane){result="[{\"status\":\"INVALID_INPUT\"}]";return result.c_str();}
 out<<'[';bool first=true;
 for(int r=0;r<count;r++){
  if(native_now()>deadline)break;
  U g[49];std::copy(base,base+49,g);bool valid=true;
  const U*ms=records+size_t(7)*r;
  for(int i=0;i<7;i++){
   if(ms[i]>>49){valid=false;break;}
   for(int p:bits(ms[i])){
    if(p<7||pc(base[p]&127)!=2){valid=false;break;}
    g[E[i]]|=U(1)<<p;g[p]|=U(1)<<E[i];
   }
  }
  if(!first)out<<',';first=false;
  try{
   if(!valid)throw std::invalid_argument("bad host mask");
   Checker checker(g,cap,deadline);checker.run();
   if(checker.status=="INFEASIBLE_ROW")out<<"{\"status\":\"INFEASIBLE_ROW\",\"empty_vertex\":"<<checker.empty<<",\"nodes\":"<<checker.nodes<<"}";
   else out<<checker.json();
  }catch(const std::exception&){out<<"{\"status\":\"INVALID_INPUT\"}";}
 }
 out<<']';result=out.str();return result.c_str();
}
