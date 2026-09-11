#include "filter.cpp"
extern "C" const char* batch_check(const U* base,const uint32_t* records,int count,int cap,double deadline){
 static thread_local std::string result;
 std::ostringstream out;out<<"[";bool first=true;
 for(int r=0;r<count;r++){
  if(native_now()>deadline)break;
  U g[49]={};
  auto add=[&](int a,int b){g[a]|=U(1)<<b;g[b]|=U(1)<<a;};
  auto ren=[](int a){return a<7?a+42:a;};
  for(int a=0;a<21;a++)for(int b=0;b<a;b++)if(base[a]>>b&1)add(ren(a),ren(b));
  const uint32_t* rec=records+14*r;
  unsigned seen=0;
  bool valid=true;
  for(int i=0;i<7;i++){
   if(rec[i]>=7 || (seen>>rec[i]&1)){valid=false;break;}
   seen|=1U<<rec[i];add(i,14+i);add(i,7+rec[i]);
  }
  int k=0;
  for(int a=0;a<7;a++)for(int b=a+1;b<7;b++,k++){
   add(21+k,a);add(21+k,b);
   for(int e=0;e<7;e++)if(rec[7+e]>>k&1)add(21+k,42+e);
  }
  if(!first)out<<',';first=false;
  try{
   if(!valid)throw std::invalid_argument("bad pairing");
   Checker c(g,cap,deadline);c.run();
   if(c.status=="INFEASIBLE_ROW")out<<"{\"status\":\"INFEASIBLE_ROW\",\"empty_vertex\":"<<c.empty<<",\"nodes\":"<<c.nodes<<"}";
   else out<<c.json();
  }catch(const std::exception&){out<<"{\"status\":\"INVALID_INPUT\"}";}
 }
 out<<']';result=out.str();return result.c_str();
}
