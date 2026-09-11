import ctypes,importlib.util,itertools,json,pathlib,time
P=pathlib.Path(__file__).parent;lib=ctypes.CDLL(str(P/'hosts.dylib'))
lib.enumerate_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.enumerate_hosts.restype=ctypes.c_char_p
lib.check_fixed_hosts.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.check_fixed_hosts.restype=ctypes.c_char_p
def ref(path,name):
 sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
def subset_exists(g,s,PV):
 need=7-len(g[s]);eligible=[p for p in PV if all(not (g[p]-{s})&(g[w]-{s}) for w in g[s])]
 for vs in itertools.combinations(eligible,need):
  ns=g[s]|set(vs)
  if any(len(ns&g[h])!=1 for h in range(7)):continue
  if any((g[v]-{s})&(g[w]-{s}) for v,w in itertools.combinations(vs,2)):continue
  return True
 return False
def main():
 records=[];guards=0;prefixes=0;start=time.monotonic()
 for label in ['a7','a6']:
  api=ref(P/f'reference_{label}.py',label)
  for index,adj in enumerate(json.loads((P/f'fixtures_{label}.json').read_text())):
   g,support,E,U=api.validate(adj);S=[u for u in U if support[u].bit_count()==1];PV=[u for u in U if support[u].bit_count()==2]
   full=api.complete_domains(g,support,U,api.Budget(100000,time.monotonic()+60));assert full['status']=='DOMAINS_COMPLETE'
   expected=all(full['initial'][s] for s in S);fixed=[sum(1<<v for v in PV if g[e]>>v&1) for e in E]
   base=list(g)
   for e in E:
    for v in PV:base[e]&=~(1<<v);base[v]&=~(1<<e)
   gm=(ctypes.c_uint64*49)(*base);fm=(ctypes.c_uint64*7)(*fixed)
   result=json.loads(lib.check_fixed_hosts(gm,fm,100000,60));assert result['status']=='COMPLETE'
   assert result['solutions']==([fixed] if expected else []) and result['empty_vertices']==E
   for p in result['prunes']:
    chosen=p['chosen'];assigned={result['order'][i] for i in range(p['depth'])}
    assert all(chosen[i]==(fixed[i] if i in assigned else 0) for i in range(7))
    partial=[{v for v in range(49) if row>>v&1} for row in base]
    for i,m in enumerate(chosen):
     for v in PV:
      if m>>v&1:partial[E[i]].add(v);partial[v].add(E[i])
    assert not subset_exists(partial,p['singleton'],PV);prefixes+=1
   for cap in [0,result['nodes']-1]:assert json.loads(lib.check_fixed_hosts(gm,fm,cap,60))['status']=='UNKNOWN';guards+=1
   assert json.loads(lib.check_fixed_hosts(gm,fm,result['nodes'],60))==result;guards+=1
   assert json.loads(lib.enumerate_hosts(gm,0,60))['status']=='UNKNOWN';guards+=1
   assert json.loads(lib.enumerate_hosts(gm,100000,-1))['status']=='UNKNOWN';guards+=1
   bad=list(base);bad[0]|=1
   assert json.loads(lib.enumerate_hosts((ctypes.c_uint64*49)(*bad),100000,60))['status']=='INVALID_INPUT';guards+=1
   records.append(dict(family=label,index=index,solutions=len(result['solutions']),prunes=len(result['prunes']),nodes=result['nodes']))
 out=dict(status='PASS',fixtures=len(records),fixed_solutions=sum(r['solutions'] for r in records),prefixes_verified=prefixes,guards=guards,seconds=time.monotonic()-start,results=records)
 (P/'test-results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='results'})
if __name__=='__main__':main()
