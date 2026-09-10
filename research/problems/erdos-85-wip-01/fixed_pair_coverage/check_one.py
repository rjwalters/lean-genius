from pathlib import Path
import subprocess,time,json,os,sys
p=Path(__file__).parent;name=sys.argv[1];bound=int(sys.argv[2]);source=p/(name+'.lean');assert source.is_file()
e=os.environ.copy();e['LEAN_PATH']=e.get('LEAN_PATH','')+os.pathsep+str(p)
t=time.monotonic()
with (p/(name+'.log')).open('w') as f:
 try:r=subprocess.run(['lean','-R',str(p),'-o',str(p/(name+'.olean')),str(source)],env=e,stdout=f,stderr=subprocess.STDOUT,timeout=bound);rc=r.returncode;timedout=False
 except subprocess.TimeoutExpired:rc=None;timedout=True
r={'returncode':rc,'timeout':timedout,'elapsed_seconds':time.monotonic()-t,'process_bound_seconds':bound}
(p/(name+'.run.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
