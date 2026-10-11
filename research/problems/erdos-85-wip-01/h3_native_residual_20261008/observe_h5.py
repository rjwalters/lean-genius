"""Read the exact existing H5 job; never launch, compile, retry, or stop anything."""
import argparse,json,shlex,subprocess
from pathlib import Path
from prepare import H5_JOB,choose_workers

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    code="""from pathlib import Path
from datetime import datetime,timezone
import json
p=Path('/opt/e85/jobs')/JOB
pid=int((p/'pid').read_text())
print(json.dumps({'job':JOB,'pid':pid,'pid_live':Path(f'/proc/{pid}').exists(),
                 'exit':(p/'exit').read_text().strip() if (p/'exit').exists() else None,
                 'observed_utc':datetime.now(timezone.utc).isoformat()},indent=2))
""".replace('JOB',repr(H5_JOB))
    raw=subprocess.check_output(['/Users/rwalters/.local/bin/e85-remote','ssh','python3 -B -c '+shlex.quote(code)])
    observation=json.loads(raw);workers=choose_workers(observation)
    with a.output.open('xb') as f:f.write(raw)
    print('Authoritative H5 observation retained; allowed residual workers:',workers)
if __name__=='__main__':main()
