"""Synthetic observed-SAT matrix; a prior UNSAT must never suppress the alarm."""
import json
from pathlib import Path
import test_summarize_phase_b_verdicts as t
import summarize_phase_b_verdicts as r
c=t.ReceiptTests();c.setUp();out=[]
try:
 good=c.run_fixture('earlier_unsat')
 for stage in ['published','wrapper','solver','log','unknown','error']:
  for solver in ['kissat','cadical']:
   name=stage+'_'+solver
   limited=stage in ['unknown','error']
   run=c.run_fixture(name,primary=('UNKNOWN' if limited else 'SAT_CANDIDATE') if solver=='kissat' else 'UNSAT',
                     secondary='UNKNOWN' if limited else 'SAT_CANDIDATE')
   state=json.loads((run/'results.json').read_text());record=state['results'][0]
   key='primary' if solver=='kissat' else 'crosscheck'
   if limited:
    raw=b's SATISFIABLE\n';(run/f'h3/solve/h3/{solver}.log').write_bytes(raw)
    record['solve'][key].update(log_sha256=r.digest(raw),log_bytes=len(raw))
   if stage=='error':record.update(status='ERROR',error='post-solve validation failed')
   c.write(run/'h3/solve/h3/result.json',record['solve']);c.write(run/'h3/result.json',record)
   if stage in ['wrapper','solver','log']:
    state.update(results=[],status='running');state.pop('not_started')
   if stage in ['solver','log']:
    (run/'h3/result.json').unlink();(run/'h3/preparation.json').unlink()
   if stage=='log':(run/'h3/solve/h3/result.json').unlink()
   c.write(run/'results.json',state)
   result=c.summary(good,run);row=next(v for v in result['rows'] if v['id']=='h3')
   out.append({'stage':stage,'solver':solver,'status':row['status'],'alarm':result['has_disagreement'],
               'passes':row['status']=='DISAGREEMENT' and result['has_disagreement']})
 print(json.dumps(out,indent=2));Path('publication-matrix.json').write_text(json.dumps(out,indent=2)+'\n')
finally:c.doCleanups()
