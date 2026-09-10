"""Independent synthetic receipt boundaries over genuine banked snapshots."""
import copy, hashlib, json, tempfile
from pathlib import Path
import summarize_phase_b_verdicts as reducer
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
EXTRA='h1_4ee646ca0ec3e2f0'
INDEX=ROOT/'phase_b_survivors_20260910.json'
SHA=hashlib.sha256(INDEX.read_bytes()).hexdigest()
results=[]

def make_run(parent,count):
    run=parent/str(count);(run/'snapshots').mkdir(parents=True)
    folder='phase_b_historical_overlay'+('_96' if count==96 else '')
    cp=ROOT/folder/'config.draft.json';config=json.loads(cp.read_bytes())
    paths={cp,INDEX}; index=json.loads(INDEX.read_bytes())
    paths.update(ROOT/'sat49'/n for n in config['tool_sha256'])
    paths.update(INDEX.parent/ref['path'] for ref in index['sources'].values())
    op=(cp.parent/config['historical_overlay']['path']).resolve();paths.add(op);overlay=json.loads(op.read_bytes())
    if count==96:
        bp=(op.parent/overlay['base_overlay']['path']).resolve();paths.add(bp);base=json.loads(bp.read_bytes())
        paths.update(op.parent/ref['path'] for ref in overlay['extra_sources'].values())
        rows=base['rows']+[overlay['extra_case']]
    else: bp=op;base=overlay;rows=base['rows']
    paths.update(bp.parent/ref['path'] for ref in base['sources'].values())
    for i,path in enumerate(sorted(paths)):
        (run/'snapshots'/f'{i:02}-{path.name}').write_bytes(path.read_bytes())
    state=dict(schema='erdos85-dispatch-results-v1',index_sha256=SHA,config_sha256=reducer.digest(cp.read_bytes()),config_commit='3f68dfb00a1716f692fad8616e6ed2e9736295e7',inventory_cases=1416,proof_logging=False,selected_cases=[],results=[],status='complete',historical_evidence=rows,historical_skipped=sorted(r['id'] for r in rows),not_started=[])
    write(run,state)
    return run,state

def write(run,state): (run/'results.json').write_text(json.dumps(state))
def summarize(runs): return reducer.summarize(INDEX,SHA,runs)
def target(summary): return next(r for r in summary['rows'] if r['id']==EXTRA)
def reject(runs,label):
    try: summarize(runs)
    except ValueError as error: results.append(dict(case=label,rejected=True,reason=str(error)))
    else: raise AssertionError(label+' accepted')

with tempfile.TemporaryDirectory() as tmp:
    p=Path(tmp);r95,s95=make_run(p,95);r96,s96=make_run(p,96)
    a=summarize([r95]);b=summarize([r96]);mixed=summarize([r95,r96]);reverse=summarize([r96,r95])
    assert a['counts']=={'NOT_RUN':1321,'HISTORICAL_VERIFIED_UNSAT':95}
    assert b['counts']==mixed['counts']==reverse['counts']=={'NOT_RUN':1320,'HISTORICAL_VERIFIED_UNSAT':96}
    old={r['id']:r['historical_evidence'] for r in a['rows'] if 'historical_evidence' in r}
    for row in mixed['rows']:
        if row['id'] in old: assert row['historical_evidence']==old[row['id']]
    assert target(mixed)['historical_evidence']['evidence_format']=='manifest_joined_mono'
    assert not mixed['all_targets_crosschecked_unsat']
    results.append(dict(case='95/96 both orders and exact old provenance',passed=True))
    original=copy.deepcopy(s96)
    for sat in (False,True):
        for solver in ('kissat','cadical'):
            s96=copy.deepcopy(original);s96.update(selected_cases=[EXTRA],status='running');s96.pop('not_started');s96['historical_skipped'].remove(EXTRA)
            directory=r96/EXTRA/'solve'/EXTRA;directory.mkdir(parents=True,exist_ok=True)
            for f in directory.iterdir(): f.unlink()
            (directory/(solver+'.log')).write_text('s SATISFIABLE\n' if sat else 's UNKNOWN\n');write(r96,s96)
            summary=summarize([r95,r96]);row=target(summary)
            assert row['status']==('DISAGREEMENT' if sat else 'INCOMPLETE'),row
            assert len(row['attempts'])==1 and 'historical_evidence' in row
            assert not summary['all_targets_crosschecked_unsat']
            results.append(dict(case='partial '+solver+' '+('SAT' if sat else 'UNKNOWN'),status=row['status']))
    write(r96,original)
    # No selected cases: leftover logs are out of scope. Each pinned historical dependency is mandatory.
    overlay=json.loads((ROOT/'phase_b_historical_overlay_96/historical-96.json').read_bytes())
    refs=[overlay['base_overlay'],*overlay['extra_sources'].values()]
    base=json.loads((ROOT/'phase_b_historical_overlay/historical-95.json').read_bytes());refs+=list(base['sources'].values())
    for ref in refs:
        f=next(f for f in (r96/'snapshots').iterdir() if reducer.digest(f.read_bytes())==ref['sha256']);raw=f.read_bytes();f.unlink()
        reject([r96],'missing '+ref['path']);f.write_bytes(raw)
    for mutation in ('omit-extra','alter-extra','skip-extra'):
        s=copy.deepcopy(original)
        if mutation=='omit-extra':s['historical_evidence'].pop()
        elif mutation=='alter-extra':s['historical_evidence'][-1]['proof_replayed']=True
        else:s['historical_skipped'].remove(EXTRA)
        write(r96,s);reject([r96],mutation)
    write(r96,original)
print(json.dumps(results,indent=2))
Path('independent-boundaries.json').write_text(json.dumps(results,indent=2)+'\n')
