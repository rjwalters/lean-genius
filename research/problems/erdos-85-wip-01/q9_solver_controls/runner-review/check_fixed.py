import argparse, contextlib, hashlib, importlib.util, io, json, tempfile
from pathlib import Path
from unittest.mock import patch

ROOT=Path(__file__).resolve().parent
SOURCE=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls')
pins=json.loads((SOURCE/'pins.json').read_text())
assert all(hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==h for f,h in pins.items())
spec=importlib.util.spec_from_file_location('reviewed_runner',SOURCE/'runner.py')
r=importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
with tempfile.TemporaryDirectory() as temp:
    p=Path(temp)
    solver=p/'sat_then_sleep'
    solver.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("audit-fixture")\nelse:\n print("s SATISFIABLE",flush=True)\n print("v 1 0",flush=True)\n time.sleep(30)\n')
    solver.chmod(0o755)
    cnf=p/'input.cnf';cnf.write_text('p cnf 1 1\n1 0\n')
    metadata=p/'metadata.json';metadata.write_text('{"fixture_only":true}')
    args=argparse.Namespace(n=80,d=9,m=2,cnf=str(cnf),metadata=str(metadata),seed=0,retry=False)
    ledger={'runs':[],'controls':{}}
    with patch.object(r,'ROOT',p),patch.object(r,'KISSAT',solver),patch.object(r,'policy',return_value=('q9',1)),contextlib.redirect_stdout(io.StringIO()):
        r.run(args,ledger,p/'ledger.json')
    record=ledger['runs'][0]
    assert record['status']=='UNKNOWN'
    r.check_model(cnf,Path(record['output']['path']))
    assert record['sat_observed'] is True and record['model_check']['status']=='PASS'
    try:r.policy(ledger,48,7,24,'new-control-hash',0,False)
    except ValueError:allowed=False
    else:raise AssertionError('SAT-observed stop bypassed')
    result={'source_pins':pins,'fixture_only':True,'sat_then_timeout_status':record['status'],
            'complete_model_check':'PASS','subsequent_control_allowed':allowed,
            'finding':'PASS: SAT observed survives timeout; next launch refused',
            'scope':'software reproduction only; no graph control or q9 instance launched'}
    (ROOT/'fixed-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
