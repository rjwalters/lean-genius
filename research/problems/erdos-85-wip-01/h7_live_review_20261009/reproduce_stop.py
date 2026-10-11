"""Reproduce observed-STOP handling at the launch pin without AWS calls."""
import ast,hashlib,json,subprocess,tempfile,types
from pathlib import Path
PIN="729127aa817263475e7aa0c65c3db34a65da3389"
SOURCE="research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/cert_controller.py"
def reproduce(repo):
    raw=subprocess.check_output(["git","-C",str(repo),"show",PIN+":"+SOURCE])
    tree=ast.parse(raw);node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="one_pass")
    stop_calls=[];writes=[]
    with tempfile.TemporaryDirectory(prefix="e85-stop-mock-") as temporary:
        vc=types.SimpleNamespace(PASS={"size":1},HARD_STOP_USD=160,PREFIX="fixture",STRIPE=Path(temporary),stop=lambda *a:stop_calls.append(a),aws=lambda *a,**kw:"")
        env={"vc":vc,"json":json,"MANIFEST":[{"id":"unfinished"}],"DRAINED":"drained","ledgers":lambda:[],"put_json":lambda *a:writes.append(a),"_reviewed_one_pass":lambda state,act:{"utc":"2026-10-09T03:22:00Z","control":["STOP","ALARM-fixture"],"estimated_spend_usd":1,"orphans_released":0}}
        exec(compile(ast.Module(body=[node],type_ignores=[]),SOURCE,"exec"),env)
        report=env["one_pass"]({},True)
    assert report["action"]=="STOP marker present; controller exits" and stop_calls==[] and writes==[]
    return {"status":"OBSERVED_STOP_EXITS_WITHOUT_FLEET_STOP_REPRODUCED","execution_pin":PIN,"source_sha256":hashlib.sha256(raw).hexdigest(),"action":report["action"],"fleet_stop_calls":len(stop_calls),"marker_cause_writes":len(writes),"cloud_calls":0,"scope":"Mocked observed worker STOP/ALARM; no live cloud mutation."}
if __name__=="__main__":
    print(json.dumps(reproduce(Path(__file__).resolve().parents[4]),indent=2))
