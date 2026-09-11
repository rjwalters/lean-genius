from pathlib import Path
import json,copy,importlib.util
from cover import check,options
P=Path(__file__).parent;fixture=json.loads((P.parent/'h7-monotone-host-prefix-verifier/fixture.json').read_text());base=fixture['base'];E=fixture['empty_vertices'];order=fixture['order'];prune=fixture['prune'];fixed=prune['chosen']
r=dict(status='COMPLETE',empty_vertices=E,order=order,solutions=[],prunes=[prune]);assert check(base,r,fixed)['coverage_proved']
# A real depth6 negative prefix accounts for the final empty with degree0.
r6=copy.deepcopy(r);r6['prunes'][0]['depth']=6;r6['prunes'][0]['chosen'][order[6]]=0;assert check(base,r6,fixed)['coverage_proved']
# Synthetic all-leaf receipts check structural coverage independently of endpoint truth.
opts=options(base,E);leaves=[];choice=[0]*7

def expand(depth,used):
 if depth==7:leaves.append(choice[:]);return
 i=order[depth]
 for m in opts[i]:
  if m&used:continue
  choice[i]=m;expand(depth+1,used|m);choice[i]=0
expand(0,0)
complete=dict(status='COMPLETE',empty_vertices=E,order=order,solutions=leaves,prunes=[]);verified=check(base,complete)
assert len(leaves)>1
bads=[]
b=copy.deepcopy(complete);b['solutions'].pop();bads.append(b)
b=copy.deepcopy(r6);b['prunes'].append(copy.deepcopy(b['prunes'][0]));bads.append(b)
b=copy.deepcopy(r6);b['prunes'].append(prune);bads.append(b)
b=copy.deepcopy(r6);b['prunes'][0]['chosen'][order[0]]=1;bads.append(b)
b=copy.deepcopy(r6);b['solutions']=[fixed];bads.append(b)
rejected=0
for b in bads:
 try:check(base,b)
 except AssertionError:rejected+=1
 else:raise AssertionError('structurally false receipt accepted')
unknown=copy.deepcopy(complete);unknown['status']='UNKNOWN';unknown['solutions']=unknown['solutions'][:1];assert not check(base,unknown)['coverage_proved']
prep=dict(status='UNKNOWN',empty_vertices=E,order=[0,1],solutions=[],prunes=[]);assert not check(base,prep)['coverage_proved']
out=dict(status='PASS',full_product_compatible_leaves=len(leaves),structural_nodes=verified['nodes'],false_receipts_rejected=rejected,unknown_guards=2,scope='Structural receipt coverage only. Synthetic all-leaf receipts are not claims of singleton feasibility. Real fixed-prefix negative fixture tested separately by direct49graph endpoint checker. No family search.')
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
