from pathlib import Path
import itertools,json
p=Path(__file__).parent
def conv(x,y):return [sum(x[s]*y[(t-s)%3] for s in range(3)) for t in range(3)]
count=0
for x,y in itertools.product(itertools.product(range(2),repeat=3),repeat=2):
 X=[[x[(j-i)%3] for j in range(3)] for i in range(3)]
 Y=[[y[(j-i)%3] for j in range(3)] for i in range(3)]
 z=conv(x,y)
 assert all(sum(X[i][k]*Y[k][j] for k in range(3))==z[(j-i)%3] for i in range(3) for j in range(3))
 count+=1
forced=[]
for a,b in itertools.permutations(range(3),2):
 remaining=set(range(3))-{0,(a-b)%3}
 assert remaining=={(b-a)%3}
 for x,y in itertools.product(range(3),repeat=2):
  assert ((x+y)%3 in remaining)==((x+y)%3==(b-a)%3)
 forced.append([a,b,next(iter(remaining))])
(p/'results.json').write_text(json.dumps({'mask_pairs':count,'matrix_entries_checked':count*9,'forced_phase_cases':forced,'search_launched':False},indent=2)+'\n')
print('PASS: 64 convolution identities, 576 matrix entries, six forced phase cases; no search.')
