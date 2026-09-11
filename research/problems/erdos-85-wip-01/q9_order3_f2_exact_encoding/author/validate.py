from pathlib import Path
import itertools,json
for u,v in itertools.product((0,1),repeat=2):assert max(0,u+v-1)==u*v
pairs=[]
for x,y in itertools.product(range(3),repeat=2):
 if x==y==2:continue
 bx,dx=int(x>0),int(x==2);by,dy=int(y>0),int(y==2)
 assert dx*dy==0 and x*y==bx*by+dx*by+bx*dy
 assert x*(x-1)==2*dx and y*(y-1)==2*dy
 pairs.append([x,y])
assert len(pairs)==8
for diag,other in itertools.product((0,2),range(3)):
 if diag==other==2:continue
 assert int(diag>0)==int(diag==2)
 assert diag*other==int(diag>0)*int(other>0)+int(diag==2)*int(other>0)+int(diag>0)*int(other==2)
result={'status':'PASS_ENCODING_IDENTITIES','binary_product_cases':4,'admissible_entry_pairs':pairs,'matrix_positions':210,'binary_variables':420,'nonnegative_auxiliaries':11400,'search_launched':False}
(Path(__file__).parent/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
