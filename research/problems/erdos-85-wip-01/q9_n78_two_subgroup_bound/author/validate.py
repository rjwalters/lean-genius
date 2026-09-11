from pathlib import Path
import itertools,json,math
p=Path(__file__).parent
words=[x for x in range(1,16) if x.bit_count()>=3];assert len(words)==5
pairs=[]
for x,y in itertools.combinations(words,2):
 assert 0<(x^y).bit_count()<3;pairs.append([x,y,x^y])
def v2(n):
 k=0
 while n%2==0:n//=2;k+=1
 return k
assert v2(math.factorial(4))==3 and v2(math.factorial(3))==1 and v2(78)==1
(p/'results.json').write_text(json.dumps({'permitted_words':words,'pairs':pairs,'v2_4_factorial':3,'v2_3_factorial':1,'v2_78':1,'graph_search':False},indent=2)+'\n')
print('PASS: ten codeword pairs and factorial/orbit valuations')
