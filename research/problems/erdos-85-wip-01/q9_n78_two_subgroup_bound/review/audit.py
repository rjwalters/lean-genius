from pathlib import Path
from itertools import combinations
from math import factorial
import hashlib,json
s=Path('/tmp/erdos85-sol1-q9-n78-two-subgroup-bound');p=Path(__file__).parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
premises=json.loads((s/'premises.json').read_text());print('premise shape',type(premises).__name__)
words=[w for w in range(16) if w.bit_count()>=3];checks=[]
for a,b in combinations(words,2):
 assert 0<(a^b).bit_count()<3;checks.append([a,b,a^b])
assert len(checks)==10
bounds=[]
for n in (3,4):
 q=factorial(n);part=1
 while q%2==0:part*=2;q//=2
 bounds.append(part)
assert bounds==[2,8]
(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());(p/'results.json').write_text(json.dumps({'status':'PASS','allowed_words':words,'xor_checks':checks,'S3_S4_two_parts':bounds},indent=2)+'\n')
print('Ten code pairs and factorial valuations PASS')
