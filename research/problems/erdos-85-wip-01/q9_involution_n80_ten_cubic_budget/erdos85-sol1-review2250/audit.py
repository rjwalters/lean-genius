import itertools,time
start=time.monotonic();pos=list(itertools.combinations_with_replacement(range(5),2));counts=[0,0,0,0]
for m in range(32768):
 assert time.monotonic()-start<60, 'UNKNOWN:60s cap'
 rows=[0]*5
 for k,(i,j) in enumerate(pos):
  if m>>k&1:rows[i]|=1<<j;rows[j]|=1<<i
 counts[0]+=1
 if any(r.bit_count()!=3 for r in rows):continue
 counts[1]+=1
 if any(rows[i]>>i&1 and rows[j]>>j&1 and rows[i]>>j&1 for i in range(5) for j in range(i)):continue
 counts[2]+=1
 if any((rows[i]&rows[j]).bit_count()>2 for i in range(5) for j in range(i)):continue
 counts[3]+=1
assert counts==[32768,112,40,0]
print(counts)
