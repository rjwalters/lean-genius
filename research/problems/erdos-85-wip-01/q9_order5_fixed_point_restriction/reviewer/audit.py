from pathlib import Path
import hashlib, json, sqlite3
src = Path('/tmp/erdos85-sol1-q9-order5-fixed-points')
for f,h in json.loads((src/'pins.json').read_text()).items():
    assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
premises=[]
for rid in (2140,2153,2161,2162,2163):
    row=c.execute('select id,status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert row[1]=='resolved' and row[2].startswith('PASS')
    premises.append(dict(id=row[0],status=row[1],resolution=row[2]))
out=[]
for N in (78,80):
    retained=[]
    # Direct original edge-bound and common-neighbour inequalities,
    # without using the author's eliminated quadratic inequality.
    for F in range(1,N):
        M=N-F
        if M%5 or M<1+8*7 or F<1+4*3: continue
        for b in range(F+1):
            if 5*b>M: continue
            if 12*b+72*(F-b)>F*(F-1): continue
            retained.append((F,b,M))
    assert retained == ([(13,13,65)] if N==78 else [])
    out.append(dict(N=N,retained_before_triangle_obstruction=retained))
assert 13*4*3==13*12 and (13*4//2)%3 != 0
Path(__file__).with_name('results.json').write_text(json.dumps(dict(status='PASS',cases=out,premises=premises),indent=2)+'\n')
print(out)
