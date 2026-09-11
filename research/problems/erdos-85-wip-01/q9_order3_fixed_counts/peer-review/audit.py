from pathlib import Path
import hashlib, itertools, json
src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-fixed-counts')
for f,h in json.loads((src/'pins.json').read_text()).items():
    assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
expected=json.loads((src/'results.json').read_text())['orders']
out={}
for N in (78,80):
    initial=set(); reduced=set(); exclusions=[]
    for M in range(57,N+1,3):
        F=N-M
        for a9,a6,a3 in itertools.product(range(F+1),repeat=3):
            a0=F-a3-a6-a9
            if a0<0: continue
            counts=(a0,a3,a6,a9)
            if any(n and d>=F for n,d in zip(counts,(0,3,6,9))):continue
            S=3*a3+6*a6+9*a9
            if S%2 or 9*F-S>M or 6*a3+30*a6+72*a9>F*(F-1):continue
            initial.add((F,counts))
            if a9 or a6 or (a3 and a3<10):continue
            reduced.add((F,a3))
        if F>=14:
            L=10*F-N
            assert 2*L>F
            margin=L*(L-F)-F*F*(F-1)
            assert margin>0
            exclusions.append((F,L,margin))
    peer=expected[str(N)]
    assert initial=={(r['fixed'],tuple(r['degree_counts'])) for r in peer['initial_profiles']}
    assert reduced=={(r['fixed'],r['nonisolated']) for r in peer['after_cubic_lemma']}
    assert set(exclusions)=={(r['fixed'],r['degree_sum_lower'],r['cauchy_excess']) for r in peer['cauchy_excluded']}
    final=[]; isolation_options={}
    for F,b in sorted(reduced):
        if b:
            assert (N,F,b)==(80,11,10)
            group_count=11; forbidden=3; moved_degree=8
            assert group_count-forbidden==moved_degree
            forced_external=10*6
            internal_sum=9*moved_degree-forced_external
            assert internal_sum==12 and internal_sum>9
            continue
        if F==0: final.append(F); continue
        # Enumerate possible matching sizes on nine neighbours, then apply
        # free 3-orbits to unmatched vertices and the zero-codegree budget.
        options=[9-2*t for t in range(5) if (9-2*t)%3==0 and F-1+(9-2*t)<=N-73]
        if options:
            assert options==[3]
            final.append(F);isolation_options[F]=options
    assert final==peer['final_fixed_counts']
    out[N]=dict(initial_profiles=len(initial),final_fixed_counts=final,unmatched_neighbours=isolation_options)
Path(__file__).with_name('results.json').write_text(json.dumps(dict(status='PASS',orders=out),indent=2)+'\n')
print(out)
