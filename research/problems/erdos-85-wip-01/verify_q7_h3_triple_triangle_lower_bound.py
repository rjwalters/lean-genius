"""Exact scalar conclusion of the universal H3 triple triangle coverage proof."""
for m in [1,2,3]:
    uncovered_empty=24-12-(1+2*m)
    unmatched_N=6-2*m
    lower=max((uncovered_empty+2)//3,unmatched_N)
    assert uncovered_empty==11-2*m
    assert lower=={1:4,2:3,3:2}[m]
    assert 6+m+lower==11
    # Any nonnegative integer X satisfying the two coverage bounds is >=lower.
    for X in range(lower):assert 3*X<uncovered_empty or X<unmatched_N
    assert 3*lower>=uncovered_empty and lower>=unmatched_N
    print(f'PASS m={m}: X>={lower}, hence T=6+m+X>=11')
print('Universal scalar consequence; graph coverage assumptions proved in accompanying note; no profile exclusion.')
