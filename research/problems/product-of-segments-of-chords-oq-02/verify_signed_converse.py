import numpy as np

def power_check(P,A,B,C,D, tol=1e-9):
    # Build circle through A,B,C (assume affinely independent), return center O, r2
    # Solve |X-A|^2=|X-B|^2 and |X-A|^2=|X-C|^2  -> linear in X
    # 2(B-A).X = |B|^2-|A|^2 ; 2(C-A).X = |C|^2-|A|^2
    M = np.array([2*(B-A), 2*(C-A)])
    rhs = np.array([B@B - A@A, C@C - A@A])
    O = np.linalg.solve(M, rhs)
    r2 = (A-O)@(A-O)
    return O, r2

rng = np.random.default_rng(0)
fails=0; tested=0
for _ in range(20000):
    P = rng.normal(size=2)
    A = rng.normal(size=2)
    C = rng.normal(size=2)
    u=A-P; v=C-P
    if abs(np.cross(u,v))<1e-3: continue   # lin indep
    t = rng.normal(); s = rng.normal()
    if abs(s)<1e-6: continue
    # signed: t|u|^2 = s|v|^2  -> choose s from t
    s = t*(u@u)/(v@v)
    B = P + t*u
    D = P + s*v
    # need A,B,C affinely independent: requires t!=1
    if abs(t-1)<1e-3: continue
    try:
        O,r2 = power_check(P,A,B,C,D)
    except np.linalg.LinAlgError:
        continue
    dD = (D-O)@(D-O)
    tested+=1
    if abs(dD-r2)>1e-6*(1+r2):
        fails+=1
        if fails<5: print("FAIL", t,s, dD, r2)
print(f"tested={tested} fails={fails}")
