import numpy as np
rng = np.random.default_rng(0)
maxerr = {}
def upd(k,e):
    maxerr[k]=max(maxerr.get(k,0.0),abs(e))
N=300000
for _ in range(N):
    # random unit vectors
    u=rng.normal(size=3); u/=np.linalg.norm(u)
    v=rng.normal(size=3); v/=np.linalg.norm(v)
    w=rng.normal(size=3); w/=np.linalg.norm(w)
    ca=np.dot(v,w); cb=np.dot(w,u); cc=np.dot(u,v)
    # Binet-Cauchy numerators (vertex angles A@u, B@v, C@w)
    # cosA numerator = ca - cb*cc  == <u x v, u x w>
    upd('A_num', np.dot(np.cross(u,v),np.cross(u,w)) - (ca - cb*cc))
    # cosB numerator = cb - ca*cc  == <v x w, v x u>
    upd('B_num', np.dot(np.cross(v,w),np.cross(v,u)) - (cb - ca*cc))
    # cosC numerator = cc - ca*cb  == <w x u, w x v>
    upd('C_num', np.dot(np.cross(w,u),np.cross(w,v)) - (cc - ca*cb))
    # side sine-norms: ||u x v||^2 = 1-cc^2 (=sin^2 c)
    upd('sc2', np.dot(np.cross(u,v),np.cross(u,v)) - (1-cc**2))
    upd('sb2', np.dot(np.cross(w,u),np.cross(w,u)) - (1-cb**2))
    upd('sa2', np.dot(np.cross(v,w),np.cross(v,w)) - (1-ca**2))
    # triple^2 = Gram = tp2
    tp = np.dot(u,np.cross(v,w))
    tp2 = 1 - ca**2 - cb**2 - cc**2 + 2*ca*cb*cc
    upd('tp2', tp**2 - tp2)
for k,e in maxerr.items():
    print(f"{k}: max|err| = {e:.2e}")
print("OK" if all(e<1e-10 for e in maxerr.values()) else "FAIL")
