# Unit tests of the invariant machinery on small lattices with known answers.
import sys; sys.argv=[sys.argv[0], '/dev/null', '--crosscheck']  # prevent main()
import importlib.util
spec=importlib.util.spec_from_file_location('l6', 'l6probe.py'); l6=importlib.util.module_from_spec(spec)
import builtins; l6.__name__='l6'; spec.loader.exec_module(l6)
def sym(G, prec=40):
    J,P,bl,_ = l6.jordan_2adic(G, prec)
    return " ".join(e["symbol"] for e in l6.cs_symbol(J, bl, prec))
def diag(*ds):
    n=len(ds); return [[ds[i] if i==j else 0 for j in range(n)] for i in range(n)]
tests = [
 (diag(1,1,1,1), "1^+4_4"), (diag(3,), "1^-1_3"), (diag(1,1,7,7), "1^+4_0"), (diag(1,1,3,3), "1^+4_0"),
 (diag(2,6), "2^-2_4"), ([[0,1],[1,0]], "1^+2_II"), ([[2,1],[1,2]], "1^-2_II"),
 ([[2,1,0],[1,2,0],[0,0,1]], "1^-3_5"),   # A2 + <1>: det 3, oddity 1+4 = 5
 ([[0,1,0],[1,0,0],[0,0,1]], "1^+3_1"),   # H + <1> = <1,1,7>: oddity 9=1
 (diag(4,12), "4^-2_4"), (diag(1,8), "1^+1_1 8^+1_1"),
 ([[16,0],[0,1]], "1^+1_1 16^+1_1"),
]
for G, expect in tests:
    got = sym(G); print(("OK  " if got==expect else "BAD ") + f"{G} -> {got} (expected {expect})")
# Hasse invariants via minors route vs direct formula on small forms
def hasse_minors(G, p):
    m = l6.bareiss_minors(G); n=len(G)
    d=[m[0]]+[m[k]*m[k-1] for k in range(1,n)]
    return l6.hasse_invariant(d, p)
print("c_2<3,3> =", hasse_minors(diag(3,3),2), "(expect -1)")
print("c_2<2,6> =", hasse_minors(diag(2,6),2), "(expect -1)")
print("c_2<1,1,1,1> =", hasse_minors(diag(1,1,1,1),2), "(expect 1)")
print("c_7<7,7> =", hasse_minors(diag(7,7),7), "(expect (7,7)_7=(7,-1)_7=(-1/7)=-1)")
print("c_7<7,21> =", hasse_minors(diag(7,21),7), "(expect (7,21)_7 = (7,7)(7,3) = -1*(3/7) = -(-1) = +1)")
print("c_3<1,3,3> =", hasse_minors(diag(1,3,3),3), "(expect (3,3)_3 = (-1/3) = -1)")
# 2-adic Jordan on a bigger random lattice: check P^T G P == J
import random
random.seed(1)
n=12
B=[[random.randrange(-5,6) for _ in range(n)] for _ in range(n)]
G=[[sum(B[k][i]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
J,P,bl,precP = l6.jordan_2adic(G, 60)
mod=1<<precP
PtGP = l6.matmul_mod(l6.matmul_mod(l6.transpose(P), G, mod), P, mod)
print("random Gram: P^T G P == J:", all(PtGP[i][j]%mod==J[i][j]%mod for i in range(n) for j in range(n)), "blocks:", [(v,len(ix)) for v,ix in bl], "v2(det)=", l6.v2(l6.bareiss_minors(G)[-1]))
# overlattice of B^T B must be representable: an odd unimodular overlattice with symbol 1^+n_{n mod 8} exists (B^-1 gives I_n)
if l6.bareiss_minors(G)[-1] != 0:
    ov = l6.overlattice_greedy(G, 60, verbose=False)
    Ju,_,blu,_ = l6.jordan_2adic(ov["G"], ov["prec"], track_P=False)
    print("overlattice of B^T B (random B): unimodular", ov["unimodular"], "odd", ov.get("odd"), "symbol", " ".join(e["symbol"] for e in l6.cs_symbol(Ju, blu, ov["prec"])), "expected for I_12: 1^+12_4")
# odd p Jordan
d = l6.jordan_padic_odd(diag(7,21), 7, 6); print("7-adic jordan <7,21>:", [(v,u%7) for v,u in d], "c_7 =", l6.hasse_from_padic_diag(d,7))
d = l6.jordan_padic_odd([[0,7],[7,0]], 7, 6); print("7-adic jordan 7H:", [(v,u%7) for v,u in d], "c_7 =", l6.hasse_from_padic_diag(d,7), "(7H ~ <7,-7>: (7,-7)_7 = 1)")
