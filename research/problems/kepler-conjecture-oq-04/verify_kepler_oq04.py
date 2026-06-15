#!/usr/bin/env python3
r"""
kepler-conjecture-oq-04 — exact-arithmetic certificate for the packing-density
hierarchy of non-spherical bodies in R^3.

The OQ-04 Lean file (`proofs/Proofs/KeplerConjectureOQ04.lean`) records several
numerical facts from the literature; until now none had a committed reproducible
checker (its sibling OQs do). This script supplies one. It is a VERIFICATION /
DOCUMENTATION artifact — it does NOT resolve the open optimal densities
(tetrahedra and ellipsoids remain open); it certifies the *inequalities the Lean
proof relies on* (de-risking the Docker-gated build) and the conceptual crux
behind the Bezdek–Kuperberg lattice result.

Parts:
  A. The refutation `4000/4671 > π/(3√2)` — exact, via the SAME linear chain the
     Lean uses (`Real.pi_lt_d2`: π<3.15, √2>1.4), plus the tighter squaring route
     with exact integer margins, so the next builder knows which π-bound suffices.
  B. Affine-invariance crux: a lattice packing's density is invariant under any
     invertible linear map, so the densest LATTICE ellipsoid packing equals the
     densest lattice ball packing = FCC = π/(3√2) (Bezdek–Kuperberg). Hence the
     0.7707 ellipsoid record REQUIRES a non-lattice packing.
  C. The literature density hierarchy, ordered.
"""

from fractions import Fraction as F
from math import isqrt, pi, sqrt

fail = []
def check(name, cond, detail=""):
    print(f"  [{'OK' if cond else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not cond: fail.append(name)

# ----------------------------------------------------------------------------
print("="*72)
print("Part A — refutation  4000/4671 > π/(3√2) = fccDensity  (exact)")
print("="*72)

# fccDensity = π/(3√2) = π/√18.  Target: 4000/4671 > π/(3√2).
# Cross-multiply (all positive): 4000·3·√2 > 4671·π, i.e. 12000·√2 > 4671·π.

# --- A1: the LINEAR chain the Lean proof uses (Real.pi_lt_d2 + √2>1.4) ---
# π < 3.15   and   √2 > 1.4   (since 1.4² = 1.96 < 2).
check("π < 3.15  (Real.pi_lt_d2)", pi < 3.15, f"π≈{pi:.6f}")
check("√2 > 1.4  (1.4²=1.96<2)", F(14,10)**2 < 2, "1.96 < 2")
lhs = F(4671) * F(315,100)     # 4671·3.15  ≥ 4671·π  (upper bound on RHS of cross-mult)
rhs = F(12000) * F(14,10)      # 12000·1.4  ≤ 12000·√2 (lower bound on LHS)
check("4671·3.15 < 12000·1.4", lhs < rhs,
      f"{float(lhs)} < {float(rhs)}  (exact gap {rhs-lhs} = {float(rhs-lhs)})")
# chain: 4671·π < 4671·3.15 < 12000·1.4 < 12000·√2  ⇒  π/(3√2) < 4000/4671.
check("⇒ linear chain certifies the refutation", (pi < 3.15) and (lhs < rhs)
      and (F(14,10)**2 < 2))

# --- A2: tighter SQUARING route with exact integer margins (per knowledge.md) ---
# 12000·√2 > 4671·π ⟺ 12000²·2 > 4671²·π² ⟺ 288_000_000 > 21_818_241·π².
L = 12000**2 * 2
M = 4671**2
check("12000²·2 = 288_000_000", L == 288_000_000, str(L))
check("4671² = 21_818_241", M == 21_818_241, str(M))
# Valid rational UPPER bounds on π² (each strictly > π²≈9.86960440109):
#   9.8696045  (tight, Real.pi_sq_lt-style)   and   9.9225 = 3.15²  (loose, π<3.15).
for tag, pisq_ub in [("tight π²<9.8696045", F(98696045,10**7)),
                     ("loose π²<9.9225 (π<3.15)", F(99225,10**4))]:
    valid = float(pisq_ub) > pi**2          # the bound is a genuine upper bound
    prod = M * pisq_ub
    margin = L - prod
    check(f"288e6 > 21_818_241·({tag})  [bound valid]", (margin > 0) and valid,
          f"product≈{float(prod):,.0f}  exact margin≈{float(margin):,.0f}")
check("both rational bounds genuinely exceed π²",
      9.8696045 > pi**2 and 9.9225 > pi**2, f"π²≈{pi**2:.8f}")

# numeric values, for the record
check("4000/4671 ≈ 0.856348", abs(float(F(4000,4671)) - 0.8563477) < 1e-6,
      f"{float(F(4000,4671)):.8f}")
check("π/(3√2) ≈ 0.740480", abs(pi/(3*sqrt(2)) - 0.7404805) < 1e-6,
      f"{pi/(3*sqrt(2)):.8f}")
check("dimer beats FCC by ≈0.1159", abs((float(F(4000,4671)) - pi/(3*sqrt(2))) - 0.11587) < 1e-4,
      f"{float(F(4000,4671)) - pi/(3*sqrt(2)):.6f}")

# ----------------------------------------------------------------------------
print("="*72)
print("Part B — affine invariance ⇒ densest LATTICE ellipsoid = FCC (Bezdek–Kuperberg)")
print("="*72)
# A lattice packing of body K by lattice Λ has density  δ = vol(K)/covol(Λ).
# Under an invertible linear map T (det≠0):  K↦T(K), Λ↦T(Λ),
#   vol(T(K)) = |det T|·vol(K),  covol(T(Λ)) = |det T|·covol(Λ),
# so δ is UNCHANGED. The ball↦ellipsoid map T=diag(1,1,α) turns the optimal FCC
# ball packing into an ellipsoid lattice packing of the SAME density π/(3√2).
# Demonstrate numerically: build FCC, scale by several T, confirm δ invariant.

# FCC as the D3 lattice with basis rows; nearest-neighbor distance = √2,
# spheres of radius √2/2. Density = (vol ball r=√2/2)/covol. (stdlib only)
def det3(M):
    a,b,c=M
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))

# FCC basis (rows), covolume |det| = 2 (conventional FCC with edge 2 cube, 4 pts):
fcc = [[1,1,0],[1,0,1],[0,1,1]]
covol_fcc = abs(det3(fcc))            # = 2
# nearest distance in this FCC basis = √2 ⇒ sphere radius = √2/2, vol = (4/3)π r³
r = sqrt(2)/2
vol_ball = (4/3)*pi*r**3
delta_fcc = vol_ball/covol_fcc
check("FCC sphere density = π/(3√2)", abs(delta_fcc - pi/(3*sqrt(2))) < 1e-12,
      f"{delta_fcc:.10f} vs {pi/(3*sqrt(2)):.10f}")

def apply_T(T, basis):
    # T diagonal diag(t0,t1,t2) applied to lattice basis rows (columns of generator)
    return [[T[k]*basis[i][k] for k in range(3)] for i in range(3)]

ok_inv = True
for alpha in [0.5, 1.0, 1.4142135, 2.0, 3.0]:
    T = [1.0, 1.0, alpha]
    ell_basis = apply_T(T, fcc)
    covol_ell = abs(det3(ell_basis))                 # = |det T|·covol_fcc = α·2
    vol_ell = (4/3)*pi*(1.0)*(1.0)*alpha * (r**3)    # vol of ellipsoid = α·vol_ball
    delta_ell = vol_ell/covol_ell
    same = abs(delta_ell - delta_fcc) < 1e-9
    ok_inv = ok_inv and same
    print(f"    α={alpha:<9} δ_lattice_ellipsoid={delta_ell:.10f}  (Δ from FCC {delta_ell-delta_fcc:+.2e})")
check("lattice ellipsoid density ≡ FCC for all α (affine invariance)", ok_inv)
check("⇒ 0.7707 ellipsoid record needs NON-lattice packing",
      0.7707 > pi/(3*sqrt(2)), f"0.7707 > {pi/(3*sqrt(2)):.4f}; lattice can only reach {pi/(3*sqrt(2)):.4f}")

# ----------------------------------------------------------------------------
print("="*72)
print("Part C — literature density hierarchy (ordered)")
print("="*72)
fcc_d = pi/(3*sqrt(2))
hierarchy = [
    ("FCC sphere bound (Kepler, PROVEN upper)", fcc_d),
    ("Ellipsoid α≈√2, non-lattice (Donev 2004)", 0.7707),
    ("Tetrahedra: Conway–Torquato 2006 (lower)", 0.717),
    ("Tetrahedra: Chen 2008 (lower)", 0.778),
    ("Tetrahedra: Kallus–Elser–Gravel 2010", 0.8226),
    ("Tetrahedra: dimer 4000/4671 (Chen–Engel–Glotzer 2010, best)", float(F(4000,4671))),
]
for name, d in hierarchy:
    print(f"    {d:.6f}  {name}")
check("ellipsoid record (0.7707) strictly exceeds FCC", 0.7707 > fcc_d)
check("dimer (0.85638) is the max listed", float(F(4000,4671)) == max(d for _,d in hierarchy))
check("dimer > all tetra lower bounds", float(F(4000,4671)) > 0.8226 > 0.778 > 0.717)

print()
print("="*72)
if fail:
    print(f"FAILURES: {fail}")
    raise SystemExit(1)
print("ALL CHECKS PASS.  (Open: exact optimal densities for tetrahedra & ellipsoids.)")
