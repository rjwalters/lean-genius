#!/usr/bin/env python3
"""
Certify that the GLOBAL slice-volume continuity hypotheses
(`hcont_pos` / `hcont_neg`) of
`ham_sandwich_(standard_)of_scalar_continuity`
(`proofs/Proofs/BrouwerFixedPointOQ01OQ03OQ01.lean`) are MATHEMATICALLY FALSE
for the standard *linear* parameterization, and therefore cannot be discharged
as stated — while the honest restriction `ContinuousOn (Sphere n)` IS true.

Why this matters (see knowledge.md §"Gap 1"): the Borsuk–Ulam chain in this
project threads a *global* `Continuous toFun` field (`SphereFun.continuous'`),
so `ham_sandwich_of_scalar_continuity` asks for global continuity of
  x ↦ (volume (body ∩ {y | ⟪u x, y⟫ < t x})).toReal
over ALL of `EuclideanSpace ℝ (Fin (n+1))`. For the standard linear maps
`u`, `t` this map JUMPS at `x = 0`. A future Aristotle/Docker session must NOT
attempt to prove the global statement; the deliverable is the
`ContinuousOn (Sphere n)` reformulation + dominated convergence.

This script is exact/closed-form (n = 1, body an interval) — no dependencies,
fully reproducible. Run: `python3 verify_gap1_discontinuity.py`.

Setup (n = 1: one body in ℝ¹, direction sphere S¹ ⊂ ℝ²):
  x = (x1, x2) ∈ ℝ²,  u(x) = x1 ∈ ℝ  (linear direction),  t(x) = x2 ∈ ℝ.
  body = [A, B] ⊂ ℝ.
  g(x) := length( body ∩ { y ∈ ℝ | u(x)·y < t(x) } ).
The same ray argument generalizes to every n ≥ 1 (knowledge.md): along a ray
x = s·w (s → 0⁺) with u(w) ≠ 0 the half-space is INDEPENDENT of s, so the limit
is a fixed positive slice volume, while g(0) = 0.
"""

A, B = -2.0, 3.0          # body = [A, B], length 5
LEN = B - A


def slice_len(x1: float, x2: float) -> float:
    """length( [A,B] ∩ {y | x1*y < x2} )."""
    if x1 == 0.0:
        # {y | 0 < x2} is all of ℝ (x2>0) or ∅ (x2≤0).
        return LEN if x2 > 0.0 else 0.0
    thr = x2 / x1                       # boundary point y = x2/x1
    if x1 > 0.0:
        # half-space is {y < thr}
        lo, hi = A, min(B, thr)
    else:
        # half-space is {y > thr}
        lo, hi = max(A, thr), B
    return max(0.0, hi - lo)


def approx(a: float, b: float, tol: float = 1e-12) -> bool:
    return abs(a - b) <= tol


def main() -> None:
    print("=" * 70)
    print("Gap 1 certification: global slice-volume continuity is FALSE at x=0")
    print(f"body = [{A}, {B}]  (length {LEN}),  u(x)=x1, t(x)=x2  (linear)")
    print("=" * 70)

    g0 = slice_len(0.0, 0.0)
    print(f"\n(1) value at the origin:  g(0,0) = {g0}")
    assert approx(g0, 0.0), "expected g(0)=0 (empty half-space)"

    # Approach 0 along several rays w=(cosθ,sinθ); show the limit is a FIXED
    # positive constant independent of s, hence ≠ g(0)=0  ⇒ jump discontinuity.
    print("\n(2) limits along rays x = s·(cosθ, sinθ) as s → 0+ :")
    import math
    jump_witnessed = False
    for deg in (30, 60, 120, 210, 300):
        th = math.radians(deg)
        w1, w2 = math.cos(th), math.sin(th)
        vals = [slice_len(s * w1, s * w2) for s in (1.0, 1e-1, 1e-3, 1e-6, 1e-9)]
        const = all(approx(v, vals[0]) for v in vals)
        limit = vals[0]
        tag = "JUMP vs g(0)=0" if (const and not approx(limit, 0.0)) else ""
        if const and not approx(limit, 0.0):
            jump_witnessed = True
        print(f"   θ={deg:3d}°  w=({w1:+.3f},{w2:+.3f})  "
              f"g(s·w) = {limit:.6f} (const in s: {const})  {tag}")
    assert jump_witnessed, "expected at least one ray with positive constant limit"
    print("\n   ⇒ g is NOT continuous at 0: rays give limit > 0, but g(0)=0.")
    print("   ⇒ the GLOBAL hcont_pos/hcont_neg hypotheses are non-dischargeable.")

    # On the sphere S¹ (s = 1), the map θ ↦ g is continuous (no x=0 there).
    print("\n(3) restriction to the sphere S¹ (‖x‖=1): continuous, no jumps.")
    import math
    N = 2000
    prev = None
    max_step = 0.0
    for k in range(N + 1):
        th = -math.pi + 2 * math.pi * k / N
        v = slice_len(math.cos(th), math.sin(th))
        if prev is not None:
            max_step = max(max_step, abs(v - prev))
        prev = v
    # length changes by at most O(2π/N · LEN); with N=2000 a continuous map
    # has small consecutive steps (no O(LEN) jump).
    print(f"   max |g(θ_k+1) - g(θ_k)| over {N} samples = {max_step:.4f}")
    assert max_step < 0.5 * LEN, "unexpected large jump on the sphere"
    print("   ⇒ ContinuousOn (Sphere n) is the honest, TRUE statement.")

    print("\n" + "=" * 70)
    print("PASS — global continuity false at 0; sphere continuity holds.")
    print("Deliverable for backend-up session: reformulate SphereFun /")
    print("Borsuk–Ulam chain with ContinuousOn (Sphere n) + DCT (NOT global).")
    print("=" * 70)


if __name__ == "__main__":
    main()
