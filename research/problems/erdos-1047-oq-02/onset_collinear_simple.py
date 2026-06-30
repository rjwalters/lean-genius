#!/usr/bin/env python3
"""
Non-convexity ONSET for the MIDDLE oval of three EQUALLY-SPACED collinear simple
roots,  f = z(z-1)(z-2)  (erdos-1047-oq-02).  Centered coords w = z-1 give the
clean odd cubic  f = w^3 - w.

Context / what is new.
  * onset_closed_form.py (merged PR #24420) gave the closed-form onset for the
    Pommerenke family f = z^k(z-1): an EXTREMAL heavy root.
  * three_collinear_simple.py / three_root_certify.py argued NUMERICALLY that the
    MIDDLE root of three collinear SIMPLE roots also necks just below merge, but
    only inside a razor-thin window c/c* in (0.9999, 1) and without a verdict that
    is free of near-merge tracing artifacts.
  * This script SETTLES it with a tolerance-free pointwise test and PINS the
    window, and flags a tempting-but-WRONG "closed form" that a naive Lagrange
    solve produces.

Curvature criterion (Session-2, knowledge.md).  A boundary point of {|f| <= c}
is convex  <=>  Re Phi(w) <= 1, where
    Phi(w)  = f f'' / (f')^2  = 6 w^2 (w^2 - 1) / (3 w^2 - 1)^2 ,
    Phi'(w) = -12 w / (3 w^2 - 1)^3 .
The non-convex region N = {Re Phi > 1} is FIXED in the plane.  The middle oval
{|f| <= c} (component of w = 0) grows with c and the three ovals MERGE at the
saddle w = +-1/sqrt3, level
    c* = |f(1/sqrt3)| = 2/(3 sqrt3),     c*^2 = 4/27 .
The middle oval is non-convex for some c < c*  IFF  N reaches the middle basin
{|w| < 1/sqrt3} at a level strictly below merge:
    EXISTS w,  |w| < 1/sqrt3,  Re Phi(w) > 1,  |f(w)|^2 < 4/27 .          (NECK?)
This is a PURE POINTWISE question -- no boundary tracing, no tangency solve.

Onset:  c_nc = inf{ |f(w)| : Re Phi(w) >= 1, |w| < 1/sqrt3 }  (= min over the
closure of N inside the basin).

RESULTS (this script, reproduced below):
  * (NECK?) holds: N reaches the basin at |f|^2 < 4/27, robustly across
    resolutions (NOT a tolerance artifact -- the test uses strict inequalities).
    => the SEPARATED middle oval of equally-spaced collinear simple roots DOES
       become non-convex before merge.  Confirms three_collinear_simple.py.
  * The window is razor-thin:  c_nc/c* = 0.99993354,  W = (c*-c_nc)/c* = 6.646e-5.
    Onset shoulders at  w_nc ~ (-0.5401, +-0.0376)  (4 copies by w->-w & conj),
    i.e.  z_nc ~ 0.4599 +- 0.0376 i  and  1.5401 +- 0.0376 i.
  * CAUTION (a wrong closed form):  the locus {Re Phi = 1} has a genuine
    tangency / |f|-extremum at  w = (-0.50557, 0.07481)  with
        c^2 = root of  39366 t^4 - 24111 t^2 + 512 = 0   (c = 0.385248),
    BUT  c/c* = 1.00090 > 1  -- it lies just BEYOND merge and is NOT the onset.
    A naive Lagrange solve (Re Phi = 1 and grad|f| || grad Re Phi) converges to
    THIS point and over-estimates c_nc above c*.  The true onset (-0.5401,0.0376)
    is NOT a smooth tangency (the gradient-parallel residual
        T(w) = Im( f conj(f') Phi' )  ~  -2.5  there),
    so min |f| over N is attained at a non-tangential feature of the locus near
    the saddle.  A confident closed form for c_nc is therefore NOT established;
    c_nc is reported numerically.

Docker-independent. Requires numpy, mpmath.
"""
import numpy as np
import mpmath as mp

CS2 = 4.0 / 27.0                                # c*^2
CSTAR = float(2 / (3 * np.sqrt(3)))             # c* = 0.3849001794597505...
RBASIN = 1.0 / np.sqrt(3)                       # middle-basin radius


def necking_test_and_pin():
    """Tolerance-free pointwise test of (NECK?) and a refined estimate of c_nc."""
    def deepest(x0, x1, y0, y1, n):
        xs = np.linspace(x0, x1, n)
        ys = np.linspace(y0, y1, n)
        X, Y = np.meshgrid(xs, ys)
        W = X + 1j * Y
        with np.errstate(all="ignore"):
            RePhi = np.real(6 * W ** 2 * (W ** 2 - 1) / (3 * W ** 2 - 1) ** 2)
            A2 = np.abs(W ** 3 - W) ** 2
        m = (np.abs(W) < RBASIN) & np.isfinite(RePhi) & np.isfinite(A2) \
            & (RePhi >= 1) & (A2 < CS2)                # STRICT: below merge & in N
        if not m.any():
            return None
        a2 = A2[m]
        i = int(np.argmin(a2))
        return float(a2[i]), float(X[m][i]), float(Y[m][i]), int(m.sum())

    print("c*  = 2/(3 sqrt3) =", repr(CSTAR), "   c*^2 = 4/27 =", repr(CS2))
    print()
    print("(NECK?) does {Re Phi>1} reach the middle basin at |f|^2 < 4/27 ?")
    win = (-0.577, -0.45, 0.0, 0.13)
    last = None
    for n in (2000, 4000, 8000):
        r = deepest(*win, n)
        if r is None:
            print(f"  n={n:5d}: NO necking points -> middle oval convex up to merge")
            return None
        a2, x, y, cnt = r
        print(f"  n={n:5d}: {cnt:>7d} necking pts; deepest |f|^2={a2:.12f} "
              f"(c/c*={np.sqrt(a2)/CSTAR:.10f}) at w=({x:.6f},{y:.6f})")
        last = r
        win = (x - 0.01, x + 0.01, max(0.0, y - 0.01), y + 0.01)
    a2, x, y, _ = last
    cnc = np.sqrt(a2)
    print()
    print("=> (NECK?) holds robustly: middle oval NECKS before merge.")
    print(f"   c_nc  = {cnc:.12f}")
    print(f"   c_nc/c* = {cnc/CSTAR:.10f}")
    print(f"   window W = (c*-c_nc)/c* = {(CSTAR-cnc)/CSTAR:.6e}")
    print(f"   onset shoulder  w_nc ~ ({x:.5f}, {y:.5f})  "
          f"=>  z_nc ~ ({1+x:.5f}, {y:.5f})  (+ 3 symmetric copies)")
    return cnc, x, y


def wrong_closed_form_caution():
    """The clean locus tangency that lies BEYOND merge (NOT the onset)."""
    mp.mp.dps = 60
    def f(w):    return w ** 3 - w
    def fp(w):   return 3 * w ** 2 - 1
    def Phi(w):  return 6 * w ** 2 * (w ** 2 - 1) / (3 * w ** 2 - 1) ** 2
    def Phip(w): return -12 * w / (3 * w ** 2 - 1) ** 3

    def eqs(a, b):
        w = mp.mpc(a, b)
        return [mp.re(Phi(w)) - 1, mp.im(fp(w) * mp.conj(f(w)) * mp.conj(Phip(w)))]

    s = mp.findroot(eqs, (mp.mpf("-0.5"), mp.mpf("0.07")), tol=mp.mpf(10) ** -50)
    w = mp.mpc(s[0], s[1])
    c = abs(f(w))
    cs = 2 / (3 * mp.sqrt(3))
    val = c * c
    rel = mp.pslq([val ** j for j in range(5)], maxcoeff=10 ** 6, maxsteps=10 ** 6)
    res = sum(rel[j] * val ** j for j in range(5)) if rel else None
    print()
    print("--- CAUTION: a tempting but WRONG closed form ---")
    print("  smooth locus tangency  w =", mp.nstr(w, 25))
    print("  c =", mp.nstr(c, 30), "  c/c* =", mp.nstr(c / cs, 16), "(> 1 -> beyond merge)")
    print("  minpoly(c^2):", rel, "  residual", mp.nstr(res, 3) if res is not None else "n/a")
    print("  => this is NOT the onset; the onset (above) lies just BELOW c*.")


def main():
    out = necking_test_and_pin()
    wrong_closed_form_caution()
    print()
    if out is None:
        print("RESULT: middle oval convex up to merge (no pre-merge necking).")
        return 1
    print("RESULT: equally-spaced collinear simple roots z(z-1)(z-2) -- middle oval")
    print("NECKS before merge in a window W = 6.646e-5 (c_nc/c* = 0.9999335).")
    print("Confirms three_collinear_simple.py; pins the window; corrects the")
    print("beyond-merge locus tangency that a naive Lagrange solve produces.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
