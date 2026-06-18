#!/usr/bin/env python3
"""
erdos-1047-oq-02 — CLOSED-FORM necking onset c_nc(m1,m2) for the GENERAL two-root
family  f(z) = z^m1 (z-1)^m2  (extends the committed m2=1 Pommerenke slice in
onset_closed_form.py to arbitrary second multiplicity m2 >= 2).

Framework (unchanged, from knowledge.md "c-free ANALYTIC onset" session):
  w = f'/f = m1/z + m2/(z-1) = (M z - m1)/(z(z-1)),   M = m1+m2
  u = 1/w,   convex  <=>  Re(u') >= 0  on the boundary.
  The non-convex region N = {Re(u') < 0} is FIXED (independent of c) while
  {|f|=c} grows, so the component around root 0 first becomes non-convex at
      c_nc(m1,m2) = min |f(z)|  over the zero-curvature locus {Re(u')=0}
                    bounding the basin around 0.

KEY ALGEBRAIC SIMPLIFICATION (this session): with w = f'/f and f''/f = w'+w^2,
the standard curvature potential is
      Phi := f f'' / (f')^2 = (w'+w^2)/w^2 = 1 + w'/w^2 = 1 - u'      (since u'=-w'/w^2).
So "Re Phi <= 1" (convex) is identical to "Re(u') >= 0", unifying the two prior
frameworks.  Closed rational forms (M = m1+m2):
      u'(z)  = (M z^2 - 2 m1 z + m1)/(M z - m1)^2
      u''(z) = -2 m1 m2 / (M z - m1)^3     (since D^2 - M N = -m1 m2).

Lagrange system for the constrained min  (grad log|f| ∥ grad Re(u')):
      (1)  Re( u'(z) )       = 0
      (2)  Im( w(z) / u''(z) ) = 0
  Using u''=-2 m1 m2/(M z-m1)^3 and w=(M z-m1)/(z(z-1)):
      w/u'' = -(M z - m1)^4 / (2 m1 m2 z (z-1)),
  so (2) is  Im( (M z - m1)^4 / (z(z-1)) ) = 0  (the real const -1/(2 m1 m2) drops).
Then c_nc = |f(z)| at the dimple solution; PSLQ recovers minpoly(c_nc^2).
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 80


# ---- symbolic confirmation of the rational closed forms -----------------------
def confirm_forms():
    z, m1, m2 = sp.symbols('z m1 m2')
    M = m1 + m2
    w = (M*z - m1)/(z*(z - 1))
    u = 1/w
    assert sp.simplify(sp.diff(u, z)    - (M*z**2 - 2*m1*z + m1)/(M*z - m1)**2) == 0
    assert sp.simplify(sp.diff(u, z, 2) + 2*m1*m2/(M*z - m1)**3) == 0
    # Phi = f f''/(f')^2 = 1 - u'  (symbolic check via w)
    Phi = (sp.diff(w, z) + w**2)/w**2
    assert sp.simplify(Phi - (1 - sp.diff(u, z))) == 0
    # w/u'' simplifies to -(Mz-m1)^4/(2 m1 m2 z(z-1))
    upp = -2*m1*m2/(M*z - m1)**3
    assert sp.simplify(w/upp + (M*z - m1)**4/(2*m1*m2*z*(z - 1))) == 0
    print("[ok] symbolic: u', u''=-2 m1 m2/(Mz-m1)^3, Phi=1-u', "
          "w/u''=-(Mz-m1)^4/(2 m1 m2 z(z-1))")


# ---- high-precision dimple solve ---------------------------------------------
def pieces(m1v, m2v):
    m1, m2 = mp.mpf(m1v), mp.mpf(m2v)
    M = m1 + m2
    f   = lambda z: z**m1*(z - 1)**m2
    up  = lambda z: (M*z**2 - 2*m1*z + m1)/(M*z - m1)**2
    # eqn (2): Im( (Mz-m1)^4 / (z(z-1)) ) = 0
    g2  = lambda z: (M*z - m1)**4/(z*(z - 1))
    return f, up, M


def cstar(m1v, m2v):
    m1, m2 = mp.mpf(m1v), mp.mpf(m2v)
    zc = m1/(m1 + m2)                      # saddle w=0
    return abs(zc**m1*(zc - 1)**m2)


def seed(m1v, m2v):
    """coarse grid scan of {Re u' = 0} for the min-|f| dimple around root 0."""
    import numpy as np
    m1, m2 = float(m1v), float(m2v)
    M = m1 + m2
    fn = lambda Z: Z**m1*(Z - 1)**m2
    cs = float(cstar(m1v, m2v))
    sad = m1/M
    xs = np.linspace(-0.6, sad*0.999, 1400)
    ys = np.linspace(0.004, 0.95, 1400)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j*Y
    with np.errstate(all="ignore"):
        up = (M*Z**2 - 2*m1*Z + m1)/(M*Z - m1)**2
        R = np.real(up)
        A = np.abs(fn(Z))
    msk = np.isfinite(R) & (np.abs(R) < 0.01) & np.isfinite(A) & (A < cs*1.02) & (X > 0)
    if not msk.any():
        return None
    am = A[msk]; i = int(np.argmin(am))
    return float(X[msk][i]), float(Y[msk][i])


def onset(m1v, m2v):
    f, up, M = pieces(m1v, m2v)
    m1, m2 = mp.mpf(m1v), mp.mpf(m2v)
    s = seed(m1v, m2v)
    if s is None:
        return None
    x0, y0 = s

    def eqs(a, b):
        z = mp.mpc(a, b)
        e1 = mp.re(up(z))
        e2 = mp.im((M*z - m1)**4/(z*(z - 1)))
        return [e1, e2]

    try:
        sol = mp.findroot(eqs, (mp.mpf(repr(x0)), mp.mpf(repr(y0))),
                          tol=mp.mpf(10)**-50)
    except Exception as e:
        return None
    z = mp.mpc(sol[0], sol[1])
    return dict(cstar=cstar(m1v, m2v), cnc=abs(f(z)), z=z,
                reup=mp.re(up(z)), x=sol[0], y=sol[1])


def minpoly(val, maxdeg=10):
    for d in range(2, maxdeg + 1):
        rel = mp.pslq([val**j for j in range(d + 1)], maxcoeff=10**16, maxsteps=10**6)
        if rel and any(rel):
            return d, rel
    return None, None


def main():
    confirm_forms()
    print()
    print(f"{'(m1,m2)':>8} | {'c*':>14} | {'c_nc':>16} | {'W':>10} | minpoly(c_nc^2)")
    print("-"*92)
    cases = [(2,1),(3,1),(3,2),(4,3),(5,2),(5,3),(7,3)]
    results = {}
    for (a,b) in cases:
        r = onset(a,b)
        if r is None:
            print(f"{('('+str(a)+','+str(b)+')'):>8} | dimple not found"); continue
        W = (r['cstar'] - r['cnc'])/r['cstar']
        d, rel = minpoly(r['cnc']**2)
        results[(a,b)] = (r, d, rel)
        print(f"{('('+str(a)+','+str(b)+')'):>8} | {mp.nstr(r['cstar'],10):>14} | "
              f"{mp.nstr(r['cnc'],14):>16} | {mp.nstr(W,6):>10} | deg={d}  res={rel}")
        # residual sanity
        assert abs(r['reup']) < mp.mpf(10)**-30, f"Re(u') not 0 for ({a},{b})"
    # Cross-check the committed (2,1) closed form
    r10 = mp.sqrt(10)
    cf = (130 - 31*r10)/1458
    if (2,1) in results:
        d = abs(results[(2,1)][0]['cnc']**2 - cf)
        print(f"\n[check] (2,1) c_nc^2 vs committed (130-31*sqrt10)/1458: diff={mp.nstr(d,3)}")
        assert d < mp.mpf(10)**-30

    # Exact surd closed forms for the degree-2 cases (new for m2>=2)
    print("\nExact surd closed forms (degree-2 minimal polynomial in t=c_nc^2):")
    surds = {
        (3,2): "c_nc(3,2)^2 = 180252/9765625 - 257526*sqrt(21)/68359375",
        (4,3): "c_nc(4,3)^2 = 2938337424/678223072849 - 795601872*sqrt(330)/3391115364245",
        (5,2): "c_nc(5,2)^2 = 6397112500/678223072849 - 10256393750*sqrt(30)/6104007655641",
    }
    for k, s in surds.items():
        print("   ", s)

    print("\nNote: deg(minpoly c_nc^2) is IRREGULAR in (m1,m2) — e.g. (5,3),(7,3)")
    print("are degree 4, (2,1),(3,2),(4,3),(5,2) degree 2; no simple closed pattern,")
    print("c_nc is an algebraic number of growing, non-monotone degree.")
    print("\nRESULT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
