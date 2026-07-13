#!/usr/bin/env python3
"""
Hunt for a curvature-verified non-convex SEPARATE lemniscate component.

Two questions:
 (Q1) For low-degree examples (deg 2 Cassini, deg 3 z^3-z), do separate
      components stay convex right up to the merge threshold? (-> supports a
      partial characterization)
 (Q2) Pommerenke's family f(z)=z^k(z-a): for which k,a,c does the component
      around the multiple root 0 become NON-CONVEX while still separate from
      the component around a?  This is the canonical Erdos #1047 counterexample;
      exhibiting it with a computed kappa<0 answers the gallery's open question
      "make counterexamples explicit with computed convexity violations."

Method: numerically (no symbolics). g=|f|^2 sampled on a grid; components via
ndimage.label; boundary curvature via finite differences of g, calibrated so a
disk has kappa>0. We scan c upward, locate the largest c with the desired number
of separate components (just below merge), and report min curvature per component.
"""
import numpy as np
from scipy import ndimage


def make_g(roots, mult):
    """f(z)=prod (z-r)^m ; return g(x,y)=|f|^2 and its needed partials by AUTODIFF-free
    finite differences are avoided -- instead use exact complex evaluation + analytic
    derivative of g via f and f'."""
    roots = np.array(roots, dtype=complex)
    mult = np.array(mult, dtype=int)

    def f(z):
        out = np.ones_like(z, dtype=complex)
        for r, m in zip(roots, mult):
            out = out * (z - r) ** m
        return out

    def fp(z):
        # f'(z) = f(z) * sum m_i/(z-r_i)
        s = np.zeros_like(z, dtype=complex)
        for r, m in zip(roots, mult):
            s = s + m / (z - r)
        return f(z) * s

    def fpp(z):
        # f'' = f * [ (sum m/(z-r))^2 - sum m/(z-r)^2 ]
        s1 = np.zeros_like(z, dtype=complex)
        s2 = np.zeros_like(z, dtype=complex)
        for r, m in zip(roots, mult):
            s1 = s1 + m / (z - r)
            s2 = s2 + m / (z - r) ** 2
        return f(z) * (s1 ** 2 - s2)

    return f, fp, fpp


def curvature_on_curve(pts, f, fp, fpp):
    """Convex-calibrated signed curvature of {g=c} at complex points pts, where g=|f|^2.
    Using g = f*conj(f). With w=x+iy:
      g_x = 2 Re(conj(f) f'),  g_y = 2 Re(conj(f) (i f')) = -2 Im(conj(f) f')
    Let A=conj(f)*f'. g_x=2 Re A, g_y=-2 Im A.
    Second derivatives (df/dx=f', df/dy=i f'):
      g_xx = 2 Re(conj(f) f'') + 2 |f'|^2
      g_yy = 2 Re(conj(f)(i^2 f'')) + 2 |i f'|^2 = -2 Re(conj(f) f'') + 2|f'|^2
      g_xy = 2 Re(conj(f)(i f'')) + 2 Re(conj(f') (i f')) = -2 Im(conj(f) f'') + 2 Re(i |f'|^2... )
    Compute carefully numerically instead:
    """
    z = pts
    F = f(z); Fp = fp(z); Fpp = fpp(z)
    A = np.conj(F) * Fp
    gx = 2 * A.real
    gy = -2 * A.imag
    # df/dx = f', df/dy = i f'
    # g = F conj(F).  g_xx = 2 Re( conj(F) F_xx + |F_x|^2 ), F_xx=f''
    gxx = 2 * (np.conj(F) * Fpp).real + 2 * (np.abs(Fp) ** 2)
    # F_y = i f', F_yy = i^2 f'' = -f''
    gyy = 2 * (np.conj(F) * (-Fpp)).real + 2 * (np.abs(1j * Fp) ** 2)
    # g_xy = 2 Re( conj(F) F_xy + conj(F_x) F_y ), F_xy = i f''
    gxy = 2 * (np.conj(F) * (1j * Fpp)).real + 2 * (np.conj(Fp) * (1j * Fp)).real
    num = gx ** 2 * gyy - 2 * gx * gy * gxy + gy ** 2 * gxx
    den = (gx ** 2 + gy ** 2)
    good = den > 1e-12
    k = np.full(z.shape, np.nan)
    k[good] = num[good] / den[good] ** 1.5
    return k


def newton(pts, f, fp, c, steps=5):
    z = pts.copy()
    for _ in range(steps):
        F = f(z)
        g = (F.real ** 2 + F.imag ** 2) - c
        A = np.conj(F) * fp(z)
        gx = 2 * A.real
        gy = -2 * A.imag
        n2 = gx ** 2 + gy ** 2
        n2[n2 < 1e-14] = 1e-14
        z = z - g * (gx + 1j * gy) / n2
    return z


def components_and_curv(roots, mult, c, R, res=700):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    f, fp, fpp = make_g(roots, mult)
    xs = np.linspace(-R, R, res); ys = np.linspace(-R, R, res)
    X, Y = np.meshgrid(xs, ys)
    Z = X + 1j * Y
    G = np.abs(f(Z)) ** 2
    ncomp = ndimage.label(G <= c)[1]
    cs = plt.contour(X, Y, G, levels=[c])
    loops = []
    for seg in cs.allsegs[0]:
        if len(seg) < 10:
            continue
        pts = seg[:, 0] + 1j * seg[:, 1]
        pts = newton(pts, f, fp, c)
        k = curvature_on_curve(pts, f, fp, fpp)
        k = k[np.isfinite(k)]
        if len(k):
            loops.append((float(np.min(k)), float(np.max(k)), len(k)))
    plt.close("all")
    return ncomp, loops


def find_merge(roots, mult, R, target_comps, clo, chi, res=500):
    """Bisect to find threshold where #components drops below target."""
    f, _, _ = make_g(roots, mult)
    xs = np.linspace(-R, R, res); ys = np.linspace(-R, R, res)
    X, Y = np.meshgrid(xs, ys); Z = X + 1j * Y
    G = np.abs(f(Z)) ** 2
    def nc(c):
        return ndimage.label(G <= c)[1]
    for _ in range(40):
        cm = 0.5 * (clo + chi)
        if nc(cm) >= target_comps:
            clo = cm
        else:
            chi = cm
    return clo  # largest c with >= target components


def scan_just_below_merge(name, roots, mult, R, target, cmax_guess):
    cstar = find_merge(roots, mult, R, target, 1e-6, cmax_guess)
    print(f"\n### {name}  roots={roots} mult={mult}")
    print(f"  merge threshold c* (>= {target} comps below this) ~ {cstar:.6f}")
    for frac in [0.5, 0.8, 0.95, 0.99, 0.999]:
        c = cstar * frac
        ncomp, loops = components_and_curv(roots, mult, c, R)
        mins = [round(l[0], 4) for l in loops]
        worst = min((l[0] for l in loops), default=None)
        tag = "  <<< NON-CONVEX SEPARATE COMPONENT" if (worst is not None and worst < -1e-2) else ""
        print(f"  c={c:.6f} (={frac} c*) grid_comps={ncomp} loop_min_kappas={mins} worst={worst}{tag}")


if __name__ == "__main__":
    # Q1: low-degree, do separate comps stay convex up to merge?
    scan_just_below_merge("Cassini z^2-1", [-1, 1], [1, 1], 2.0, 2, 1.5)
    scan_just_below_merge("z^3-z", [0, 1, -1], [1, 1, 1], 2.0, 3, 0.5)

    # Q2: Pommerenke z^k(z-a). Sweep k and a; look for non-convex comp around 0.
    print("\n========== POMMERENKE z^k(z-a) SWEEP ==========")
    for k in [2, 3, 4, 5, 6, 8, 10]:
        for a in [0.6, 0.8, 1.0, 1.3]:
            roots = [0.0, a]; mult = [k, 1]
            R = max(1.6 * a, 1.5)
            try:
                cstar = find_merge(roots, mult, R, 2, 1e-9, (a ** k) * a * 0.9)
                # test just below merge
                c = cstar * 0.97
                ncomp, loops = components_and_curv(roots, mult, c, R, res=800)
                worst = min((l[0] for l in loops), default=None)
                mins = [round(l[0], 4) for l in loops]
                tag = "  <<< NON-CONVEX!" if (worst is not None and worst < -1e-2) else ""
                print(f"  k={k} a={a}: c*~{cstar:.5f} c={c:.5f} comps={ncomp} mins={mins}{tag}")
            except Exception as e:
                print(f"  k={k} a={a}: ERR {e}")
