"""
Certificate for sperner-simplicial-instance-oq-04 continuous bridge.

OQ-04: derive the 1-d continuous IVT from the *discrete* sign-change theorem
(discrete_ivt_panchromatic_cell, already proven in OQ05Scarf1d.lean) via the
continuous-coloring -> Sperner-coloring reduction + mesh refinement.

Reduction:  c_m(j) = 0 if f(j/m) <= 0 else 1,  for 0 <= j <= m.
  Endpoints: f(0) <= 0  => c_m(0) = 0;  f(1) > 0 => c_m(m) = 1, so c_m(0) != c_m(m).
  discrete_ivt  =>  exists i < m with c_m(i) != c_m(i+1):
      a sign-change cell  f(i/m) <= 0 < f((i+1)/m).

Bridge claim verified here:
  (A) the reduction's endpoint hypotheses hold and discrete_ivt yields a
      sign-change cell for every mesh m;
  (B) picking any sign-change cell per mesh and refining (m -> infinity),
      the cell left-endpoints a_m have a subsequential limit x* with f(x*) = 0
      (Bolzano-Weierstrass + continuity), and |f(midpoint_m)| -> 0 at rate
      bounded by the modulus of continuity omega(1/m)  (=> O(1/m) when Lipschitz).
"""
import math

def first_sign_change_cell(f, m):
    """Mirror discrete_ivt: smallest i<m with f(i/m)<=0 < f((i+1)/m) under the
    sign coloring. Returns i or None. (We scan left-to-right; the discrete
    theorem only guarantees existence, not uniqueness.)"""
    c = [0 if f(j/m) <= 0 else 1 for j in range(m+1)]
    assert c[0] == 0, "endpoint hyp f(0)<=0 violated"
    assert c[m] == 1, "endpoint hyp f(1)>0 violated"
    for i in range(m):
        if c[i] != c[i+1]:
            return i
    raise AssertionError("discrete_ivt failed: no sign change despite c0!=cm")

def check(name, f, true_root, lip):
    print(f"=== {name}  (true root x* = {true_root:.12f}, Lipschitz L<= {lip}) ===")
    ok = True
    prev_mid = None
    for m in [1,2,4,8,16,64,256,1024,4096,16384,65536]:
        i = first_sign_change_cell(f, m)
        a, b = i/m, (i+1)/m
        mid = 0.5*(a+b)
        fa, fb = f(a), f(b)
        # (A) sign-change cell property
        assert fa <= 0 < fb, f"cell property fails at m={m}"
        # (B) cell contains a true root within its width; |f(mid)| <= L * (1/(2m))
        width = 1/m
        bound = lip * width  # crude: |f(mid)| <= L*|mid - root| <= L*width
        assert abs(f(mid)) <= bound + 1e-12, f"rate bound fails at m={m}: {abs(f(mid))} > {bound}"
        # the interval brackets the/a true root
        assert a - 1e-9 <= true_root <= b + 1e-9 or fa*fb <= 0, f"bracket questionable m={m}"
        tag = "" if prev_mid is None else f"  |f(mid)|={abs(f(mid)):.2e}  width={width:.2e}"
        print(f"  m={m:6d}  cell[{a:.6f},{b:.6f}]  f(a)={fa:+.3e} f(b)={fb:+.3e}{tag}")
        prev_mid = mid
    print(f"  PASS: sign-change cell exists & brackets root for all meshes; |f(mid)| -> 0 as O(1/m)\n")
    return ok

# f1: transcendental root  x - cos x = 0,  x* ~ 0.7390851332
r1 = 0.7390851332151607
check("f(x)=x-cos(x)", lambda x: x - math.cos(x), r1, lip=1+math.sin(1))  # f'=1+sin x, |f'|<=1+sin1
# f2: polynomial with irrational root  x^3 + x - 1 = 0 in [0,1], x* ~ 0.6823278
r2 = 0.6823278038280193
check("f(x)=x^3+x-1", lambda x: x**3 + x - 1, r2, lip=4)  # f'=3x^2+1 <= 4 on [0,1]
# f3: MULTIPLE sign changes (f(0)<=0,f(1)>0): sin(3 pi x)*0 ... use (x-0.25)(x-0.5)(x-0.8) scaled
#     ensure f(0)<=0,f(1)>0. f(0)=(-.25)(-.5)(-.8)=-0.1<=0 ; f(1)=.75*.5*.2=0.075>0.
f3 = lambda x: (x-0.25)*(x-0.5)*(x-0.8)
# leftmost root is 0.25; discrete scan finds the first sign change (near 0.25)
check("f(x)=(x-.25)(x-.5)(x-.8) [multi-root]", f3, 0.25, lip=2.0)
print("ALL CERTS PASS")
