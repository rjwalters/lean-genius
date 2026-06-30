from fractions import Fraction as F
from sympy import divisor_count, isprime
import math

# Parent convention: x = sum_{n>=0} tau(n+1) / prod_{i=1..n} a_i
# Renormalized tail at level N: T_N = sum_{n>N} tau(n+1)/ prod_{i=N+1..n} a_i
#   leading term n=N+1: tau(N+2)/a_{N+1}

def tau(m): return int(divisor_count(m))

def T_N(a, N, K=400):
    # a: function n->a_n for n>=1.  Compute partial T_N up to n=N+K (exact Fraction).
    s = F(0); denom = F(1)
    for n in range(N+1, N+1+K):
        denom *= a(n)          # after this, denom = prod_{i=N+1..n} a_i
        s += F(tau(n+1),1)/denom
    return s

def x_value(a, M=600):
    s=F(0); denom=F(1)
    for n in range(0, M):
        if n>=1: denom*=a(n)
        s += F(tau(n+1),1)/denom
    return s

print("=== (1) identity sanity: (prod_{1..N} a_i) * x = integer + T_N ===")
a = lambda n: n+1            # a_n = n+1, monotone polynomial-ish (linear)
x = x_value(a, 500)
for N in [0,1,2,3,5,8]:
    P = F(1)
    for i in range(1,N+1): P*=a(i)
    lhs = P*x
    t = T_N(a,N)
    print(f" N={N}: frac(P*x)={float(lhs-math.floor(lhs)):.6f}  T_N={float(t):.6f}  match={abs(float((lhs-math.floor(lhs))-t))<1e-9}")

print("\n=== (2) polynomial growth a_n=n^2: does T_N -> 0? (engine fires => irrational) ===")
a = lambda n: n*n if n>=2 else 2
for N in [2,5,10,20,40,80,160]:
    print(f" N={N:4d}  T_N={float(T_N(a,N)):.3e}")

print("\n=== (3) SLOW non-monotone a_n that tracks tau (adversarial: keep leading term ~1) ===")
# choose a_{N+1} ~ tau(N+2) so leading term tau(N+2)/a_{N+1} ~ 1, but must ->inf
# a_n = max(tau(n+1), floor(sqrt(n)))  -> ->inf (via sqrt) but dips toward tau on primes
a = lambda n: max(tau(n+1), int(math.isqrt(n))+2)
for N in [10,50,100,300,600,1000,2000]:
    print(f" N={N:5d}  a_(N+1)={a(N+1):5d}  tau(N+2)={tau(N+2):3d}  T_N={float(T_N(a,N)):.4f}")

print("\n=== (4) very slow a_n=floor(log) -> inf but subpolynomial; liminf T_N? ===")
a = lambda n: max(2, int(math.log(n+2))+1)
vals=[]
for N in range(50, 3000, 23):
    vals.append(float(T_N(a,N,K=600)))
print(f" a_n~log n: min T_N={min(vals):.4f}  max={max(vals):.4f}  (over N in [50,3000])")

print("\n=== (5) liminf along PRIME-shifted N (tau(N+2)=2 small leading) for slow a_n=log ===")
a = lambda n: max(2, int(math.log(n+2))+1)
pv=[]
for N in range(50, 4000):
    if isprime(N+2):
        pv.append((N, a(N+1), float(T_N(a,N,K=600))))
import statistics
tn=[v[2] for v in pv]
print(f"  #prime-N samples={len(pv)}  min T_N={min(tn):.4f}  max={max(tn):.4f}")
print(f"  smallest 5: {sorted(tn)[:5]}")
