from fractions import Fraction as F
from sympy import divisor_count
import math
def tau(m): return int(divisor_count(m))
def T_N(a,N,K=500):
    s=F(0); d=F(1)
    for n in range(N+1,N+1+K):
        d*=a(n); s+=F(tau(n+1),1)/d
    return float(s)

print("threshold probe: a_n = floor(n^delta)+2, does T_N->0 ?")
for delta in [1.0, 0.6, 0.3, 0.15, 0.0]:
    a=(lambda dd: (lambda n: int(n**dd)+2))(delta)
    tail=[T_N(a,N) for N in [50,100,400,1600,3200]]
    print(f" delta={delta:4.2f}: T_N at N=50,100,400,1600,3200 = "+", ".join(f"{t:.4f}" for t in tail))

print("\n(log)^2 growth (subpolynomial): a_n = floor((log n)^2)+2")
a=lambda n: int(math.log(n+2)**2)+2
print(" T_N:", ", ".join(f"{T_N(a,N):.4f}" for N in [50,100,400,1600,3200]))
