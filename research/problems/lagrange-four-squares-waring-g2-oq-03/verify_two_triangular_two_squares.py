#!/usr/bin/env python3
"""Independent build-free certificate for the two-triangular / 4n+1 two-square slice.

Checks, by brute force:
  [A] n is a sum of two triangular numbers  <=>  4n+1 is a sum of two squares.
  [B] the rotation identity 4*(T a + T b)+1 = (a+b+1)^2 + (a-b)^2  over a Z^2 box.
  [C] the naive 'no prime factor == 3 mod 4' form is FALSE (n=2: 9=3^2),
      while the even-power form holds.
Companion to proofs/Proofs/TwoTrianglesTwoSquares.lean.
"""
import math

def is_tri(m):
    if m < 0: return False
    k = (math.isqrt(8*m+1)-1)//2
    return any(kk>=0 and kk*(kk+1)//2==m for kk in (k-1,k,k+1))

def sum_two_tri(n):
    a=0
    while a*(a+1)//2 <= n:
        if is_tri(n - a*(a+1)//2): return True
        a+=1
    return False

def sum_two_sq(m):
    x=0
    while x*x<=m:
        r=m-x*x
        s=math.isqrt(r)
        if s*s==r: return True
        x+=1
    return False

# [A]
bad=0; N=20000
for n in range(N):
    if sum_two_tri(n) != sum_two_sq(4*n+1): bad+=1
print(f"[A] checked n in [0,{N}): mismatches = {bad}")

# [B]
ok=True
T=lambda k:k*(k+1)//2
for a in range(-50,50):
    for b in range(-50,50):
        if 4*(T(a)+T(b))+1 != (a+b+1)**2+(a-b)**2: ok=False
print(f"[B] rotation identity over [-50,50]^2: {'PASS' if ok else 'FAIL'}")

# [C]
def factor(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
naive_fail=False; evenpow_ok=True
for n in range(N):
    m=4*n+1; f=factor(m)
    no3 = all(not(p%4==3) for p in f)
    evenpow = all((e%2==0) for p,e in f.items() if p%4==3)
    if sum_two_tri(n) != no3 and not naive_fail:
        naive_fail=True
        print(f"[C] naive 'no prime==3mod4' FALSE first at n={n}: 4n+1={m}={f}, two-tri={sum_two_tri(n)}")
    if sum_two_tri(n) != evenpow: evenpow_ok=False
print(f"[C] even-power characterization over [0,{N}): {'PASS' if evenpow_ok else 'FAIL'}")
