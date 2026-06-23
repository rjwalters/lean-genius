from sympy import isprime

def is_excluded(n):
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7

def legendre(a, p):  # p odd prime
    a %= p
    if a == 0: return 0
    r = pow(a, (p-1)//2, p)
    return 1 if r == 1 else -1

def witness_exists_ne3(m):
    for d in range(1, 300):
        p = d*m - 1
        if p > 2 and p % 2 == 1 and isprime(p):
            if legendre(-d, p) == 1:
                return (d, p)
    return None

def residue3_exists(m):
    t = 1
    while t*t <= m:
        rem = m - t*t
        if rem % 2 == 0:
            mm = rem // 2
            if mm >= 2 and isprime(mm) and mm % 4 != 3:
                return (t, mm)
        t += 2
    return None

bad_ne3, bad_res3, witness_on_3 = [], [], []
for m in range(2, 4000):
    if m % 4 == 0 or is_excluded(m):
        continue
    r = m % 8
    if r == 3:
        if residue3_exists(m) is None: bad_res3.append(m)
        if witness_exists_ne3(m) is not None: witness_on_3.append(m)
    else:
        if witness_exists_ne3(m) is None: bad_ne3.append(m)

print("4-free non-excluded cores, m up to 4000")
print("m%8 in {1,2,5,6}, NO Dirichlet witness (want empty):", bad_ne3[:20], "count", len(bad_ne3))
print("m%8 = 3, NO residue-3 prime deficit (want empty):", bad_res3[:20], "count", len(bad_res3))
print("m%8 = 3 where monolithic witness works (want empty=obstruction holds):", witness_on_3[:20], "count", len(witness_on_3))
