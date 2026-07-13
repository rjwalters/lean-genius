# Modular obstruction search for Fermat defect-one, Level 3.
# For each (n, eps, p): does a^n + b^n + eps == c^n (mod p) have ANY primitive
# solution (a,b,c not all == 0 mod p)? If NO solution exists -> obstruction.

def search(n, eps, p):
    # eps in {+1,-1}. Work in Z/p. eps mod p:
    e = eps % p
    found = None
    for a in range(p):
        for b in range(p):
            for c in range(p):
                if a == 0 and b == 0 and c == 0:
                    continue  # exclude all-zero (non-primitive)
                lhs = (pow(a, n, p) + pow(b, n, p) + e) % p
                rhs = pow(c, n, p) % p
                if lhs == rhs:
                    found = (a, b, c)
                    break
            if found: break
        if found: break
    return found  # None means OBSTRUCTION

primes = [3,5,7,11,13]
ns = [4,5,6]
signs = {'neg': +1, 'pos': -1}
# Mapping: negative defect a^n+b^n+1=c^n  -> eps=+1
#          positive defect a^n+b^n=c^n+1 -> a^n+b^n-1=c^n -> eps=-1

print("n  sign  p   result")
obstructions = []
for n in ns:
    for sname, eps in signs.items():
        for p in primes:
            r = search(n, eps, p)
            status = "SOLUTION "+str(r) if r else "*** OBSTRUCTION ***"
            print(f"{n}  {sname}({'+1' if eps==1 else '-1'}) {p:3d}  {status}")
            if r is None:
                obstructions.append((n, sname, eps, p))
        print()

print("=== OBSTRUCTIONS FOUND ===")
if obstructions:
    for o in obstructions:
        print(o)
else:
    print("NONE in p in {3,5,7,11,13} for n in {4,5,6}, both signs.")
