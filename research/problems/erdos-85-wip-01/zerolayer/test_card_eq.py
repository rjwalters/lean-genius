#!/usr/bin/env python3
"""Unit test for model4444_hlift.card_eq (exact-k cardinality).

Extracts card_eq from the encoder source and brute-forces model counts:
for each (n, k), the number of assignments to the n input lits that
extend to a satisfying assignment of the counter clauses must equal
C(n, k).  Passes on (5,2), (6,3), (4,4), (7,1) — run to reverify.
"""
import itertools, math, os

SRC = os.path.join(os.path.dirname(__file__), "model4444_hlift.py")
src = open(SRC).read()
header = """
RULE_COUNTS = {}
def bump(r, n=1): pass
nv = 0
aux_cnt = 0
def newvar():
    global nv; nv += 1; return nv
clauses = []
"""
start = src.index("def card_eq(lits, k):")
end = src.index("for v in range(N):", start)
body = src[start:end]

ok_all = True
for (n, k) in [(5, 2), (6, 3), (4, 4), (7, 1)]:
    ns = {}
    exec(header + body, ns)
    ns["nv"] = n
    ns["card_eq"](list(range(1, n + 1)), k)
    clauses, NV = ns["clauses"], ns["nv"]
    cnt = 0
    for bits in itertools.product([False, True], repeat=n):
        naux = NV - n
        for aux in itertools.product([False, True], repeat=naux):
            assign = {i + 1: bits[i] for i in range(n)}
            assign.update({n + 1 + i: aux[i] for i in range(naux)})
            if all(any((assign[abs(l)] if l > 0 else not assign[abs(l)])
                       for l in c) for c in clauses):
                cnt += 1
                break
    expect = math.comb(n, k)
    ok = cnt == expect
    ok_all &= ok
    print(f"n={n} k={k}: models {cnt} expect {expect}",
          "OK" if ok else "FAIL")
print("card_eq:", "ALL OK" if ok_all else "FAILURES PRESENT")

# ---- parity (XOR chain) test: replicate the v3 odd-a_v encoding shape
# and check model count = number of odd-weight assignments = 2^(n-1).
def xor_chain_test(n):
    nv = [n]
    clauses = []
    def newvar():
        nv[0] += 1; return nv[0]
    p = 1
    for lit in range(2, n + 1):
        q = newvar()
        clauses.append((-q, p, lit))
        clauses.append((-q, -p, -lit))
        clauses.append((q, -p, lit))
        clauses.append((q, p, -lit))
        p = q
    clauses.append((p,))
    cnt = 0
    for bits in itertools.product([False, True], repeat=n):
        naux = nv[0] - n
        for aux in itertools.product([False, True], repeat=naux):
            assign = {i + 1: bits[i] for i in range(n)}
            assign.update({n + 1 + i: aux[i] for i in range(naux)})
            if all(any((assign[abs(l)] if l > 0 else not assign[abs(l)])
                       for l in c) for c in clauses):
                cnt += 1
                break
    return cnt

pok = True
for n in (3, 4, 5):
    cnt = xor_chain_test(n)
    expect = 2 ** (n - 1)
    ok = cnt == expect
    pok &= ok
    print(f"xor n={n}: odd-weight models {cnt} expect {expect}",
          "OK" if ok else "FAIL")
print("parity:", "ALL OK" if pok else "FAILURES PRESENT")
