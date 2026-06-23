#!/usr/bin/env python3
"""Numerical certificate for ShannonChannelCodingBEC.lean.

Confirms the two identities the Lean proof establishes for the binary erasure
channel BEC(p) (input Bool, output Option Bool, erasure = `none`):

  W x (some y) = (1 - p) if x == y else 0
  W x none     = p

  1. bec_conditional_entropy : H(X | Y) = p * H(X)   (any input distribution)
  2. bec_mi_eq               : I(X; Y) = (1 - p) * H(X)
  3. bec_capacity            : sup_q I(X; Y) = (1 - p) * log 2  (uniform input)

All entropies use natural logarithm, matching the Lean `shannonEntropy`.
"""
import math

OUTS = ("n", "0", "1")  # n = erasure (none); "0","1" = some false/true


def W(p, x, o):
    if o == "n":
        return p
    return (1 - p) if str(x) == o else 0.0


def entropy(q):  # q indexed by x in {0,1}
    return -sum((qi * math.log(qi) if qi > 0 else 0.0) for qi in q)


def conditional_HX_given_Y(p, q):
    J = {(x, o): q[x] * W(p, x, o) for x in (0, 1) for o in OUTS}
    mY = {o: sum(J[(x, o)] for x in (0, 1)) for o in OUTS}
    s = 0.0
    for x in (0, 1):
        for o in OUTS:
            j = J[(x, o)]
            if j > 0:
                s += j * math.log(j / mY[o])
    return -s  # H(X|Y) = -sum J log(J/mY)


def mutual_info(p, q):
    return entropy(q) - conditional_HX_given_Y(p, q)


def main():
    ok = True
    tol = 1e-12
    for p in (0.05, 0.1, 0.25, 0.5, 0.7, 0.9, 0.99):
        for q in ([0.5, 0.5], [0.3, 0.7], [0.9, 0.1], [1.0, 0.0]):
            HXgY = conditional_HX_given_Y(p, q)
            MI = mutual_info(p, q)
            HX = entropy(q)
            e1 = abs(HXgY - p * HX)
            e2 = abs(MI - (1 - p) * HX)
            ok &= e1 < tol and e2 < tol
        cap_uniform = mutual_info(p, [0.5, 0.5])
        e3 = abs(cap_uniform - (1 - p) * math.log(2))
        ok &= e3 < tol
        print(f"p={p:<5} capacity=(1-p)log2={ (1-p)*math.log(2):.10f} "
              f"uniform_MI={cap_uniform:.10f} err={e3:.1e}")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
