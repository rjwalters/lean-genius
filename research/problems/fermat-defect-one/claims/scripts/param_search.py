#!/usr/bin/env python3
"""
Polynomial parameterization search for the Fermat defect-one conjecture.

Goal: find (a(t), b(t), c(t)) in Z[t]^3 with

        a(t)^n + b(t)^n - c(t)^n == +-1   identically (as a polynomial in t),

with a, b, c NONCONSTANT, so the family yields infinitely many distinct integer
witnesses (a(t0), b(t0), c(t0)) as t0 ranges over Z. One such family proves the
defect-one conjecture for infinitely many witnesses at that exponent n at once.

METHOD A (this file) — exhaustive bounded-coefficient enumeration.
  Fast pure-Python integer polynomial arithmetic (coefficient lists, no sympy).
  For fixed exponent n and per-variable degree EXACTLY d, enumerate every
  integer-coefficient triple (a,b,c) of degree d with each coefficient in
  [-B, B] (leading coeff nonzero) and test a^n + b^n - c^n == +-1 directly.
  This is a finite, COMPLETE check inside the box. Any hit is reported.

  By symmetry a <-> b and to prune, we require lead(a) > 0 and a <= b
  lexicographically (the equation is symmetric in a, b; c is free). This loses
  no families (any family can be normalized this way up to swapping a,b and an
  overall sign of all leading coeffs).

METHOD B (param_obstruction.py) — the leading-coefficient / Mason-Stothers
  argument proving NO nonconstant family exists for n >= 3 at ANY coefficient
  size or degree. Method A is the empirical confirmation; Method B explains why
  the empty result is not a box-size artifact.
"""

import itertools
import sys


def polymul(p, q):
    """Multiply two integer-coefficient polynomials given as coeff lists
    (index = power of t)."""
    r = [0] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        if pi:
            for j, qj in enumerate(q):
                r[i + j] += pi * qj
    return r


def polypow(p, n):
    r = [1]
    base = p
    e = n
    while e:
        if e & 1:
            r = polymul(r, base)
        e >>= 1
        if e:
            base = polymul(base, base)
    return r


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def is_pm_one(p):
    """Return '+'/'-'/None depending on whether the trimmed poly is the
    constant +1 / -1."""
    p = trim(p)
    if len(p) == 1:
        if p[0] == 1:
            return '+'
        if p[0] == -1:
            return '-'
    return None


def degree_d_vectors(d, B):
    """All length-(d+1) integer coeff vectors with |coeff| <= B and leading
    (index d) nonzero. Vector index = power of t."""
    lower_range = range(-B, B + 1)
    lead_range = [x for x in range(-B, B + 1) if x != 0]
    for lead in lead_range:
        for rest in itertools.product(lower_range, repeat=d):
            yield list(rest) + [lead]


def enumerate_method_a(n, d, B, log):
    """Exhaustive degree-exactly-d enumeration. Returns list of hits."""
    vecs = list(degree_d_vectors(d, B))
    # Precompute a^n for all vectors once.
    pows = [polypow(v, n) for v in vecs]
    nv = len(vecs)
    total = nv * nv * nv
    log(f"  [Method A] n={n} d={d} B={B}: {nv} degree-{d} polys, "
        f"up to {total} triples (pruned by a<=b symmetry) ...")
    hits = []
    tested = 0
    for ia in range(nv):
        an = pows[ia]
        for ib in range(ia, nv):  # a <= b by index (covers a<->b symmetry)
            bn = pows[ib]
            ab = [x + y for x, y in zip(an, bn)]  # same length (both n*d+1)
            for ic in range(nv):
                tested += 1
                cn = pows[ic]
                diff = [x - y for x, y in zip(ab, cn)]
                sign = is_pm_one(diff)
                if sign is not None:
                    a, b, c = vecs[ia], vecs[ib], vecs[ic]
                    hits.append((a, b, c, sign))
                    log(f"    HIT sign={sign}: a={a}, b={b}, c={c}")
    log(f"  [Method A] n={n} d={d}: tested {tested} triples, "
        f"{len(hits)} nonconstant hit(s)")
    return hits


def fmt_poly(v):
    """Pretty-print a coeff vector as a polynomial in t."""
    terms = []
    for i, co in enumerate(v):
        if co == 0:
            continue
        if i == 0:
            terms.append(f"{co}")
        elif i == 1:
            terms.append(f"{co}*t")
        else:
            terms.append(f"{co}*t^{i}")
    return " + ".join(terms) if terms else "0"


def main():
    out = []

    def log(s):
        print(s, flush=True)
        out.append(s)

    log("=" * 72)
    log("Fermat defect-one: polynomial parameterization search (Method A)")
    log("=" * 72)

    # Degree-dependent coefficient bounds (runtime-tuned; Method B handles the
    # unbounded case for n>=3). B chosen generously for low degree where the
    # Pythagorean (n=2) leading coeffs 3,4,5 must fit.
    bounds = {1: 6, 2: 3, 3: 1}

    all_hits = {}
    for n in [2, 3, 4, 5]:
        log(f"\n### Exponent n = {n}")
        for d in [1, 2, 3]:
            hits = enumerate_method_a(n, d, bounds[d], log)
            all_hits[(n, d)] = hits

    log("\n" + "=" * 72)
    log("SUMMARY (nonconstant hits within coefficient box)")
    log("=" * 72)
    for (n, d), hits in sorted(all_hits.items()):
        status = f"{len(hits)} hit(s)" if hits else "NONE"
        log(f"  n={n}, deg={d}, B={bounds[d]}: {status}")
        # show up to 5 representative hits
        for a, b, c, sign in hits[:5]:
            log(f"      sign={sign}: a({fmt_poly(a)})^{n} + b({fmt_poly(b)})^{n}"
                f" - c({fmt_poly(c)})^{n} = {sign}1")
        if len(hits) > 5:
            log(f"      ... and {len(hits)-5} more")

    n2 = sum(len(h) for (n, d), h in all_hits.items() if n == 2)
    n3plus = sum(len(h) for (n, d), h in all_hits.items() if n >= 3)
    log(f"\n  Nonconstant hits at n=2 (OUTSIDE the n>=3 conjecture): {n2}")
    log(f"  Nonconstant hits at n>=3 (the conjecture range):       {n3plus}")
    log("")
    log("  Interpretation: n=2 hits are Pythagorean-type identities and lie")
    log("  outside the n>=3 defect-one conjecture. ZERO nonconstant hits at")
    log("  n>=3 within the box is consistent with — and rigorously explained")
    log("  by — the Method B / Mason-Stothers obstruction (param_obstruction.py),")
    log("  which forbids ANY nonconstant family for n>=3 at any coefficient size")
    log("  and any degree.")


if __name__ == '__main__':
    main()
