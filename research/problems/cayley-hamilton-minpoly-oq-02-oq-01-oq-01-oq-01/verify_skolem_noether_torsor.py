#!/usr/bin/env python3
r"""
cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01 — Skolem–Noether for central
simple algebras: the conjugator TORSOR structure, on explicit finite-field instances.

The slug's REFINE deliverable (researcher-1) pins the structure of the conjugator
set in Skolem–Noether: if f, g : A → B are two K-algebra embeddings of a central
simple K-algebra A into a central simple K-algebra B, then by Skolem–Noether g = u·f·u⁻¹
for some unit u ∈ Bˣ, and the set

    S = { u ∈ Bˣ : g(a) = u·f(a)·u⁻¹  for all a ∈ A }

is a **torsor** under the unit group of the centralizer C_B(f(A)): it is a coset
u₀·(C_B(f(A)))ˣ, on which the centralizer-unit group acts freely and transitively.
By the double-centralizer theorem C_B(f(A)) is itself central simple with
dim_K C_B(f(A)) = dim_K B / dim_K A; the A = B case recovers Aut_K(B) ≅ Bˣ/Kˣ.

That is an abstract-algebra fact (and the Lean formalization target is a free+transitive
`MulAction (C_B(f(A)))ˣ S`). This script gives a CONCRETE, exhaustive, exact certificate
on finite-field matrix instances, where every group is finite and fully enumerable:

  K = 𝔽_q,  A = M_m(𝔽_q)  ↪  B = M_n(𝔽_q)   (n = m·k)  via  f(a) = a ⊗ I_k.

We pick a second embedding g = c·f(·)·c⁻¹ for a fixed c ∈ GL_n(𝔽_q), enumerate
S exhaustively, and verify:

  (T1) S is nonempty (Skolem–Noether: a conjugator exists);
  (T2) C_B(f(A)) = I_m ⊗ M_k, so dim_K C_B(f(A)) = k² = dim B / dim A  (double centralizer);
  (T3) |S| = |(C_B(f(A)))ˣ| = |GL_k(𝔽_q)|  (torsor ⇒ equal cardinality);
  (T4) for any u₀ ∈ S, { u₀⁻¹·u : u ∈ S } = (C_B(f(A)))ˣ  (free + transitive coset);
  (T5) A = B case (k = 1): |S| = |𝔽_qˣ| = q − 1, recovering Aut_K(M_m) ≅ M_m(𝔽_q)ˣ/𝔽_qˣ.

Pure stdlib, exact GF(q) arithmetic, exhaustive enumeration (no sampling).
Run:  python3 verify_skolem_noether_torsor.py     (exit 0 ⇔ all pass)
"""

from __future__ import annotations
import itertools
import sys

# ---------------------------------------------------------------------------
# GF(q) matrix arithmetic (q prime)
# ---------------------------------------------------------------------------

def matmul(A, B, q):
    n = len(A); m = len(B[0]); kk = len(B)
    return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(kk)) % q
                       for j in range(m)) for i in range(n))

def ident(n):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))

def kron(A, B, q):
    ra, ca = len(A), len(A[0]); rb, cb = len(B), len(B[0])
    out = []
    for i in range(ra):
        for p in range(rb):
            row = []
            for j in range(ca):
                for r in range(cb):
                    row.append((A[i][j] * B[p][r]) % q)
            out.append(tuple(row))
    return tuple(out)

def inv(M, q):
    """Inverse over GF(q) via Gauss–Jordan; returns None if singular."""
    n = len(M)
    a = [list(row) + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    for col in range(n):
        piv = next((r for r in range(col, n) if a[r][col] % q != 0), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        invp = pow(a[col][col] % q, q - 2, q)  # Fermat inverse (q prime)
        a[col] = [(x * invp) % q for x in a[col]]
        for r in range(n):
            if r != col and a[r][col] % q != 0:
                f = a[r][col] % q
                a[r] = [(a[r][t] - f * a[col][t]) % q for t in range(2 * n)]
    return tuple(tuple(a[i][n:]) for i in range(n))

def all_matrices(n, q):
    for flat in itertools.product(range(q), repeat=n * n):
        yield tuple(tuple(flat[i * n + j] for j in range(n)) for i in range(n))

def is_invertible(M, q):
    return inv(M, q) is not None

def elementary_basis(m):
    """The m² elementary matrices E_{ij} spanning M_m."""
    out = []
    for i in range(m):
        for j in range(m):
            out.append(tuple(tuple(1 if (r, c) == (i, j) else 0
                                   for c in range(m)) for r in range(m)))
    return out

# ---------------------------------------------------------------------------
# core: enumerate the centralizer, its units, and the conjugator set S
# ---------------------------------------------------------------------------

def embed(a, k, q):
    """f(a) = a ⊗ I_k."""
    return kron(a, ident(k), q)

def run_instance(m, k, q, c_seed):
    n = m * k
    Iden = ident(n)
    fbasis = [embed(a, k, q) for a in elementary_basis(m)]
    # fixed second embedding g = c f(.) c^{-1}
    # build a concrete invertible c deterministically from c_seed
    c = c_seed
    cinv = inv(c, q)
    assert cinv is not None, "seed c must be invertible"
    gbasis = [matmul(matmul(c, fb, q), cinv, q) for fb in fbasis]

    # centralizer C_B(f(A)) = { x : x f(a) = f(a) x for all basis a }
    centralizer = []
    units_Z = []
    S = []
    for x in all_matrices(n, q):
        commutes = all(matmul(x, fb, q) == matmul(fb, x, q) for fb in fbasis)
        if commutes:
            centralizer.append(x)
            if is_invertible(x, q):
                units_Z.append(x)
        # conjugator set: x f(a) = g(a) x for all a  (i.e. g = x f x^{-1}), x invertible
        if is_invertible(x, q):
            if all(matmul(x, fb, q) == matmul(gb, x, q) for fb, gb in zip(fbasis, gbasis)):
                S.append(x)
    return n, fbasis, gbasis, centralizer, units_Z, S

def gl_order(k, q):
    o = 1
    for i in range(k):
        o *= (q**k - q**i)
    return o

# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 76)
    print("Skolem–Noether conjugator torsor — exact finite-field certificates")
    print("=" * 76)
    ok = True

    # a few deterministic invertible seeds c (per dimension), built by hand
    def seed(n, q):
        # companion-like invertible matrix: I with an extra 1 in the corner + shift
        M = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        M[0][n - 1] = 1
        if n >= 2:
            M[n - 1][0] = 1
            M[n - 1][n - 1] = 0  # make it a genuine permutation-ish mix
        cand = tuple(tuple(row) for row in M)
        return cand if is_invertible(cand, q) else ident(n)

    # instances: (m, k, q, label)
    instances = [
        (2, 2, 2, "A=M2 ↪ B=M4 over F2  (genuine CSA, dim C_B = k²=4)"),
        (1, 2, 2, "A=K ↪ B=M2 over F2  (A central scalars; C_B = B)"),
        (2, 1, 2, "A=B=M2 over F2       (A=B case: Aut ≅ Bˣ/Kˣ)"),
        (2, 1, 3, "A=B=M2 over F3       (A=B case over F3)"),
    ]

    for (m, k, q, label) in instances:
        n = m * k
        c = seed(n, q)
        nn, fb, gb, centralizer, Z, S = run_instance(m, k, q, c)
        dimC = None
        # dim of centralizer = log_q |centralizer| (it's a K-subspace)
        size = len(centralizer)
        # |centralizer| = q^{dim}
        dimC = 0
        t = size
        while t > 1:
            t //= q
            dimC += 1
        glk = gl_order(k, q)
        t1 = len(S) >= 1
        t2 = (dimC == k * k)
        t3 = (len(S) == len(Z) == glk)
        # torsor: u0^{-1} S == Z
        torsor = True
        if S:
            u0inv = inv(S[0], q)
            coset = set(matmul(u0inv, u, q) for u in S)
            torsor = (coset == set(Z))
        t4 = torsor
        inst_ok = t1 and t2 and t3 and t4
        ok &= inst_ok
        print(f"\n[{label}]")
        print(f"   n={n} q={q}: |centralizer C_B(f(A))| = {size} = q^{dimC} "
              f"(expect dim k²={k*k}: {'OK' if t2 else 'FAIL'})")
        print(f"   |S| (conjugators) = {len(S)},  |Z|=|GL_{k}(F{q})| = {glk} "
              f"({'OK' if t3 else 'FAIL'})")
        print(f"   S nonempty (Skolem–Noether): {'OK' if t1 else 'FAIL'}")
        print(f"   torsor  u₀⁻¹·S == (C_B(f(A)))ˣ : {'OK' if t4 else 'FAIL'}")

    # (T5) A=B case cardinality: |S| = q-1
    print("\n(T5) A=B case |S| should equal q-1 (Aut_K(M_m) ≅ M_m(F_q)ˣ/F_qˣ):")
    for (m, k, q, label) in instances:
        if k == 1:
            n = m
            _, _, _, _, _, S = run_instance(m, k, q, seed(n, q))
            flag = (len(S) == q - 1)
            ok &= flag
            print(f"   M_{m}(F{q}): |S|={len(S)}  q-1={q-1}  {'OK' if flag else 'FAIL'}")

    print("\n" + "-" * 76)
    print("ALL PASS — the conjugator set is a free+transitive (C_B(f(A)))ˣ-torsor"
          if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)
