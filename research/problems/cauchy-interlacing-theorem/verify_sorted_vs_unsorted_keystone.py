#!/usr/bin/env python3
"""
Verification certificate for the SORTED-vs-UNSORTED keystone bug
(cauchy-interlacing-theorem, flagged in s06/#24977 and s07).

Background
----------
Cauchy interlacing: for Hermitian A ∈ ℂ^{n×n} with principal (n-1)×(n-1)
submatrix B (delete one matching row/column), the *sorted* eigenvalues
interlace:  λ_k ≤ μ_k ≤ λ_{k+1}   (ascending convention).

The slug's keystone `eigenvalue_eq_iSup_iInf_rayleigh` was (s06/s07) stated over
Mathlib's `LinearMap.IsSymmetric.eigenvalues`, which is indexed by the
*eigenbasis* and is **NOT sorted**. The interlacing statement is FALSE if the
eigenvalues are read in this unsorted, basis-dependent order: the index `k` no
longer denotes "the k-th smallest", so `λ_k ≤ μ_k ≤ λ_{k+1}` need not hold.

This script provides a CONCRETE NUMERICAL WITNESS of that failure, turning the
abstract s06/s07 note into a checkable fact. It guards against a future session
"fixing" the keystone back onto the unsorted enumeration.

It checks, over many random Hermitian matrices:

  (A) interlacing ALWAYS holds for the SORTED eigenvalues (ascending), AND for
      the descending `eigenvalues₀` convention used by the Lean statement of
      record — confirming the corrected statement is true.

  (B) there EXISTS a Hermitian A and an unsorted (basis-order) enumeration of
      its eigenvalues for which `λ_k ≤ μ_k ≤ λ_{k+1}` FAILS — confirming the
      keystone is false as originally written.

Exits non-zero if (A) ever fails or (B) cannot be witnessed.
"""

import itertools
import sys

import numpy as np

rng = np.random.default_rng(20260616)


def random_hermitian(n: int) -> np.ndarray:
    M = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    return (M + M.conj().T) / 2.0


def principal_drop(A: np.ndarray, j: int) -> np.ndarray:
    """Delete row/col j (matching), giving the (n-1)×(n-1) principal submatrix."""
    idx = [i for i in range(A.shape[0]) if i != j]
    return A[np.ix_(idx, idx)]


def sorted_interlaces(A: np.ndarray, j: int, tol: float = 1e-9) -> bool:
    """λ_k ≤ μ_k ≤ λ_{k+1} for ascending-sorted eigenvalues (k = 0..n-2)."""
    lam = np.sort(np.linalg.eigvalsh(A).real)          # ascending
    mu = np.sort(np.linalg.eigvalsh(principal_drop(A, j)).real)
    n = len(lam)
    for k in range(n - 1):
        if not (lam[k] <= mu[k] + tol and mu[k] <= lam[k + 1] + tol):
            return False
    return True


def descending_interlaces(A: np.ndarray, j: int, tol: float = 1e-9) -> bool:
    """λ_i ≥ μ_i ≥ λ_{i+1} for descending `eigenvalues₀` convention."""
    lam = np.sort(np.linalg.eigvalsh(A).real)[::-1]     # descending
    mu = np.sort(np.linalg.eigvalsh(principal_drop(A, j)).real)[::-1]
    n = len(lam)
    for i in range(n - 1):
        if not (lam[i] + tol >= mu[i] and mu[i] + tol >= lam[i + 1]):
            return False
    return True


def unsorted_can_fail(A: np.ndarray, j: int, tol: float = 1e-9):
    """
    Mathlib's `eigenvalues` is indexed by the eigenbasis, i.e. an ARBITRARY
    permutation of the spectrum. Model that by testing whether SOME permutation
    of A's eigenvalues (paired against the sorted μ) violates
    `λ_k ≤ μ_k ≤ λ_{k+1}`. Returns the witnessing permutation, or None.
    """
    eig = np.linalg.eigvalsh(A).real
    mu = np.sort(np.linalg.eigvalsh(principal_drop(A, j)).real)
    n = len(eig)
    for perm in itertools.permutations(range(n)):
        lam = eig[list(perm)]
        ok = all(
            (lam[k] <= mu[k] + tol and mu[k] <= lam[k + 1] + tol)
            for k in range(n - 1)
        )
        if not ok:
            return perm, lam, mu
    return None


def main() -> int:
    ok = True

    # (A) sorted/descending interlacing always holds.
    print("== (A) sorted & descending interlacing hold over 4000 random trials ==")
    trials = 0
    for n in (2, 3, 4, 5):
        for _ in range(1000):
            A = random_hermitian(n)
            for j in range(n):
                trials += 1
                if not sorted_interlaces(A, j):
                    ok = False
                    print(f"  ASCENDING FAIL n={n} drop j={j}")
                if not descending_interlaces(A, j):
                    ok = False
                    print(f"  DESCENDING FAIL n={n} drop j={j}")
    print(f"  checked {trials} (matrix, dropped-index) pairs — all interlace [{'OK' if ok else 'FAIL'}]")

    # (B) unsorted (basis-order) enumeration can violate interlacing.
    print("\n== (B) witness: an UNSORTED eigenvalue order that BREAKS interlacing ==")
    witness = None
    for _ in range(2000):
        n = 3
        A = random_hermitian(n)
        w = unsorted_can_fail(A, 0)
        if w is not None:
            witness = (A, w)
            break
    if witness is None:
        ok = False
        print("  could NOT find a witness (unexpected) — check tol/logic [FAIL]")
    else:
        A, (perm, lam, mu) = witness
        print(f"  3×3 Hermitian A, drop index 0; eigenbasis-order permutation {perm}")
        print(f"    unsorted λ = {np.round(lam, 4)}")
        print(f"    sorted   μ = {np.round(mu, 4)}  (submatrix, ascending)")
        # show the first violated triple
        for k in range(len(lam) - 1):
            if not (lam[k] <= mu[k] + 1e-9 and mu[k] <= lam[k + 1] + 1e-9):
                print(f"    VIOLATION at k={k}: need λ_{k}={lam[k]:.4f} ≤ μ_{k}={mu[k]:.4f} "
                      f"≤ λ_{k+1}={lam[k+1]:.4f}  → FALSE")
                break
        print("  ⟹ the keystone is FALSE over Mathlib's unsorted `eigenvalues`; it must be")
        print("     stated over `eigenvalues₀`/`sortedEigs` (descending) as in the Lean record.")

    print("\nRESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
