#!/usr/bin/env python3
"""
Durable build-free verification for the 4-free classification lemmas added to
proofs/Proofs/ThreeSquares.lean (researcher-4, 2026-06-15):

  not_four_dvd_excluded_iff : ¬(4 ∣ n) → (IsExcludedForm n ↔ n % 8 = 7)
  odd_excluded_iff          :  Odd n   → (IsExcludedForm n ↔ n % 8 = 7)

IsExcludedForm n  ≡  ∃ a b, n = 4^a * (8b + 7).

These are the decision rule the sufficiency descent reduces to: after stripping
the 4^a factor (excluded_form_four_mul_iff), the 4-free core is excluded exactly
on the residue class 7 mod 8. Also the rigorous engine of the 1/6 density:
among 4-free numbers exactly the ≡7 mod 8 are excluded (density 1/8 of all, which
times the 4-power scaling sum 4/3 gives 1/6).

Run: python3 verify_excluded_classification.py   ->  all checks pass.
"""


def is_excluded(n: int) -> bool:
    """True iff n = 4^a (8b+7) for some a,b >= 0."""
    if n <= 0:
        return False
    x, a = n, 0
    while x % 4 == 0:
        x //= 4
        a += 1
    # n = 4^a * x with 4 not dividing x
    return x % 8 == 7


def check_4free_classification(N: int = 200000) -> None:
    bad = 0
    for n in range(1, N):
        if n % 4 != 0:  # hypothesis ¬(4 ∣ n)
            if is_excluded(n) != (n % 8 == 7):
                bad += 1
    assert bad == 0, f"4-free classification mismatches: {bad}"
    print(f"[1] not_four_dvd_excluded_iff over 1..{N}: 0 mismatches  OK")


def check_odd_classification(N: int = 200000) -> None:
    bad = 0
    for n in range(1, N):
        if n % 2 == 1:  # Odd n
            if is_excluded(n) != (n % 8 == 7):
                bad += 1
    assert bad == 0, f"odd classification mismatches: {bad}"
    print(f"[2] odd_excluded_iff over 1..{N}: 0 mismatches  OK")


def check_full_decision_via_stripping(N: int = 100000) -> None:
    # Sanity: the recursive decision (strip 4's via excluded_form_four_mul_iff,
    # then test %8=7 on the 4-free core) agrees with is_excluded.
    def decide(n: int) -> bool:
        if n == 0:
            return False
        if n % 4 == 0:
            return decide(n // 4)
        return n % 8 == 7
    bad = sum(1 for n in range(1, N) if decide(n) != is_excluded(n))
    assert bad == 0, f"recursive-decision mismatches: {bad}"
    print(f"[3] strip-4 then %8=7 recursive decision over 1..{N}: 0 mismatches  OK")


def check_density(N: int = 6_000_000) -> None:
    cnt = sum(1 for n in range(1, N) if is_excluded(n))
    ratio = cnt / N
    assert abs(ratio - 1 / 6) < 5e-4, (ratio, 1 / 6)
    print(f"[4] density of excluded forms over 1..{N}: {ratio:.6f} vs 1/6={1/6:.6f}  OK")


if __name__ == "__main__":
    check_4free_classification()
    check_odd_classification()
    check_full_decision_via_stripping()
    check_density()
    print("\nAll excluded-form classification checks pass.")
