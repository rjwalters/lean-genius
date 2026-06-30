#!/usr/bin/env python3
"""
Verification certificate for the IntFractPair.stream bundling of ∛3.

This is the open question #1 carried since S5 (~30 sessions): tie the per-aᵢ
nested-floor lemmas `cbrt3_aᵢ` to Mathlib's *canonical* continued-fraction
API `IntFractPair.stream`.

Mathlib's `IntFractPair.stream` (Mathlib/Algebra/ContinuedFractions/Computation/Basic.lean)
is the recursion the whole CF machinery is built on:

    IntFractPair.of v      = ⟨b := ⌊v⌋, fr := Int.fract v⟩
    IntFractPair.stream v 0 = some (IntFractPair.of v)
    IntFractPair.stream v (n+1) =
        (stream v n).bind (fun p => if p.fr = 0 then none else some (of p.fr⁻¹))

So for a non-terminating (irrational) v the stream never hits `none`, and the
n-th partial quotient is `aₙ = (stream v n).get.b`.

This script independently reimplements that recursion in exact-ish high
precision and checks two things the Lean bridge relies on:

  (A) The stream's b-components match the proven OEIS A002945 prefix
      a₀..a₁₁ = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5]
      (the prefix the gallery has machine-checked via cbrt3_a0..cbrt3_a11).

  (B) The *fract-chain identity* the bridge proof uses at every level:
          xₙ₊₁ = (Int.fract xₙ)⁻¹ = (xₙ - aₙ)⁻¹
      where x₀ = v and aₙ = ⌊xₙ⌋, i.e. the value whose floor is aₙ is exactly
      the nested reciprocal expression appearing in `cbrt3_aₙ`.

If either check fails the script exits non-zero. It is a regression anchor for
the bridge file `proofs/Proofs/CubeRoot3IrrationalOQ04Stream.lean`.
"""

from decimal import Decimal, getcontext
import sys

getcontext().prec = 120

# Proven prefix (machine-checked in the gallery as cbrt3_a0 .. cbrt3_a11).
PROVEN_PREFIX = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5]


def cbrt3() -> Decimal:
    """High-precision ∛3 via Newton iteration on f(x) = x^3 - 3."""
    x = Decimal(3) ** (Decimal(1) / Decimal(3))  # decimal power seed
    three = Decimal(3)
    for _ in range(200):
        x = x - (x * x * x - three) / (3 * x * x)
    return x


def stream_b_and_fract(v: Decimal, n: int):
    """
    Reimplements Mathlib's IntFractPair.stream, returning, for each index
    0..n-1, the pair (b, fr) = (⌊xᵢ⌋, fract xᵢ) and the underlying xᵢ.

    Here x₀ = v and xᵢ₊₁ = (fract xᵢ)⁻¹, exactly the Mathlib recursion
    (none of these `fr` hit 0 because ∛3 is irrational).
    """
    out = []
    x = v
    for _ in range(n):
        b = int(x.to_integral_value(rounding="ROUND_FLOOR"))
        fr = x - Decimal(b)
        out.append((b, fr, x))
        if fr == 0:
            break
        x = Decimal(1) / fr
    return out


def nested_reciprocal_value(v: Decimal, i: int) -> Decimal:
    """
    The value whose floor `cbrt3_aᵢ` asserts to equal aᵢ:
        i = 0 : v
        i = 1 : 1/(v - a₀)
        i = 2 : 1/(1/(v - a₀) - a₁)
        ...
    Built directly from the proven floors PROVEN_PREFIX (NOT from the stream),
    so that matching it against the stream's xᵢ is a genuine cross-check of the
    fract-chain identity (B).
    """
    x = v
    for j in range(i):
        x = Decimal(1) / (x - Decimal(PROVEN_PREFIX[j]))
    return x


def main() -> int:
    v = cbrt3()
    # sanity: v^3 ≈ 3
    assert abs(v * v * v - Decimal(3)) < Decimal(10) ** (-100), "cbrt3 newton failed"

    n = len(PROVEN_PREFIX)
    stream = stream_b_and_fract(v, n)

    ok = True

    # (A) b-components match the proven prefix.
    print("== (A) IntFractPair.stream b-components vs proven prefix ==")
    for i, (b, fr, x) in enumerate(stream):
        match = (b == PROVEN_PREFIX[i])
        ok = ok and match
        flag = "OK " if match else "MISMATCH"
        print(f"  n={i:2d}  stream.b={b:2d}  proven a{i}={PROVEN_PREFIX[i]:2d}  [{flag}]")

    # (B) fract-chain identity: stream's xᵢ == nested-reciprocal value from floors,
    #     and fract(xᵢ) == xᵢ - aᵢ.
    print("\n== (B) fract-chain identity  xᵢ(stream) == 1/(…-a) nest, fract=xᵢ-aᵢ ==")
    for i, (b, fr, x) in enumerate(stream):
        nest = nested_reciprocal_value(v, i)
        d_x = abs(x - nest)
        d_fr = abs(fr - (x - Decimal(PROVEN_PREFIX[i])))
        same_x = d_x < Decimal(10) ** (-80)
        same_fr = d_fr < Decimal(10) ** (-80)
        ok = ok and same_x and same_fr
        flag = "OK " if (same_x and same_fr) else "MISMATCH"
        print(f"  n={i:2d}  |x-nest|={d_x:.2e}  |fract-(x-a)|={d_fr:.2e}  [{flag}]")

    # (C) explicit n=0,1,2 witnesses the orphan Lean file proves first.
    print("\n== (C) explicit small-index witnesses (the bridge's first theorems) ==")
    a0 = int(v.to_integral_value(rounding="ROUND_FLOOR"))
    print(f"  stream cbrt3 0 = some (of cbrt3);  (of cbrt3).b = ⌊cbrt3⌋ = {a0}  (= cbrt3_floor_eq_one)")
    fr0 = v - Decimal(a0)
    x1 = Decimal(1) / fr0
    a1 = int(x1.to_integral_value(rounding="ROUND_FLOOR"))
    print(f"  (of cbrt3).fr = fract cbrt3 = cbrt3 - 1 != 0;  x1 = (fract cbrt3)⁻¹ = 1/(cbrt3-1)")
    print(f"  stream cbrt3 1 = some (of x1);  (of x1).b = ⌊1/(cbrt3-1)⌋ = {a1}  (= cbrt3_a1)")
    fr1 = x1 - Decimal(a1)
    x2 = Decimal(1) / fr1
    a2 = int(x2.to_integral_value(rounding="ROUND_FLOOR"))
    print(f"  fract x1 = x1 - 2 = 1/(cbrt3-1) - 2;  x2 = 1/(1/(cbrt3-1) - 2)")
    print(f"  stream cbrt3 2 = some (of x2);  (of x2).b = ⌊1/(1/(cbrt3-1)-2)⌋ = {a2}  (= cbrt3_a2)")
    ok = ok and (a0, a1, a2) == (1, 2, 3)

    print("\nRESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
