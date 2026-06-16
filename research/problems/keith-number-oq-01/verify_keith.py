#!/usr/bin/env python3
"""Independent numeric certificate for: the smallest Keith number is 14.

A Keith number is an n-digit number N >= 10 whose digit recurrence reaches N.
The recurrence: start from the decimal digits of N (most-significant first);
each new term is the sum of the previous n terms (a sliding length-n window).

Mirrors the Lean definitions in proofs/Proofs/KeithNumberOQ01.lean:
  - msd_digits  ~ msdDigits
  - reaches     ~ reaches (fuel-bounded, stop once running sum >= target)
  - is_keith    ~ IsKeith (requires 10 <= n)

Confirms (a) 14 is Keith, (b) no 0 <= n < 14 is Keith.
"""


def msd_digits(n: int) -> list[int]:
    return [int(c) for c in str(n)]


def reaches(target: int, fuel: int, window: list[int]) -> bool:
    w = list(window)
    for _ in range(fuel):
        s = sum(w)
        if s == target:
            return True
        if s > target:
            return False
        w = w[1:] + [s]
    return False


def is_keith(n: int) -> bool:
    return n >= 10 and reaches(n, 40, msd_digits(n))


def main() -> None:
    assert is_keith(14), "14 must be Keith (1,4,5,9,14)"
    for n in range(0, 14):
        assert not is_keith(n), f"{n} unexpectedly Keith"
        print(f"n={n:2d}  keith={is_keith(n)}")
    print("n=14  keith=True  (sequence 1,4,5,9,14)")
    # Sanity: OEIS A007629 next terms.
    nxt = [n for n in range(10, 50) if is_keith(n)]
    assert nxt[:4] == [14, 19, 28, 47], f"unexpected Keith prefix {nxt[:4]}"
    print(f"first Keith numbers: {nxt[:4]} (matches OEIS A007629)")
    print("CERT PASS: 14 is the least Keith number.")


if __name__ == "__main__":
    main()
