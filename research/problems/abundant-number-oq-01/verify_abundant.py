#!/usr/bin/env python3
"""Independent numeric certificate for: the smallest abundant number is 12.

n is abundant iff sum of proper divisors of n exceeds n.
Confirms (a) 12 is abundant, (b) no 1 <= n < 12 is abundant.
"""

def proper_divisor_sum(n: int) -> int:
    return sum(d for d in range(1, n) if n % d == 0)


def is_abundant(n: int) -> bool:
    return proper_divisor_sum(n) > n


def main() -> None:
    assert is_abundant(12), "12 must be abundant"
    assert proper_divisor_sum(12) == 16, "proper divisors of 12 sum to 1+2+3+4+6=16"
    for n in range(0, 12):
        s = proper_divisor_sum(n)
        assert not is_abundant(n), f"{n} unexpectedly abundant (sigma'={s})"
        print(f"n={n:2d}  properDivisorSum={s:2d}  abundant={is_abundant(n)}")
    print("n=12  properDivisorSum=16  abundant=True")
    print("CERT PASS: 12 is the least abundant number.")


if __name__ == "__main__":
    main()
