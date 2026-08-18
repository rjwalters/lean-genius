#!/usr/bin/env python3
"""Regression gate for the Stage-1 modular integer-lift domain bug."""

from pathlib import Path


def main():
    source = Path(__file__).with_name("model4444_service.py").read_text(
        encoding="utf-8")
    assert 'NewIntVar(-22, 22, f"d{o1}{o2}{e}{f}")' in source
    assert "AddModuloEquality(dm, d + 24, 12)" in source
    assert "NewIntVar(-11, 11" not in source
    # Exhaust the true difference-of-differences range.  Adding 24 keeps the
    # modulo input nonnegative and does not alter its residue.
    for left in range(-11, 12):
        for right in range(-11, 12):
            lift = left - right
            assert -22 <= lift <= 22
            assert (lift + 24) % 12 == lift % 12
    # The concrete generator-image witness that exposed the old bug.
    assert 13 > 11 and (13 + 24) % 12 == 1
    print("SERVICE LIFT REGRESSION OK")


if __name__ == "__main__":
    main()
