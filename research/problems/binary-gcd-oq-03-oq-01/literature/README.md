# Literature: binary-gcd-oq-03-oq-01

## Key References

### Primary
- **BinaryGCD.lean** (`proofs/Proofs/BinaryGCD.lean`)
  — Parent proof with Stein's binary GCD formalization

### Algorithms / Complexity
- Lehmer, D.H. (1938): "Euclid's Algorithm for Large Numbers" — original paper
- Knuth, D.E. (1997): TAOCP Vol. 2, §4.5.2 — detailed analysis
- Schönhage, A. (1971): "Schnelle Berechnung von Kettenbruchentwicklungen"

### Lean 4 / Mathlib
- `Mathlib.Data.Nat.GCD.Basic` — `Nat.gcd`, `Nat.xgcd`
- `Mathlib.Data.Int.GCD` — `Int.gcd_eq_gcd_ab` (Bezout)
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup` — SL(2,ℤ) matrices
