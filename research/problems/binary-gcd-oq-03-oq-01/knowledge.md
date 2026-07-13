# Knowledge: binary-gcd-oq-03-oq-01

## Key Facts

### Algorithm Description
Lehmer's GCD (1938): Approximates multiple Euclidean steps using leading digits.
1. Extract leading k bits of a and b → â, b̂
2. Run extended Euclidean on â, b̂ to get matrix M = [[A,B],[C,D]]
3. Check if M is valid (same steps as exact Euclidean)
4. Apply M: a' = A*a + B*b, b' = C*a + D*b

### Key Invariants
- det(M) = ±1 (so gcd is preserved)
- Each step reduces a + b by at least half
- Termination: O(log(min(a,b))) matrix steps

### Mathlib Availability (to verify)
- `Nat.xgcd`: Extended Euclidean, returns Bezout coefficients
- `Int.gcd_eq_gcd_ab`: Bezout identity
- Matrix arithmetic in ℤ²: fully available

## References
- Lehmer, D.H. (1938): "Euclid's Algorithm for Large Numbers"
- Knuth, D.E. (1997): The Art of Computer Programming, Vol. 2, §4.5.2
