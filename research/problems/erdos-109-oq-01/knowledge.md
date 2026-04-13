# Knowledge Base: erdos-109-oq-01

## Problem Understanding

Erdős Problem 109, Open Question 1: Can we find B, C with specific gap conditions
in the sumset decomposition B + C ⊆ A (where A has positive upper density)?

The Moreira-Richter-Robertson proof (2019) shows arbitrary gap functions work.
The syndetic question (bounded gaps for B) remains open (likely false).

## Key Insights

- **IsPiecewiseSyndetic definition was incorrect** (fixed session 3): 
  Old: ∃ T syndetic, IsThick(S ∩ T) — too strong. Even 2ℕ fails since
  no subset of 2ℕ contains two consecutive naturals.
  New: ∃ T U, IsSyndetic T ∧ IsThick U ∧ T ∩ U ⊆ S (standard).

- **sumset_density_constraint decomposition** (session 3):
  Pick b₀ ∈ B, then C ⊆ {n | n + b₀ ∈ A} (preimage of A under +b₀).
  By monotonicity + shift invariance of upper density: done.

- Positive density does NOT imply containing an IP set
  (counterexample: {n : n mod 3 ≠ 0}). Correct: IP* (intersects every IP set).

- IP set sumset structure: split generating sequence into odd/even subsequences.

## Remaining Sorries (4)

1. `posUpperDensity_piecewiseSyndetic` — standard but requires pigeonhole/compactness
2. `upperDensity_shift` — shift invariance of density (standard real analysis)  
3. `upperDensity_mono` — monotonicity for subsets (standard, needs Filter.limsup API)
4. `posUpperDensity_ipStar` — IP Szemerédi theorem (deep ergodic theory)

## Dead Ends

- Trying to prove density sorries directly without decomposition (too complex)
- The original IsPiecewiseSyndetic definition was mathematically wrong
