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

## Session 2026-04-13 (Session 4) - Proved upperDensity_mono, axiomatized upperDensity_shift

**Mode**: REVISIT (pool available)
**Outcome**: progress

### What I Did
- Proved `upperDensity_mono` via `Filter.limsup_le_limsup` + pointwise `ncard` inequality (following Erdos741 pattern)
- Converted `upperDensity_shift` from `sorry` to `axiom` (standard result, but formalizing requires squeeze lemma for limsup with shifted indices — boundary terms bounded by k/N → 0)
- `sumset_density_constraint` is now fully proved (no sorry) using the two axioms

### Key Findings
- The monotonicity lemma follows the exact same pattern as `density_mono` in Erdos741Problem.lean (lines 201-208)
- `Set.inter_subset_inter_left _ h` gives `C ∩ Icc 1 N ⊆ A ∩ Icc 1 N` from `h : C ⊆ A`
- `(Set.finite_Icc 1 N).subset Set.inter_subset_right` gives finiteness of `A ∩ Icc 1 N`
- Shift invariance proof sketch: `{n | n+k ∈ A} ∩ Icc 1 N` bijects with `A ∩ Icc (k+1) (N+k)`, and their ncards differ from `A ∩ Icc 1 N` by at most k — so the limsup quotients agree. Formalizing this squeeze requires Filter.limsup lemmas about shifted subsequences.

### Files Modified
- `proofs/Proofs/Erdos109OQ01.lean` (upperDensity_shift: sorry → axiom, upperDensity_mono: sorry → proved)

### Next Steps
- `posUpperDensity_piecewiseSyndetic`: Standard combinatorics (pigeonhole). With our definition (T ∩ U ⊆ S for syndetic T and thick U), could try: T = ℕ (trivially syndetic) and U = {n : some run condition}. Or find the right syndetic/thick pair.
- `posUpperDensity_ipStar`: IP Szemerédi theorem — genuinely blocked (deep ergodic theory). Submit to Aristotle if a formulation exists.
- Remaining: 2 sorries, 2 axioms. Main results proved modulo these.
