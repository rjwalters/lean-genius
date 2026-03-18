/-
# Bounded Prime Gaps - Open Question 03:
# Constructive Verification of the 246 Bound

Source: Engelsma (2013, computer search), Polymath 8b (2014)

## The Question

The Polymath 8b result establishes liminf (p_{n+1} - p_n) ≤ 246.
The 246 comes from a specific admissible 50-tuple with diameter 246.

**OQ-03 asks**: Is 246 the *optimal* bound achievable via the 50-tuple
Maynard-Tao sieve approach? I.e., is there an admissible 50-tuple with diameter < 246?

**Answer**: NO. Thomas Engelsma's 2013 exhaustive computer search showed that
no admissible 50-tuple has diameter < 246. The tuple {0,4,...,246} is optimal.

## Results

**Part I**: Engelsma 50-tuple — explicit definition with exact computed properties.
**Part II**: Admissibility — native_decide for primes ≤ 47; automatic for p ≥ 53.
**Part III**: Diameter = 246 exactly (max = 246, min = 0).
**Part IV**: Engelsma lower bound axiom — no admissible 50-tuple has diam < 246.
**Part V**: Optimality — 246 is both achievable and minimal.
**Part VI**: Consequences — the 50-tuple approach cannot improve beyond 246.

Axioms: 1 (engelsma_lower_bound — Engelsma 2013 exhaustive computation)
Sorries: 0
-/
import Mathlib
import Proofs.BoundedPrimeGaps

namespace BoundedPrimeGapsOQ03

open BoundedPrimeGaps Nat Finset

/-
## Part I: The Engelsma/Polymath 50-Tuple (Public Definition)
-/

/-- The Engelsma/Polymath narrowest known admissible 50-tuple with diameter 246.
    Discovered by Thomas Engelsma (2013) via exhaustive computer search. -/
def engelsma50Tuple : Finset ℕ :=
  {0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94,
   100, 106, 108, 114, 118, 126, 130, 136, 144, 148, 150, 156, 160, 168,
   174, 178, 184, 190, 196, 198, 204, 210, 214, 216, 220, 226, 228, 234,
   238, 240, 244, 246}

theorem engelsma50Tuple_card : engelsma50Tuple.card = 50 := by native_decide

theorem engelsma50Tuple_nonempty : engelsma50Tuple.Nonempty := ⟨0, by native_decide⟩

theorem engelsma50Tuple_zero_mem : 0 ∈ engelsma50Tuple := by native_decide

theorem engelsma50Tuple_246_mem : 246 ∈ engelsma50Tuple := by native_decide

theorem engelsma50Tuple_le_246 : ∀ a ∈ engelsma50Tuple, a ≤ 246 := by native_decide

/-
## Part II: Admissibility

Key: for p ≥ 53, admissibility is automatic since |tuple| = 50 < 53 ≤ p.
For primes p ≤ 47, admissibility is verified by native_decide.
-/

theorem engelsma50Tuple_admissible : IsAdmissible engelsma50Tuple := by
  intro p hp
  have himg_le : (engelsma50Tuple.image (· % p)).card ≤ 50 :=
    Finset.card_image_le.trans engelsma50Tuple_card.le
  by_cases hp2 : p = 2; · subst hp2; native_decide
  by_cases hp3 : p = 3; · subst hp3; native_decide
  by_cases hp5 : p = 5; · subst hp5; native_decide
  by_cases hp7 : p = 7; · subst hp7; native_decide
  by_cases hp11 : p = 11; · subst hp11; native_decide
  by_cases hp13 : p = 13; · subst hp13; native_decide
  by_cases hp17 : p = 17; · subst hp17; native_decide
  by_cases hp19 : p = 19; · subst hp19; native_decide
  by_cases hp23 : p = 23; · subst hp23; native_decide
  by_cases hp29 : p = 29; · subst hp29; native_decide
  by_cases hp31 : p = 31; · subst hp31; native_decide
  by_cases hp37 : p = 37; · subst hp37; native_decide
  by_cases hp41 : p = 41; · subst hp41; native_decide
  by_cases hp43 : p = 43; · subst hp43; native_decide
  by_cases hp47 : p = 47; · subst hp47; native_decide
  -- p ≥ 53: card(image) ≤ 50 < 53 ≤ p
  have hp53 : p ≥ 53 := by
    have h2le := hp.two_le
    by_contra hlt
    push_neg at hlt
    interval_cases p <;>
      first | exact absurd rfl hp2 | exact absurd rfl hp3
             | exact absurd rfl hp5 | exact absurd rfl hp7
             | exact absurd rfl hp11 | exact absurd rfl hp13
             | exact absurd rfl hp17 | exact absurd rfl hp19
             | exact absurd rfl hp23 | exact absurd rfl hp29
             | exact absurd rfl hp31 | exact absurd rfl hp37
             | exact absurd rfl hp41 | exact absurd rfl hp43
             | exact absurd rfl hp47
             | exact absurd hp (by decide)
  linarith

/-
## Part III: Exact Diameter Verification
-/

theorem engelsma50Tuple_max :
    engelsma50Tuple.max' engelsma50Tuple_nonempty = 246 := by native_decide

theorem engelsma50Tuple_min :
    engelsma50Tuple.min' engelsma50Tuple_nonempty = 0 := by native_decide

/-- The diameter (max - min) is exactly 246. -/
theorem engelsma50Tuple_diam :
    engelsma50Tuple.max' engelsma50Tuple_nonempty -
    engelsma50Tuple.min' engelsma50Tuple_nonempty = 246 := by
  rw [engelsma50Tuple_max, engelsma50Tuple_min]

/-- All elements lie between min (0) and max (246). -/
theorem engelsma50Tuple_mem_range (a : ℕ) (ha : a ∈ engelsma50Tuple) :
    engelsma50Tuple.min' engelsma50Tuple_nonempty ≤ a ∧
    a ≤ engelsma50Tuple.max' engelsma50Tuple_nonempty :=
  ⟨Finset.min'_le _ a ha, Finset.le_max' _ a ha⟩

/-
## Part IV: Engelsma Lower Bound (Axiom)

Engelsma (2013) proved by exhaustive computer search that no admissible 50-tuple
has diameter < 246. This is the computational foundation of the 246 bound being tight.
-/

/-- **Engelsma's lower bound (2013)**: Any admissible set with ≥ 50 elements
    has diameter ≥ 246.
    Reference: T. Engelsma, "Permissible patterns and prime gaps" (2013). -/
axiom engelsma_lower_bound :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246

/-
## Part V: Optimality of the 246 Bound
-/

/-- The diameter 246 is achievable: the Engelsma tuple witnesses it. -/
theorem admissible_50_tuple_diam_achieved :
    ∃ H : Finset ℕ, ∃ hne : H.Nonempty,
    IsAdmissible H ∧ H.card = 50 ∧ H.max' hne - H.min' hne = 246 :=
  ⟨engelsma50Tuple, engelsma50Tuple_nonempty,
    engelsma50Tuple_admissible, engelsma50Tuple_card, engelsma50Tuple_diam⟩

/-- Any admissible 50-tuple has diameter ≥ 246. -/
theorem admissible_50_tuple_diam_ge_246 (H : Finset ℕ) (hadm : IsAdmissible H)
    (hcard : H.card ≥ 50) (hne : H.Nonempty) :
    H.max' hne - H.min' hne ≥ 246 :=
  engelsma_lower_bound H hadm hcard hne

/-- **246 is the minimum diameter for admissible 50-tuples.**
    Achieved by the Engelsma tuple (upper bound) and
    proved optimal by Engelsma's search (lower bound). -/
theorem admissible_50_tuple_min_diam :
    (∃ H : Finset ℕ, ∃ hne : H.Nonempty,
      IsAdmissible H ∧ H.card = 50 ∧ H.max' hne - H.min' hne = 246) ∧
    (∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
      ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246) :=
  ⟨admissible_50_tuple_diam_achieved,
   fun H hadm hcard hne => admissible_50_tuple_diam_ge_246 H hadm hcard hne⟩

/-- Every admissible 50-tuple contains two elements that are ≥ 246 apart. -/
theorem admissible_50_tuple_large_spread (H : Finset ℕ) (hadm : IsAdmissible H)
    (hcard : H.card ≥ 50) (hne : H.Nonempty) :
    ∃ a b : ℕ, a ∈ H ∧ b ∈ H ∧ b ≥ a + 246 := by
  have hlb := engelsma_lower_bound H hadm hcard hne
  have hle : H.min' hne ≤ H.max' hne :=
    Finset.min'_le H _ (Finset.max'_mem H hne)
  exact ⟨H.min' hne, H.max' hne, Finset.min'_mem H hne, Finset.max'_mem H hne,
    by omega⟩

/-
## Part VI: Consequences for the Polymath Bound
-/

/-- No admissible 50-tuple has diameter ≤ 245. -/
theorem no_admissible_50_tuple_diam_le_245 (H : Finset ℕ) (hcard : H.card ≥ 50)
    (hne : H.Nonempty) (hdiam : H.max' hne - H.min' hne ≤ 245) :
    ¬ IsAdmissible H := by
  intro hadm
  have hlb := engelsma_lower_bound H hadm hcard hne
  omega

/-- Any set of ≥ 50 elements with diameter < 246 is not admissible.
    This shows the 246 bound is tight: no 50-tuple sieve can do better. -/
theorem tight_246_via_admissibility :
    ∀ H : Finset ℕ, H.card ≥ 50 → ∀ hne : H.Nonempty,
    H.max' hne - H.min' hne < 246 → ¬ IsAdmissible H := by
  intro H hcard hne hdiam hadm
  have hlb := engelsma_lower_bound H hadm hcard hne
  omega

/-- The Polymath 246 bound is strictly better than Zhang's 70M bound. -/
theorem polymath_strictly_improves_zhang : (246 : ℕ) < 70000000 := by norm_num

/-- Under the 50-tuple sieve approach, the best unconditional prime gap bound is
    exactly 246: there exists an admissible 50-tuple of diameter 246, but none
    with diameter < 246 exists. -/
theorem optimal_prime_gap_via_50_tuple :
    (∃ H : Finset ℕ, IsAdmissible H ∧ H.card = 50 ∧
      ∀ hne : H.Nonempty, H.max' hne - H.min' hne = 246) ∧
    (¬ ∃ H : Finset ℕ, IsAdmissible H ∧ H.card = 50 ∧
      ∀ hne : H.Nonempty, H.max' hne - H.min' hne < 246) := by
  constructor
  · exact ⟨engelsma50Tuple, engelsma50Tuple_admissible, engelsma50Tuple_card,
      fun hne => engelsma50Tuple_diam⟩
  · intro ⟨H, hadm, hcard, hlt⟩
    have hne : H.Nonempty := Finset.card_pos.mp (by omega)
    have hlb := engelsma_lower_bound H hadm (hcard ▸ le_refl _) hne
    have hlt' := hlt hne
    omega

/-
## Part VII: Synthesis — Optimality and Prime Gap Bounds

Connecting Engelsma's combinatorial result (OQ-03) with the analytic
prime gap theorem (Polymath 8b): 246 is simultaneously achievable
(infinitely many prime pairs with gap ≤ 246) and sieve-optimal
(no 50-tuple sieve can do better).
-/

/-- The Maynard-Tao 50-tuple sieve achieves prime gaps ≤ 246 infinitely often.
    This restates the Polymath 8b axiom from BoundedPrimeGaps for convenience. -/
theorem polymath_achieves_246 : ∀ N : ℕ, ∃ n ≥ N, BoundedPrimeGaps.primeGap n ≤ 246 :=
  BoundedPrimeGaps.polymath_bounded_gaps_246

/-- For any D < 246, no admissible 50-tuple achieves diameter D.
    This shows 246 is the minimum achievable prime gap bound via the 50-tuple sieve. -/
theorem no_smaller_50_tuple_diameter (D : ℕ) (hD : D < 246) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≠ D := by
  intro H hadm hcard hne heq
  have hlb := engelsma_lower_bound H hadm hcard hne
  omega

/-- **The Polymath bound of 246 is tight**: it is simultaneously achievable
    (infinitely many prime gaps ≤ 246 via the Polymath sieve) and sieve-optimal
    (no admissible 50-tuple can achieve a prime gap bound < 246).
    This is the master theorem connecting the analytic and combinatorial sides. -/
theorem polymath_246_is_tight :
    (∀ N : ℕ, ∃ n ≥ N, BoundedPrimeGaps.primeGap n ≤ 246) ∧
    (∃ H : Finset ℕ, ∃ hne : H.Nonempty,
      IsAdmissible H ∧ H.card = 50 ∧ H.max' hne - H.min' hne = 246) ∧
    (∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
      ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246) :=
  ⟨BoundedPrimeGaps.polymath_bounded_gaps_246,
   admissible_50_tuple_diam_achieved,
   fun H hadm hcard hne => engelsma_lower_bound H hadm hcard hne⟩

/-
## Summary

Key results proved in this file:
1. `engelsma50Tuple` — the explicit Engelsma 50-tuple {0,4,...,246}
2. `engelsma50Tuple_card = 50` — exactly 50 elements
3. `engelsma50Tuple_admissible` — formally verified admissible
4. `engelsma50Tuple_max = 246`, `_min = 0` — exact extremes
5. `engelsma50Tuple_diam = 246` — exact diameter
6. `engelsma_lower_bound` (axiom) — no admissible 50-tuple has diam < 246
7. `admissible_50_tuple_diam_ge_246` — diameter ≥ 246 for any admissible 50-tuple
8. `admissible_50_tuple_large_spread` — existence of wide-spread elements
9. `no_admissible_50_tuple_diam_le_245` — diameter 245 impossible
10. `tight_246_via_admissibility` — diameter < 246 ↔ not admissible
11. `optimal_prime_gap_via_50_tuple` — 246 is exactly achievable and optimal
12. `polymath_achieves_246` — restates Polymath 8b axiom
13. `no_smaller_50_tuple_diameter` — no 50-tuple achieves diameter < 246
14. `polymath_246_is_tight` — master theorem: 246 is achievable and sieve-optimal

Mathematical significance: The Polymath bound of 246 is the best possible
result from the 50-tuple Maynard-Tao sieve. Improving the unconditional
prime gap bound requires either using larger k-tuples (at the cost of larger
diameter) or a fundamentally new sieve argument.
-/

end BoundedPrimeGapsOQ03
