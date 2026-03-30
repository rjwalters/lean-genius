/-
Erdős Problem #195: Monotone Arithmetic Progressions in Permutations

Source: https://erdosproblems.com/195
Status: OPEN

Statement:
What is the largest k such that in any permutation of ℤ there must exist a
monotone k-term arithmetic progression x₁ < x₂ < ... < xₖ?

Known Results:
- Geneson (2019): k ≤ 5 — constructed a permutation avoiding 6-term MAPs
- Adenwalla (2022): k ≤ 4 — improved to avoid 5-term MAPs
- The exact value is UNKNOWN: 3 ≤ k ≤ 4

References:
- [ErGr79, ErGr80] Erdős-Graham: Original problem
- [Ge19] Geneson (2019): First upper bound k ≤ 5
- [Ad22] Adenwalla (2022): Improved to k ≤ 4
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos195

/- ## Part I: Basic Definitions -/

/-- A bijection from ℤ to ℤ (a permutation of the integers) -/
def IsPermutation (f : ℤ → ℤ) : Prop :=
  Function.Bijective f

/-- An arithmetic progression of length k with start a and common difference d:
    a, a+d, a+2d, ..., a+(k-1)d -/
def IsAP (xs : List ℤ) : Prop :=
  xs.length ≥ 2 ∧ ∃ d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i + 1 < xs.length →
    xs.get! (i + 1) - xs.get! i = d

/-- A monotone arithmetic progression (MAP) in a permutation f:
    An AP x₁ < x₂ < ... < xₖ such that the positions of these values
    in the permutation are also increasing: f⁻¹(x₁) < f⁻¹(x₂) < ... < f⁻¹(xₖ) -/
def IsMonotoneAP (f : ℤ → ℤ) (xs : List ℤ) : Prop :=
  IsAP xs ∧
  xs.Chain' (· < ·) ∧
  ∀ i j : ℕ, i < j → j < xs.length →
    ∃ pᵢ pⱼ : ℤ, f pᵢ = xs.get! i ∧ f pⱼ = xs.get! j ∧ pᵢ < pⱼ

/-- The permutation f contains a monotone AP of length k -/
def HasMAP (f : ℤ → ℤ) (k : ℕ) : Prop :=
  ∃ xs : List ℤ, xs.length = k ∧ IsMonotoneAP f xs

/-- The permutation f has no monotone AP of length k -/
def AvoidsMAP (f : ℤ → ℤ) (k : ℕ) : Prop :=
  ¬HasMAP f k

/- ## Part II: The Problem -/

/-- The question: what is the largest k such that every permutation of ℤ has
    a k-term MAP? This existential characterizes the answer. -/
def LargestUnavoidableMAP : Prop :=
  ∃ k : ℕ,
    (∀ f : ℤ → ℤ, IsPermutation f → HasMAP f k) ∧
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f (k + 1))

/- ## Part III: Upper Bounds -/

/-- Geneson (2019): There exists a permutation of ℤ avoiding 6-term MAPs.
    This gives k ≤ 5. -/
axiom geneson_2019 :
  ∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 6

/-- Adenwalla (2022): There exists a permutation of ℤ avoiding 5-term MAPs.
    This improves the bound to k ≤ 4. -/
axiom adenwalla_2022 :
  ∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 5

/- ## Part IV: Lower Bound -/

/-- Every permutation of ℤ contains a 3-term MAP.
    This is believed to be true but non-trivial to prove formally. -/
axiom trivial_lower_bound :
  ∀ f : ℤ → ℤ, IsPermutation f → HasMAP f 3

/- ## Part V: The Gap -/

/-- The open question: is the answer 3 or 4?
    We know 3 ≤ k ≤ 4 from the bounds above. -/
def OpenQuestion : Prop :=
  (∀ f : ℤ → ℤ, IsPermutation f → HasMAP f 4) ∨
  (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 4)

/- ## Part VI: Adenwalla's Bound Implies Geneson's -/

/-- Adenwalla's result implies Geneson's: if we can avoid 5-MAPs, we certainly
    avoid 6-MAPs (since any 6-MAP contains a 5-MAP as a subsequence). -/
theorem adenwalla_implies_geneson :
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 5) →
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 6) := by
  intro ⟨f, hperm, havoid⟩
  exact ⟨f, hperm, fun ⟨xs, hlen, hmap⟩ => by
    -- A 6-MAP contains a 5-MAP prefix, contradicting AvoidsMAP f 5
    apply havoid
    obtain ⟨⟨hlen2, d, hd, hAP⟩, hchain, hpos⟩ := hmap
    refine ⟨xs.take 5, by simp [List.length_take, hlen], ?_⟩
    refine ⟨⟨by simp [List.length_take, hlen]; omega, d, hd, fun i hi => ?_⟩,
            List.Chain'.take hchain, fun i j hij hjlen => ?_⟩
    · -- AP property preserved under take
      have hi' : i + 1 < xs.length := by
        simp [List.length_take, hlen] at hi; omega
      rw [List.get!_take (by simp [List.length_take, hlen] at hi ⊢; omega),
          List.get!_take (by simp [List.length_take, hlen] at hi ⊢; omega)]
      exact hAP i hi'
    · -- Position monotonicity preserved under take
      have hjlen' : j < xs.length := by
        simp [List.length_take, hlen] at hjlen; omega
      rw [List.get!_take (by simp [List.length_take, hlen] at hjlen ⊢; omega),
          List.get!_take (by simp [List.length_take, hlen] at hjlen ⊢; omega)]
      exact hpos i j hij hjlen'⟩

/- ## Part VII: Examples -/

/-- The identity permutation f(n) = n -/
def identityPerm : ℤ → ℤ := id

/-- The identity is a permutation -/
theorem identity_is_perm : IsPermutation identityPerm :=
  Function.bijective_id

/-- The negation permutation f(n) = -n -/
def negationPerm : ℤ → ℤ := fun n => -n

/-- Negation is a permutation -/
theorem negation_is_perm : IsPermutation negationPerm :=
  ⟨fun a b h => by simp [negationPerm] at h; exact h,
   fun b => ⟨-b, by simp [negationPerm]⟩⟩

/- ## Part VIII: Summary -/

/-- Erdős Problem #195 Summary:
    Upper bound: k ≤ 4 (Adenwalla 2022) — a permutation exists avoiding 5-MAPs.
    Lower bound: k ≥ 3 — every permutation has 3-MAPs.
    The gap: is k = 3 or k = 4? OPEN. -/
theorem erdos_195_summary :
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 5) ∧
    (∀ f : ℤ → ℤ, IsPermutation f → HasMAP f 3) := by
  exact ⟨adenwalla_2022, trivial_lower_bound⟩

end Erdos195
