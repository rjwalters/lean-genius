/-
  Erdős Problem #286 — Open Question oq-02:
  Discharging the `representation_monotone` axiom (and, with it, the whole
  existence theorem) *without* any axioms.

  Source: https://erdosproblems.com/286
  Parent gallery entry: `Proofs/Erdos286Problem.lean` (Erdos286)

  ## Context

  Erdős #286 asks, for k ≥ 2, whether `1` can be written as a sum of k distinct
  unit fractions whose denominators all lie in a *short* interval of width
  ≈ (e-1)k. Croot (2001) proved this with the sharp constant; the parent gallery
  file encodes the sharp statement as `croot_theorem` (an axiom) and the
  step k → k+1 as a second axiom `representation_monotone`, then combines them to
  prove the *bounded-interval existence* statement

      erdos_286 : ∀ k ≥ 3, ∃ width, HasShortIntervalRepresentation k width.

  The parent's `conclusion.openQuestions` lists, as oq-02:

      "Prove `representation_monotone` from the unit fraction splitting identity
       1/n = 1/(n+1) + 1/(n(n+1)), tracking interval widths."

  ## What this file contributes

  1. `representation_monotone_ge2` — the splitting step is proved as a genuine
     theorem (0 axioms) for every k ≥ 2.  The largest denominator m of an
     existing representation is split via 1/m = 1/(m+1) + 1/(m(m+1)); because m
     is the maximum, the two new denominators are fresh and distinct, so the
     cardinality grows by exactly one and the reciprocal sum is preserved.

  2. `erdos_286_exists` — the *identical* statement to the parent's `erdos_286`,
     but proved with **zero axioms**: induction from the explicit base case k = 3
     using `representation_monotone_ge2`.  (Mere bounded-interval existence never
     needed Croot's deep result — only the splitting step.  Croot is required
     solely for the *sharp* width ⌈(e-1+ε)k⌉, which we do NOT claim here.)

  3. `unrestricted_monotone_false` — a soundness observation: the parent's
     `representation_monotone` is stated for *all* k, but at k = 1 it is FALSE.
     A representation with k = 1 exists (`{1}`), and it would force a k = 2
     representation, which is impossible (`no_k2_representation`).  Hence the
     hypothesis k ≥ 2 in `representation_monotone_ge2` is not cosmetic: the
     unrestricted axiom is unsound, and the `ge2` form is the correct theorem.

  All denominator definitions are re-declared here so the file is self-contained.
-/

import Mathlib

namespace Erdos286OQ02

open Finset BigOperators

/- ## Definitions (mirroring the parent entry) -/

/-- A unit-fraction representation of a rational `q` using denominators from `S`. -/
def IsUnitFractionSum (S : Finset ℕ) (q : ℚ) : Prop :=
  (∀ n ∈ S, n > 0) ∧ ∑ n ∈ S, (1 : ℚ) / n = q

/-- `S` gives a unit-fraction representation of `1`. -/
def SumsToOne (S : Finset ℕ) : Prop := IsUnitFractionSum S 1

/-- There are `k` distinct positive integers in an interval of the given `width`
whose reciprocals sum to `1`. -/
def HasShortIntervalRepresentation (k : ℕ) (width : ℕ) : Prop :=
  ∃ a : ℕ, ∃ S : Finset ℕ,
    S.card = k ∧
    (∀ n ∈ S, a ≤ n ∧ n ≤ a + width) ∧
    SumsToOne S

/- ## The base case k = 3 (axiom-free; no `native_decide`) -/

/-- `1 = 1/2 + 1/3 + 1/6`, with denominators in `[2,6]` (width 4). -/
theorem base_k3 : HasShortIntervalRepresentation 3 4 := by
  refine ⟨2, {2, 3, 6}, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · show ∑ n ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / n = 1
    have h26 : (3 : ℕ) ∉ ({6} : Finset ℕ) := by decide
    have h236 : (2 : ℕ) ∉ ({3, 6} : Finset ℕ) := by decide
    rw [Finset.sum_insert h236, Finset.sum_insert h26, Finset.sum_singleton]
    norm_num

/- ## The splitting step, proved as a theorem -/

/-- **Monotonicity (oq-02).** For every `k ≥ 2`, a representation with `k`
denominators yields one with `k + 1` denominators (in some, possibly much
larger, interval).  Proof: split the *largest* denominator `m` via the partial
fraction identity `1/m = 1/(m+1) + 1/(m(m+1))`.  Maximality of `m` guarantees
`m+1` and `m(m+1)` are new and mutually distinct, so the cardinality increases
by exactly one and the reciprocal sum is unchanged.

The hypothesis `2 ≤ k` is essential — see `unrestricted_monotone_false`. -/
theorem representation_monotone_ge2 (k width : ℕ) (hk : 2 ≤ k)
    (h : HasShortIntervalRepresentation k width) :
    ∃ width', HasShortIntervalRepresentation (k + 1) width' := by
  simp only [HasShortIntervalRepresentation, SumsToOne, IsUnitFractionSum] at h
  obtain ⟨a, S, hcard, hint, hpos, hsum⟩ := h
  have hne : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  -- the maximum element, with its defining properties
  obtain ⟨m, hm_mem, hm_max⟩ : ∃ m, m ∈ S ∧ ∀ n ∈ S, n ≤ m :=
    ⟨S.max' hne, S.max'_mem hne, fun n hn => Finset.le_max' S n hn⟩
  have hm_pos : 0 < m := hpos m hm_mem
  -- with at least two denominators, `1 ∉ S`, hence the maximum is ≥ 2
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h' | h'
    · exfalso
      have hsub : S ⊆ {1} := by
        intro x hx
        have hx1 := hm_max x hx
        have hx2 := hpos x hx
        simp only [Finset.mem_singleton]
        omega
      have hcle := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hcle
      omega
    · exact h'
  -- the new denominators are fresh and distinct
  have hmm_gt : m < m * (m + 1) := by nlinarith
  have hm1_notS : m + 1 ∉ S := fun hmem => by have := hm_max _ hmem; omega
  have hmm_notS : m * (m + 1) ∉ S := fun hmem => by have := hm_max _ hmem; omega
  have hne_new : m + 1 ≠ m * (m + 1) := by
    have : m + 1 < m * (m + 1) := by nlinarith
    omega
  have hm1_nE : m + 1 ∉ S.erase m := fun hh => hm1_notS (Finset.mem_of_mem_erase hh)
  have hmm_nE : m * (m + 1) ∉ S.erase m := fun hh => hmm_notS (Finset.mem_of_mem_erase hh)
  have hA : m + 1 ∉ insert (m * (m + 1)) (S.erase m) := by
    simp only [Finset.mem_insert]; push_neg; exact ⟨hne_new, hm1_nE⟩
  -- the reciprocal sum over the remaining denominators
  have hsumT : ∑ n ∈ S.erase m, (1 : ℚ) / n = 1 - 1 / (m : ℚ) := by
    have key : (1 : ℚ) / m + ∑ n ∈ S.erase m, (1 : ℚ) / n = 1 := by
      rw [Finset.add_sum_erase S (fun n => (1 : ℚ) / n) hm_mem]; exact hsum
    linarith
  -- assemble the new representation
  refine ⟨m * (m + 1), ?_⟩
  simp only [HasShortIntervalRepresentation, SumsToOne, IsUnitFractionSum]
  refine ⟨1, insert (m + 1) (insert (m * (m + 1)) (S.erase m)), ?_, ?_, ?_, ?_⟩
  · -- cardinality grows by one
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hmm_nE,
        Finset.card_erase_of_mem hm_mem, hcard]
    omega
  · -- every new denominator lies in [1, 1 + m(m+1)]
    intro n hn
    simp only [Finset.mem_insert] at hn
    rcases hn with rfl | rfl | hnE
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · have hnS := Finset.mem_of_mem_erase hnE
      have h1 := hpos n hnS
      have h2 := hm_max n hnS
      exact ⟨by omega, by omega⟩
  · -- positivity
    intro n hn
    simp only [Finset.mem_insert] at hn
    rcases hn with rfl | rfl | hnE
    · omega
    · omega
    · exact hpos n (Finset.mem_of_mem_erase hnE)
  · -- the reciprocals still sum to 1
    rw [Finset.sum_insert hA, Finset.sum_insert hmm_nE, hsumT]
    have hM : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hM1 : (m : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/- ## Bounded-interval existence with NO axioms -/

/-- **Erdős #286, bounded-interval existence (axiom-free).** For every `k ≥ 3`
there is a representation of `1` by `k` distinct unit fractions with denominators
in a bounded interval.  This is the parent's `erdos_286`, here proved with zero
axioms: induction from `base_k3` using `representation_monotone_ge2`.  (The sharp
width ≈ (e-1)k still requires Croot's theorem and is not claimed.) -/
theorem erdos_286_exists :
    ∀ k, 3 ≤ k → ∃ width, HasShortIntervalRepresentation k width := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨4, base_k3⟩
  | succ n hn ih =>
    obtain ⟨w, hw⟩ := ih
    exact representation_monotone_ge2 n w (by omega) hw

/- ## Soundness: the unrestricted axiom is false -/

/-- **k = 2 is impossible.** `1 = 1/x + 1/y` with distinct positive integers has
no solution: it forces `(x-1)(y-1) = 1`, hence `x = y = 2`. -/
theorem no_k2_representation (width : ℕ) :
    ¬ HasShortIntervalRepresentation 2 width := by
  intro h
  simp only [HasShortIntervalRepresentation, SumsToOne, IsUnitFractionSum] at h
  obtain ⟨_a, S, hcard, _hint, hpos, hsumeq⟩ := h
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hx : 0 < x := hpos x (by simp)
  have hy : 0 < y := hpos y (by simp)
  rw [Finset.sum_pair hxy] at hsumeq
  have hx0 : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hy0 : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_add_div _ _ hx0 hy0, div_eq_one_iff_eq (mul_ne_zero hx0 hy0)] at hsumeq
  have key : (x : ℚ) + y = x * y := by linarith [hsumeq]
  have hnat : x + y = x * y := by exact_mod_cast key
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have e : (x' + 1) * (y' + 1) = x' * y' + x' + y' + 1 := by ring
  rw [e] at hnat
  have hprod : x' * y' = 1 := by linarith [hnat]
  have hx'1 : x' = 1 := Nat.dvd_one.mp ⟨y', hprod.symm⟩
  have hy'1 : y' = 1 := Nat.dvd_one.mp ⟨x', by rw [mul_comm] at hprod; exact hprod.symm⟩
  exact hxy (by omega)

/-- `1 = 1/1` is a (degenerate) representation with a single denominator. -/
theorem has_rep_one : HasShortIntervalRepresentation 1 0 := by
  refine ⟨1, {1}, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · show ∑ n ∈ ({1} : Finset ℕ), (1 : ℚ) / n = 1
    rw [Finset.sum_singleton]; norm_num

/-- **The unrestricted monotonicity statement is FALSE.** The parent gallery
file declares `representation_monotone` for *all* `k`, but at `k = 1` it fails:
`{1}` is a valid k=1 representation, yet no k=2 representation exists.  Thus the
`2 ≤ k` hypothesis of `representation_monotone_ge2` is necessary, and the
unrestricted axiom is unsound. -/
theorem unrestricted_monotone_false :
    ¬ (∀ k width : ℕ, HasShortIntervalRepresentation k width →
        ∃ width', HasShortIntervalRepresentation (k + 1) width') := by
  intro H
  obtain ⟨w', hw'⟩ := H 1 0 has_rep_one
  exact no_k2_representation w' hw'

end Erdos286OQ02
