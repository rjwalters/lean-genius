/-
# Erdős Problem #643 — A general-`t` lower bound via the full star

Erdős Problem #643 concerns the extremal function `f(n,t)`: the least number of
edges forcing any `t`-uniform hypergraph on `n` vertices to contain a *crossed
pair*, i.e. four edges `A, B, C, D` with

  `A ∪ B = C ∪ D`   and   `A ∩ B = C ∩ D = ∅`   and   `{A,B} ≠ {C,D}`.

The conjecture (OPEN for `t ≥ 3`) is `f(n,t) = (1 + o(1))·C(n,t-1)`.

The parent formalization `Erdos643Problem.lean` establishes the `t = 3` lower
bound `f(n,3) ≥ C(n-1,2) + ⌊(n-1)/3⌋` via a Star ∪ Matching construction, but
leaves the **general** lower bound `f(n,t) ≥ C(n-1,t-1) + ⌊(n-1)/t⌋` as a `sorry`.

This file isolates the *dominant term* of that lower bound, axiom-free, for
**every** `t ≥ 1`. The construction is the **full star** `St₀ = { e : e.card = t,
0 ∈ e }`: all `t`-subsets through a fixed vertex `0`. Any two of its edges share
`0`, hence are never disjoint, so the star contains no crossed pair. It has
exactly `C(n-1,t-1)` edges, giving

  `f(n,t) ≥ C(n-1,t-1) + 1`     (for all `t ≥ 1`, `n ≥ 1`).

We further prove the exact binomial identity `(n-k)·C(n,k) = n·C(n-1,k)` and use
it to show `C(n-1,t-1)/C(n,t-1) → 1`, i.e. the star is the **asymptotically
optimal** construction for the lower bound:

  `f(n,t) ≥ (1 + o(1))·C(n,t-1)`.

This delivers the lower half of the conjecture's main term for all `t`; the
second-order matching term `⌊(n-1)/t⌋` and the matching upper bound remain open
(axiomatized / `sorry` in the parent).

Self-contained (the parent file does not currently build against Mathlib 4.26.0),
re-declaring the minimal definitions with identical semantics to `Erdos643Problem`.

Reference: https://erdosproblems.com/643
-/

import Mathlib

namespace Erdos643Star

open Finset
open scoped Classical

/-! ## Definitions (identical semantics to the parent `Erdos643Problem`) -/

/-- A hypergraph is a collection of edges (finite subsets of vertices). -/
abbrev Hypergraph (V : Type*) := Set (Finset V)

/-- A hypergraph is `t`-uniform if every edge has exactly `t` vertices. -/
def IsUniform {V : Type*} (H : Hypergraph V) (t : ℕ) : Prop :=
  ∀ e, e ∈ H → e.card = t

/-- The number of edges in a hypergraph. -/
noncomputable def edgeCount {V : Type*} (H : Hypergraph V) : ℕ := H.ncard

/-- Four edges form a *crossed pair*: same union, both pairs disjoint, and the
unordered pairs differ. -/
def IsCrossedPair {V : Type*} (A B C D : Finset V) : Prop :=
  A ∪ B = C ∪ D ∧ A ∩ B = ∅ ∧ C ∩ D = ∅ ∧ ({A, B} : Set (Finset V)) ≠ {C, D}

/-- A hypergraph contains a crossed pair. -/
def HasCrossedPair {V : Type*} (H : Hypergraph V) : Prop :=
  ∃ A B C D : Finset V, A ∈ H ∧ B ∈ H ∧ C ∈ H ∧ D ∈ H ∧ IsCrossedPair A B C D

/-- There is a `t`-uniform crossed-pair-free hypergraph on `Fin n` with exactly
`k` edges. -/
def CrossedPairFreeWithEdges (n t k : ℕ) : Prop :=
  ∃ H : Hypergraph (Fin n), IsUniform H t ∧ edgeCount H = k ∧ ¬HasCrossedPair H

/-- The extremal function: the least `m` such that every `t`-uniform hypergraph on
`n` vertices with `≥ m` edges contains a crossed pair. Well-defined because the
number of `t`-subsets is `C(n,t)`, so no crossed-pair-free family can have more
than `C(n,t)` edges. -/
noncomputable def f (n t : ℕ) : ℕ :=
  Nat.find (⟨Nat.choose n t + 1, by
    rintro k hk ⟨H, hUnif, hCard, -⟩
    have hsub : H ⊆ ↑(Finset.powersetCard t (Finset.univ : Finset (Fin n))) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, hUnif e he⟩
    have hle : H.ncard ≤ Nat.choose n t := by
      refine le_trans (Set.ncard_le_ncard hsub
        (Finset.powersetCard t Finset.univ).finite_toSet) ?_
      rw [Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]
    unfold edgeCount at hCard
    omega⟩ : ∃ m, ∀ k ≥ m, ¬CrossedPairFreeWithEdges n t k)

/-! ## The full star construction -/

/-- The **full star** at vertex `0`: all `t`-element edges containing `0`. -/
def starHypergraph (n t : ℕ) [NeZero n] : Hypergraph (Fin n) :=
  { e | e.card = t ∧ (0 : Fin n) ∈ e }

/-- The star is `t`-uniform. -/
lemma starHypergraph_isUniform (n t : ℕ) [NeZero n] :
    IsUniform (starHypergraph n t) t :=
  fun _ he => he.1

/-- The star has no crossed pair: any two edges both contain `0`, so they are
never disjoint, contradicting `A ∩ B = ∅`. -/
lemma starHypergraph_noCrossedPair (n t : ℕ) [NeZero n] :
    ¬HasCrossedPair (starHypergraph n t) := by
  rintro ⟨A, B, _, _, hA, hB, _, _, _, hAB, _, _⟩
  have hA0 : (0 : Fin n) ∈ A := hA.2
  have hB0 : (0 : Fin n) ∈ B := hB.2
  simp_all +decide [Finset.ext_iff]

/-- The star has exactly `C(n-1,t-1)` edges. -/
lemma starHypergraph_card (n t : ℕ) [NeZero n] (ht : 1 ≤ t) :
    edgeCount (starHypergraph n t) = Nat.choose (n - 1) (t - 1) := by
  unfold edgeCount starHypergraph
  rw [show {e : Finset (Fin n) | e.card = t ∧ (0 : Fin n) ∈ e}
        = ↑(Finset.image (fun s : Finset (Fin n) => insert (0 : Fin n) s)
            (Finset.powersetCard (t - 1) ((Finset.univ : Finset (Fin n)).erase 0)))
        from ?_]
  · rw [Set.ncard_coe_finset, Finset.card_image_of_injOn]
    · rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
    · intro s hs t' ht' hst
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hs ht'
      have h0s : (0 : Fin n) ∉ s := fun h => (Finset.mem_erase.mp (hs.1 h)).1 rfl
      have h0t : (0 : Fin n) ∉ t' := fun h => (Finset.mem_erase.mp (ht'.1 h)).1 rfl
      have := congrArg (fun u => Finset.erase u (0 : Fin n)) hst
      simpa [Finset.erase_insert h0s, Finset.erase_insert h0t] using this
  · ext e
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hcard, h0⟩
      exact ⟨e.erase 0,
        ⟨fun x hx => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩,
          by rw [Finset.card_erase_of_mem h0, hcard]⟩,
        Finset.insert_erase h0⟩
    · rintro ⟨s, ⟨hssub, hscard⟩, rfl⟩
      have h0s : (0 : Fin n) ∉ s := fun h => (Finset.mem_erase.mp (hssub h)).1 rfl
      exact ⟨by rw [Finset.card_insert_of_notMem h0s, hscard]; omega,
        Finset.mem_insert_self 0 s⟩

/-- The star witnesses a crossed-pair-free family with `C(n-1,t-1)` edges. -/
lemma star_crossedPairFree (n t : ℕ) [NeZero n] (ht : 1 ≤ t) :
    CrossedPairFreeWithEdges n t (Nat.choose (n - 1) (t - 1)) :=
  ⟨starHypergraph n t, starHypergraph_isUniform n t,
    starHypergraph_card n t ht, starHypergraph_noCrossedPair n t⟩

/-! ## The general-`t` lower bound -/

/-- **Main result.** For every `t ≥ 1` and `n ≥ 1`,
`f(n,t) ≥ C(n-1,t-1) + 1`. The full star at `0` is a crossed-pair-free family
with `C(n-1,t-1)` edges, so any family forced to contain a crossed pair must be
strictly larger. -/
theorem f_ge_star (n t : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) :
    Nat.choose (n - 1) (t - 1) + 1 ≤ f n t := by
  haveI : NeZero n := ⟨by omega⟩
  unfold f
  rw [Nat.le_find_iff]
  intro m hm hp
  exact hp (Nat.choose (n - 1) (t - 1)) (by omega) (star_crossedPairFree n t ht)

/-- The lower bound in the form matching the parent's `f_lower_bound` signature
(`t ≥ 2`, `n ≥ t`): `f(n,t) ≥ C(n-1,t-1) + 1`, the main term of the conjectured
lower bound, now for all `t ≥ 2`. -/
theorem f_ge_main_term (n t : ℕ) (ht : 2 ≤ t) (hn : t ≤ n) :
    Nat.choose (n - 1) (t - 1) + 1 ≤ f n t :=
  f_ge_star n t (by omega) (by omega)

/-- Specialization to `t = 3`: `f(n,3) ≥ C(n-1,2) + 1`. This recovers the main
term of the parent's `f_three_lower_bound = C(n-1,2) + ⌊(n-1)/3⌋` (the parent's
extra `⌊(n-1)/3⌋` matching term is a strictly second-order improvement). -/
theorem f_three_ge_main_term (n : ℕ) (hn : 3 ≤ n) :
    Nat.choose (n - 1) 2 + 1 ≤ f n 3 :=
  f_ge_main_term n 3 (by norm_num) hn

/-! ## Asymptotic optimality of the star bound -/

/-- The exact "column" identity for binomial coefficients:
`(n - k)·C(n,k) = n·C(n-1,k)` for `n ≥ 1`. Combining the Pascal-type recurrences
`succ_mul_choose_eq` and `choose_succ_right_eq`. -/
theorem choose_pred_identity (n k : ℕ) (hn : 1 ≤ n) :
    (n - k) * Nat.choose n k = n * Nat.choose (n - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := Nat.add_one_mul_choose_eq m k
  have h2 := Nat.choose_succ_right_eq (m + 1) k
  rw [h1, h2]
  ring

/-- The ratio `C(n-1,t-1)/C(n,t-1)` tends to `1`: the full star captures the
asymptotically dominant term of the lower bound. Equivalently
`f(n,t) ≥ (1 + o(1))·C(n,t-1)`, the lower half of the Erdős #643 conjecture's
main term, for every fixed `t ≥ 1`. -/
theorem star_ratio_tendsto (t : ℕ) (ht : 1 ≤ t) :
    Filter.Tendsto
      (fun n : ℕ => (Nat.choose (n - 1) (t - 1) : ℝ) / Nat.choose n (t - 1))
      Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun n : ℕ => (↑n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hzero : Filter.Tendsto (fun n : ℕ => (↑(t - 1) : ℝ) / (↑n))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (↑(t - 1) : ℝ) / (↑n))
      Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.const_sub 1 hzero
  rw [sub_zero] at hlim
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop t] with n hn
  have ha : t - 1 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hCpos : (0 : ℝ) < Nat.choose n (t - 1) := by
    exact_mod_cast Nat.choose_pos ha
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hid := choose_pred_identity n (t - 1) hn1
  have hsub : ((n - (t - 1) : ℕ) : ℝ) = (n : ℝ) - ((t - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub ha]
  have hRHS : (Nat.choose (n - 1) (t - 1) : ℝ) / (Nat.choose n (t - 1) : ℝ)
      = ((n : ℝ) - ((t - 1 : ℕ) : ℝ)) / (n : ℝ) := by
    rw [div_eq_div_iff hCpos.ne' hnpos.ne', ← hsub,
      mul_comm (Nat.choose (n - 1) (t - 1) : ℝ) (n : ℝ)]
    exact_mod_cast hid.symm
  rw [hRHS, sub_div, div_self hnpos.ne']

end Erdos643Star
