import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

/-
# Ramsey Numbers for k-Uniform Hypergraphs (OQ-03 of erdos-szekeres)

## What This Establishes

Erdős–Szekeres (Wiedijk #73, formalized in `Proofs/ErdosSzekeres.lean`) is the
*sequence* refinement of graph Ramsey (`k = 2`). OQ-03 of `erdos-szekeres` asks
for the generalization to `k`-uniform hypergraphs: for `k ≥ 2`, define the
diagonal hypergraph Ramsey number `R_k(s,t)` as the least `n` such that every
2-coloring of `[n]^{(k)}` (the `k`-subsets of `{0,...,n-1}`) contains a
monochromatic `s`-clique of one color or a monochromatic `t`-clique of the
other.

After **S3** (this revision) the `k = 1` pigeonhole sanity check
`ramseyNumber_one s t = s + t - 1` is proved — the simplest instance of the
hypergraph Ramsey theorem and a unit test for the API introduced in S2.
The general existence theorem `ramsey_existence` (OQ-03a, two-layer Ramsey
1930 induction) and the Erdős–Rado tower upper bound (OQ-03b) remain
`sorry`-marked, deferred to S4+ per
`research/problems/erdos-szekeres-oq-03/state.md`.

## Status

- [x] Definitions: `kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`.
- [x] `IsMonochromatic_of_card_lt_k`: any subset smaller than `k` is trivially
  monochromatic of every color (the `powersetCard` is empty).
- [x] `is_ramsey_zero_false` / `is_ramsey_zero_true`: degenerate `s = 0` /
  `t = 0` base cases (the empty set witnesses both).
- [x] **`isRamsey_one_iff` and `ramseyNumber_one` (S3)**: the `k = 1` case
  is the pigeonhole `s + t - 1` bound, by partitioning singletons.
- [ ] `ramsey_existence` (OQ-03a): the general result, stated as `sorry`.
  Proof strategy in `state.md`.

## Approach

- We model `k`-subsets of `{0,...,n-1}` as elements of
  `(Finset.univ : Finset (Fin n)).powersetCard k`, and a 2-coloring as
  `Finset (Fin n) → Bool` (only the values on `k`-subsets matter for
  `IsMonochromatic`).
- `ramseyNumber k s t` is defined as `sInf {n | IsRamsey n k s t}`; for
  parameter values where the set is empty (e.g. degenerate inputs), this
  returns `0`. Once `ramsey_existence` is proved, the value is the true
  Ramsey number for all `k ≥ 2`, `s, t ≥ k`.

## References

- F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2)
  30 (1930), 264–286 — original proof of OQ-03a.
- P. Erdős, R. Rado, *A partition calculus in set theory*, Bull. AMS 62
  (1956), 427–489 — the tower upper bound (OQ-03b).
- P. Erdős, A. Hajnal, *On Ramsey like theorems*, Combinatorics (Oxford 1972),
  123–140 — stepping-up lower bound (OQ-03c).
-/

namespace RamseyK

open Finset

/-- A 2-coloring of the `k`-subsets of `{0,...,n-1}`. We model it as a
function on all of `Finset (Fin n)`; only the values on subsets of cardinality
`k` are inspected by `IsMonochromatic`. -/
abbrev kColoring (n : ℕ) := Finset (Fin n) → Bool

/-- A subset `S ⊆ {0,...,n-1}` is **monochromatic of color `c`** for a coloring
`χ` at uniformity `k` if every `k`-subset of `S` is colored `c`. -/
def IsMonochromatic {n : ℕ} (χ : kColoring n) (k : ℕ)
    (S : Finset (Fin n)) (c : Bool) : Prop :=
  ∀ T ∈ S.powersetCard k, χ T = c

/-- The **Ramsey condition** `IsRamsey n k s t`: every 2-coloring of the
`k`-subsets of `{0,...,n-1}` contains either a monochromatic `false` `s`-clique
or a monochromatic `true` `t`-clique. -/
def IsRamsey (n k s t : ℕ) : Prop :=
  ∀ χ : kColoring n,
    (∃ S : Finset (Fin n), S.card = s ∧ IsMonochromatic χ k S false) ∨
    (∃ S : Finset (Fin n), S.card = t ∧ IsMonochromatic χ k S true)

/-- The **k-uniform hypergraph Ramsey number**: the least `n` such that
`IsRamsey n k s t` holds. By `sInf` convention on `ℕ`, this is `0` if no
such `n` exists; once `ramsey_existence` is proved for `k ≥ 2`, `s, t ≥ k`,
this returns the true Ramsey number. -/
noncomputable def ramseyNumber (k s t : ℕ) : ℕ :=
  sInf {n | IsRamsey n k s t}

/-- A subset smaller than the uniformity `k` has no `k`-subsets and is
trivially monochromatic of every color. -/
lemma isMonochromatic_of_card_lt {n k : ℕ} (χ : kColoring n)
    (S : Finset (Fin n)) (c : Bool) (h : S.card < k) :
    IsMonochromatic χ k S c := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTsub, hTcard⟩ := hT
  have hTle : T.card ≤ S.card := Finset.card_le_card hTsub
  exfalso
  omega

/-- (OQ-03a) **Ramsey's hypergraph theorem.** For every uniformity `k ≥ 2`
and every pair of target sizes `s, t ≥ k`, there is a finite `n` such that
every 2-coloring of `[n]^{(k)}` contains a monochromatic `s`- or `t`-clique.

This is the main result of the OQ-03 entry. The proof (Ramsey 1930) is by
two-layer induction on `k` and `s + t`; see `state.md` for the strategy.
Deferred to S4+ (S3 closed the `k = 1` sanity check; the `k ≥ 2` induction
needs the additional neighborhood-collapse machinery). -/
theorem ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    ∃ n, IsRamsey n k s t := by
  sorry

/-- The empty set is a `0`-clique, monochromatic of every color. -/
lemma isMonochromatic_empty_zero {n k : ℕ} (χ : kColoring n) (c : Bool)
    (hk : 1 ≤ k) :
    IsMonochromatic χ k (∅ : Finset (Fin n)) c := by
  apply isMonochromatic_of_card_lt
  rw [Finset.card_empty]
  exact hk

/-- Degenerate base case: when the `false`-target size is `0`, every coloring
trivially has a `0`-monochromatic `false` "clique" — the empty set. Hence
`IsRamsey n k 0 t` holds for all `n, k, t` with `k ≥ 1`. -/
lemma is_ramsey_zero_false (n k t : ℕ) (hk : 1 ≤ k) : IsRamsey n k 0 t := by
  intro χ
  refine Or.inl ⟨∅, ?_, ?_⟩
  · exact Finset.card_empty
  · exact isMonochromatic_empty_zero χ false hk

/-- Symmetric degenerate base case for the `true`-target. -/
lemma is_ramsey_zero_true (n k s : ℕ) (hk : 1 ≤ k) : IsRamsey n k s 0 := by
  intro χ
  refine Or.inr ⟨∅, ?_, ?_⟩
  · exact Finset.card_empty
  · exact isMonochromatic_empty_zero χ true hk

/-- (S3 helper.) At uniformity `k = 1`, the Ramsey condition is equivalent to
the pigeonhole bound `s + t - 1 ≤ n`.

* Forward (`s + t - 1 ≤ n → IsRamsey n 1 s t`): partition `Fin n` by
  `χ {·}`; one of the two color classes has cardinality `≥ s` or `≥ t`.
* Backward (`IsRamsey n 1 s t → s + t - 1 ≤ n`): contrapositive — if
  `n ≤ s + t - 2` then the coloring with `min (s-1) n` `false`-singletons
  and the rest `true` exhibits no monochromatic `s`- or `t`-clique. -/
lemma isRamsey_one_iff (n s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    IsRamsey n 1 s t ↔ s + t - 1 ≤ n := by
  classical
  constructor
  · -- (⇒) IsRamsey n 1 s t → s + t - 1 ≤ n.  Contrapositive: if n ≤ s+t-2 we
    -- exhibit a coloring that defeats every monochromatic s/t-clique candidate.
    intro hR
    by_contra hlt
    push_neg at hlt
    -- hlt : n < s + t - 1, equivalently n ≤ s + t - 2.
    -- Build the "bad" coloring: first `a = min (s-1) n` singletons are `false`,
    -- rest `true`. (Definition only depends on each singleton's element.)
    set a : ℕ := min (s - 1) n with ha_def
    -- Decidability of `a ≤ i.val` for `i : Fin n` lets us define χ.
    let χ : kColoring n := fun S => decide (∃ i ∈ S, a ≤ i.val)
    -- Two helper facts about χ on singletons.
    have hχ_false : ∀ i : Fin n, i.val < a → χ {i} = false := by
      intro i hi
      show decide (∃ j ∈ ({i} : Finset (Fin n)), a ≤ j.val) = false
      simp only [Finset.mem_singleton, exists_eq_left]
      exact decide_eq_false (Nat.not_le_of_lt hi)
    have hχ_true : ∀ i : Fin n, a ≤ i.val → χ {i} = true := by
      intro i hi
      show decide (∃ j ∈ ({i} : Finset (Fin n)), a ≤ j.val) = true
      simp only [Finset.mem_singleton, exists_eq_left]
      exact decide_eq_true hi
    -- Two card bounds via the globally-injective `Fin.val : Fin n → ℕ`.
    -- (1) Any S with `∀ i ∈ S, i.val < a` has |S| ≤ a (image ⊆ Finset.range a).
    -- (2) Any S with `∀ i ∈ S, a ≤ i.val` has |S| ≤ n - a (image ⊆ Finset.Ico a n).
    have hcard_lo : ∀ (S : Finset (Fin n)), (∀ i ∈ S, i.val < a) → S.card ≤ a := by
      intro S hS
      have h_im : S.image (fun i : Fin n => i.val) ⊆ Finset.range a := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hiS, rfl⟩
        exact Finset.mem_range.mpr (hS i hiS)
      calc S.card
          = (S.image (fun i : Fin n => i.val)).card :=
              (Finset.card_image_of_injective S Fin.val_injective).symm
        _ ≤ (Finset.range a).card := Finset.card_le_card h_im
        _ = a := Finset.card_range a
    have hcard_hi : ∀ (S : Finset (Fin n)), (∀ i ∈ S, a ≤ i.val) → S.card ≤ n - a := by
      intro S hS
      have h_im : S.image (fun i : Fin n => i.val) ⊆ Finset.Ico a n := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hiS, rfl⟩
        exact Finset.mem_Ico.mpr ⟨hS i hiS, i.isLt⟩
      calc S.card
          = (S.image (fun i : Fin n => i.val)).card :=
              (Finset.card_image_of_injective S Fin.val_injective).symm
        _ ≤ (Finset.Ico a n).card := Finset.card_le_card h_im
        _ = n - a := Nat.card_Ico a n
    -- Helper: from monochromatic-`c` on S, every `i ∈ S` has `χ {i} = c`.
    have hmono_singleton : ∀ {S : Finset (Fin n)} {c : Bool},
        IsMonochromatic χ 1 S c → ∀ i ∈ S, χ {i} = c := by
      intro S c hmono i hiS
      apply hmono
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.singleton_subset_iff.mpr hiS, Finset.card_singleton i⟩
    rcases hR χ with ⟨S, hScard, hSmono⟩ | ⟨S, hScard, hSmono⟩
    · -- false-clique S of size s: every i ∈ S has χ {i} = false ⇒ i.val < a.
      have hSlt : ∀ i ∈ S, i.val < a := by
        intro i hiS
        have hχ : χ {i} = false := hmono_singleton hSmono i hiS
        by_contra hge
        push_neg at hge
        have : χ {i} = true := hχ_true i hge
        simp [this] at hχ
      have hcard : S.card ≤ a := hcard_lo S hSlt
      have ha_bound : a ≤ s - 1 := by simp [a]; omega
      omega
    · -- true-clique S of size t: every i ∈ S has a ≤ i.val.
      have hSge : ∀ i ∈ S, a ≤ i.val := by
        intro i hiS
        have hχ : χ {i} = true := hmono_singleton hSmono i hiS
        by_contra hlt'
        push_neg at hlt'
        have : χ {i} = false := hχ_false i hlt'
        simp [this] at hχ
      have hcard : S.card ≤ n - a := hcard_hi S hSge
      -- Bound n - a ≤ t - 1, case-split on the `min`.
      have ha_bound : n - a ≤ t - 1 := by
        rcases le_or_lt (s - 1) n with hsa | hsa
        · -- a = s - 1
          have ha_eq : a = s - 1 := by simp [a]; omega
          omega
        · -- a = n
          have ha_eq : a = n := by simp [a]; omega
          omega
      omega
  · -- (⇐) s + t - 1 ≤ n → IsRamsey n 1 s t.  Pigeonhole partition of `Fin n`
    -- by the color χ {·}; one color class has size ≥ s or ≥ t.
    intro hge χ
    -- F := false-singletons, G := true-singletons; they partition `Fin n`.
    let F : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => χ {i} = false)
    let G : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => χ {i} = true)
    have hF_neg : (Finset.univ.filter (fun i : Fin n => ¬ (χ {i} = false))) = G := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G]
      cases hc : χ {i} <;> simp [hc]
    have hsum : F.card + G.card = n := by
      have h :
          (Finset.univ.filter (fun i : Fin n => χ {i} = false)).card +
            (Finset.univ.filter (fun i : Fin n => ¬ (χ {i} = false))).card =
          (Finset.univ : Finset (Fin n)).card :=
        Finset.filter_card_add_filter_neg_card_eq_card _
      rw [hF_neg] at h
      have hcard_univ : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ, Fintype.card_fin]
      simpa [F, hcard_univ] using h
    by_cases hFs : s ≤ F.card
    · -- |F| ≥ s: pick S ⊆ F with |S| = s; every singleton of S has χ {·} = false.
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hFs
      refine Or.inl ⟨S, hScard, ?_⟩
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hTcard
      have hi : i ∈ S := Finset.singleton_subset_iff.mp hTsub
      have hiF : i ∈ F := hSsub hi
      simpa [F, Finset.mem_filter] using hiF
    · -- |F| < s ⇒ |G| > n - s ≥ (s+t-1) - s = t - 1, hence |G| ≥ t.
      push_neg at hFs
      have hGcard : t ≤ G.card := by omega
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hGcard
      refine Or.inr ⟨S, hScard, ?_⟩
      intro U hU
      rw [Finset.mem_powersetCard] at hU
      obtain ⟨hUsub, hUcard⟩ := hU
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hUcard
      have hi : i ∈ S := Finset.singleton_subset_iff.mp hUsub
      have hiG : i ∈ G := hSsub hi
      simpa [G, Finset.mem_filter] using hiG

/-- (S3, OQ-03 sanity check.) **The `k = 1` Ramsey number is the pigeonhole bound**
`R_1(s, t) = s + t - 1`. This is the base case of the Erdős–Rado tower upper bound
and the simplest instance of the hypergraph Ramsey theorem. It serves as a unit
test for the `RamseyK.IsRamsey` / `RamseyK.ramseyNumber` API introduced in S2.

The proof reduces to `isRamsey_one_iff` plus the standard `Nat.sInf` computation
on the upward-closed set `{n | s + t - 1 ≤ n} = Set.Ici (s + t - 1)`. -/
theorem ramseyNumber_one (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ramseyNumber 1 s t = s + t - 1 := by
  unfold ramseyNumber
  have hset : {n | IsRamsey n 1 s t} = {n | s + t - 1 ≤ n} := by
    ext n; rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    exact isRamsey_one_iff n s t hs ht
  rw [hset]
  -- sInf {n | s+t-1 ≤ n} = s+t-1
  apply le_antisymm
  · exact Nat.sInf_le (le_refl _)
  · refine le_csInf ⟨s + t - 1, le_refl _⟩ ?_
    intro n hn
    exact hn

/-! ### S4-prep: color symmetry and degenerate-side `ramseyNumber` base cases

The following three lemmas extend the API surface for S4 (the
`ramsey_existence` two-layer induction). They are independent of the
`ramseyNumber_one`/`isRamsey_one_iff` machinery developed in S3 — they
follow directly from the S2 definitions and the `is_ramsey_zero_*`
degenerate base cases.

* `IsRamsey.swap` — the Ramsey condition is symmetric in `(s, t)` because
  negating a coloring swaps the two color targets. Needed in S4 to halve
  the induction (only one side of the recursive bound needs treatment).
* `ramseyNumber_zero_false` / `ramseyNumber_zero_true` — when one
  target size is zero, the empty set is a witness, so `ramseyNumber`
  collapses to `0`. These are the natural companions to `ramseyNumber_one`
  on the other end of the parameter range.
-/

/-- **Color symmetry of `IsRamsey`.** Negating a coloring `χ ↦ !χ` swaps which
color receives the `s`-target and which receives the `t`-target, so the
Ramsey condition is invariant under exchanging `s` and `t`. -/
lemma IsRamsey.swap {n k s t : ℕ} : IsRamsey n k s t ↔ IsRamsey n k t s := by
  -- The forward direction suffices; the reverse follows by reusing the same proof.
  suffices h : ∀ {a b}, IsRamsey n k a b → IsRamsey n k b a from ⟨h, h⟩
  intro a b H χ
  -- Negate the coloring; apply the hypothesis; flip the resulting clique's color.
  rcases H (fun S => !χ S) with ⟨S, hSc, hSm⟩ | ⟨S, hSc, hSm⟩
  · -- An `a`-clique monochromatic-`false` under `!χ` is monochromatic-`true` under `χ`.
    refine Or.inr ⟨S, hSc, ?_⟩
    intro T hT
    have hflip : !(χ T) = false := hSm T hT
    cases hχ : χ T with
    | false => simp [hχ] at hflip
    | true => exact hχ
  · -- A `b`-clique monochromatic-`true` under `!χ` is monochromatic-`false` under `χ`.
    refine Or.inl ⟨S, hSc, ?_⟩
    intro T hT
    have hflip : !(χ T) = true := hSm T hT
    cases hχ : χ T with
    | false => exact hχ
    | true => simp [hχ] at hflip

/-- **`ramseyNumber` collapses when the `false`-target is zero.** With `s = 0` the
empty set is a trivially monochromatic `false`-clique of size `0`, so
`IsRamsey 0 k 0 t` already holds and the infimum is `0`. -/
lemma ramseyNumber_zero_false (k t : ℕ) (hk : 1 ≤ k) :
    ramseyNumber k 0 t = 0 := by
  unfold ramseyNumber
  have h0 : (0 : ℕ) ∈ {n | IsRamsey n k 0 t} := is_ramsey_zero_false 0 k t hk
  exact Nat.le_zero.mp (Nat.sInf_le h0)

/-- **`ramseyNumber` collapses when the `true`-target is zero.** Symmetric to
`ramseyNumber_zero_false`. -/
lemma ramseyNumber_zero_true (k s : ℕ) (hk : 1 ≤ k) :
    ramseyNumber k s 0 = 0 := by
  unfold ramseyNumber
  have h0 : (0 : ℕ) ∈ {n | IsRamsey n k s 0} := is_ramsey_zero_true 0 k s hk
  exact Nat.le_zero.mp (Nat.sInf_le h0)

end RamseyK
