import Mathlib
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

After **S8 ACT-F** (this revision) `ramsey_existence` is **fully proved** —
the file is 0-sorry / 0-axiom. The Ramsey 1930 two-layer induction runs in
`ramsey_existence_of_one_le`: outer structural induction on the uniformity
`k` (base `k = 1` is the S3 pigeonhole), inner bounded induction on the
target sum `s + t` (boundaries `s = k` / `t = k` are the S4
`is_ramsey_self_*` lemmas), with the genuine step assembled from the S6/S7
link-and-splice machinery through the new transfer lemma `IsRamsey.within`.

## Status

- [x] Definitions: `kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`.
- [x] `IsMonochromatic_of_card_lt_k`: any subset smaller than `k` is trivially
  monochromatic of every color (the `powersetCard` is empty).
- [x] `is_ramsey_zero_false` / `is_ramsey_zero_true`: degenerate `s = 0` /
  `t = 0` base cases (the empty set witnesses both).
- [x] **`isRamsey_one_iff` and `ramseyNumber_one` (S3)**: the `k = 1` case
  is the pigeonhole `s + t - 1` bound, by partitioning singletons.
- [x] **`IsRamsey.swap` and `ramseyNumber_zero_*` (S4-prep)**: color symmetry
  and degenerate-`ramseyNumber` collapses.
- [x] **`IsRamsey.anti_s` / `IsRamsey.anti_t` (S4 ACT-C)**: anti-monotonicity
  in the target sizes, by extracting a sub-clique of the desired smaller size.
- [x] **`is_ramsey_self_right` / `is_ramsey_self_left` (S4 ACT-C)**: the
  `s = k` and `t = k` boundary cases at `n = t` and `n = s`, respectively.
- [x] **`kColoring.link` / `IsMonochromatic.link_lifts` (S6 ACT-D)**: the
  link (neighborhood) coloring and its `(k-1) → k` monochromaticity transfer.
- [x] **`IsMonochromatic.insert_vertex` (S7 ACT-E)**: the splice composing a
  non-vertex-side sub-clique with vertex-side link coverage.
- [x] **`IsRamsey.within` / `ramsey_existence_of_one_le` /
  `ramsey_existence` (S8 ACT-F)**: the transfer lemma and the full Ramsey
  1930 double induction — OQ-03a is closed, 0 sorries, 0 axioms.

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
      -- a = min (s - 1) n ≤ s - 1, contradicting hcard + hScard : S.card = s.
      have ha_bound : a ≤ s - 1 := min_le_left _ _
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
        rcases le_or_gt (s - 1) n with hsa | hsa
        · -- a = s - 1
          have ha_eq : a = s - 1 := by
            show min (s - 1) n = s - 1
            exact min_eq_left hsa
          omega
        · -- a = n (when s - 1 > n)
          have ha_eq : a = n := by
            show min (s - 1) n = n
            exact min_eq_right (le_of_lt hsa)
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
      cases hc : χ {i} <;> simp
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
  -- sInf {n | s+t-1 ≤ n} = s+t-1: `s+t-1` is the min of the upward-closed set.
  apply le_antisymm
  · -- sInf ≤ s+t-1: membership witness `s+t-1 ≤ s+t-1`.
    apply Nat.sInf_le
    rw [Set.mem_setOf_eq]
  · -- s+t-1 ≤ sInf: every member of the set is ≥ s+t-1.
    apply le_csInf
    · refine ⟨s + t - 1, ?_⟩
      rw [Set.mem_setOf_eq]
    · intro n hn
      rw [Set.mem_setOf_eq] at hn
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
    have hflip : Bool.not (χ T) = false := hSm T hT
    simpa using hflip
  · -- A `b`-clique monochromatic-`true` under `!χ` is monochromatic-`false` under `χ`.
    refine Or.inl ⟨S, hSc, ?_⟩
    intro T hT
    have hflip : Bool.not (χ T) = true := hSm T hT
    simpa using hflip

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

/-! ### S4 ACT-C: structural lemmas and boundary cases of `ramsey_existence`

The four lemmas below are the structural foundation for the S5 two-layer
Ramsey-1930 induction:

* `IsRamsey.anti_s`, `IsRamsey.anti_t` — anti-monotonicity in the target sizes.
  A larger `s`-target is strictly harder to satisfy, so shrinking it preserves
  the Ramsey condition. Needed in S5 to lift the recursive bound (which only
  produces an `(s-1)`- or `(t-1)`-clique on a sub-coloring) up to the
  outer `s`- or `t`-clique.
* `is_ramsey_self_right`, `is_ramsey_self_left` — the `s = k` (resp. `t = k`)
  boundary case: at uniformity `k`, target sizes `(k, t)` are settled by
  `n = t`. Either some `k`-subset is colored `false` (giving a `k`-clique
  monochromatic-`false`) or every `k`-subset is colored `true` (giving the
  full `t`-vertex set as a monochromatic-`true` `t`-clique).

With these in hand, `ramsey_existence` (below) is reduced to its
genuinely-inductive case `s > k ∧ t > k` (the S5 target).
-/

/-- **Anti-monotonicity of `IsRamsey` in the `s`-target.** A larger `s` is
strictly harder to satisfy — shrinking it preserves the Ramsey condition. The
proof: any `s`-clique contains an `s'`-sub-clique (via
`Finset.exists_subset_card_eq`), and monochromaticity descends to subsets. -/
lemma IsRamsey.anti_s {n k s s' t : ℕ} (hss' : s' ≤ s)
    (h : IsRamsey n k s t) : IsRamsey n k s' t := by
  intro χ
  rcases h χ with ⟨S, hSc, hSm⟩ | ⟨S, hSc, hSm⟩
  · -- false-clique S of size s; extract an s'-sized sub-clique.
    have hs'S : s' ≤ S.card := hSc ▸ hss'
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hs'S
    refine Or.inl ⟨S', hS'card, ?_⟩
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    exact hSm T (Finset.mem_powersetCard.mpr ⟨hTsub.trans hS'sub, hTcard⟩)
  · -- t-clique branch: pass through unchanged.
    exact Or.inr ⟨S, hSc, hSm⟩

/-- **Anti-monotonicity of `IsRamsey` in the `t`-target.** Symmetric to
`IsRamsey.anti_s`. -/
lemma IsRamsey.anti_t {n k s t t' : ℕ} (htt' : t' ≤ t)
    (h : IsRamsey n k s t) : IsRamsey n k s t' := by
  intro χ
  rcases h χ with ⟨S, hSc, hSm⟩ | ⟨S, hSc, hSm⟩
  · exact Or.inl ⟨S, hSc, hSm⟩
  · have ht'S : t' ≤ S.card := hSc ▸ htt'
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq ht'S
    refine Or.inr ⟨S', hS'card, ?_⟩
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    exact hSm T (Finset.mem_powersetCard.mpr ⟨hTsub.trans hS'sub, hTcard⟩)

/-- **Boundary case `s = k`.** At uniformity `k` and target sizes `(k, t)` with
`k ≤ t`, the Ramsey condition holds at `n = t`.

Proof: case-split on whether some `k`-subset is colored `false`.

* **Case A.** If some `S` with `|S| = k` has `χ S = false`, then `S` itself is
  a `k`-clique with monochromatic-`false` `k`-subsets — its only `k`-subset is
  `S`, by `Finset.eq_of_subset_of_card_le` applied to the inclusion.
* **Case B.** If no `k`-subset is colored `false`, then every `k`-subset of
  `Finset.univ : Finset (Fin t)` is colored `true`, and `Finset.univ` is a
  `t`-clique with `card = t` (by `Fintype.card_fin`). -/
lemma is_ramsey_self_right (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    IsRamsey t k k t := by
  classical
  intro χ
  by_cases h : ∃ S : Finset (Fin t), S.card = k ∧ χ S = false
  · -- Case A: a false-colored k-subset is itself the mono-false k-clique.
    obtain ⟨S, hScard, hSχ⟩ := h
    refine Or.inl ⟨S, hScard, ?_⟩
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    -- |T| = k = |S| with T ⊆ S ⇒ T = S.
    have hT_eq : T = S := Finset.eq_of_subset_of_card_le hTsub (by omega)
    rw [hT_eq]
    exact hSχ
  · -- Case B: every k-subset is colored true; Finset.univ is the mono-true t-clique.
    push_neg at h
    refine Or.inr ⟨Finset.univ, ?_, ?_⟩
    · rw [Finset.card_univ, Fintype.card_fin]
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨_, hTcard⟩ := hT
      -- From `h`, χ T ≠ false; in `Bool`, this forces χ T = true.
      have hχ_ne : χ T ≠ false := fun hχ => h T hTcard hχ
      cases hT_color : χ T with
      | false => exact absurd hT_color hχ_ne
      | true => rfl

/-- **Boundary case `t = k`.** Symmetric to `is_ramsey_self_right` via
`IsRamsey.swap`. -/
lemma is_ramsey_self_left (k s : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) :
    IsRamsey s k s k :=
  IsRamsey.swap.mpr (is_ramsey_self_right k s hk hks)

/-! ### S5-prep: monotonicity infrastructure for `ramsey_existence`'s inductive step

The S5 target (the genuinely-inductive case `s > k ∧ t > k` of
`ramsey_existence`) is the Ramsey 1930 two-layer induction on `k` and `s + t`.
It needs three monotonicity facts that are independent of `ramsey_existence`
itself and clean to state from the S2/S4-prep API:

* `IsMonochromatic.mono` — monochromaticity is preserved by passing to a
  subset (every `k`-subset of the smaller set is a `k`-subset of the larger
  one).
* `IsRamsey.mono_n` — the Ramsey condition is monotone in `n`. Restricting
  any coloring of `[m]^{(k)}` along the embedding `Fin n ↪ Fin m` produces a
  clique on the smaller side, which lifts back unchanged.
* `ramseyNumber_swap` — `ramseyNumber k s t = ramseyNumber k t s`, immediate
  corollary of `IsRamsey.swap` since both `sInf`-defining sets agree
  pointwise.
-/

/-- **Monochromaticity is preserved by passing to a subset.** Every
`k`-subset of `S'` is a `k`-subset of `S` (because `S' ⊆ S`), so the
defining quantifier of `IsMonochromatic χ k S' c` is implied by that of
`IsMonochromatic χ k S c`. -/
lemma IsMonochromatic.mono {n k : ℕ} {χ : kColoring n} {c : Bool}
    {S S' : Finset (Fin n)} (hSub : S' ⊆ S)
    (hMono : IsMonochromatic χ k S c) : IsMonochromatic χ k S' c := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTS', hTcard⟩ := hT
  exact hMono T (Finset.mem_powersetCard.mpr ⟨hTS'.trans hSub, hTcard⟩)

/-- **`IsRamsey` is monotone in `n`.** If `IsRamsey n k s t` and `n ≤ m`,
restricting any coloring of `[m]^{(k)}` along the canonical embedding
`Fin n ↪ Fin m` (built from `Fin.castLE` and its injectivity) produces a
clique on the `Fin n` side, which then lifts back along the same embedding
to a clique of the same size in `Fin m`. The lift uses `Finset.subset_map_iff`
to recognise every `k`-subset of the lifted clique as itself the image of a
unique `k`-subset on the smaller side, where monochromaticity is known by
hypothesis. -/
lemma IsRamsey.mono_n {n m k s t : ℕ} (h : n ≤ m)
    (hR : IsRamsey n k s t) : IsRamsey m k s t := by
  intro χ
  let f : Fin n ↪ Fin m := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  let χ' : kColoring n := fun S => χ (S.map f)
  rcases hR χ' with ⟨S, hSc, hSm⟩ | ⟨S, hSc, hSm⟩
  · refine Or.inl ⟨S.map f, ?_, ?_⟩
    · rw [Finset.card_map]; exact hSc
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      obtain ⟨T₀, hT₀sub, hT₀eq⟩ := Finset.subset_map_iff.mp hTsub
      have hT₀card : T₀.card = k := by
        have hcard := congrArg Finset.card hT₀eq
        rw [Finset.card_map] at hcard
        omega
      have key : χ' T₀ = false :=
        hSm T₀ (Finset.mem_powersetCard.mpr ⟨hT₀sub, hT₀card⟩)
      rw [hT₀eq]
      exact key
  · refine Or.inr ⟨S.map f, ?_, ?_⟩
    · rw [Finset.card_map]; exact hSc
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      obtain ⟨T₀, hT₀sub, hT₀eq⟩ := Finset.subset_map_iff.mp hTsub
      have hT₀card : T₀.card = k := by
        have hcard := congrArg Finset.card hT₀eq
        rw [Finset.card_map] at hcard
        omega
      have key : χ' T₀ = true :=
        hSm T₀ (Finset.mem_powersetCard.mpr ⟨hT₀sub, hT₀card⟩)
      rw [hT₀eq]
      exact key

/-- **`ramseyNumber` is symmetric in the two color targets.** Immediate
corollary of `IsRamsey.swap`: the defining `sInf` sets agree pointwise under
exchanging `s` and `t`. -/
lemma ramseyNumber_swap (k s t : ℕ) :
    ramseyNumber k s t = ramseyNumber k t s := by
  unfold ramseyNumber
  congr 1
  ext n
  exact IsRamsey.swap

/-! ### S6 ACT-D: link coloring (neighborhood-collapse infrastructure)

For the Ramsey 1930 recursive bound (the genuine inductive case
`s > k ∧ t > k` of `ramsey_existence`), the key construction is the
**link** of a vertex `v`: given a `k`-uniform 2-coloring `χ`, the link
at `v` is the `(k-1)`-uniform coloring on `[n] \ {v}` that sends each
`(k-1)`-subset `T` (disjoint from `v`) to `χ (insert v T)`. By
induction on uniformity, the link finds a large `(k-1)`-monochromatic
clique `S ⊆ [n] \ {v}`; the lift `insert v S` is then `k`-monochromatic
on every `k`-subset *containing* `v`, by the very definition of the
link.

We encode the link as a coloring on the full `Fin n` since
`kColoring n` is type-uniform (the uniformity is supplied by
`IsRamsey`'s `k` parameter). The two declarations below give the link's
defining `simp` rule and the `(k-1) → k` monochromaticity transfer
used by the recursion. -/

/-- The **link coloring** at vertex `v`: on a finset `T`, return the
`χ`-color of `insert v T`. When `v ∉ T`, this is precisely the
neighborhood coloring used in the Ramsey 1930 induction; when `v ∈ T`
(so `insert v T = T`), the link agrees with `χ` and the value is
inert for the recursion's purposes. -/
def kColoring.link {n : ℕ} (χ : kColoring n) (v : Fin n) : kColoring n :=
  fun T => χ (insert v T)

@[simp] lemma kColoring.link_apply {n : ℕ} (χ : kColoring n) (v : Fin n)
    (T : Finset (Fin n)) :
    (kColoring.link χ v) T = χ (insert v T) := rfl

/-- **Link lift (vertex side).** If `S ⊆ Fin n \ {v}` is a
`(k-1)`-monochromatic clique of colour `c` for the link coloring
`χ.link v`, then every `k`-subset of `insert v S` that **contains** `v`
is coloured `c` under the original `χ`.

This is the "vertex side" of the Ramsey 1930 neighborhood-collapse
recursion: combined with a `k`-monochromatic sub-clique `S' ⊆ S` of the
appropriate target size for `χ` itself (the "non-vertex side"), it
proves that `insert v S'` is a `k`-monochromatic clique of size
`|S'| + 1` for `χ`, since every `k`-subset of `insert v S'` either
lies in `S'` (handled by the sub-clique's monochromaticity) or contains
`v` (handled here). -/
lemma IsMonochromatic.link_lifts {n k : ℕ} (χ : kColoring n) (v : Fin n)
    (c : Bool) (S : Finset (Fin n)) (hvS : v ∉ S)
    (hSm : IsMonochromatic (kColoring.link χ v) (k - 1) S c) :
    ∀ T ∈ (insert v S).powersetCard k, v ∈ T → χ T = c := by
  intro T hT hvT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTsub, hTcard⟩ := hT
  -- Decompose `T = insert v T'` with `T' = T.erase v ⊆ S`, `|T'| = k - 1`.
  have hT_eq : T = insert v (T.erase v) := (Finset.insert_erase hvT).symm
  set T' := T.erase v with hT'def
  have hT'_sub : T' ⊆ S := by
    intro x hx
    obtain ⟨hxv, hxT⟩ := Finset.mem_erase.mp hx
    have hxInsert : x ∈ insert v S := hTsub hxT
    rcases Finset.mem_insert.mp hxInsert with hxv' | hxS
    · exact absurd hxv' hxv
    · exact hxS
  have hT'_card : T'.card = k - 1 := by
    have hcard_erase : (T.erase v).card = T.card - 1 :=
      Finset.card_erase_of_mem hvT
    rw [hT'def, hcard_erase, hTcard]
  have hT'_mem : T' ∈ S.powersetCard (k - 1) :=
    Finset.mem_powersetCard.mpr ⟨hT'_sub, hT'_card⟩
  have hlink : (kColoring.link χ v) T' = c := hSm T' hT'_mem
  rw [kColoring.link_apply] at hlink
  rw [hT_eq]
  exact hlink

/-- **Splice (insert vertex).** If `S' ⊆ Fin n \ {v}` is a `k`-monochromatic
clique of colour `c` for `χ`, and every `k`-subset of `insert v S'` that
contains `v` is also coloured `c` by `χ`, then `insert v S'` is itself
a `k`-monochromatic clique of colour `c`.

This is the S7 splice lemma: it combines a *non-vertex side* sub-clique
(`hS'` — `S'` is already `k`-mono under `χ`) with the *vertex side*
link-derived coverage (`hLink` — produced by `IsMonochromatic.link_lifts`
in S6) to yield a single mono-clique of size `|S'| + 1`.

The proof is a case-split on `v ∈ T` for each `k`-subset `T ⊆ insert v S'`:
when `v ∈ T`, `hLink` discharges directly; when `v ∉ T`, `T ⊆ S'` and `hS'`
discharges. -/
lemma IsMonochromatic.insert_vertex {n k : ℕ} {χ : kColoring n} {c : Bool}
    {v : Fin n} {S' : Finset (Fin n)} (hvS' : v ∉ S')
    (hS' : IsMonochromatic χ k S' c)
    (hLink : ∀ T ∈ (insert v S').powersetCard k, v ∈ T → χ T = c) :
    IsMonochromatic χ k (insert v S') c := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTsub, hTcard⟩ := hT
  by_cases hvT : v ∈ T
  · -- Case `v ∈ T`: `hLink` applies directly.
    exact hLink T (Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩) hvT
  · -- Case `v ∉ T`: then `T ⊆ S'` (every element of `T` lies in `insert v S'`
    -- but is not `v`), so the non-vertex-side hypothesis `hS'` discharges.
    have hT_sub_S' : T ⊆ S' := by
      intro x hxT
      have hxInsert : x ∈ insert v S' := hTsub hxT
      rcases Finset.mem_insert.mp hxInsert with hxv | hxS'
      · exact absurd (hxv ▸ hxT) hvT
      · exact hxS'
    exact hS' T (Finset.mem_powersetCard.mpr ⟨hT_sub_S', hTcard⟩)

/-! ### S8 ACT-F: the Ramsey 1930 recursion body — `ramsey_existence` closes

Two final pieces complete the proof:

* `IsRamsey.within` — a **transfer lemma**: an `IsRamsey ν k s t` certificate
  can be run inside any `ν`-element vertex subset `A ⊆ Fin m`. The order
  embedding `Fin ν ↪o Fin m` enumerating `A` (`Finset.orderEmbOfFin`) pulls
  a coloring of `[m]^{(k)}` back to `[ν]^{(k)}`; the extracted clique maps
  forward into `A`, with monochromaticity transported along
  `Finset.subset_map_iff` exactly as in `IsRamsey.mono_n`.
* `ramsey_existence_of_one_le` — the two-layer Ramsey 1930 induction:
  **outer** structural induction on the uniformity `k` (base `k = 1` is the
  S3 pigeonhole `isRamsey_one_iff`), **inner** bounded induction on the
  target sum `s + t` (boundaries `s = k` / `t = k` are the S4
  `is_ramsey_self_*` lemmas). The genuine step at uniformity `k + 1` picks
  `n₁` with `IsRamsey n₁ (k+1) (s-1) t` and `n₂` with
  `IsRamsey n₂ (k+1) s (t-1)` from the inner IH, then `m` with
  `IsRamsey m k n₁ n₂` from the outer IH, and shows `m + 1` works: run the
  `k`-uniform certificate on the link coloring at the last vertex `v`
  (inside the `m`-element complement of `v`), then run the appropriate
  `(k+1)`-uniform certificate inside the resulting link-monochromatic
  clique; either it produces the *other*-colored target clique outright, or
  a same-colored clique one short of target, which `insert_vertex` splices
  with `v` (via `link_lifts`) to full size.
-/

/-- **Transfer lemma.** An `IsRamsey ν k s t` certificate can be run inside
any `ν`-element vertex subset `A` of `Fin m`: every coloring of `[m]^{(k)}`
admits a monochromatic `s`- or `t`-clique **contained in `A`**.

The proof pulls `χ` back along the order embedding `Fin ν ↪o Fin m`
enumerating `A` (`Finset.orderEmbOfFin`), extracts the clique on the `Fin ν`
side, and maps it forward; monochromaticity transports along
`Finset.subset_map_iff` exactly as in `IsRamsey.mono_n` (of which this is
the relativized refinement: `mono_n` is essentially the case `A = univ`). -/
lemma IsRamsey.within {ν k s t : ℕ} (hR : IsRamsey ν k s t)
    {m : ℕ} (χ : kColoring m) (A : Finset (Fin m)) (hA : A.card = ν) :
    (∃ S : Finset (Fin m), S ⊆ A ∧ S.card = s ∧ IsMonochromatic χ k S false) ∨
    (∃ S : Finset (Fin m), S ⊆ A ∧ S.card = t ∧ IsMonochromatic χ k S true) := by
  classical
  let f : Fin ν ↪ Fin m := (A.orderEmbOfFin hA).toEmbedding
  have hf_mem : ∀ i, f i ∈ A := fun i => A.orderEmbOfFin_mem hA i
  let χ' : kColoring ν := fun S => χ (S.map f)
  -- Monochromaticity for the pulled-back coloring pushes forward along `f`.
  have transfer : ∀ (S : Finset (Fin ν)) (c : Bool), IsMonochromatic χ' k S c →
      IsMonochromatic χ k (S.map f) c := by
    intro S c hSm T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    obtain ⟨T₀, hT₀sub, hT₀eq⟩ := Finset.subset_map_iff.mp hTsub
    have hT₀card : T₀.card = k := by
      have hcard := congrArg Finset.card hT₀eq
      rw [Finset.card_map] at hcard
      omega
    have key : χ' T₀ = c := hSm T₀ (Finset.mem_powersetCard.mpr ⟨hT₀sub, hT₀card⟩)
    rw [hT₀eq]
    exact key
  have hsub : ∀ S : Finset (Fin ν), S.map f ⊆ A := by
    intro S x hx
    rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
    exact hf_mem i
  rcases hR χ' with ⟨S, hSc, hSm⟩ | ⟨S, hSc, hSm⟩
  · exact Or.inl ⟨S.map f, hsub S, by rw [Finset.card_map]; exact hSc,
      transfer S false hSm⟩
  · exact Or.inr ⟨S.map f, hsub S, by rw [Finset.card_map]; exact hSc,
      transfer S true hSm⟩

/-- **Ramsey's hypergraph theorem, full parameter range `k ≥ 1`.** The
two-layer Ramsey 1930 induction; see the section docstring above for the
architecture. Stated with explicit `∀` binders so both induction layers can
be run without generalization bookkeeping. -/
theorem ramsey_existence_of_one_le :
    ∀ k s t : ℕ, 1 ≤ k → k ≤ s → k ≤ t → ∃ n, IsRamsey n k s t := by
  intro k
  induction k with
  | zero => intro s t h1 _ _; exact absurd h1 (by omega)
  | succ k ihk =>
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- Uniformity 1: the pigeonhole bound `n = s + t - 1` (S3).
      intro s t _ hs ht
      exact ⟨s + t - 1, (isRamsey_one_iff (s + t - 1) s t hs ht).mpr le_rfl⟩
    · -- Uniformity `k + 1 ≥ 2`. Outer IH is available at uniformity `k`.
      have IH : ∀ s' t', k ≤ s' → k ≤ t' → ∃ n, IsRamsey n k s' t' :=
        fun s' t' => ihk s' t' hk1
      -- Inner bounded induction on the target sum `s + t`.
      have H : ∀ N s t, s + t ≤ N → k + 1 ≤ s → k + 1 ≤ t →
          ∃ n, IsRamsey n (k + 1) s t := by
        intro N
        induction N with
        | zero => intro s t hsum hs _; exact absurd hsum (by omega)
        | succ N ihN =>
          intro s t hsum hs ht
          rcases eq_or_lt_of_le hs with hs_eq | hs_lt
          · -- `s = k + 1` boundary: `n = t` via `is_ramsey_self_right`.
            refine ⟨t, ?_⟩
            rw [← hs_eq]
            exact is_ramsey_self_right (k + 1) t (by omega) ht
          rcases eq_or_lt_of_le ht with ht_eq | ht_lt
          · -- `t = k + 1` boundary: `n = s` via `is_ramsey_self_left`.
            refine ⟨s, ?_⟩
            rw [← ht_eq]
            exact is_ramsey_self_left (k + 1) s (by omega) hs
          -- Genuine case `s > k + 1 ∧ t > k + 1`: the Ramsey 1930 recursion.
          -- Inner IH at the two shrunk targets (each sum drops below `N + 1`).
          obtain ⟨n₁', hn₁'⟩ := ihN (s - 1) t (by omega) (by omega) ht
          obtain ⟨n₂', hn₂'⟩ := ihN s (t - 1) (by omega) hs (by omega)
          -- Enlarge both witnesses to `≥ k` so they are legal `k`-uniform targets.
          have hn₁ : IsRamsey (max n₁' k) (k + 1) (s - 1) t :=
            IsRamsey.mono_n (le_max_left _ _) hn₁'
          have hn₂ : IsRamsey (max n₂' k) (k + 1) s (t - 1) :=
            IsRamsey.mono_n (le_max_left _ _) hn₂'
          -- Outer IH: a `k`-uniform certificate targeting those two sizes.
          obtain ⟨m, hm⟩ := IH (max n₁' k) (max n₂' k)
            (le_max_right _ _) (le_max_right _ _)
          refine ⟨m + 1, ?_⟩
          intro χ
          -- Distinguished vertex and its `m`-element complement.
          set v : Fin (m + 1) := Fin.last m
          have hA_card : ((Finset.univ : Finset (Fin (m + 1))).erase v).card = m := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
              Fintype.card_fin]
            omega
          -- Run the `k`-uniform certificate on the link coloring at `v`,
          -- inside the complement of `v`.
          rcases hm.within (kColoring.link χ v) (Finset.univ.erase v) hA_card with
            ⟨S, hSsub, hScard, hSm⟩ | ⟨S, hSsub, hScard, hSm⟩
          · -- Link-mono-**false** `(k)`-clique `S`, `|S| = max n₁' k ≥ n₁'`.
            have hvS : v ∉ S := fun hv' => (Finset.mem_erase.mp (hSsub hv')).1 rfl
            -- Run the `(k+1)`-uniform certificate `hn₁` inside `S`.
            rcases hn₁.within χ S hScard with
              ⟨S', hS'sub, hS'card, hS'm⟩ | ⟨S', _, hS'card, hS'm⟩
            · -- χ-mono-false `(s-1)`-clique `S' ⊆ S`: splice `v` in.
              have hvS' : v ∉ S' := fun hv' => hvS (hS'sub hv')
              have hLink : ∀ T ∈ (insert v S').powersetCard (k + 1), v ∈ T →
                  χ T = false := fun T hT hvT =>
                IsMonochromatic.link_lifts (k := k + 1) χ v false S hvS hSm T
                  (Finset.powersetCard_mono (Finset.insert_subset_insert v hS'sub) hT)
                  hvT
              refine Or.inl ⟨insert v S', ?_,
                IsMonochromatic.insert_vertex hvS' hS'm hLink⟩
              rw [Finset.card_insert_of_notMem hvS', hS'card]
              omega
            · -- χ-mono-true `t`-clique: done outright.
              exact Or.inr ⟨S', hS'card, hS'm⟩
          · -- Link-mono-**true** `(k)`-clique `S`, `|S| = max n₂' k ≥ n₂'`: symmetric.
            have hvS : v ∉ S := fun hv' => (Finset.mem_erase.mp (hSsub hv')).1 rfl
            rcases hn₂.within χ S hScard with
              ⟨S', _, hS'card, hS'm⟩ | ⟨S', hS'sub, hS'card, hS'm⟩
            · -- χ-mono-false `s`-clique: done outright.
              exact Or.inl ⟨S', hS'card, hS'm⟩
            · -- χ-mono-true `(t-1)`-clique `S' ⊆ S`: splice `v` in.
              have hvS' : v ∉ S' := fun hv' => hvS (hS'sub hv')
              have hLink : ∀ T ∈ (insert v S').powersetCard (k + 1), v ∈ T →
                  χ T = true := fun T hT hvT =>
                IsMonochromatic.link_lifts (k := k + 1) χ v true S hvS hSm T
                  (Finset.powersetCard_mono (Finset.insert_subset_insert v hS'sub) hT)
                  hvT
              refine Or.inr ⟨insert v S', ?_,
                IsMonochromatic.insert_vertex hvS' hS'm hLink⟩
              rw [Finset.card_insert_of_notMem hvS', hS'card]
              omega
      intro s t _ hs ht
      exact H (s + t) s t le_rfl hs ht

/-- (OQ-03a) **Ramsey's hypergraph theorem.** For every uniformity `k ≥ 2`
and every pair of target sizes `s, t ≥ k`, there is a finite `n` such that
every 2-coloring of `[n]^{(k)}` contains a monochromatic `s`- or `t`-clique.

This is the main result of the OQ-03 entry, now fully proved (S8 ACT-F): it
is the `k ≥ 2` restriction of `ramsey_existence_of_one_le`, the classical
Ramsey 1930 two-layer induction on `k` (uniformity, outer layer) and `s + t`
(target sizes, inner layer). Boundary cases `s = k` / `t = k` are
`is_ramsey_self_right` / `is_ramsey_self_left`; the genuine inductive case
runs the neighborhood-collapse recursion through `kColoring.link`,
`IsRamsey.within`, `IsMonochromatic.link_lifts`, and
`IsMonochromatic.insert_vertex`. -/
theorem ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    ∃ n, IsRamsey n k s t :=
  ramsey_existence_of_one_le k s t (by omega) hs ht

/-! ### S9: `sInf` glue and the recursive Erdős–Rado inequality (OQ-03b, step 1)

With `ramsey_existence_of_one_le` in hand, the `sInf` defining
`ramseyNumber` ranges over a nonempty set (in the legal parameter range),
so its two defining properties become available as lemmas:

* `ramseyNumber_le_of_isRamsey` — any Ramsey witness bounds the number
  from above (`Nat.sInf_le`);
* `isRamsey_ramseyNumber` — the number itself satisfies the Ramsey
  condition (`Nat.sInf_mem` on the nonempty defining set);
* `min_le_ramseyNumber` — the trivial vertex-count lower bound: a
  monochromatic clique needs at least `min s t` vertices. This is what
  certifies inner `ramseyNumber` values as legal (≥ `k`) target sizes
  when they are fed back into a lower-uniformity Ramsey number.

They combine into the **recursive Erdős–Rado inequality**

  `R_{k+1}(s, t) ≤ R_k(R_{k+1}(s-1, t), R_{k+1}(s, t-1)) + 1`,

whose proof is the S8 genuine-case recursion body re-run at the `sInf`
witnesses. The body is extracted as the standalone step lemma
`IsRamsey.step` (explicit witnesses `n₁`, `n₂`, `m` instead of the
existentials of `ramsey_existence_of_one_le`, and no `max`-bumping —
the `sInf` values are already large enough by `min_le_ramseyNumber`).
Iterating the inequality down to the pigeonhole base
`R_1(s, t) = s + t - 1` (`ramseyNumber_one`) is what produces the
Erdős–Rado tower upper bound (the S10 target). -/

/-- **Upper `sInf` glue.** Any `n` satisfying the Ramsey condition bounds
`ramseyNumber k s t` from above. No side conditions: this direction of the
`sInf` characterization needs no nonemptiness. -/
lemma ramseyNumber_le_of_isRamsey {n k s t : ℕ} (h : IsRamsey n k s t) :
    ramseyNumber k s t ≤ n := by
  unfold ramseyNumber
  exact Nat.sInf_le h

/-- **Membership `sInf` glue.** In the parameter range of
`ramsey_existence_of_one_le` the set `{n | IsRamsey n k s t}` is nonempty,
so its infimum is a genuine member (`Nat.sInf_mem`): `ramseyNumber k s t`
itself satisfies the Ramsey condition. -/
lemma isRamsey_ramseyNumber (k s t : ℕ) (hk : 1 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    IsRamsey (ramseyNumber k s t) k s t := by
  obtain ⟨n, hn⟩ := ramsey_existence_of_one_le k s t hk hs ht
  have h : sInf {n | IsRamsey n k s t} ∈ {n | IsRamsey n k s t} :=
    Nat.sInf_mem ⟨n, hn⟩
  exact h

/-- **Vertex-count lower bound.** A monochromatic `s`- or `t`-clique carries
`s` (resp. `t`) distinct vertices of `Fin n`, so `IsRamsey n k s t` forces
`min s t ≤ n`; applying this at `n = ramseyNumber k s t` (a Ramsey witness
by `isRamsey_ramseyNumber`) gives `min s t ≤ ramseyNumber k s t`. Run the
witness on any coloring — the constant-`true` one will do. -/
lemma min_le_ramseyNumber (k s t : ℕ) (hk : 1 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    min s t ≤ ramseyNumber k s t := by
  have hR := isRamsey_ramseyNumber k s t hk hs ht
  have hcard_le : ∀ S : Finset (Fin (ramseyNumber k s t)),
      S.card ≤ ramseyNumber k s t := by
    intro S
    calc S.card ≤ (Finset.univ : Finset (Fin (ramseyNumber k s t))).card :=
          Finset.card_le_card (Finset.subset_univ S)
      _ = ramseyNumber k s t := by rw [Finset.card_univ, Fintype.card_fin]
  rcases hR (fun _ => true) with ⟨S, hScard, _⟩ | ⟨S, hScard, _⟩
  · have := hcard_le S
    have hmin : min s t ≤ s := min_le_left _ _
    omega
  · have := hcard_le S
    have hmin : min s t ≤ t := min_le_right _ _
    omega

/-- **The Ramsey 1930 recursion step, isolated.** If `n₁` handles targets
`(s-1, t)` and `n₂` handles `(s, t-1)` at uniformity `k + 1`, and `m`
handles targets `(n₁, n₂)` at uniformity `k`, then `m + 1` handles `(s, t)`
at uniformity `k + 1`.

This is the genuine-case body of `ramsey_existence_of_one_le`, restated
with explicit witnesses so it can be run at the `sInf` values in
`ramseyNumber_succ_le`: run the `k`-uniform certificate `hm` on the link
coloring at the last vertex `v` (inside the `m`-element complement of `v`
via `IsRamsey.within`), then run `hn₁` or `hn₂` inside the resulting
link-monochromatic clique; either it produces the *other*-colored target
clique outright, or a same-colored clique one vertex short of target,
which `IsMonochromatic.insert_vertex` splices with `v` (coverage of the
`v`-containing `k+1`-subsets coming from `IsMonochromatic.link_lifts`). -/
lemma IsRamsey.step {k s t n₁ n₂ m : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hn₁ : IsRamsey n₁ (k + 1) (s - 1) t)
    (hn₂ : IsRamsey n₂ (k + 1) s (t - 1))
    (hm : IsRamsey m k n₁ n₂) : IsRamsey (m + 1) (k + 1) s t := by
  intro χ
  -- Distinguished vertex and its `m`-element complement.
  set v : Fin (m + 1) := Fin.last m
  have hA_card : ((Finset.univ : Finset (Fin (m + 1))).erase v).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      Fintype.card_fin]
    omega
  -- Run the `k`-uniform certificate on the link coloring at `v`,
  -- inside the complement of `v`.
  rcases hm.within (kColoring.link χ v) (Finset.univ.erase v) hA_card with
    ⟨S, hSsub, hScard, hSm⟩ | ⟨S, hSsub, hScard, hSm⟩
  · -- Link-mono-**false** `k`-clique `S`, `|S| = n₁`.
    have hvS : v ∉ S := fun hv' => (Finset.mem_erase.mp (hSsub hv')).1 rfl
    rcases hn₁.within χ S hScard with
      ⟨S', hS'sub, hS'card, hS'm⟩ | ⟨S', _, hS'card, hS'm⟩
    · -- χ-mono-false `(s-1)`-clique `S' ⊆ S`: splice `v` in.
      have hvS' : v ∉ S' := fun hv' => hvS (hS'sub hv')
      have hLink : ∀ T ∈ (insert v S').powersetCard (k + 1), v ∈ T →
          χ T = false := fun T hT hvT =>
        IsMonochromatic.link_lifts (k := k + 1) χ v false S hvS hSm T
          (Finset.powersetCard_mono (Finset.insert_subset_insert v hS'sub) hT)
          hvT
      refine Or.inl ⟨insert v S', ?_,
        IsMonochromatic.insert_vertex hvS' hS'm hLink⟩
      rw [Finset.card_insert_of_notMem hvS', hS'card]
      omega
    · -- χ-mono-true `t`-clique: done outright.
      exact Or.inr ⟨S', hS'card, hS'm⟩
  · -- Link-mono-**true** `k`-clique `S`, `|S| = n₂`: symmetric.
    have hvS : v ∉ S := fun hv' => (Finset.mem_erase.mp (hSsub hv')).1 rfl
    rcases hn₂.within χ S hScard with
      ⟨S', _, hS'card, hS'm⟩ | ⟨S', hS'sub, hS'card, hS'm⟩
    · -- χ-mono-false `s`-clique: done outright.
      exact Or.inl ⟨S', hS'card, hS'm⟩
    · -- χ-mono-true `(t-1)`-clique `S' ⊆ S`: splice `v` in.
      have hvS' : v ∉ S' := fun hv' => hvS (hS'sub hv')
      have hLink : ∀ T ∈ (insert v S').powersetCard (k + 1), v ∈ T →
          χ T = true := fun T hT hvT =>
        IsMonochromatic.link_lifts (k := k + 1) χ v true S hvS hSm T
          (Finset.powersetCard_mono (Finset.insert_subset_insert v hS'sub) hT)
          hvT
      refine Or.inr ⟨insert v S', ?_,
        IsMonochromatic.insert_vertex hvS' hS'm hLink⟩
      rw [Finset.card_insert_of_notMem hvS', hS'card]
      omega

/-- (OQ-03b, recursion layer) **The recursive Erdős–Rado inequality.** For
`k ≥ 1` and target sizes `s, t ≥ k + 2` (the genuinely recursive range —
smaller targets are the boundary collapses `ramseyNumber_one` and
`is_ramsey_self_right`/`left`):

  `R_{k+1}(s, t) ≤ R_k(R_{k+1}(s-1, t), R_{k+1}(s, t-1)) + 1.`

Proof: instantiate the recursion body `IsRamsey.step` at the three `sInf`
witnesses supplied by `isRamsey_ramseyNumber`; the vertex-count bound
`min_le_ramseyNumber` certifies the two inner Ramsey numbers as legal
(≥ `k`) target sizes at uniformity `k`, so no `max`-bumping is needed.
Iterating this inequality down to the pigeonhole base
`R_1(s, t) = s + t - 1` yields the Erdős–Rado tower upper bound (S10). -/
theorem ramseyNumber_succ_le (k s t : ℕ) (hk : 1 ≤ k)
    (hs : k + 2 ≤ s) (ht : k + 2 ≤ t) :
    ramseyNumber (k + 1) s t ≤
      ramseyNumber k (ramseyNumber (k + 1) (s - 1) t)
        (ramseyNumber (k + 1) s (t - 1)) + 1 := by
  set n₁ := ramseyNumber (k + 1) (s - 1) t with hn₁_def
  set n₂ := ramseyNumber (k + 1) s (t - 1) with hn₂_def
  have hn₁ : IsRamsey n₁ (k + 1) (s - 1) t :=
    isRamsey_ramseyNumber (k + 1) (s - 1) t (by omega) (by omega) (by omega)
  have hn₂ : IsRamsey n₂ (k + 1) s (t - 1) :=
    isRamsey_ramseyNumber (k + 1) s (t - 1) (by omega) (by omega) (by omega)
  -- The inner Ramsey numbers are ≥ k + 1 > k by the vertex-count bound.
  have hk₁ : k ≤ n₁ := by
    have h := min_le_ramseyNumber (k + 1) (s - 1) t (by omega) (by omega) (by omega)
    rw [← hn₁_def] at h
    omega
  have hk₂ : k ≤ n₂ := by
    have h := min_le_ramseyNumber (k + 1) s (t - 1) (by omega) (by omega) (by omega)
    rw [← hn₂_def] at h
    omega
  -- The `sInf` witness at uniformity `k` with the inner numbers as targets.
  have hm : IsRamsey (ramseyNumber k n₁ n₂) k n₁ n₂ :=
    isRamsey_ramseyNumber k n₁ n₂ hk hk₁ hk₂
  exact ramseyNumber_le_of_isRamsey
    (IsRamsey.step (by omega) (by omega) hn₁ hn₂ hm)

end RamseyK
