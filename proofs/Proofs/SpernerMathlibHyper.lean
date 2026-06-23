/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib
import Proofs.SpernerMathlib

/-!
# Sperner's Lemma — Hypergraph Generalisation (S2 ACT)

A palette-relative, cell-dependent-index version of the parity argument in
`Proofs/SpernerMathlib.lean`. The dependent index type `ι : Cell → Type*`
lets each cell carry its own arity (hence "hypergraph"), and the abstract
palette `P` replaces `Fin (d + 1)`.

This file is the **S2 ACT** deliverable for `sperner-mathlib-oq-01`. It
integrates the prior PREP work:

* S1 OBSERVE (#18282): axioms inventory + weakening map
* S1b OBSERVE (#18344): `IsDoorHyper` needs a distinguished `top : P`
* S2 PREP (#18360): Σ-type ergonomics and file skeleton
* S1e OBSERVE (#18411): the `hι_size` palette-cardinality constraint
* S2 PREP audit (#18638): Mathlib bearer pinning at v4.26.0 SHA 2df2f01
* S2c PREP (#18688): cardinality dichotomy + Equiv-transport reduction
* S2d PREP (#18727): door-parity bearer chains
* S2e PREP (#18788): Σ-pair involution bearer chain

Specialization recovers `SpernerMathlib` when `ι := fun _ => Fin (d + 1)`,
`P := Fin (d + 1)`, and `top := Fin.last d` (deferred to follow-up).

## Architecture

§1 Setup            (variables, type abbreviations, decidability)
§2 Definitions      (IsPanchromaticHyper, IsDoorHyper)
§3 Per-cell parity  (door_count_parity_hyper)
§4 Global parity    (even_card_interior_doors_hyper)
§5 Main theorem     (sperner_parity_hyper, exists_panchromatic_hyper)

The two structural sorries (`door_count_parity_hyper` and
`even_card_interior_doors_hyper`) are tracked per S2c/S2d/S2e PREP and are
the only sorries in this file; higher-level results chain through.

## References

* Parent file `Proofs/SpernerMathlib.lean` (verified, 897 lines, 0 sorries)
* `research/problems/sperner-mathlib-oq-01/{knowledge,state}.md`
-/

namespace SpernerMathlibHyper

open Finset

/-! ## §1 Setup -/

section Setup

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The vertex map: cell `s` indexes its vertices by `ι s`. -/
abbrev VertexMap (V : Type*) (Cell : Type*) (ι : Cell → Type*) : Type _ :=
  ∀ s : Cell, ι s → V

/-- The dependent-index adjacency map: each cell-face pair `(s, i)`
points to a face of some neighbouring cell (or `none` at the boundary). -/
abbrev AdjMap (Cell : Type*) (ι : Cell → Type*) : Type _ :=
  ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s')

end Setup

/-! ## §2 Definitions -/

section Definitions

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A cell is panchromatic if its coloring is surjective onto the palette. -/
def IsPanchromaticHyper (vertex : VertexMap V Cell ι) (c : V → P) (s : Cell) :
    Prop :=
  Function.Surjective (c ∘ vertex s)

/-- A face `(s, k)` is a door (palette-relative): every non-`top` palette
element is realised by some other vertex of `s`. The `top : P` parameter
plays the role of `Fin.last d` in the parent file — without it, the door
condition would lose its asymmetry and the parity argument would fail.
See S1b OBSERVE for the gap-and-fix. -/
def IsDoorHyper (vertex : VertexMap V Cell ι) (c : V → P)
    (top : P) (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p

instance decidableIsPanchromaticHyper (vertex : VertexMap V Cell ι)
    (c : V → P) (s : Cell) :
    Decidable (IsPanchromaticHyper vertex c s) := by
  unfold IsPanchromaticHyper Function.Surjective; exact inferInstance

instance decidableIsDoorHyper (vertex : VertexMap V Cell ι) (c : V → P)
    (top : P) (s : Cell) (k : ι s) :
    Decidable (IsDoorHyper vertex c top s k) := by
  unfold IsDoorHyper; exact inferInstance

end Definitions

/-! ## §3 Per-cell parity -/

section PerCellParity

variable {ι_one : Type*} [Fintype ι_one] [DecidableEq ι_one]
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Per-cell parity (palette-relative). The door-count modulo 2 equals
the surjectivity indicator. This is the structural lemma; under the
`hι_size : Fintype.card ι_one ≤ Fintype.card P` constraint it reduces
(per S2c PREP) via cardinality dichotomy:

* **Strict case** `|ι| < |P|`: both sides are 0 by pigeonhole.
* **Equality case** `|ι| = |P|`: `Fintype.equivOfCardEq`-transport
  reduces to `SpernerMathlib.door_count_parity` (parent, verified).

The detailed bearer chain is documented in
`sessions/2026-05-13-s2c-prep-cardinality-dichotomy-and-equiv-transport.md`
and `sessions/2026-05-13-s2d-prep-subsorries-bearer-chains.md`.
-/
theorem door_count_parity_hyper
    (f : ι_one → P) (top : P)
    (hι_size : Fintype.card ι_one ≤ Fintype.card P) :
    (Finset.univ.filter (fun k : ι_one =>
      ∀ p : P, p ≠ top → ∃ i : ι_one, i ≠ k ∧ f i = p)).card % 2
    = if Function.Surjective f then 1 else 0 := by
  classical
  by_cases hcard : Fintype.card ι_one < Fintype.card P
  · -- Strict case (S3 ACT): pigeonhole rules out doors and rules out
    -- surjectivity, so both sides are 0.
    have hnotsurj : ¬ Function.Surjective f := fun hsurj =>
      absurd (Fintype.card_le_of_surjective f hsurj) (not_le.mpr hcard)
    have hP_pos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨top⟩
    have hempty : (Finset.univ.filter (fun k : ι_one =>
        ∀ p : P, p ≠ top → ∃ i : ι_one, i ≠ k ∧ f i = p)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨_, hdoor⟩ := hk
      -- The "door" hypothesis says every non-`top` palette element appears in
      -- the image of `Finset.univ.erase k` under `f`. Chain through
      -- `card_le_card` + `card_image_le` to deduce card P ≤ card ι_one,
      -- contradicting the strict-case hypothesis.
      have hsub : (Finset.univ.erase top : Finset P)
          ⊆ ((Finset.univ.erase k : Finset ι_one).image f) := by
        intro p hp
        rw [Finset.mem_erase] at hp
        obtain ⟨hp_ne, _⟩ := hp
        obtain ⟨i, hi_ne, hi_eq⟩ := hdoor p hp_ne
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ i⟩, hi_eq⟩
      have hcardP : (Finset.univ.erase top : Finset P).card =
          Fintype.card P - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ]
      have hcardι : (Finset.univ.erase k : Finset ι_one).card =
          Fintype.card ι_one - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
      have h1 : (Finset.univ.erase top : Finset P).card ≤
          ((Finset.univ.erase k : Finset ι_one).image f).card :=
        Finset.card_le_card hsub
      have h2 : ((Finset.univ.erase k : Finset ι_one).image f).card ≤
          (Finset.univ.erase k : Finset ι_one).card := Finset.card_image_le
      have h12 : Fintype.card P - 1 ≤ Fintype.card ι_one - 1 := by
        rw [← hcardP, ← hcardι]; exact le_trans h1 h2
      -- `k : ι_one` exhibits inhabitation; combined with `hP_pos`, this lets
      -- us cancel both `- 1`s.
      have hι_pos : 0 < Fintype.card ι_one := Fintype.card_pos_iff.mpr ⟨k⟩
      have hP_le : Fintype.card P ≤ Fintype.card ι_one := by
        calc Fintype.card P
            = Fintype.card P - 1 + 1 := (Nat.sub_add_cancel hP_pos).symm
          _ ≤ Fintype.card ι_one - 1 + 1 := Nat.add_le_add_right h12 1
          _ = Fintype.card ι_one := Nat.sub_add_cancel hι_pos
      exact absurd hP_le (not_le.mpr hcard)
    rw [hempty]
    simp [hnotsurj]
  · -- Equality case (deferred to S4): `card ι_one = card P` via
    -- `le_antisymm hι_size (not_lt.mp hcard)`; transport `f` to the parent's
    -- `Fin (d+1)` shape via `Fintype.equivOfCardEq` + a `top`-permutation
    -- normalisation, then invoke `SpernerMathlib.door_count_parity`. See
    -- S2c PREP cardinality dichotomy and S2d PREP bearer chains (S5 ACT impl).
    have hcard_eq : Fintype.card ι_one = Fintype.card P :=
      le_antisymm hι_size (not_lt.mp hcard)
    have hP_pos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨top⟩
    set n := Fintype.card P - 1 with hn_def
    have hcardP_succ : Fintype.card P = n + 1 := by omega
    have hcardι_succ : Fintype.card ι_one = n + 1 := by
      rw [hcard_eq, hcardP_succ]
    let eι : ι_one ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcardι_succ
    let eP_base : P ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcardP_succ
    let eP : P ≃ Fin (n + 1) :=
      eP_base.trans (Equiv.swap (eP_base top) (Fin.last n))
    have he_top : eP top = Fin.last n := by
      simp [eP, Equiv.swap_apply_left]
    let f' : Fin (n + 1) → Fin (n + 1) := fun i' => eP (f (eι.symm i'))
    have hparent := Sperner.door_count_parity n f'
    have hlhs_card :
        (Finset.univ.filter (fun k : ι_one =>
          ∀ p : P, p ≠ top → ∃ i : ι_one, i ≠ k ∧ f i = p)).card =
        (Finset.univ.filter (fun k' : Fin (n + 1) =>
          ∀ j : Fin n, ∃ i' : Fin (n + 1), i' ≠ k' ∧
            f' i' = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).card := by
      apply Finset.card_equiv eι
      intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hk j
        set p : P := eP.symm ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ with hp_def
        have hp_ne_top : p ≠ top := by
          intro heq
          have h1 : eP p = eP top := congr_arg eP heq
          rw [he_top] at h1
          have h2 : eP p = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
            rw [hp_def, Equiv.apply_symm_apply]
          rw [h2] at h1
          have hval : j.val = (Fin.last n).val := congr_arg Fin.val h1
          simp [Fin.last] at hval
          exact absurd hval (Nat.ne_of_lt j.isLt)
        obtain ⟨i, hi_ne, hi_eq⟩ := hk p hp_ne_top
        refine ⟨eι i, fun heq => hi_ne (eι.injective heq), ?_⟩
        show f' (eι i) = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
        simp only [f', Equiv.symm_apply_apply]
        rw [hi_eq, hp_def, Equiv.apply_symm_apply]
      · intro hk' p hp_ne_top
        have hep_ne_last : eP p ≠ Fin.last n := by
          intro heq
          exact hp_ne_top (eP.injective (heq.trans he_top.symm))
        have hval_lt : (eP p).val < n := by
          have hle : (eP p).val ≤ n := Nat.lt_succ_iff.mp (eP p).isLt
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact hlt
          · exfalso
            apply hep_ne_last
            apply Fin.ext
            simp [Fin.last, heq]
        let j : Fin n := ⟨(eP p).val, hval_lt⟩
        have hj_eq : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) = eP p :=
          Fin.ext rfl
        obtain ⟨i', hi'_ne, hi'_eq⟩ := hk' j
        refine ⟨eι.symm i', ?_, ?_⟩
        · intro hke
          apply hi'_ne
          rw [← hke, Equiv.apply_symm_apply]
        · apply eP.injective
          show eP (f (eι.symm i')) = eP p
          have hf' : eP (f (eι.symm i')) = f' i' := rfl
          rw [hf', hi'_eq, hj_eq]
    have hsurj_iff : Function.Surjective f ↔ Function.Surjective f' := by
      constructor
      · intro hsurj j'
        obtain ⟨i, hi⟩ := hsurj (eP.symm j')
        refine ⟨eι i, ?_⟩
        show eP (f (eι.symm (eι i))) = j'
        rw [Equiv.symm_apply_apply, hi, Equiv.apply_symm_apply]
      · intro hsurj p
        obtain ⟨i', hi'⟩ := hsurj (eP p)
        refine ⟨eι.symm i', eP.injective ?_⟩
        show eP (f (eι.symm i')) = eP p
        have hf' : eP (f (eι.symm i')) = f' i' := rfl
        rw [hf', hi']
    rw [hlhs_card, hparent]
    exact (if_congr hsurj_iff rfl rfl).symm

end PerCellParity

/-! ## §4 Global parity -/

section GlobalParity

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Total adjacency: send a cell-face pair to itself on the boundary,
or to its adjacent pair in the interior. Mirrors `adjMap` in the parent
but ranges over the dependent Σ-type. -/
private def adjMapHyper (adj : AdjMap Cell ι)
    (p : Σ s : Cell, ι s) : Σ s : Cell, ι s :=
  match adj p.1 p.2 with
  | some sk => sk
  | none => p

/-- Extract the adjacent Σ-pair when adjacency is known to be interior. -/
private lemma adjHyper_some_of_ne_none (adj : AdjMap Cell ι)
    (p : Σ s : Cell, ι s) (h : adj p.1 p.2 ≠ none) :
    ∃ sk : Σ s' : Cell, ι s', adj p.1 p.2 = some sk := by
  cases hadj : adj p.1 p.2 with
  | none => exact absurd hadj h
  | some sk => exact ⟨sk, rfl⟩

/-- Door transfer through a shared face (hypergraph form). -/
private lemma isDoorHyper_of_shared_face
    (vertex : VertexMap V Cell ι)
    {c : V → P} {top : P} {s : Cell} {k : ι s}
    {s' : Cell} {k' : ι s'}
    (hvert : (Finset.univ.erase k).image (vertex s) =
      (Finset.univ.erase k').image (vertex s'))
    (h : IsDoorHyper vertex c top s k) : IsDoorHyper vertex c top s' k' := by
  intro p hp_ne_top
  obtain ⟨i, hi_ne, hi_eq⟩ := h p hp_ne_top
  have hmem : vertex s i ∈ (Finset.univ.erase k').image (vertex s') := by
    rw [← hvert]
    exact mem_image.mpr ⟨i, mem_erase.mpr ⟨hi_ne, mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := mem_image.mp hmem
  exact ⟨i', (mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩

/-- Door transfer through adjacency (iff form, hypergraph). -/
private lemma isDoorHyper_iff_of_adj
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    {c : V → P} {top : P} {s : Cell} {k : ι s}
    {s' : Cell} {k' : ι s'} (hadj_eq : adj s k = some ⟨s', k'⟩) :
    IsDoorHyper vertex c top s k ↔ IsDoorHyper vertex c top s' k' :=
  ⟨isDoorHyper_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq),
   isDoorHyper_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq).symm⟩

/-- Hypergraph interior-door pairing. The count of interior doors is
even because adjacency provides a fixed-point-free involution on the
Σ-type, preserving the door predicate. See S2e PREP for the Σ-pair
involution bearer chain. -/
theorem even_card_interior_doors_hyper
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι)
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (top : P) (c : V → P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧
        adj p.1 p.2 ≠ none)).card := by
  -- S4 ACT: applies `Sperner.even_card_fpf_invol` with the involution
  -- `adjMapHyper adj` on the Σ-type filter. The three side-conditions
  -- (involution, set-stability, fixed-point-free) follow from
  -- `hadj_symm`, `isDoorHyper_iff_of_adj`, and `hadj_ne` respectively.
  -- The Σ-form differs from the parent's `Cell × Fin (d+1)` only in the
  -- fixed-point-free step, which requires `Sigma.eta` rather than the
  -- parent's `Prod.fst`/`Prod.snd` definitional unfolding. See S2e PREP
  -- bearer chain.
  set S := (Finset.univ : Finset (Σ s : Cell, ι s)).filter
    (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)
  -- Helper: reduce `adjMapHyper adj q = sk` when `adj q.1 q.2 = some sk`.
  -- The match-form in `adjMapHyper` doesn't auto-reduce under `simp only`;
  -- we instead expose the reduction as a local lemma via `unfold`.
  have hMap : ∀ (q : Σ s : Cell, ι s) (sk : Σ s : Cell, ι s),
      adj q.1 q.2 = some sk → adjMapHyper adj q = sk := by
    intro q sk hq
    unfold adjMapHyper; rw [hq]
  apply Sperner.even_card_fpf_invol S (adjMapHyper adj)
  · -- involution: adjMapHyper (adjMapHyper p) = p
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    have h2 := hMap (⟨s', k'⟩ : Σ s : Cell, ι s) ⟨p.1, p.2⟩ hadj_back
    -- structure-eta closes ⟨p.1, p.2⟩ = p as rfl after the rewrites
    rw [h1, h2]
  · -- set-stability: adjMapHyper adj p ∈ S
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    rw [h1]
    refine ⟨(isDoorHyper_iff_of_adj vertex adj hadj_vertex hadj_eq).mp hdoor, ?_⟩
    rw [hadj_back]; exact Option.noConfusion
  · -- fixed-point-free: adjMapHyper adj p ≠ p
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ := adjHyper_some_of_ne_none adj p hadj_ne'
    have h1 := hMap p ⟨s', k'⟩ hadj_eq
    rw [h1]
    -- heq : (⟨s', k'⟩ : Σ s, ι s) = p; chain Sigma.eta with heq.symm.
    intro heq
    exact hadj_ne p.1 p.2 s' k' hadj_eq ((Sigma.eta p).trans heq.symm)

/-! ## §4b Door-count bookkeeping (hypergraph)

Σ-type analogues of the parent's `per_cell_door_parity`,
`card_doors_eq_sum`, and `doors_partition`. These are the finite-sum
bearers that let §5 chain §3 (per-cell parity) and §4 (interior
involution) into the global parity statement. -/

omit [DecidableEq V] [DecidableEq Cell] [Fintype Cell] in
/-- Per-cell parity (hypergraph): the door count of a single cell `s`
is congruent mod 2 to its panchromaticity indicator. Specialises
`door_count_parity_hyper` to `f := c ∘ vertex s`. -/
lemma per_cell_door_parity_hyper
    (vertex : VertexMap V Cell ι) (c : V → P) (top : P)
    (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P) (s : Cell) :
    (univ.filter (fun k : ι s => IsDoorHyper vertex c top s k)).card % 2 =
    if IsPanchromaticHyper vertex c s then 1 else 0 := by
  have h := door_count_parity_hyper (c ∘ vertex s) top (hι_size s)
  have h1 : (univ.filter (fun k : ι s => IsDoorHyper vertex c top s k)) =
      (univ.filter (fun k : ι s =>
        ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ (c ∘ vertex s) i = p)) := by
    ext k; simp only [mem_filter, mem_univ, true_and]; rfl
  rw [h1]
  have h2 : IsPanchromaticHyper vertex c s ↔
      Function.Surjective (c ∘ vertex s) := Iff.rfl
  simp only [h2]; convert h using 2

omit [DecidableEq V] [DecidableEq Cell] in
/-- Total door count equals the sum of per-cell door counts (hypergraph).
The Σ-type analogue of `card_doors_eq_sum`, bridged by `Fintype.sum_sigma`. -/
lemma card_doors_eq_sum_hyper
    (vertex : VertexMap V Cell ι) (c : V → P) (top : P) :
    ((univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2)).card =
    ∑ s : Cell, (univ.filter
      (fun k : ι s => IsDoorHyper vertex c top s k)).card := by
  have hlhs : ((univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2)).card =
    ∑ p : Σ s : Cell, ι s,
      if IsDoorHyper vertex c top p.1 p.2 then 1 else 0 := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  have hrhs : ∀ s : Cell,
      (univ.filter (fun k : ι s => IsDoorHyper vertex c top s k)).card =
      ∑ k : ι s, if IsDoorHyper vertex c top s k then 1 else 0 := by
    intro s
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  rw [hlhs, sum_congr rfl (fun s _ => hrhs s), Fintype.sum_sigma]

omit [DecidableEq V] in
/-- Total doors split into interior (`adj ≠ none`) and boundary
(`adj = none`) doors (hypergraph). Σ-type analogue of `doors_partition`. -/
lemma doors_partition_hyper
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι) (c : V → P) (top : P) :
    ((univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2)).card =
    ((univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card +
    ((univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext p
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      by_cases hadj_eq : adj p.1 p.2 = none
      · right; exact ⟨h, hadj_eq⟩
      · left; exact ⟨h, hadj_eq⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [disjoint_left]
    intro p h₁ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    exact h₁.2 h₂.2

end GlobalParity

/-! ## §5 Main theorem -/

section MainTheorem

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Hypergraph Sperner parity: the panchromatic cell count is congruent
modulo 2 to the boundary-door count. Chains through the structural
results in §3 and §4. -/
theorem sperner_parity_hyper
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι)
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)
    (top : P) (c : V → P) :
    (Finset.univ.filter (IsPanchromaticHyper vertex c)).card % 2 =
    ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧
        adj p.1 p.2 = none)).card % 2 := by
  -- Strategy (mirrors parent `sperner_parity`):
  --   1. Per-cell parity: per_cell_door_parity_hyper (§3 + §4b).
  --   2. Sum the per-cell parities over Cell (Sperner.sum_mod_congr).
  --   3. Total doors split into interior (even, §4) and boundary (§4b).
  --   4. The interior contribution vanishes mod 2.
  have hper := per_cell_door_parity_hyper vertex c top hι_size
  have hsum :
      (∑ s : Cell, (univ.filter
        (fun k : ι s => IsDoorHyper vertex c top s k)).card) % 2 =
      (∑ s : Cell, if IsPanchromaticHyper vertex c s then 1 else 0) % 2 :=
    Sperner.sum_mod_congr univ _ _ (fun s _ => by rw [hper s]; split <;> simp)
  have hfc_sum :
      (∑ s : Cell,
        if IsPanchromaticHyper vertex c s then (1 : ℕ) else 0) =
      (univ.filter (IsPanchromaticHyper vertex c)).card := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  have hdoor_sum := card_doors_eq_sum_hyper vertex c top
  have hpart := doors_partition_hyper vertex adj c top
  have heven := even_card_interior_doors_hyper vertex adj hadj_symm
    hadj_vertex hadj_ne top c
  obtain ⟨m, hm⟩ := heven
  calc (univ.filter (IsPanchromaticHyper vertex c)).card % 2
    _ = (∑ s : Cell,
        if IsPanchromaticHyper vertex c s then 1 else 0) % 2 := by rw [hfc_sum]
    _ = (∑ s : Cell, (univ.filter
        (fun k : ι s => IsDoorHyper vertex c top s k)).card) % 2 := hsum.symm
    _ = ((univ : Finset (Σ s : Cell, ι s)).filter
        (fun p => IsDoorHyper vertex c top p.1 p.2)).card % 2 := by rw [hdoor_sum]
    _ = (((univ : Finset (Σ s : Cell, ι s)).filter
        (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card +
       ((univ : Finset (Σ s : Cell, ι s)).filter
        (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card) % 2 := by
      rw [hpart]
    _ = ((univ : Finset (Σ s : Cell, ι s)).filter
        (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card % 2 := by
      rw [hm, Nat.add_mod,
        show (m + m) % 2 = 0 from by simp [← Nat.two_mul, Nat.mul_mod_right],
        Nat.zero_add, Nat.mod_mod_of_dvd]
      exact ⟨1, rfl⟩

/-- **Hypergraph Sperner's Lemma**: if the boundary-door count is odd,
some cell is panchromatic. -/
theorem exists_panchromatic_hyper
    (vertex : VertexMap V Cell ι) (adj : AdjMap Cell ι)
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)
    (top : P) (c : V → P)
    (hbdry : Odd ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧
        adj p.1 p.2 = none)).card) :
    ∃ s : Cell, IsPanchromaticHyper vertex c s := by
  have hparity := sperner_parity_hyper vertex adj hadj_symm hadj_vertex
    hadj_ne hι_size top c
  have hodd : Odd (Finset.univ.filter
      (IsPanchromaticHyper vertex c)).card := by
    rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
  have hpos : 0 < (Finset.univ.filter
      (IsPanchromaticHyper vertex c)).card := hodd.pos
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (mem_filter.mp hs).2⟩

end MainTheorem

end SpernerMathlibHyper
