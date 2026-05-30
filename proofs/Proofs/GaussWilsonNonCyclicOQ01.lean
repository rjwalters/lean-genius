import Proofs.GaussWilsonNonCyclic
import Proofs.GaussWilsonNonCyclicOQ01A
import Proofs.GaussWilsonNonCyclicOQ01B
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# Gauss–Wilson Non-Cyclic OQ-01 — Phase C: Main iff Theorem (scaffold)

This file delivers the **scaffold** of `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`
for `gauss-wilson-non-cyclic-oq-01`, building on Phase A and Phase B.

**Main theorem.** For `n ≥ 1`,

  ∏ x : (ZMod n)ˣ, x = -1   ↔   IsCyclic (ZMod n)ˣ.

This scaffold ships the **structural case-split** following S5b PREP's
corrected proof skeleton (3 bugs in S5 PREP's design memo: `interval_cases`
without upper bound, `all_goals` after `decide`, `absurd h_cyc h_cyc` type
mismatch). The two implication-direction sub-lemmas
`prod_eq_neg_one_of_isCyclic_aux` and `prod_eq_one_of_not_isCyclic_aux`
remain strategic sorries — their discharge is the natural S7/S8 work.

## Phase chain

| Phase | File | Status |
|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | merged, build-verified (S2 PR #18147) |
| B (partial) | `GaussWilsonNonCyclicOQ01B.lean` | merged, build-pending (S3 PR #18232), 1 strategic sorry |
| C (scaffold, THIS FILE) | `GaussWilsonNonCyclicOQ01.lean` | proposed; 2 strategic sorries deferred to S7/S8 |

## Mathlib citations consumed (verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `IsCyclic.card_pow_eq_one_le` (`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317`)
- `ZMod.prod_univ_units_id_eq_neg_one`-style: see `Mathlib/NumberTheory/Wilson.lean`
- `Finset.prod_filter`, `Finset.prod_mul_distrib` (umbrella `Mathlib.Tactic` pull-ins)

## Why scaffold and not full Phase C?

Per S5b PREP §3.3, the cyclic direction admits a 1-line shortcut via
`prod_univ_units_id_eq_neg_one` only when `n` is **prime** (so `ZMod n` is
a field). For composite cyclic `n ∈ {4, p^k≥2, 2p^k}`, the manual
"`G[2] = {1, -1}`" argument via `IsCyclic.card_pow_eq_one_le` is required.
That argument is ~30-40 LOC and orthogonal to the case-split scaffold
here. The non-cyclic direction additionally consumes the Phase B
strategic sorry chain (S4 in flight) so its discharge depends on S4 ACT.

Strategic-sorry isolation gives the next researcher a clearly-stated
pair of sub-lemmas to close, while shipping the *outer* iff structure
build-pending. Companion to S3 ACT's strategic-sorry isolation in Phase B.

## Spec

- `problem.md` § "Approach map" sub-problem C: this file's main theorem.
- S5b PREP `2026-05-13-s5b-prep-design-bugs-and-mathlib-audit.md` (PR #18607)
  — corrected proof skeleton + Mathlib API erratum.
-/

namespace GaussWilsonNonCyclicOQ01

open Finset GaussWilsonNonCyclicOQ01

/-- Re-derivation of `GaussWilsonNonCyclic.neg_one_ne_one_units'`, which is
    `private` in the parent file. For `n ≥ 3`, `(-1 : (ZMod n)ˣ) ≠ 1`. -/
private lemma neg_one_ne_one_units_of_ge_three {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  have hv := congr_arg (Units.val : (ZMod n)ˣ → ZMod n) h
  simp only [Units.val_neg, Units.val_one] at hv
  apply (show (-1 : ZMod n) ≠ 1 by
    intro heq
    have h11 : (1 : ZMod n) + 1 = 0 := by
      have := neg_add_cancel (1 : ZMod n); rwa [heq] at this
    have h2eq : (2 : ZMod n) = 1 + 1 := by norm_num
    have hchar : (2 : ZMod n) = 0 := by rw [h2eq]; exact h11
    have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast hchar)
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega))
  exact hv

/-- **Cyclic direction.** For `n ≥ 3` with `(ZMod n)ˣ` cyclic, the
    product of units equals `-1`.

    Mathematical content: in a finite cyclic group `G`, the 2-torsion
    subset `{x : G | x^2 = 1}` has cardinality `≤ 2` (Mathlib's
    `IsCyclic.card_pow_eq_one_le` at `n := 2`). For `(ZMod n)ˣ` with
    `n ≥ 3`, both `1` and `-1` lie in the 2-torsion subset and are
    distinct (`neg_one_ne_one_units_of_ge_three`), forcing exactly
    `{1, -1}`. Then Phase A reduces `∏ univ` to `∏ {1, -1} = 1 · (-1) = -1`.

    Discharged in S7 ACT (this file) following S7 PREP § 3.2 recipe
    (PR #18700). The uniform `IsCyclic.card_pow_eq_one_le` route works
    for prime, prime-power, and `2 * p^k` cyclic moduli — no prime
    case-split needed. -/
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hcyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  haveI : IsCyclic (ZMod n)ˣ := hcyc
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  set S : Finset (ZMod n)ˣ := univ.filter (fun x => x ^ 2 = 1) with hS_def
  have h_card_le : S.card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num : (0 : ℕ) < 2)
  have h_neq : (1 : (ZMod n)ˣ) ≠ -1 :=
    fun h => neg_one_ne_one_units_of_ge_three hn h.symm
  have h_one_mem : (1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter]
  have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter]
  have h_pair_sub : ({1, -1} : Finset (ZMod n)ˣ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h_one_mem
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact h_neg_mem
  have h_pair_card : ({1, -1} : Finset (ZMod n)ˣ).card = 2 :=
    Finset.card_pair h_neq
  have h_S_eq : S = ({1, -1} : Finset (ZMod n)ˣ) :=
    (Finset.eq_of_subset_of_card_le h_pair_sub
      (h_pair_card.symm ▸ h_card_le)).symm
  rw [h_S_eq, Finset.prod_pair h_neq, one_mul]

/-- **(STRATEGIC SORRY — non-cyclic direction)** For `n ≥ 3` with
    `(ZMod n)ˣ` non-cyclic, the product of units equals `1`.

    Mathematical content: by the parent file's
    `card_sq_eq_one_ge_three`, the 2-torsion subset of `(ZMod n)ˣ` has
    cardinality `≥ 3`. Since the 2-torsion is a subgroup and elementary
    2-abelian, its cardinality is a power of 2, so `≥ 4`. Phase A
    reduces `∏ univ` to `∏ (2-torsion)`. Phase B
    (`prod_univ_eq_one_of_elementary_card_ge_four`) gives `∏ (2-torsion) = 1`.

    This direction consumes Phase B's strategic sorry chain transitively
    (`prod_univ_eq_pow_card_div_two_of_elementary`, S4 in flight).
    Deferred to S8 ACT (after S4 ACT closes the Phase B chain).

    Subtleties for S8 implementer:
    - The 2-torsion subset is `univ.filter (fun x => x ^ 2 = 1) : Finset (ZMod n)ˣ`.
    - To apply Phase B, lift the filter to a subgroup `H ≤ (ZMod n)ˣ` and
      invoke `Phase B.prod_univ_eq_one_of_elementary_card_ge_four` on
      `H`. This requires either constructing the subgroup explicitly
      or working in the subtype.
    - Phase A is stated for `∏ x : G, x` where `G` is a finite commutative
      group; the bridge is `Finset.prod_subtype_eq_prod_filter` or
      `Finset.prod_attach`. -/
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  -- Step 1: Phase A reduction.
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  -- Step 2: Build the 2-torsion subgroup T.
  let T : Subgroup (ZMod n)ˣ :=
    { carrier := {x | x ^ 2 = 1}
      one_mem' := by show (1 : (ZMod n)ˣ) ^ 2 = 1; exact one_pow _
      mul_mem' := fun {a b} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) => by
        show (a * b) ^ 2 = 1
        rw [mul_pow, ha, hb, mul_one]
      inv_mem' := fun {a} (ha : a ^ 2 = 1) => by
        show (a⁻¹) ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  -- Step 3: T is a 2-group, so Nat.card T = 2^k for some k.
  have hT_pgroup : IsPGroup 2 T := fun ⟨g, hg⟩ =>
    ⟨1, Subtype.ext (by show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ);
                        rw [pow_one]; exact hg)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : DecidablePred (· ∈ T) := Classical.decPred _
  haveI : Fintype T := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup
  -- Step 4: T.card = #filter ≥ 3 → 2^k ≥ 3 → k ≥ 2 → T.card ≥ 4.
  have h_card_filter :
      Fintype.card T = (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
    have e : T ≃ { x : (ZMod n)ˣ // x ^ 2 = 1 } :=
      { toFun := fun y => ⟨y.1, y.2⟩
        invFun := fun y => ⟨y.1, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    exact Fintype.card_subtype _
  have h_T_ge_3 : 3 ≤ Fintype.card T := by
    rw [h_card_filter]
    exact GaussWilsonNonCyclic.card_sq_eq_one_ge_three hn hncyc
  have h_T_pow : Fintype.card T = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact hk
  have h_T_ge_4 : 4 ≤ Fintype.card T := by
    rw [h_T_pow] at h_T_ge_3 ⊢
    rcases k with _ | _ | k'
    · norm_num at h_T_ge_3
    · norm_num at h_T_ge_3
    · calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k' + 2) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  -- Step 5: Apply Phase B to T.
  have hT_exp : ∀ x : T, x ^ 2 = 1 := fun ⟨g, hg⟩ => Subtype.ext (by
    show g ^ 2 = 1; exact hg)
  have hT_prod : (∏ x : T, x) = 1 :=
    prod_univ_eq_one_of_elementary_card_ge_four hT_exp h_T_ge_4
  -- Step 6: Bridge to ambient Finset.
  have h_bridge :
      ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1), x
        = ((∏ x : T, x : T) : (ZMod n)ˣ) := by
    rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]
    apply Finset.prod_subtype
    intro x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩
      exact hsq
    · intro hT
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
  rw [h_bridge, hT_prod, OneMemClass.coe_one]

/-- **The main Gauss–Wilson product formula for `(ZMod n)ˣ`.**

    For `n ≥ 1`,

      `∏ x : (ZMod n)ˣ, x = -1 ↔ IsCyclic (ZMod n)ˣ`.

    Proof structure (corrected from S5 PREP per S5b PREP §2):

    1. **Small cases `n ∈ {1, 2}`**: dispatched by `decide`.
       Both are trivially cyclic, and the product `(ZMod n)ˣ`-side
       evaluates by computation. `interval_cases` here is sound because
       both bounds `1 ≤ n < 3` are present (bug 1 fix).

    2. **`n ≥ 3`**: case-split on `IsCyclic (ZMod n)ˣ` via `by_cases`.
       - **`IsCyclic`** branch: apply `prod_eq_neg_one_of_isCyclic_aux`.
       - **`¬IsCyclic`** branch: forward direction `prod = -1 ⟹ IsCyclic`
         is contrapositively-vacuous via
         `prod_eq_one_of_not_isCyclic_aux` (giving `prod = 1 ≠ -1`).
         Backward direction `IsCyclic ⟹ prod = -1` is impossible by
         hypothesis (bug 3 fix: rename `h_cyc` inside the `refine`-binder
         to avoid shadowing).

    The original S5 PREP design memo (PR #18465 ≈ #18502) contained
    4 bugs in the proof skeleton flagged by S5b PREP (PR #18607); this
    file ships the corrected version. -/
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic
    {n : ℕ} [NeZero n] :
    (∏ x : (ZMod n)ˣ, x) = -1 ↔ IsCyclic (ZMod n)ˣ := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  -- Dispatch small cases `n ∈ {1, 2}` separately, then handle `n ≥ 3` generically.
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- n ∈ {1, 2}
    interval_cases n
    · -- n = 1: (ZMod 1)ˣ is trivial (subsingleton); both sides hold.
      refine ⟨fun _ => isCyclic_of_subsingleton, fun _ => ?_⟩
      exact Subsingleton.elim _ _
    · -- n = 2: (ZMod 2)ˣ has one element (1 = -1); both sides hold.
      refine ⟨fun _ => isCyclic_of_subsingleton, fun _ => ?_⟩
      exact Subsingleton.elim _ _
  · -- n ≥ 3
    by_cases h_cyc : IsCyclic (ZMod n)ˣ
    · -- Cyclic case: both sides hold (via prod_eq_neg_one_of_isCyclic_aux).
      refine ⟨fun _ => h_cyc, fun _ => ?_⟩
      exact prod_eq_neg_one_of_isCyclic_aux hge h_cyc
    · -- Non-cyclic case: both sides fail.
      refine ⟨fun h_prod => ?_, fun h_cyc' => absurd h_cyc' h_cyc⟩
      -- LHS = -1, but non-cyclicity forces LHS = 1 via Phase A + Phase B.
      have hp1 : (∏ x : (ZMod n)ˣ, x) = 1 :=
        prod_eq_one_of_not_isCyclic_aux hge h_cyc
      have : (1 : (ZMod n)ˣ) = -1 := hp1.symm.trans h_prod
      exact absurd this.symm (neg_one_ne_one_units_of_ge_three hge)

end GaussWilsonNonCyclicOQ01
