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
# Gauss–Wilson Non-Cyclic OQ-01 — Phase C: Main iff Theorem

This file delivers the main theorem `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`
for `gauss-wilson-non-cyclic-oq-01`, building on Phase A and Phase B.

**Main theorem.** For `n ≥ 1`,

  ∏ x : (ZMod n)ˣ, x = -1   ↔   IsCyclic (ZMod n)ˣ.

Both implication-direction auxiliary lemmas
(`prod_eq_neg_one_of_isCyclic_aux` for the cyclic direction and
`prod_eq_one_of_not_isCyclic_aux` for the non-cyclic direction) are
discharged in this file. Sorry-free, axiom-free, build-verified at
Mathlib v4.26.0.

## Phase chain

| Phase | File | Status |
|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | build-verified (S2 PR #18147) |
| B | `GaussWilsonNonCyclicOQ01B.lean` | build-verified (S3 PR #18232 + S8 ACT PR #18957) |
| C (THIS FILE) | `GaussWilsonNonCyclicOQ01.lean` | build-verified (S6 PR #18652 scaffold + S7 ACT PR #18743 cyclic direction + S9 ACT PR #19075 `[NeZero n]` + S12 ACT PR #19440 non-cyclic direction + S14 ACT PR #21156 L112 Hermit fix) |

## Mathlib citations consumed (verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `IsCyclic.card_pow_eq_one_le` (`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317`)
- `IsPGroup.iff_card` (`Mathlib/GroupTheory/PGroup.lean:46`)
- `SubmonoidClass.coe_finset_prod`, `Finset.prod_subtype`
- `Finset.prod_filter`, `Finset.prod_pair`, `Finset.card_pair`
  (umbrella `Mathlib.Tactic` pull-ins)

## Proof architecture

- **Cyclic direction** (`prod_eq_neg_one_of_isCyclic_aux`): apply Phase A
  to reduce `∏ univ` to `∏ 2-torsion`, then use
  `IsCyclic.card_pow_eq_one_le` to bound the 2-torsion at ≤ 2 elements;
  combined with `{1, -1} ⊆ 2-torsion` (`-1 ≠ 1` for `n ≥ 3`), pin the
  2-torsion to exactly `{1, -1}` and compute the product.
- **Non-cyclic direction** (`prod_eq_one_of_not_isCyclic_aux`): apply
  Phase A, lift the 2-torsion to a subgroup `T`, show `IsPGroup 2 T`,
  use `IsPGroup.iff_card` to get `|T| = 2^k`, combine with the parent
  file's `card_sq_eq_one_ge_three` to get `|T| ≥ 4`, then apply Phase B
  `prod_univ_eq_one_of_elementary_card_ge_four`.

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

/-- **Non-cyclic direction.** For `n ≥ 3` with `(ZMod n)ˣ` non-cyclic,
    the product of units equals `1`.

    Mathematical content: by the parent file's
    `card_sq_eq_one_ge_three`, the 2-torsion subset of `(ZMod n)ˣ` has
    cardinality `≥ 3`. Since the 2-torsion is a subgroup and elementary
    2-abelian, its cardinality is a power of 2, so `≥ 4`. Phase A
    reduces `∏ univ` to `∏ (2-torsion)`. Phase B
    (`prod_univ_eq_one_of_elementary_card_ge_four`) gives `∏ (2-torsion) = 1`.

    Discharged in S12 ACT (PR #19440) by lifting the 2-torsion filter to
    an explicit subgroup `T : Subgroup (ZMod n)ˣ`, proving `IsPGroup 2 T`,
    extracting `Nat.card T = 2^k` via `IsPGroup.iff_card`, and bridging to
    the ambient `Finset` product via `SubmonoidClass.coe_finset_prod` +
    `Finset.prod_subtype`. -/
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
