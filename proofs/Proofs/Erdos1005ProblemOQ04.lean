import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Chain

/-
# Erdős Problem #1005 (OQ-04): Consecutive vs. Pairwise Similar Ordering

## Parent

Erdős #1005 studies the longest run `f(n)` of **consecutive similarly ordered**
Farey fractions of order `n`. Two fractions `a/b`, `c/d` are *similarly ordered*
when `(a - c)(b - d) ≥ 0` (numerator and denominator move the same way). In the
parent formalization (`Erdos1005ProblemProvable.lean`) a run of `k` consecutive
fractions counts only when **every pair** in the run is similarly ordered
(`isSimOrdered`): the relation is symmetric and reflexive but, crucially, **not
transitive**, so the pairwise condition is genuinely stronger than checking only
adjacent pairs.

This raises the open question (OQ-04):

> Does the answer change if one considers *consecutive* similarly ordered runs
> (adjacent pairs only) rather than *pairwise* similarly ordered runs? The
> non-transitivity gap could make these differ significantly.

## This file

We separate the two notions cleanly, using Mathlib's two standard list
predicates as the exact formal counterparts:

* `List.Chain' R l`    — the **consecutive** (adjacent-pairs-only) condition;
* `List.Pairwise R l`  — the **pairwise** (all-pairs) condition.

Results, all fully machine-checked (0 sorries, 0 axioms, no `native_decide`):

* `simOrdered_refl`, `simOrdered_symm` — the relation is reflexive and symmetric.
* `simOrdered_not_transitive` — it is **not** transitive: an explicit triple of
  order-4 Farey fractions `1/4, 1/2, 2/3` witnesses the failure.
* `pairwise_imp_consecutive` — pairwise ⟹ consecutive (the trivial direction).
* `farey4_block_chain'` — the genuine length-5 consecutive block of `F₄`,
  `1/4, 1/3, 1/2, 2/3, 3/4`, **is** consecutively similarly ordered.
* `farey4_block_not_pairwise` — yet that same block is **not** pairwise similarly
  ordered (`1/4` and `2/3` clash).
* `consecutive_strictly_weaker` — combining the two: there is a list that is
  consecutively but not pairwise similarly ordered, so the consecutive notion is
  strictly weaker. Hence the consecutive run length dominates the pairwise one,
  `f_consec(n) ≥ f(n)`, and can strictly exceed it locally.
* `farey4_block_consecutive_in_F4` — certification that the five witnesses really
  are *consecutive* in `F₄` (each adjacent pair is unimodular with denominator
  sum `> 4`, so no order-4 fraction lies between them). This makes the separation
  a statement about a real run of the Farey sequence, not cherry-picked
  non-adjacent fractions.

**Scope.** This resolves the *qualitative* form of OQ-04: the two run notions are
provably distinct, with `f_consec ≥ f`. Whether the two **asymptotic constants**
differ (i.e. whether `f_consec(n)/n` and `f(n)/n` have different limits) remains
open, as does the parent constant itself.

Reference: https://erdosproblems.com/1005
-/

namespace Erdos1005OQ04

-- ══════════════════════════════════════════════════════════════════
-- § 1: Farey fractions (mirrors the parent scaffold)
-- ══════════════════════════════════════════════════════════════════

/-- A Farey fraction of order `n`: a pair `(p, q)` with `0 ≤ p ≤ q`,
    `1 ≤ q ≤ n`, and `gcd(p, q) = 1`. -/
structure FareyFraction (n : ℕ) where
  p : ℕ
  q : ℕ
  hq_pos : 1 ≤ q
  hq_le : q ≤ n
  hp_le : p ≤ q
  hcoprime : Nat.Coprime p q

/-- The rational value of a Farey fraction. -/
def FareyFraction.toRat {n : ℕ} (f : FareyFraction n) : ℚ :=
  f.p / f.q

/-- Two unimodular neighbours satisfy `bc - ad = 1`. -/
def IsConsecutiveFarey {n : ℕ} (f g : FareyFraction n) : Prop :=
  g.p * f.q - f.p * g.q = 1

-- ══════════════════════════════════════════════════════════════════
-- § 2: The "similarly ordered" relation
-- ══════════════════════════════════════════════════════════════════

/-- Two Farey fractions `a/b`, `c/d` are **similarly ordered** when
    `(a - c)(b - d) ≥ 0`: numerator and denominator change in the same
    direction. This is the relation studied in Erdős #1005, written here in
    its native product form over `ℤ`. -/
def SimOrdered {n : ℕ} (f g : FareyFraction n) : Prop :=
  (0 : ℤ) ≤ ((f.p : ℤ) - g.p) * ((f.q : ℤ) - g.q)

instance {n : ℕ} : DecidableRel (SimOrdered (n := n)) :=
  fun f g => by unfold SimOrdered; infer_instance

/-- `SimOrdered` is reflexive: `(a-a)(b-b) = 0 ≥ 0`. -/
lemma simOrdered_refl {n : ℕ} (f : FareyFraction n) : SimOrdered f f := by
  unfold SimOrdered; simp

/-- `SimOrdered` is symmetric: `(a-c)(b-d) = (c-a)(d-b)`. -/
lemma simOrdered_symm {n : ℕ} (f g : FareyFraction n) :
    SimOrdered f g ↔ SimOrdered g f := by
  unfold SimOrdered
  constructor <;> intro h <;> nlinarith [h]

-- ══════════════════════════════════════════════════════════════════
-- § 3: Non-transitivity — the source of the gap
-- ══════════════════════════════════════════════════════════════════

/-- `1/4` as an order-4 Farey fraction. -/
def f14 : FareyFraction 4 := ⟨1, 4, by decide, by decide, by decide, by decide⟩
/-- `1/3` as an order-4 Farey fraction. -/
def f13 : FareyFraction 4 := ⟨1, 3, by decide, by decide, by decide, by decide⟩
/-- `1/2` as an order-4 Farey fraction. -/
def f12 : FareyFraction 4 := ⟨1, 2, by decide, by decide, by decide, by decide⟩
/-- `2/3` as an order-4 Farey fraction. -/
def f23 : FareyFraction 4 := ⟨2, 3, by decide, by decide, by decide, by decide⟩
/-- `3/4` as an order-4 Farey fraction. -/
def f34 : FareyFraction 4 := ⟨3, 4, by decide, by decide, by decide, by decide⟩

/-- `SimOrdered` is **not transitive**. Witness: `1/4 ~ 1/2` (numerators tie),
    `1/2 ~ 2/3` (both increase), but `1/4 ̸~ 2/3` — going from `1/4` to `2/3` the
    numerator rises while the denominator falls, `(1-2)(4-3) = -1 < 0`. This is
    exactly the obstruction that forces the pairwise condition in the parent and
    that OQ-04 asks about. -/
theorem simOrdered_not_transitive :
    ¬ ∀ f g h : FareyFraction 4, SimOrdered f g → SimOrdered g h → SimOrdered f h := by
  intro H
  have hbad : SimOrdered f14 f23 :=
    H f14 f12 f23 (by decide) (by decide)
  revert hbad; decide

-- ══════════════════════════════════════════════════════════════════
-- § 4: Consecutive vs. pairwise as list predicates
-- ══════════════════════════════════════════════════════════════════

/-- A list of fractions is **consecutively** similarly ordered when every
    *adjacent* pair is similarly ordered (`List.IsChain`). This is the run notion
    OQ-04 proposes: it inspects only neighbours `(xᵢ, xᵢ₊₁)`. -/
def ConsecutivelySimOrdered {n : ℕ} (l : List (FareyFraction n)) : Prop :=
  l.IsChain SimOrdered

/-- A list of fractions is **pairwise** similarly ordered when *every* pair is
    similarly ordered (`List.Pairwise`). This is the parent's run notion
    (`isSimOrdered`): it inspects all pairs `(xᵢ, xⱼ)`, `i < j`. -/
def PairwiseSimOrdered {n : ℕ} (l : List (FareyFraction n)) : Prop :=
  l.Pairwise SimOrdered

/-- **Trivial direction.** Every pairwise similarly ordered run is, in
    particular, consecutively similarly ordered. So `f(n) ≤ f_consec(n)`. -/
theorem pairwise_imp_consecutive {n : ℕ} (l : List (FareyFraction n)) :
    PairwiseSimOrdered l → ConsecutivelySimOrdered l :=
  List.Pairwise.isChain

-- ══════════════════════════════════════════════════════════════════
-- § 5: The separating witness — a real length-5 block of F₄
-- ══════════════════════════════════════════════════════════════════

/-- The consecutive block `1/4, 1/3, 1/2, 2/3, 3/4` of the Farey sequence `F₄`
    (in increasing order). -/
def farey4Block : List (FareyFraction 4) := [f14, f13, f12, f23, f34]

/-- Every **adjacent** pair of `farey4Block` is similarly ordered: the block is
    consecutively similarly ordered. (Along the block the numerators go
    `1,1,1,2,3` and denominators `4,3,2,3,4`; each step moves both coordinates the
    same way or holds one fixed.) -/
theorem farey4_block_chain' : ConsecutivelySimOrdered farey4Block := by
  unfold ConsecutivelySimOrdered farey4Block
  rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons,
      List.isChain_cons_cons]
  exact ⟨by decide, by decide, by decide, by decide, List.isChain_singleton _⟩

/-- The same block is **not** pairwise similarly ordered: the non-adjacent pair
    `1/4` (head) and `2/3` clashes, `(1-2)(4-3) = -1 < 0`. -/
theorem farey4_block_not_pairwise : ¬ PairwiseSimOrdered farey4Block := by
  unfold PairwiseSimOrdered farey4Block
  rw [List.pairwise_cons]
  rintro ⟨hhead, -⟩
  have hbad : SimOrdered f14 f23 := hhead f23 (by simp)
  revert hbad; decide

/-- **Main separation.** There is a list of Farey fractions that is
    consecutively but *not* pairwise similarly ordered. Together with
    `pairwise_imp_consecutive`, the consecutive notion is therefore **strictly
    weaker** than the pairwise notion: the implication of §4 has no converse.

    Consequence for the run-length functions: the longest consecutive run
    dominates the longest pairwise run, `f_consec(n) ≥ f(n)`, and the inequality
    is strict at the level of individual runs — the length-5 block above is a
    single consecutive run that no pairwise run can contain. -/
theorem consecutive_strictly_weaker :
    (∃ l : List (FareyFraction 4),
        ConsecutivelySimOrdered l ∧ ¬ PairwiseSimOrdered l) ∧
    (∀ l : List (FareyFraction 4), PairwiseSimOrdered l → ConsecutivelySimOrdered l) :=
  ⟨⟨farey4Block, farey4_block_chain', farey4_block_not_pairwise⟩,
   pairwise_imp_consecutive⟩

-- ══════════════════════════════════════════════════════════════════
-- § 6: The witnesses really are consecutive in F₄
-- ══════════════════════════════════════════════════════════════════
--
-- To make §5 a statement about a genuine run of the Farey sequence (and not
-- merely about an arbitrary list), we certify that `1/4, 1/3, 1/2, 2/3, 3/4`
-- are pairwise *adjacent* in `F₄`: each consecutive pair is unimodular and its
-- denominators sum past `4`, so no order-4 fraction lies strictly between them.
-- The adjacency engine below mirrors the sibling file `Erdos1005ProblemOQ03`.

/-- Strict order of two Farey fractions is cross-multiplication. -/
theorem toRat_lt_iff {n : ℕ} (f g : FareyFraction n) :
    f.toRat < g.toRat ↔ f.p * g.q < g.p * f.q := by
  unfold FareyFraction.toRat
  have hf : (0 : ℚ) < f.q := Nat.cast_pos.mpr f.hq_pos
  have hg : (0 : ℚ) < g.q := Nat.cast_pos.mpr g.hq_pos
  rw [div_lt_div_iff₀ hf hg]
  constructor <;> intro h <;> exact_mod_cast h

/-- **Key lemma** (denominator-sum bound). If `a/b < p/q < c/d` and the outer
    pair is unimodular (`bc - ad = 1`), then `q ≥ b + d`. -/
theorem intermediate_denom_ge {n : ℕ} (f g h : FareyFraction n)
    (huni : IsConsecutiveFarey f g)
    (h1 : f.toRat < h.toRat) (h2 : h.toRat < g.toRat) :
    f.q + g.q ≤ h.q := by
  have hcb : g.p * f.q = f.p * g.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  have hfh : f.p * h.q < h.p * f.q := (toRat_lt_iff f h).mp h1
  have hhg : h.p * g.q < g.p * h.q := (toRat_lt_iff h g).mp h2
  have hcbZ : (g.p : ℤ) * f.q = (f.p : ℤ) * g.q + 1 := by exact_mod_cast hcb
  have h1Z : (f.p : ℤ) * h.q + 1 ≤ (h.p : ℤ) * f.q := by exact_mod_cast hfh
  have h2Z : (h.p : ℤ) * g.q + 1 ≤ (g.p : ℤ) * h.q := by exact_mod_cast hhg
  have key : (h.q : ℤ)
      = (g.q : ℤ) * ((h.p : ℤ) * f.q - (f.p : ℤ) * h.q)
        + (f.q : ℤ) * ((g.p : ℤ) * h.q - (h.p : ℤ) * g.q) := by
    linear_combination (-(h.q : ℤ)) * hcbZ
  have t1 : (1 : ℤ) ≤ (h.p : ℤ) * f.q - (f.p : ℤ) * h.q := by linarith
  have t2 : (1 : ℤ) ≤ (g.p : ℤ) * h.q - (h.p : ℤ) * g.q := by linarith
  have bound : (f.q : ℤ) + g.q ≤ h.q := by
    nlinarith [mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℤ) ≤ (g.q : ℤ)),
               mul_le_mul_of_nonneg_left t2 (by linarith : (0:ℤ) ≤ (f.q : ℤ)), key]
  exact_mod_cast bound

/-- **Adjacency (sufficiency).** A unimodular pair with `b + d > n` is adjacent
    in `F_n`: no Farey fraction of order `n` lies strictly between them. -/
theorem farey_adjacent_of_denom_sum_gt {n : ℕ} (f g : FareyFraction n)
    (huni : IsConsecutiveFarey f g) (hsum : n < f.q + g.q) :
    ∀ h : FareyFraction n, ¬ (f.toRat < h.toRat ∧ h.toRat < g.toRat) := by
  rintro h ⟨h1, h2⟩
  have hge : f.q + g.q ≤ h.q := intermediate_denom_ge f g h huni h1 h2
  exact absurd (le_trans hge h.hq_le) (by omega)

/-- Each consecutive pair of `farey4Block` is unimodular (`bc - ad = 1`). -/
theorem farey4_block_unimodular :
    IsConsecutiveFarey f14 f13 ∧ IsConsecutiveFarey f13 f12 ∧
    IsConsecutiveFarey f12 f23 ∧ IsConsecutiveFarey f23 f34 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold IsConsecutiveFarey; decide)

/-- Each consecutive pair of `farey4Block` is strictly increasing in value. -/
theorem farey4_block_increasing :
    f14.toRat < f13.toRat ∧ f13.toRat < f12.toRat ∧
    f12.toRat < f23.toRat ∧ f23.toRat < f34.toRat := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [toRat_lt_iff]; decide

/-- **Certification.** The five fractions `1/4, 1/3, 1/2, 2/3, 3/4` are genuinely
    *consecutive* in `F₄`: every adjacent pair is strictly increasing and
    adjacent (no order-4 fraction lies strictly between). So `farey4Block` is a
    real contiguous block of the Farey sequence — the separation of §5 concerns
    an honest consecutive run, not an arbitrary list. -/
theorem farey4_block_consecutive_in_F4 :
    (∀ h : FareyFraction 4, ¬ (f14.toRat < h.toRat ∧ h.toRat < f13.toRat)) ∧
    (∀ h : FareyFraction 4, ¬ (f13.toRat < h.toRat ∧ h.toRat < f12.toRat)) ∧
    (∀ h : FareyFraction 4, ¬ (f12.toRat < h.toRat ∧ h.toRat < f23.toRat)) ∧
    (∀ h : FareyFraction 4, ¬ (f23.toRat < h.toRat ∧ h.toRat < f34.toRat)) := by
  obtain ⟨u1, u2, u3, u4⟩ := farey4_block_unimodular
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact farey_adjacent_of_denom_sum_gt f14 f13 u1 (by decide)
  · exact farey_adjacent_of_denom_sum_gt f13 f12 u2 (by decide)
  · exact farey_adjacent_of_denom_sum_gt f12 f23 u3 (by decide)
  · exact farey_adjacent_of_denom_sum_gt f23 f34 u4 (by decide)

end Erdos1005OQ04
