/-
Proof: Concrete trivial lower bound for Erdős #1179 oq-02.
Date: 2026-06-15 (S2)
Research: erdos-1179-oq-02 (researcher-8)

Erdős #1179 (PROVED, Erdős–Hall 1976) establishes that the minimal number
of random group elements needed for an ε-uniform subset-sum representation
function is `g_ε(N) = (1 + o_ε(1)) · log₂ N`.  oq-02 asks whether the
`(1 + o(1))` multiplicative factor can be sharpened to a bounded additive
error `g_ε(N) ≤ log₂ N + O_ε(1)`, matching the trivial lower bound
`g_ε(N) ≥ log₂ N`.

This file formalises the **trivial lower bound** at the level of an individual
subset `A`, axiom-free.  The parent file `Proofs/Erdos1179Problem.lean` only
states the lower bound abstractly as `axiom basic_lower_bound` (about the
opaque, group-and-probability-quantified `gEps`).  Here we prove the concrete,
per-subset statement that underlies it:

    if `A` is ε-uniform with `ε < 1`, then `N ≤ 2 ^ |A|`,

hence `⌈log₂ N⌉ ≤ |A|`.  Every ε-uniform subset must already have at least
`log₂ N` elements — the matching target of oq-02's conjectured upper bound.

Mathematical content.  ε-uniformity with `ε < 1` forces every representation
count to be strictly positive: `F_A(g) ≥ (1 - ε)·μ > 0` where `μ = 2^|A|/N > 0`.
Since `F_A(g)` is a natural number this gives `F_A(g) ≥ 1` for all `g`, so

    2 ^ |A| = ∑_g F_A(g) ≥ ∑_g 1 = N            (parent `total_reprCount`).

Relation to the parent.  The parent's `uniform_implies_spanning` proves the
same spanning conclusion (`∀ g, F_A(g) ≥ 1`) but only under the *extra*
hypothesis `|A| ≥ ⌈log₂ N⌉` — i.e. it assumes the lower bound it would help
establish.  `epsUniform_spanning` below removes that circular hypothesis: only
`ε < 1` is needed, because `μ > 0` already follows from `N ≥ 1` without any
lower bound on `|A|`.  The lower bound is then a genuine *consequence*, not an
assumption.

No axioms; depends only on `Erdos1179.total_reprCount` and
`Erdos1179.expectedReprCount_pos` from `Proofs/Erdos1179Problem.lean`.
-/

import Proofs.Erdos1179Problem
import Mathlib

namespace Erdos1179

open Finset Real

/-- **Spanning from ε-uniformity, hypothesis-free.**  If `A` is ε-uniform with
`ε < 1`, then every group element has at least one subset-sum representation.

Unlike the parent `uniform_implies_spanning`, this requires no lower bound on
`A.card`: positivity of the expected count `μ = 2^|A| / N` (which holds for any
`N ≥ 1`) together with `ε < 1` already forces `F_A(g) ≥ (1 - ε)·μ > 0`. -/
theorem epsUniform_spanning {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) (g : G) :
    1 ≤ reprCount A g := by
  haveI : Nonempty G := ⟨0⟩
  have hN1 : 1 ≤ Fintype.card G := Fintype.card_pos
  have hμpos : 0 < expectedReprCount A.card (Fintype.card G) :=
    expectedReprCount_pos hN1
  -- From |F(g) - μ| ≤ ε·μ, the lower side gives F(g) ≥ (1 - ε)·μ.
  have hge : (1 - ε) * expectedReprCount A.card (Fintype.card G)
      ≤ (reprCount A g : ℝ) := by
    have h := (abs_le.mp (hunif g)).1
    nlinarith
  -- (1 - ε)·μ > 0, so F(g) > 0, so the natural number F(g) is ≥ 1.
  have hpos : (0 : ℝ) < (reprCount A g : ℝ) := by
    have hprod : (0 : ℝ) < (1 - ε) * expectedReprCount A.card (Fintype.card G) :=
      mul_pos (by linarith) hμpos
    linarith
  have hne : reprCount A g ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  omega

/-- **Concrete trivial lower bound (exact form).**  Any ε-uniform subset `A`
(with `ε < 1`) of an abelian group of order `N` satisfies `N ≤ 2 ^ |A|`.

Proof: each of the `N` group elements has at least one representation
(`epsUniform_spanning`), and the representation counts sum to `2 ^ |A|`
(`total_reprCount`). -/
theorem card_le_two_pow_of_epsUniform {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) :
    Fintype.card G ≤ 2 ^ A.card :=
  calc Fintype.card G = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ = ∑ _g : G, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ g : G, reprCount A g :=
        Finset.sum_le_sum (fun g _ => epsUniform_spanning A ε hε1 hunif g)
    _ = 2 ^ A.card := total_reprCount A

/-- **Concrete trivial lower bound (logarithmic form).**  Any ε-uniform subset
`A` (with `ε < 1`) has at least `⌈log₂ N⌉` elements, where `N` is the group
order.  This is the integer form of the headline bound `g_ε(N) ≥ log₂ N`:
`Nat.clog 2 N = ⌈log₂ N⌉`. -/
theorem clog_le_card_of_epsUniform {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (ε : ℝ) (hε1 : ε < 1)
    (hunif : IsEpsUniform A ε) :
    Nat.clog 2 (Fintype.card G) ≤ A.card :=
  (Nat.le_pow_iff_clog_le (by norm_num)).mp
    (card_le_two_pow_of_epsUniform A ε hε1 hunif)

end Erdos1179
