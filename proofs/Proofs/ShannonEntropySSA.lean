/-
  Strong Subadditivity of Shannon Entropy — statement and information-theoretic
  corollaries.

  The deepest classical entropy inequality,

      H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z),

  is proved (0 sorries, 0 axioms) in `Proofs/ShannonEntropy.lean` as
  `InformationTheory.strong_subadditivity`, via the conditional-mutual-information
  identity

      I(X ; Z | Y) = Σ p(x,y,z) · log[ p(x,y,z)·p_Y(y) / (p_XY(x,y)·p_YZ(y,z)) ] ≥ 0,

  each term of which is bounded below by a KL-divergence (Gibbs) inequality
  `p·log(p/q) ≥ p - q`, the block sum telescoping to `1 - 1 = 0`.

  This file records that theorem and derives its standard corollaries in the
  three-variable setting, which are *not* present in the parent file:

  * `conditioning_reduces_entropy_general` — conditioning on more variables cannot
    increase entropy: `H(X | Y, Z) ≤ H(X | Y)`;
  * `conditioning_reduces_entropy_general'` — the `X ↔ Z` dual of the same
    inequality: `H(Z | X, Y) ≤ H(Z | Y)`;
  * `conditional_mi_nonneg` — the conditional mutual information is non-negative:
    `I(X ; Z | Y) ≥ 0`.

  All three are immediate linear rearrangements of strong subadditivity.

  A previous revision of this file re-derived the entire marginal / chain-rule /
  strong-subadditivity infrastructure inline while also `import`ing the parent
  file, which declares the same names (`marginalXY`, `marginalYZ`,
  `strong_subadditivity`, …) in the same `InformationTheory` namespace. That made
  the file fail to elaborate ("already been declared") and was never CI-checked.
  This revision reuses the parent's verified development directly, so the file
  builds cleanly and stays axiom-free.

  STATUS: [VERIFIED] — machine-checked with `docker-build.sh Proofs.ShannonEntropySSA`.
  `#print axioms` on each theorem reports only the foundational trio
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `Lean.ofReduceBool`,
  or added axioms (inherited from the parent's axiom-free proof).
-/
import Mathlib
import Proofs.ShannonEntropy

open Finset

namespace InformationTheory.SSA

open InformationTheory

variable {α β γ : Type*}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Strong subadditivity of Shannon entropy.**

    `H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`.

    This is `InformationTheory.strong_subadditivity` (proved in
    `Proofs/ShannonEntropy.lean`), re-exported here as the headline theorem of the
    strong-subadditivity gallery entry. -/
theorem strong_subadditivity {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ + shannonEntropy (marginalY pXYZ) ≤
      shannonEntropy (marginalXY pXYZ) + shannonEntropy (marginalYZ pXYZ) :=
  InformationTheory.strong_subadditivity hp hsum

/-- **Conditioning reduces entropy (three-variable form).**

    `H(X | Y, Z) ≤ H(X | Y)`, where `H(X | Y, Z) = H(X, Y, Z) − H(Y, Z)` and
    `H(X | Y) = H(X, Y) − H(Y)`.  A direct rearrangement of strong subadditivity:
    the deficit is exactly the conditional mutual information `I(X ; Z | Y) ≥ 0`. -/
theorem conditioning_reduces_entropy_general {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ - shannonEntropy (marginalYZ pXYZ) ≤
      shannonEntropy (marginalXY pXYZ) - shannonEntropy (marginalY pXYZ) := by
  linarith [InformationTheory.strong_subadditivity hp hsum]

/-- **Conditioning reduces entropy (three-variable form, `X ↔ Z` dual).**

    `H(Z | X, Y) ≤ H(Z | Y)`, where `H(Z | X, Y) = H(X, Y, Z) − H(X, Y)` and
    `H(Z | Y) = H(Y, Z) − H(Y)`.  Strong subadditivity is symmetric under
    exchanging `X` and `Z` (it swaps `H(X, Y)` and `H(Y, Z)` while fixing
    `H(X, Y, Z)` and `H(Y)`), so the *same* inequality also bounds the entropy of
    `Z` conditioned on the extra variable `X`; the deficit is again
    `I(X ; Z | Y) ≥ 0`.  Together with `conditioning_reduces_entropy_general` this
    completes the symmetric conditioning pair. -/
theorem conditioning_reduces_entropy_general' {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ - shannonEntropy (marginalXY pXYZ) ≤
      shannonEntropy (marginalYZ pXYZ) - shannonEntropy (marginalY pXYZ) := by
  linarith [InformationTheory.strong_subadditivity hp hsum]

/-- **Conditional mutual information is non-negative.**

    `I(X ; Z | Y) = H(X, Y) + H(Y, Z) − H(X, Y, Z) − H(Y) ≥ 0`.  This is the
    information-theoretic content of strong subadditivity: knowing `Y`, the
    variables `X` and `Z` carry non-negative mutual information. -/
theorem conditional_mi_nonneg {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy (marginalXY pXYZ) + shannonEntropy (marginalYZ pXYZ) -
      shannonEntropy pXYZ - shannonEntropy (marginalY pXYZ) ≥ 0 := by
  linarith [InformationTheory.strong_subadditivity hp hsum]

/-! ## Conditional mutual information as a first-class quantity -/

/-- **Conditional mutual information** `I(X ; Z | Y)`, defined directly from the
    joint distribution as

      `I(X ; Z | Y) = H(X, Y) + H(Y, Z) − H(X, Y, Z) − H(Y)`.

    Packaging the expression bounded by `conditional_mi_nonneg` as a named object
    lets the two information-theoretic facts below — its non-negativity and its
    conditional-entropy-reduction identity — be stated about a single reusable
    quantity rather than an anonymous four-term difference. -/
noncomputable def conditionalMutualInfo (pXYZ : α × β × γ → ℝ) : ℝ :=
  shannonEntropy (marginalXY pXYZ) + shannonEntropy (marginalYZ pXYZ) -
    shannonEntropy pXYZ - shannonEntropy (marginalY pXYZ)

/-- **Conditional mutual information is non-negative**, `0 ≤ I(X ; Z | Y)`. This is
    strong subadditivity read as a statement about the named quantity
    `conditionalMutualInfo`; it is definitionally `conditional_mi_nonneg`. -/
theorem conditionalMutualInfo_nonneg {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    0 ≤ conditionalMutualInfo pXYZ := by
  unfold conditionalMutualInfo
  linarith [conditional_mi_nonneg hp hsum]

/-- **Conditional mutual information equals the conditioning deficit.** With the
    conditional entropies `H(X | Y) = H(X, Y) − H(Y)` and
    `H(X | Y, Z) = H(X, Y, Z) − H(Y, Z)`,

      `I(X ; Z | Y) = H(X | Y) − H(X | Y, Z)`.

    This formalizes the identity asserted in prose in the docstrings of
    `conditioning_reduces_entropy_general` and `conditional_mi_nonneg` — that the
    deficit by which the extra variable `Z` reduces the conditional entropy of `X`
    is *exactly* the conditional mutual information. It is a pure rearrangement of
    the definition, so it holds unconditionally (no probability hypotheses). -/
theorem conditionalMutualInfo_eq_conditioning_deficit (pXYZ : α × β × γ → ℝ) :
    conditionalMutualInfo pXYZ =
      (shannonEntropy (marginalXY pXYZ) - shannonEntropy (marginalY pXYZ)) -
        (shannonEntropy pXYZ - shannonEntropy (marginalYZ pXYZ)) := by
  unfold conditionalMutualInfo
  ring

/-- **Conditional mutual information equals the conditioning deficit — `X ↔ Z`
    dual.** With the conditional entropies `H(Z | Y) = H(Y, Z) − H(Y)` and
    `H(Z | X, Y) = H(X, Y, Z) − H(X, Y)`,

      `I(X ; Z | Y) = H(Z | Y) − H(Z | X, Y)`.

    This is the `X ↔ Z` dual of `conditionalMutualInfo_eq_conditioning_deficit`,
    formalizing the identity asserted in prose in the docstring of
    `conditioning_reduces_entropy_general'` — that the deficit by which the extra
    variable `X` reduces the conditional entropy of `Z` is *exactly* the same
    conditional mutual information.  Together with the primal deficit identity it
    completes the symmetric pair, matching the symmetric conditioning bounds
    `conditioning_reduces_entropy_general` / `…'`.  Like its dual it is a pure
    rearrangement of the definition, holding with no probability hypotheses. -/
theorem conditionalMutualInfo_eq_conditioning_deficit' (pXYZ : α × β × γ → ℝ) :
    conditionalMutualInfo pXYZ =
      (shannonEntropy (marginalYZ pXYZ) - shannonEntropy (marginalY pXYZ)) -
        (shannonEntropy pXYZ - shannonEntropy (marginalXY pXYZ)) := by
  unfold conditionalMutualInfo
  ring

/-- **The two conditioning deficits are equal.**

      `H(X | Y) − H(X | Y, Z) = H(Z | Y) − H(Z | X, Y)`,

    i.e. the amount by which learning `Z` reduces the conditional entropy of `X`
    equals the amount by which learning `X` reduces the conditional entropy of
    `Z`.  Both sides equal the conditional mutual information `I(X ; Z | Y)`
    (`conditionalMutualInfo_eq_conditioning_deficit` and its `'` dual), so this is
    the symmetry `I(X ; Z | Y) = I(Z ; X | Y)` read at the level of conditional
    entropies.  A pure rearrangement, valid with no probability hypotheses. -/
theorem conditioning_deficit_symm (pXYZ : α × β × γ → ℝ) :
    (shannonEntropy (marginalXY pXYZ) - shannonEntropy (marginalY pXYZ)) -
        (shannonEntropy pXYZ - shannonEntropy (marginalYZ pXYZ)) =
      (shannonEntropy (marginalYZ pXYZ) - shannonEntropy (marginalY pXYZ)) -
        (shannonEntropy pXYZ - shannonEntropy (marginalXY pXYZ)) := by
  ring

/-! ## The `X ↔ Z` symmetry of `I(X ; Z | Y)` at the level of distributions

`conditioning_deficit_symm` records the symmetry `I(X ; Z | Y) = I(Z ; X | Y)` as an
*algebraic* rearrangement of the four entropy terms.  The lemmas below upgrade it to a
genuine statement about the distribution: relabeling outcomes never changes an entropy
(`shannonEntropy_comp_equiv`), so physically swapping the roles of `X` and `Z` in the joint
law leaves `I(X ; Z | Y)` invariant. -/

/-- **Shannon entropy is a symmetric function of the probability vector.**  Relabeling the
outcomes by any bijection `e : α ≃ β` leaves the entropy unchanged: `H(p ∘ e) = H(p)`.
Entropy depends only on the multiset of probabilities, not on how the outcomes are named. -/
theorem shannonEntropy_comp_equiv {δ ε : Type*} [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε] (e : δ ≃ ε) (p : ε → ℝ) :
    shannonEntropy (p ∘ e) = shannonEntropy p := by
  unfold shannonEntropy
  simp only [Function.comp_apply]
  congr 1
  exact Equiv.sum_comp e (fun y => if p y = 0 then (0 : ℝ) else p y * Real.log (p y))

/-- The coordinate reordering `(z, y, x) ↦ (x, y, z)`, packaged as an `Equiv`.  Composing a
joint law `pXYZ : α × β × γ → ℝ` with it produces the law of the swapped triple `(Z, Y, X)`. -/
def reorderXZ {α β γ : Type*} : γ × β × α ≃ α × β × γ where
  toFun := fun p => (p.2.2, p.2.1, p.1)
  invFun := fun p => (p.2.2, p.2.1, p.1)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Conditional mutual information is symmetric in `X` and `Z` (distribution form).**
Writing `pZYX := pXYZ ∘ reorderXZ` for the joint law with `X` and `Z` swapped,
`I(X ; Z | Y)` computed from `pZYX` equals `I(X ; Z | Y)` computed from `pXYZ`:
`conditionalMutualInfo (pXYZ ∘ reorderXZ) = conditionalMutualInfo pXYZ`.

Each of the four entropy terms transports across the swap by relabeling
(`shannonEntropy_comp_equiv`): `marginalXY` of the swapped law is `marginalYZ` of the
original up to the coordinate flip `Equiv.prodComm`, `marginalYZ` ↔ `marginalXY` likewise,
`marginalY` is literally unchanged (a `Finset.sum_comm`), and the full entropy is invariant
because `reorderXZ` is a bijection.  This is the true `I(X ; Z | Y) = I(Z ; X | Y)`, of which
`conditioning_deficit_symm` is the shadow after the four terms are already written out. -/
theorem conditionalMutualInfo_swap (pXYZ : α × β × γ → ℝ) :
    conditionalMutualInfo (pXYZ ∘ reorderXZ) = conditionalMutualInfo pXYZ := by
  have hXY : marginalXY (pXYZ ∘ reorderXZ) = marginalYZ pXYZ ∘ Equiv.prodComm γ β := by
    funext zy; obtain ⟨z, y⟩ := zy; rfl
  have hYZ : marginalYZ (pXYZ ∘ reorderXZ) = marginalXY pXYZ ∘ Equiv.prodComm β α := by
    funext yx; obtain ⟨y, x⟩ := yx; rfl
  have hY : marginalY (pXYZ ∘ reorderXZ) = marginalY pXYZ := by
    funext y
    simp only [marginalY, Function.comp_apply, reorderXZ]
    exact Finset.sum_comm
  have hP : shannonEntropy (pXYZ ∘ reorderXZ) = shannonEntropy pXYZ :=
    shannonEntropy_comp_equiv reorderXZ pXYZ
  unfold conditionalMutualInfo
  rw [hXY, hYZ, hY, hP, shannonEntropy_comp_equiv (Equiv.prodComm γ β) (marginalYZ pXYZ),
    shannonEntropy_comp_equiv (Equiv.prodComm β α) (marginalXY pXYZ)]
  ring

end InformationTheory.SSA
