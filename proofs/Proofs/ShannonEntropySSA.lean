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

end InformationTheory.SSA
