/-
  Szemerédi Regularity Lemma — OQ-04: mass-ceiling ⇒ complement-piece nonemptiness.

  `MassFloor.lean` (S14) derived the deviating-corner pieces `A₁, B₁` nonempty from
  the mass *floors* `eps·|A| ≤ |A₁|`, `eps·|B| ≤ |B₁|`, shrinking the constructive
  obligation of `isWitnessedSharpStep_of_split_of_nonempty` from four nonemptiness
  side-conditions to two — the complement pieces `A₂, B₂`, which the floors do not
  control.

  This file discharges those last two.  The split is a *disjoint* union
  `A₁ ∪ A₂ = A` with `Disjoint A₁ A₂`, so cardinalities add:

    `|A| = |A₁| + |A₂|`.

  Hence a strict mass *ceiling* on the deviating piece, `|A₁| < |A|`, forces
  `|A₂| = |A| - |A₁| > 0`, i.e. `A₂` nonempty — equivalently, `A₁ ⊊ A`.  This is
  the dual of the floor engine: the floor bounds `A₁` from below, the ceiling bounds
  it strictly below `A`, and between them the whole `2×2` split is nonempty on purely
  numeric data.

  `nonempty_of_massCeiling` isolates the ceiling engine (`|A| = |A₁| + |A₂|` and
  `|A₁| < |A|` give `A₂` nonempty), and
  `isWitnessedSharpStep_of_split_of_floors_ceilings` reruns the S14 capstone with
  *all four* piece-nonemptiness facts derived — the deviating corner from the floors,
  the complements from the ceilings.  The remaining constructive obligation of
  `exists_afksTwoLevel_of_dichotomy`'s dichotomy thus carries **no** nonemptiness
  side-conditions at all: it must only produce a disjoint `2×2` split satisfying the
  mass floors `eps·|A| ≤ |A₁|`, `eps·|B| ≤ |B₁|` and the mass ceilings
  `|A₁| < |A|`, `|B₁| < |B|` on the deviating corner.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04MassFloor

namespace Szemeredi.RegularityOQ04MassCeiling

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04Freshness Szemeredi.RegularityOQ04MassFloor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Mass-ceiling ⇒ complement nonemptiness.**  For a *disjoint* split
    `A₁ ∪ A₂ = A` the cardinalities add, `|A| = |A₁| + |A₂|`, so a strict ceiling
    `|A₁| < |A|` on the deviating piece forces `|A₂| > 0`, i.e. the complement `A₂`
    is nonempty (equivalently `A₁ ⊊ A`).  The dual of `nonempty_of_massFloor`. -/
theorem nonempty_of_massCeiling {A A₁ A₂ : Finset V}
    (hsplit : A₁ ∪ A₂ = A) (hdisj : Disjoint A₁ A₂)
    (hceil : (A₁.card : ℚ) < (A.card : ℚ)) :
    A₂.Nonempty := by
  rw [← Finset.card_pos]
  have hcard : A.card = A₁.card + A₂.card := by
    rw [← hsplit]; exact Finset.card_union_of_disjoint hdisj
  have hlt : A₁.card < A.card := by exact_mod_cast hceil
  omega

/-- **Witnessed sharp step from the split + mass floors *and* ceilings (all four
    piece-nonemptinesses derived).**  Identical to `isWitnessedSharpStep_of_split_of_gap`
    except the complement pieces `A₂, B₂` are no longer taken as nonemptiness
    hypotheses: they are *derived* from the mass ceilings `|A₁| < |A|`, `|B₁| < |B|`
    (via `nonempty_of_massCeiling`), just as `A₁, B₁` are derived from the floors.
    With this, the AFKS dichotomy's remaining constructive obligation is a disjoint
    `2×2` split constrained purely by numeric mass data — floors and ceilings on the
    deviating corner — and carries no nonemptiness side-conditions. -/
theorem isWitnessedSharpStep_of_split_of_floors_ceilings
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hnext : parts (n + 1) =
      insert A₁ (insert A₂ (insert B₁ (insert B₂ (((parts n).erase A).erase B)))))
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂)
    (heps : 0 < eps) (hm : 0 < m)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hgapA : eps * A.card ≤ (A₁.card : ℚ)) (hgapB : eps * B.card ≤ (B₁.card : ℚ))
    (hceilA : (A₁.card : ℚ) < (A.card : ℚ)) (hceilB : (B₁.card : ℚ) < (B.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep G parts n eps m := by
  have hA2 : A₂.Nonempty := nonempty_of_massCeiling hsplitA hdA hceilA
  have hB2 : B₂.Nonempty := nonempty_of_massCeiling hsplitB hdB hceilB
  exact isWitnessedSharpStep_of_split_of_gap G parts n eps m A B A₁ A₂ B₁ B₂
    hA hB hAB hdisj hnext hsplitA hsplitB hdA hdB hA2 hB2 heps hm hmA hmB
    hgapA hgapB hgap

end Szemeredi.RegularityOQ04MassCeiling
