/-
  Szemerédi Regularity Lemma — OQ-04: mass-floor positivity ⇒ piece-nonemptiness.

  `Freshness.lean` (S13) reduced the item-1 dichotomy obligation to the purely
  constructive step "exhibit the refinement chain with the four split pieces
  `A₁, A₂, B₁, B₂` *nonempty*"; its capstone
  `isWitnessedSharpStep_of_split_of_nonempty` still takes all four nonemptiness
  facts as explicit hypotheses.

  This file discharges the two that are *forced by the analytic data already
  threaded through the witness*.  The witnessed sharp step keeps the mass floors

    `eps * |A| ≤ |A₁|`  and  `eps * |B| ≤ |B₁|`

  on the deviating corner, and the coarse parts carry the mass bound `m ≤ |A|`.
  When `eps > 0` and `m > 0` these force `A₁` and `B₁` nonempty with no extra
  input: `|A| ≥ m > 0`, hence `|A₁| ≥ eps·|A| > 0`.  This is exactly the
  "`E·|A| ≤ |A₁|` with `E, |A| > 0` already forces `A₁` nonempty" content named
  in the state as a residual constructive step.

  `nonempty_of_massFloor` isolates the positivity lemma; `isWitnessedSharpStep_of_split_of_gap`
  reruns the S13 capstone with the `A₁`/`B₁` nonemptiness *derived* from the gaps,
  so the constructive obligation shrinks from four nonemptiness side-conditions to
  two — only the complement pieces `A₂, B₂` (which the mass floors genuinely do
  *not* control) remain to be exhibited.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large graphs",
  Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Freshness

namespace Szemeredi.RegularityOQ04MassFloor

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04Freshness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Mass-floor positivity ⇒ nonemptiness.**  A subset `A₁` whose cardinality is
    pinned below by an `eps`-fraction of a *nonempty* block `A`, with `eps > 0`, is
    itself nonempty: `|A₁| ≥ eps·|A| > 0`.  The elementary engine behind
    piece-nonemptiness for the AFKS sharp split. -/
theorem nonempty_of_massFloor {A A₁ : Finset V} {eps : ℚ}
    (heps : 0 < eps) (hA : A.Nonempty)
    (hgap : eps * (A.card : ℚ) ≤ (A₁.card : ℚ)) :
    A₁.Nonempty := by
  rw [← Finset.card_pos]
  have hApos : (0 : ℚ) < (A.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hA
  have : (0 : ℚ) < (A₁.card : ℚ) := lt_of_lt_of_le (mul_pos heps hApos) hgap
  exact_mod_cast this

/-- **Witnessed sharp step from the split + mass floors (nonemptiness of `A₁, B₁`
    derived).**  Identical to `isWitnessedSharpStep_of_split_of_nonempty` except the
    nonemptiness of the deviating-corner pieces `A₁`, `B₁` is *derived* from the mass
    floors `eps * |A| ≤ |A₁|`, `eps * |B| ≤ |B₁|` together with `eps > 0`, `m > 0`
    (which give `|A|, |B| ≥ m > 0`).  Only the complement pieces `A₂`, `B₂` — which
    the mass floors do not constrain — remain as nonemptiness side-conditions.  This
    is the precise shape the remaining constructive step of
    `exists_afksTwoLevel_of_dichotomy`'s dichotomy must meet. -/
theorem isWitnessedSharpStep_of_split_of_gap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (A B A₁ A₂ B₁ B₂ : Finset V)
    (hA : A ∈ parts n) (hB : B ∈ parts n) (hAB : A ≠ B)
    (hdisj : ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q → Disjoint P Q)
    (hnext : parts (n + 1) =
      insert A₁ (insert A₂ (insert B₁ (insert B₂ (((parts n).erase A).erase B)))))
    (hsplitA : A₁ ∪ A₂ = A) (hsplitB : B₁ ∪ B₂ = B)
    (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂)
    (hA2 : A₂.Nonempty) (hB2 : B₂.Nonempty)
    (heps : 0 < eps) (hm : 0 < m)
    (hmA : m ≤ (A.card : ℚ)) (hmB : m ≤ (B.card : ℚ))
    (hgapA : eps * A.card ≤ (A₁.card : ℚ)) (hgapB : eps * B.card ≤ (B₁.card : ℚ))
    (hgap : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    IsWitnessedSharpStep G parts n eps m := by
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℚ) < (A.card : ℚ) := lt_of_lt_of_le hm hmA
    exact_mod_cast this
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℚ) < (B.card : ℚ) := lt_of_lt_of_le hm hmB
    exact_mod_cast this
  have hA1 : A₁.Nonempty := nonempty_of_massFloor heps hAne hgapA
  have hB1 : B₁.Nonempty := nonempty_of_massFloor heps hBne hgapB
  exact isWitnessedSharpStep_of_split_of_nonempty G parts n eps m A B A₁ A₂ B₁ B₂
    hA hB hAB hdisj hnext hsplitA hsplitB hdA hdB hA1 hA2 hB1 hB2
    hmA hmB hgapA hgapB hgap

end Szemeredi.RegularityOQ04MassFloor
