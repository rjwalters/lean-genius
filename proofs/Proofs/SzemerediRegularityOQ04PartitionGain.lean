/-
  Szemerédi Regularity Lemma — OQ-04: the whole-partition item-1 dichotomy
  (regularity-count failure ⇒ a sharp `ε⁴` 2×2 energy-increment refinement).

  ## Where this sits in the OQ-04 tower

  The strong (Alon–Fischer–Krivelevich–Szegedy) regularity lemma is assembled
  from three ingredients (see `research/problems/szemeredi-regularity-oq-04`):

  1. **Energy-increment step** — a fine partition with too many irregular pairs
     admits a refinement raising `partitionEnergy` by a fixed `δ = δ(ε)`.
  2. **Two-level statement** — the packaged AFKS conclusion (a coarse
     `ε`-regular partition + an almost-all-pairs-`E(k)`-regular refinement).
  3. **Outer-loop assembly** — run the loop, using the `[0,1]`-potential
     termination bound as the certificate.

  Items 2–3 are handled by `SzemerediRegularityOQ04TwoLevel` /
  `SzemerediRegularityOQ04Outer`; both take item 1 as an explicit
  *regular-or-refine dichotomy* hypothesis.  This file closes the remaining
  analytic gap of item 1 **at the sharp floor** by chaining, on already-verified
  primitives, the two ends the earlier sessions had left disconnected:

  * `Szemeredi.Regularity.exists_irregular_pair` — a partition whose count of
    ordered irregular pairs exceeds `ε·k(k−1)` contains a concrete irregular
    pair `(A, B)`; and
  * `RegularityOQ04Bridge.pairEnergy_prod_gain_of_irregular_eps4` — an
    `ε`-irregular pair, refined *simultaneously* on both coordinates into the
    `2×2` grid `{A′, A∖A′} × {B′, B∖B′}`, raises the pair's `pairEnergy`
    contribution by at least `ε⁴·|A||B|/n²`, with **no** factor-`¼` loss (the
    one-sided A-side/B-side routes of sessions 4–5 lost that factor via the
    triangle inequality; the direct variance-atom bound does not).

  The result, `exists_prod_gain_of_irregular_partition`, is exactly the datum
  the outer-loop assembly consumes: *if the current partition is too irregular,
  a witnessed sharp `2×2` gain-refinement exists.*  Its contrapositive packaging
  `regular_count_or_prod_gain` states the dichotomy in the `∨` shape the loop
  reads.

  Everything here is a pure chaining of verified lemmas: 0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Bridge

namespace Szemeredi.RegularityOQ04PartitionGain

open Classical
open Szemeredi.Core Szemeredi.Regularity
open Szemeredi.RegularityOQ04Energy Szemeredi.RegularityOQ04Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Item-1 dichotomy input (existence form): a too-irregular partition admits a
    sharp `ε⁴` `2×2` energy-increment refinement.**

    If the ordered-pair irregularity count of `parts` exceeds the AFKS budget
    `ε·k(k−1)` (i.e. `parts` fails the count clause of `IsRegularPartition`),
    then some pair `(A, B)` of distinct parts is `ε`-irregular, and refining it
    simultaneously on both coordinates into the `2×2` grid `{A′, A∖A′} × {B′,
    B∖B′}` raises that pair's `pairEnergy` contribution by at least
    `ε⁴·|A||B|/n²` — a definite positive jump whenever the pair carries positive
    mass.

    This is the analytic heart of the strong-regularity iteration (item 1),
    stated at the *sharp* floor: it composes `exists_irregular_pair`
    (whole-partition ⇒ one irregular pair) with `pairEnergy_prod_gain_of_irregular_eps4`
    (irregular pair ⇒ sharp `2×2` `pairEnergy` gain).  Paired with the
    `[0,1]`-potential termination bound of `SzemerediRegularityOQ04`
    (`energy_increment_count_le`, `N ≤ 1/δ`), it caps the number of such
    refinement steps and drives the AFKS outer loop. -/
theorem exists_prod_gain_of_irregular_partition (G : SimpleGraph V)
    [DecidableRel G.Adj] (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V))
    (hmany : ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬ IsEpsilonRegular G eps pq.1 pq.2)).card >
        eps * (parts.card * (parts.card - 1))) :
    ∃ A B A' B' : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧ A' ⊆ A ∧ B' ⊆ B ∧
      pairEnergy G A B +
          eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2 ≤
        pairEnergy G A' B' + pairEnergy G A' (B \ B') +
          pairEnergy G (A \ A') B' + pairEnergy G (A \ A') (B \ B') := by
  obtain ⟨A, B, hA, hB, hAB, hirr⟩ := exists_irregular_pair G eps heps parts hmany
  obtain ⟨A', B', hA', hB', hgain⟩ :=
    pairEnergy_prod_gain_of_irregular_eps4 G eps (le_of_lt heps) A B hirr
  exact ⟨A, B, A', B', hA, hB, hAB, hA', hB', hgain⟩

/-- **Item-1 dichotomy (`∨` form): regular-count OR a sharp `ε⁴` gain-refinement.**

    The regular-or-refine dichotomy in the shape the AFKS outer loop reads:
    every partition `parts` either meets the AFKS irregularity-count budget
    (`#{ordered irregular pairs} ≤ ε·k(k−1)`, the count clause of
    `IsRegularPartition`), *or* it admits a witnessed sharp `2×2` refinement of
    some irregular pair raising that pair's `pairEnergy` by at least
    `ε⁴·|A||B|/n²`.  No middle ground: the alternatives are the negation of one
    strict inequality.

    This is the `hdich`-shaped hypothesis of `exists_afksTwoLevel_of_dichotomy`
    (item 3), now discharged from first principles on the base `Szemeredi.Core`
    primitives — no unproved analytic input remains between "too irregular" and
    "energy jumps by a definite amount". -/
theorem regular_count_or_prod_gain (G : SimpleGraph V)
    [DecidableRel G.Adj] (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V)) :
    ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬ IsEpsilonRegular G eps pq.1 pq.2)).card ≤
        eps * (parts.card * (parts.card - 1)) ∨
    ∃ A B A' B' : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧ A' ⊆ A ∧ B' ⊆ B ∧
      pairEnergy G A B +
          eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2 ≤
        pairEnergy G A' B' + pairEnergy G A' (B \ B') +
          pairEnergy G (A \ A') B' + pairEnergy G (A \ A') (B \ B') := by
  by_cases hle : (((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬ IsEpsilonRegular G eps pq.1 pq.2)).card : ℚ) ≤
      eps * (parts.card * (parts.card - 1))
  · exact Or.inl hle
  · exact Or.inr (exists_prod_gain_of_irregular_partition G eps heps parts
      (not_le.mp hle))

end Szemeredi.RegularityOQ04PartitionGain
