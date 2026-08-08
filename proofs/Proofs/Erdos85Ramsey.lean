/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Walters
-/
import Proofs.Erdos85Problem

/-!
# The Ramsey reformulation of Erdős problem 85

This file makes precise the elementary relation between the minimum-degree
threshold `minDegreeForC4` and the two-colour Ramsey problem for a four-cycle
versus a star.  We state the Ramsey property directly in terms of red edges:
a blue `K_{1,s}` centred at `v` is a set of `s` red non-neighbours of `v`.
-/

open SimpleGraph Finset

namespace Erdos85

/-- On `m` labelled vertices, every red/blue colouring has either a red `C₄`
or a blue star with `s` leaves.  In the red graph `G`, the number of possible
blue neighbours of `v` is `m - 1 - G.degree v`. -/
def C4StarRamseyAt (m s : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
    containsC4 (Fin m) G ∨ ∃ v, s ≤ m - 1 - G.degree v

/-- The exact threshold translation

`R(C₄, K_{1,s}) ≤ m ↔ f(m) ≤ m - s`.

Here the left side is expressed as `C4StarRamseyAt m s`, avoiding any choice
of a convention for Ramsey numbers.  The hypotheses exclude the degenerate
small orders and ensure that a star with `s` leaves can fit on `m` vertices. -/
theorem c4StarRamseyAt_iff_minDegreeForC4_le_sub
    {m s : ℕ} (hm : 4 ≤ m) (hs : s ≤ m - 1) :
    C4StarRamseyAt m s ↔ minDegreeForC4 m ≤ m - s := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  constructor
  · intro hRamsey
    by_contra hnot
    have hlt : m - s < minDegreeForC4 m := Nat.lt_of_not_ge hnot
    obtain ⟨G, hdec, hmin, hfree⟩ :=
      (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).2 hlt
    letI := hdec
    rcases hRamsey G with hcycle | ⟨v, hv⟩
    · exact hfree hcycle
    · have hdeg : m - s ≤ G.degree v :=
        le_trans hmin (G.minDegree_le_degree v)
      have hdegree_lt : G.degree v < m := by
        simpa using G.degree_lt_card_verts v
      omega
  · intro hthreshold G hdec
    by_cases hcycle : containsC4 (Fin m) G
    · exact Or.inl hcycle
    · right
      by_contra hstar
      push Not at hstar
      have hall : ∀ v, m - s ≤ G.degree v := by
        intro v
        have hdegree_lt : G.degree v < m := by
          simpa using G.degree_lt_card_verts v
        have := hstar v
        omega
      have hmin : m - s ≤ G.minDegree :=
        G.le_minDegree_of_forall_le_degree (m - s) hall
      have hw : C4FreeMinDegreeWitness m (m - s) := ⟨G, hdec, hmin, hcycle⟩
      have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hm).1 hw
      omega

/-- In the traditional notation, the Ramsey number is the least order at
which the local Ramsey property holds. -/
noncomputable def c4StarRamseyNumber (s : ℕ) : ℕ :=
  sInf {m : ℕ | C4StarRamseyAt m s}

/-- A pointwise, convention-free characterization suitable for translating
finite Ramsey bounds into bounds on `minDegreeForC4`. -/
theorem c4StarRamseyAt_iff_threshold
    {m s : ℕ} (hm : 4 ≤ m) (hs : s ≤ m - 1) :
    C4StarRamseyAt m s ↔ minDegreeForC4 m ≤ m - s :=
  c4StarRamseyAt_iff_minDegreeForC4_le_sub hm hs

end Erdos85
