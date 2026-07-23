/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: the `h(4)` rung.

  Companion to `Erdos117Problem.lean` and the `Erdos117WIP01*` ladder.  With
  `h(3) = 3` settled exactly (`Erdos117WIP01Exact.lean`), the next rung is the
  budget-3 impossibility at threshold `4`.  The witness is the symmetric group
  `S₃ = Equiv.Perm (Fin 3)`:

  * **`S₃` has the 4-commuting property** — its non-commuting graph has clique
    number exactly `4` (the three transpositions together with a 3-cycle are
    pairwise non-commuting; any 5-subset of the 6 elements contains either the
    identity or both 3-cycles).  Verified by a kernel-checked `decide` over all
    `2⁶` subsets — no `Lean.ofReduceBool`.
  * **No 3 abelian subgroups cover `S₃`** — an abelian subgroup contains at most
    one of the three transpositions, and never both a transposition and a
    3-cycle.  So a 3-cover assigns the 3-cycle to some member, all three
    transpositions to the remaining two members, and pigeonhole puts two
    non-commuting transpositions together.  Contradiction.

  Consequences (mirroring `Erdos117WIP01Three.lean`, with `S₃` transported to
  any universe by `ULift`):

  * `not_coversWithAbelian_three` : for `n ≥ 4`, budget `3` never covers.
  * `four_le_abelianCoverNumber`  : **`h(n) ≥ 4` for all `n ≥ 4`** whenever
                                    `h(n)` is well-defined.
  * `abelianCoverNumber_three_lt_four` : `h(3) < h(4)` (conditional on `h(4)`
                                    well-definedness) — the ladder strictly
                                    increases again: `0, 1, 1, 3, ≥4, …`.
  * `abelianCoverNumber_four_eq_zero_or_four_le` : unconditionally, `h(4)` is
                                    `0` (ill-defined fallback) or `≥ 4`.

  Well-definedness of `h(4)` is genuinely open here: the centralizer-cover
  trick of `Erdos117WIP01Exact.lean` is specific to clique number 3 (the 5-case
  analysis showing centralizers abelian breaks at `ω = 4` — `S₃` itself has the
  non-abelian centralizer `C(e) = S₃`... the correct obstruction is that a
  maximal 4-clique's centralizers need not be abelian).  A uniform bound needs
  a materially new mechanism (e.g. a Neumann-type `|G : Z(G)| ≤ f(n)` bound).

  0 axioms, 0 sorries.  Kernel `decide` only (no `native_decide`).
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01
import Proofs.Erdos117WIP01Mono
import Proofs.Erdos117WIP01Cover
import Proofs.Erdos117WIP01Three
import Proofs.Erdos117WIP01Exact

/- The universe of the ambient groups (see `Erdos117WIP01Mono.lean`): the finite
   witness `S₃` lives in `Type 0` and is transported into `Type u` by `ULift`. -/
universe u

/- ## 1. The generic pigeonhole: a 4-clique defeats any 3-cover by abelian
      subgroups -/

section Pigeonhole

variable {G : Type*} [Group G]

/-- **Four pairwise non-commuting elements defeat every abelian 3-cover.**
    Generic form (no finiteness, no concrete group): if `t₁, t₂, t₃, c` are
    pairwise non-commuting and `H : Fin 3 → Subgroup G` is a family of abelian
    subgroups covering `G`, we get a contradiction.  The member containing `c`
    can contain no `tᵢ`; the remaining two members receive three transpositions,
    so two non-commuting ones share an abelian subgroup. -/
theorem not_abelian_three_cover_of_four_clique {t₁ t₂ t₃ c : G}
    (h12 : t₁ * t₂ ≠ t₂ * t₁) (h13 : t₁ * t₃ ≠ t₃ * t₁) (h23 : t₂ * t₃ ≠ t₃ * t₂)
    (h1c : t₁ * c ≠ c * t₁) (h2c : t₂ * c ≠ c * t₂) (h3c : t₃ * c ≠ c * t₃)
    {H : Fin 3 → Subgroup G} (hAb : ∀ i, IsAbelianSubgroup G (H i))
    (hCov : ∀ g : G, ∃ i, g ∈ H i) : False := by
  obtain ⟨j, hcj⟩ := hCov c
  obtain ⟨i1, hm1⟩ := hCov t₁
  obtain ⟨i2, hm2⟩ := hCov t₂
  obtain ⟨i3, hm3⟩ := hCov t₃
  -- no `tᵢ` shares the abelian member containing `c`
  have hi1 : i1 ≠ j := fun h => h1c (hAb j t₁ c (h ▸ hm1) hcj)
  have hi2 : i2 ≠ j := fun h => h2c (hAb j t₂ c (h ▸ hm2) hcj)
  have hi3 : i3 ≠ j := fun h => h3c (hAb j t₃ c (h ▸ hm3) hcj)
  -- pigeonhole: three indices avoiding `j` inside `Fin 3` must collide
  have hv1 : i1.val ≠ j.val := fun h => hi1 (Fin.ext h)
  have hv2 : i2.val ≠ j.val := fun h => hi2 (Fin.ext h)
  have hv3 : i3.val ≠ j.val := fun h => hi3 (Fin.ext h)
  have hb1 := i1.isLt
  have hb2 := i2.isLt
  have hb3 := i3.isLt
  have hbj := j.isLt
  have hcol : i1.val = i2.val ∨ i1.val = i3.val ∨ i2.val = i3.val := by omega
  rcases hcol with h | h | h
  · exact h12 (hAb i1 t₁ t₂ hm1 (Fin.ext h ▸ hm2))
  · exact h13 (hAb i1 t₁ t₃ hm1 (Fin.ext h ▸ hm3))
  · exact h23 (hAb i2 t₂ t₃ hm2 (Fin.ext h ▸ hm3))

end Pigeonhole

/- ## 2. The witness: `S₃` has the 4-commuting property, sharply -/

/-- Abbreviation for the symmetric group on three letters. -/
local notation "S₃" => Equiv.Perm (Fin 3)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- **`S₃` has the 4-commuting property**: every subset of size `> 4` contains
    two distinct commuting elements.  Mathematically: a 5-subset of the six
    elements either contains the identity or contains both 3-cycles — a
    commuting pair either way; so the non-commuting graph of `S₃` has clique
    number `4`.  Verified by a kernel-checked finite computation (`decide`)
    over all `2⁶` subsets — no `Lean.ofReduceBool` involved. -/
theorem s3_hasNCommutingProperty_four : HasNCommutingProperty S₃ 4 := by
  unfold HasNCommutingProperty
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- **The threshold is sharp**: `S₃` does *not* have the 3-commuting property —
    the three transpositions together with a 3-cycle form a pairwise
    non-commuting 4-subset.  So `S₃` enters the `h(n)` covering problem exactly
    at `n = 4`. -/
theorem s3_not_hasNCommutingProperty_three : ¬ HasNCommutingProperty S₃ 3 := by
  unfold HasNCommutingProperty
  decide

/-- The three transpositions of `S₃` are pairwise non-commuting, and none of
    them commutes with the 3-cycle `(swap 0 1) * (swap 0 2)`.  All six facts by
    kernel `decide`. -/
theorem s3_four_clique :
    let t₁ : S₃ := Equiv.swap 0 1
    let t₂ : S₃ := Equiv.swap 0 2
    let t₃ : S₃ := Equiv.swap 1 2
    let c : S₃ := Equiv.swap 0 1 * Equiv.swap 0 2
    t₁ * t₂ ≠ t₂ * t₁ ∧ t₁ * t₃ ≠ t₃ * t₁ ∧ t₂ * t₃ ≠ t₃ * t₂ ∧
      t₁ * c ≠ c * t₁ ∧ t₂ * c ≠ c * t₂ ∧ t₃ * c ≠ c * t₃ := by
  decide

/- ## 3. Budget `3` fails at every threshold `n ≥ 4` -/

/-- **Budget `3` never covers at any threshold `n ≥ 4`.**  The witness is
    `ULift S₃` (transported to universe `u`; the 4-commuting property transfers
    along `MulEquiv.ulift` and up the threshold by monotonicity).  A 3-cover by
    abelian subgroups is defeated by the transposition/3-cycle pigeonhole
    (`not_abelian_three_cover_of_four_clique`), with the six non-commutation
    facts descending to `S₃` along `ULift.down`. -/
theorem not_coversWithAbelian_three {n : ℕ} (hn : 4 ≤ n) :
    ¬ CoversWithAbelian.{u} 3 n := by
  intro h
  obtain ⟨H, hAb, hCov⟩ := h (ULift.{u} S₃)
    (hasNCommutingProperty_mono hn
      (hasNCommutingProperty_of_mulEquiv MulEquiv.ulift.symm
        s3_hasNCommutingProperty_four))
  obtain ⟨h12, h13, h23, h1c, h2c, h3c⟩ := s3_four_clique
  exact not_abelian_three_cover_of_four_clique
    (t₁ := ULift.up (Equiv.swap 0 1)) (t₂ := ULift.up (Equiv.swap 0 2))
    (t₃ := ULift.up (Equiv.swap 1 2))
    (c := ULift.up (Equiv.swap 0 1 * Equiv.swap 0 2))
    (fun h => h12 (congrArg ULift.down h)) (fun h => h13 (congrArg ULift.down h))
    (fun h => h23 (congrArg ULift.down h)) (fun h => h1c (congrArg ULift.down h))
    (fun h => h2c (congrArg ULift.down h)) (fun h => h3c (congrArg ULift.down h))
    hAb hCov

/- ## 4. The lower bound `h(n) ≥ 4` for `n ≥ 4` -/

/-- **`h(n) ≥ 4` for every `n ≥ 4`** — whenever `h(n)` is well-defined (the
    covering set is nonempty rather than the `sInf ∅ = 0` fallback; for `n ≥ 4`
    nonemptiness remains unformalized — see the header on why the `ω = 3`
    mechanism does not extend).  Proof: `h(n)` is a member of the covering set
    (`Nat.sInf_mem`), so `h(n) ≤ 3` would put `3` in the set by upward closure —
    contradicting `not_coversWithAbelian_three`. -/
theorem four_le_abelianCoverNumber {n : ℕ} (hn : 4 ≤ n)
    (hne : ∃ k, CoversWithAbelian.{u} k n) :
    4 ≤ abelianCoverNumber.{u} n := by
  by_contra hlt
  have hneSet : {k | CoversWithAbelian.{u} k n}.Nonempty := hne
  have hmem : CoversWithAbelian.{u} (abelianCoverNumber.{u} n) n := Nat.sInf_mem hneSet
  have hle : abelianCoverNumber.{u} n ≤ 3 := by omega
  exact not_coversWithAbelian_three hn (coversWithAbelian_upward hle hmem)

/-- **`h(4) ≥ 4`** — the threshold case `n = 4`. -/
theorem four_le_abelianCoverNumber_four
    (hne : ∃ k, CoversWithAbelian.{u} k 4) :
    4 ≤ abelianCoverNumber.{u} 4 :=
  four_le_abelianCoverNumber (le_refl 4) hne

/-- **`h(3) < h(4)`** (conditional on `h(4)` being well-defined): with
    `h(3) = 3` exact (`abelianCoverNumber_three`), the ladder strictly
    increases again.  Known shape: `0, 1, 1, 3, ≥4, …`. -/
theorem abelianCoverNumber_three_lt_four
    (hne : ∃ k, CoversWithAbelian.{u} k 4) :
    abelianCoverNumber.{u} 3 < abelianCoverNumber.{u} 4 := by
  have h3 : abelianCoverNumber.{u} 3 = 3 := abelianCoverNumber_three
  have h4 := four_le_abelianCoverNumber_four hne
  omega

/-- **Unconditional dichotomy for `h(4)`**: either the covering set is empty and
    `h(4) = 0` (the `sInf ∅ = 0` fallback — ruled out mathematically by Pyber's
    upper bound, which is not formalized), or `h(4) ≥ 4`.  In no case is
    `h(4) ∈ {1, 2, 3}`. -/
theorem abelianCoverNumber_four_eq_zero_or_four_le :
    abelianCoverNumber.{u} 4 = 0 ∨ 4 ≤ abelianCoverNumber.{u} 4 := by
  by_cases hne : ∃ k, CoversWithAbelian.{u} k 4
  · exact Or.inr (four_le_abelianCoverNumber_four hne)
  · left
    rw [abelianCoverNumber_eq_sInf]
    exact Nat.sInf_eq_zero.mpr
      (Or.inr (Set.not_nonempty_iff_eq_empty.mp hne))

/- ## Axiom audit -/

#print axioms s3_hasNCommutingProperty_four
#print axioms not_coversWithAbelian_three
#print axioms four_le_abelianCoverNumber
#print axioms abelianCoverNumber_three_lt_four
