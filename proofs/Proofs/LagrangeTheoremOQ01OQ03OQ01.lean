import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-
# Hall's Theorem: the Schur–Zassenhaus lifting step (0 axioms)

## Open Question (from lagrange-theorem-oq-01-oq-03, OQ-01)
> Can the full proof of Hall's theorem be formalized in Lean 4 without using
> Schur–Zassenhaus as a black box, by building the minimal normal subgroup
> induction from scratch?

## What this file settles

The parent entry `lagrange-theorem-oq-01-oq-03` axiomatized Hall's theorem for
solvable groups (`hall_solvable`) with the justification that "Schur–Zassenhaus
is not yet in Mathlib 4.26". **That justification is factually wrong.** Mathlib
4.26 DOES contain Schur–Zassenhaus as
`Subgroup.exists_right_complement'_of_coprime`
(`Mathlib/GroupTheory/SchurZassenhaus.lean`), and sibling gallery entries
(`lagrange-theorem-oq-03`, `sylow-theorem-oq-03`) already use it.

So the right answer to OQ-01 is: one should NOT rebuild Schur–Zassenhaus from
scratch — it is available — and the genuine remaining obstacle to a 0-axiom Hall
theorem is the *minimal normal subgroup* machinery (every minimal normal
subgroup of a finite solvable group is elementary abelian), which Mathlib lacks.

This file isolates and proves, **with 0 axioms**, the precise inductive
mechanism that the parent axiomatized away: the **Schur–Zassenhaus lifting
step**. Hall's proof inducts on `|G|`; in the branch where the chosen normal
subgroup `N` has order coprime to the target order `d`, the existence of a
subgroup of order `d` in the quotient `G/N` lifts to a subgroup of order `d` in
`G`. That lift is exactly Schur–Zassenhaus applied inside the preimage, and it is
what `hall_lift_of_coprime` below proves.

## Results

| Theorem | Statement | Status |
|---------|-----------|--------|
| `hall_lift_of_coprime` | If `N ⊴ G`, `gcd(\|N\|, d) = 1`, and `G/N` has a subgroup of order `d`, then so does `G` | Proved (0 axioms) |
| `hall_lift_of_coprime_subgroup` | The lifted subgroup can be taken inside the preimage of the quotient subgroup | Proved (0 axioms) |
| `schur_zassenhaus_available` | Restatement of Mathlib's Schur–Zassenhaus, witnessing it exists | Proved (0 axioms) |
| `exists_minimal_normal` | Every nontrivial finite group has a minimal nontrivial normal subgroup | Proved (0 axioms) |
| `exists_minimal_normal_atom` | …stated as an atom in the normal-subgroup lattice | Proved (0 axioms) |
| `minimal_normal_abelian_of_solvable` | A minimal normal subgroup of a solvable group is abelian | Proved (0 axioms) |
| `exists_abelian_minimal_normal` | A nontrivial finite solvable group has an abelian minimal normal subgroup | Proved (0 axioms) |

## Status of the remaining gap (for a full 0-axiom Hall theorem)

The induction has a branch where `p ∣ d` (the prime dividing the minimal normal
subgroup `N` also divides `d`). The parent entry flagged two missing Mathlib
ingredients for it; **both are now supplied in this file with 0 axioms**:

* existence of a *minimal* normal subgroup of a nontrivial finite group
  (`exists_minimal_normal` / `exists_minimal_normal_atom`, Part II), and
* the fact that in a *solvable* group such a subgroup is **abelian**
  (`minimal_normal_abelian_of_solvable`, Part III), assembled as
  `exists_abelian_minimal_normal`.

What is left for the *elementary*-abelian sharpening is only that an abelian
minimal normal subgroup is a `p`-group — its `p`-torsion is characteristic, hence
normal, hence (by minimality) all of `N`. That is a refinement of the abelian
result above, not a new obstruction. With Part I (the lifting step), the abelian
base case (`lagrange-theorem-oq-03`'s `abelian_hall_exists`), and these descent
ingredients, the pieces of a 0-axiom `hall_solvable` are in place; what remains is
the bookkeeping of the induction itself.

## References
- Hall, P. (1928), "A note on soluble groups", J. London Math. Soc.
- Gorenstein, "Finite Groups", Ch. 6 (Hall's theorem via Schur–Zassenhaus)
-/

namespace LagrangeOQ01OQ03OQ01

open Subgroup

variable {G : Type*} [Group G]

-- ============================================================
-- Part 0: Schur–Zassenhaus is available in Mathlib (record this)
-- ============================================================

/-- **Schur–Zassenhaus is in Mathlib 4.26.** A normal subgroup `N ⊴ G` whose
order is coprime to its index has a complement. This is `Mathlib`'s
`Subgroup.exists_right_complement'_of_coprime`; we restate it to document, against
the parent entry's claim, that the theorem is available and needs no axiom. -/
theorem schur_zassenhaus_available (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ K : Subgroup G, N.IsComplement' K :=
  Subgroup.exists_right_complement'_of_coprime hN

-- ============================================================
-- Part I: The Schur–Zassenhaus lifting step of Hall's theorem
-- ============================================================

/-- **Hall lifting step (subgroup form).** Let `G` be finite, `N ⊴ G` a normal
subgroup, and `Q ≤ G/N` a subgroup of order `d` with `gcd(|N|, d) = 1`. Then the
preimage `L = π⁻¹(Q)` contains a subgroup `K` of order `d` (a complement to `N`
inside `L`). This is the inductive step of Hall's theorem: it lifts a Hall
subgroup from the quotient to the group via Schur–Zassenhaus. -/
theorem hall_lift_of_coprime_subgroup [Finite G] (N : Subgroup G) [N.Normal]
    {d : ℕ} (Q : Subgroup (G ⧸ N)) (hQ : Nat.card Q = d)
    (hcop : Nat.Coprime (Nat.card N) d) :
    ∃ K : Subgroup G, K ≤ Q.comap (QuotientGroup.mk' N) ∧ Nat.card K = d := by
  -- `L` is the preimage of `Q` under the quotient map.
  set L := Q.comap (QuotientGroup.mk' N) with hLdef
  -- `N ≤ L` since `N = ker(π)` and the kernel lands in every preimage.
  have hNL : N ≤ L := by
    intro x hx
    rw [hLdef, mem_comap]
    have hx1 : (QuotientGroup.mk' N) x = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact one_mem Q
  -- Index of the preimage equals the index of `Q` (π is surjective).
  have hLidx : L.index = Q.index :=
    Subgroup.index_comap_of_surjective (H := Q) (QuotientGroup.mk'_surjective N)
  -- Order of `L`: `|L| = |N| * d`.
  have hQpos : Q.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcardL : Nat.card L = Nat.card N * d := by
    have key : Nat.card L * Q.index = (Nat.card N * d) * Q.index := by
      have lhs : Nat.card L * Q.index = Nat.card G := by
        rw [← hLidx]; exact Subgroup.card_mul_index L
      have rhs : (Nat.card N * d) * Q.index = Nat.card G := by
        rw [← hQ, mul_assoc, Subgroup.card_mul_index Q, ← Subgroup.index_eq_card]
        exact Subgroup.card_mul_index N
      rw [lhs, rhs]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hQpos) key
  -- `N` as a subgroup of `↥L`, with the same cardinality as `N`.
  have hmap : (N.subgroupOf L).map L.subtype = N := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNL]
  have hNLcard : Nat.card (N.subgroupOf L) = Nat.card N := by
    have h := Subgroup.card_subtype L (N.subgroupOf L)
    rw [hmap] at h
    exact h.symm
  -- Its index inside `↥L` is `d`.
  have hidxNL : (N.subgroupOf L).index = d := by
    have h := Subgroup.card_mul_index (N.subgroupOf L)
    rw [hNLcard, hcardL] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  -- Schur–Zassenhaus inside `↥L`: `N.subgroupOf L` has a complement `KL`.
  have hcop' : Nat.Coprime (Nat.card (N.subgroupOf L)) (N.subgroupOf L).index := by
    rw [hNLcard, hidxNL]; exact hcop
  obtain ⟨KL, hKL⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  -- The complement has order `d`.
  have hKLcard : Nat.card KL = d := by
    have h := hKL.card_mul
    rw [hNLcard, hcardL] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  -- Push `KL` back into `G`; it lands inside `L` and keeps order `d`.
  refine ⟨KL.map L.subtype, ?_, ?_⟩
  · exact map_subtype_le KL
  · rw [Subgroup.card_subtype]; exact hKLcard

/-- **Hall lifting step (existence form).** If `N ⊴ G` is normal with order
coprime to `d`, and the quotient `G/N` has a subgroup of order `d`, then `G` has
a subgroup of order `d`. This is the Schur–Zassenhaus inductive step of Hall's
theorem, formalized with 0 axioms. -/
theorem hall_lift_of_coprime [Finite G] (N : Subgroup G) [N.Normal]
    {d : ℕ} (Q : Subgroup (G ⧸ N)) (hQ : Nat.card Q = d)
    (hcop : Nat.Coprime (Nat.card N) d) :
    ∃ K : Subgroup G, Nat.card K = d := by
  obtain ⟨K, _, hK⟩ := hall_lift_of_coprime_subgroup N Q hQ hcop
  exact ⟨K, hK⟩

-- ============================================================
-- Part II: Existence of a minimal normal subgroup
-- ============================================================
--
-- This is the first of the two structural inputs the parent entry flagged as
-- missing from Mathlib (the other being "minimal normal ⇒ elementary abelian in
-- the solvable case", handled in Part III). Hall's induction, in the branch where
-- the relevant prime divides the target order `d`, needs a *minimal* normal
-- subgroup to descend along. Mathlib 4.26 has no such existence theorem; we supply
-- it with 0 axioms.

/-- In a finite group, a subgroup contained in another of no-smaller cardinality
must equal it. (Antisymmetry of `≤` forced by finite cardinality.) -/
private theorem eq_of_le_of_card_le [Finite G] {M N : Subgroup G}
    (hle : M ≤ N) (hcard : Nat.card N ≤ Nat.card M) : M = N := by
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  simpa only [Nat.card_coe_set_eq] using hcard

/-- **Existence of a minimal normal subgroup.** Every nontrivial finite group `G`
has a normal subgroup `N ≠ ⊥` that is minimal among nontrivial normal subgroups:
any normal `M` with `M ≤ N` and `M ≠ ⊥` already equals `N`. This is the
structural ingredient (beyond the Schur–Zassenhaus lifting step of Part I) that
Hall's induction uses to handle the branch where the prime dividing the chosen
minimal normal subgroup also divides the target order. Mathlib 4.26 has no such
theorem; proved here with 0 axioms by minimizing `Nat.card` over the finite,
nonempty (`⊤` qualifies) collection of nontrivial normal subgroups. -/
theorem exists_minimal_normal [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → M = N := by
  haveI : Nontrivial (Subgroup G) := Subgroup.nontrivial_iff.mpr inferInstance
  -- The subtype of nontrivial normal subgroups is finite and nonempty (`⊤`).
  haveI : Nonempty {N : Subgroup G // N.Normal ∧ N ≠ ⊥} :=
    ⟨⟨⊤, inferInstance, top_ne_bot⟩⟩
  -- Pick one of minimal order.
  obtain ⟨⟨N, hNnorm, hNne⟩, hmin⟩ :=
    Finite.exists_min
      (fun s : {N : Subgroup G // N.Normal ∧ N ≠ ⊥} => Nat.card (s.1 : Subgroup G))
  refine ⟨N, hNnorm, hNne, ?_⟩
  intro M hMnorm hMle hMne
  -- `M` is itself a nontrivial normal subgroup, so minimality gives `|N| ≤ |M|`.
  have hge : Nat.card N ≤ Nat.card M := hmin ⟨M, hMnorm, hMne⟩
  -- Combined with `M ≤ N`, finite cardinality forces `M = N`.
  exact eq_of_le_of_card_le hMle hge

/-- Restatement of `exists_minimal_normal` as an *atom* in the lattice of normal
subgroups: a minimal normal subgroup `N` has, below it, no normal subgroup other
than `⊥` and `N` itself. -/
theorem exists_minimal_normal_atom [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
  obtain ⟨N, hNnorm, hNne, hmin⟩ := exists_minimal_normal (G := G)
  refine ⟨N, hNnorm, hNne, fun M hMnorm hMle => ?_⟩
  by_cases hM : M = ⊥
  · exact Or.inl hM
  · exact Or.inr (hmin M hMnorm hMle hM)

-- ============================================================
-- Part III: A minimal normal subgroup of a solvable group is abelian
-- ============================================================
--
-- This closes the *second* structural gap the parent entry flagged. Together with
-- Part II it gives the full descent target for Hall's induction: a nontrivial
-- finite solvable group has an abelian minimal normal subgroup to factor out.

/-- **A minimal normal subgroup of a solvable group is abelian.** If `N ⊴ G` is
nontrivial and minimal among normal subgroups (every normal `M ≤ N` is `⊥` or
`N`), and `G` is solvable, then `N` is abelian: any two of its elements commute.

Proof: the commutator subgroup `⁅N, N⁆` is normal in `G` (commutator of normal
subgroups) and, since `G` is solvable and `N ≠ ⊥`, strictly smaller than `N`
(`IsSolvable.commutator_lt_of_ne_bot`). Minimality then forces `⁅N, N⁆ = ⊥`,
i.e. every commutator of elements of `N` is trivial. Mathlib 4.26 has the
solvable-commutator descent but not this minimal-normal consequence. -/
theorem minimal_normal_abelian_of_solvable [IsSolvable G]
    (N : Subgroup G) [N.Normal] (hNne : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  -- `⁅N, N⁆` is normal in `G` and strictly below `N` (solvable, `N ≠ ⊥`).
  have hlt : ⁅N, N⁆ < N := IsSolvable.commutator_lt_of_ne_bot hNne
  -- Minimality: the only normal subgroup strictly below `N` is `⊥`.
  have hbot : ⁅N, N⁆ = ⊥ := by
    rcases hmin ⁅N, N⁆ inferInstance hlt.le with h | h
    · exact h
    · exact absurd h hlt.ne
  -- `⁅N, N⁆ = ⊥` says every commutator of elements of `N` is trivial.
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ (⊥ : Subgroup G) :=
    Subgroup.commutator_le.mp hbot.le a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

/-- **A nontrivial finite solvable group has an abelian minimal normal subgroup.**
The combined descent target for Hall's induction: a normal `N ≠ ⊥` that is an atom
in the normal-subgroup lattice (Part II) and is abelian (Part III). This is the
ingredient the parent entry axiomatized away; it is now assembled with 0 axioms.
What remains for a full elementary-abelian conclusion is only that an abelian
minimal normal subgroup is a `p`-group (its `p`-torsion is characteristic, hence
normal, hence all of `N` by minimality) — a refinement, not a new obstruction. -/
theorem exists_abelian_minimal_normal [Finite G] [Nontrivial G] [IsSolvable G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      (∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) := by
  obtain ⟨N, hNnorm, hNne, hatom⟩ := exists_minimal_normal_atom (G := G)
  haveI := hNnorm
  exact ⟨N, hNnorm, hNne, hatom, minimal_normal_abelian_of_solvable N hNne hatom⟩

-- ============================================================
-- Part IV: Sanity specializations
-- ============================================================

/-- Degenerate check: when `N` is trivial, the lift is the identity — a subgroup
of order `d` in `G/⊥ ≅ G` is essentially one in `G`. (Stated abstractly via the
coprimality `gcd(1, d) = 1`, which always holds.) -/
theorem hall_lift_trivial_coprime [Finite G]
    {d : ℕ} (Q : Subgroup (G ⧸ (⊥ : Subgroup G))) (hQ : Nat.card Q = d) :
    ∃ K : Subgroup G, Nat.card K = d :=
  hall_lift_of_coprime (⊥ : Subgroup G) Q hQ (by
    rw [Subgroup.card_bot]; exact Nat.coprime_one_left d)

end LagrangeOQ01OQ03OQ01
