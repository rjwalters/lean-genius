/-
  Szemerédi Regularity OQ04 — S28a: the unbounded two-level statement is DEGENERATE

  ## The finding

  The formalized AFKS target `IsAFKSTwoLevel G ε E Vparts Wparts` (TwoLevel.lean)
  asks for a fine partition that (i) refines `Vparts`, (ii) sits over an ε-regular
  coarse partition, and (iii) is `E(k)`-regular on all but an ε-fraction of pairs.
  Unlike the actual Alon–Fischer–Krivelevich–Szegedy strong lemma, it does NOT
  bound the number of fine parts (`|Wparts| ≤ L(ε, k)`).

  That omission is fatal to the statement's content: for any positive fine
  tolerance, EVERY pair of singletons is `E`-regular — a subset of a singleton
  carrying at least `E·1 > 0` mass is the singleton itself, so the density
  difference in the regularity test is literally `0`.  Hence the DISCRETE
  partition (all singletons) is equitable, refines every covering coarse
  partition, and has zero irregular pairs: `IsAFKSTwoLevel` is witnessed
  trivially (`exists_afksTwoLevel_discrete` below), with no graph theory at all.

  ## What this means for the program

  The S12–S27 oracle machinery is NOT wasted — its mass-floor invariant is
  precisely what excludes this degeneracy, and the machinery targets the
  *bounded* statement the real AFKS lemma makes.  This file:

  * proves the degeneracy honestly (`isEpsilonRegular_singleton`,
    `exists_afksTwoLevel_discrete`);
  * defines the corrected target `IsAFKSTwoLevelBounded` — the same three
    clauses plus the part-count bound `Wparts.card ≤ L` that carries the actual
    mathematical content.  The S27 restoration layer keeps `|Wparts| ≤ n/m`
    (mass floor `m`), so the oracle route proves the bounded statement with an
    `n`-dependent bound; the genuine AFKS bound `L(ε,k)` (n-independent,
    tower-type) additionally needs the S28 gain amplification recorded in the
    tracker blocker.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000), Lemma 3.2 (note the explicit bound on the
  number of parts there).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04TwoLevel

namespace Szemeredi.RegularityOQ04Discrete

open Szemeredi.Core
open Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- **Singleton pairs are `eps`-regular for every positive tolerance.**  A subset
of a singleton carrying mass at least `eps · 1 > 0` must be the singleton itself,
so the only instance of the regularity test compares the pair's density with
itself: the difference is `0`.  This is the engine of the degeneracy: regularity
testing has no content at singleton scale. -/
theorem isEpsilonRegular_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (a b : V) :
    IsEpsilonRegular G eps ({a} : Finset V) ({b} : Finset V) := by
  intro A' B' hA' hB' hcardA hcardB
  have hAcard : (({a} : Finset V).card : ℚ) = 1 := by simp
  have hBcard : (({b} : Finset V).card : ℚ) = 1 := by simp
  rw [hAcard, mul_one] at hcardA
  rw [hBcard, mul_one] at hcardB
  have hA'ne : A'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A' with rfl | h
    · simp at hcardA
      linarith
    · exact h
  have hB'ne : B'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B' with rfl | h
    · simp at hcardB
      linarith
    · exact h
  have hA'eq : A' = {a} := by
    rcases Finset.subset_singleton_iff.mp hA' with h | h
    · exact absurd h (Finset.nonempty_iff_ne_empty.mp hA'ne)
    · exact h
  have hB'eq : B' = {b} := by
    rcases Finset.subset_singleton_iff.mp hB' with h | h
    · exact absurd h (Finset.nonempty_iff_ne_empty.mp hB'ne)
    · exact h
  rw [hA'eq, hB'eq, sub_self, abs_zero]
  exact le_of_lt heps

/-- **The discrete partition trivially witnesses the unbounded two-level target.**
For any `ε ≥ 0`, any coarse partition `Vparts` that is `ε`-regular and covers `V`,
and any positive fine tolerance `E |Vparts|`, the all-singletons partition
`Finset.univ.image ({·})` satisfies `IsAFKSTwoLevel G ε E Vparts ·` — covering,
disjoint, ±1-equitable, refining, with ZERO irregular pairs.

No graph-theoretic input is used: this shows the formalized target, which (unlike
AFKS Lemma 3.2) does not bound the number of fine parts, is degenerate.  The
mathematical content of the strong lemma lives in the part-count bound — see
`IsAFKSTwoLevelBounded` below and the S28 program notes. -/
theorem exists_afksTwoLevel_discrete (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (hε : 0 ≤ ε)
    (Vparts : Finset (Finset V))
    (hcoarse : IsRegularPartition G ε Vparts)
    (hVcover : ∀ v : V, ∃ A ∈ Vparts, v ∈ A)
    (hE : 0 < E Vparts.card) :
    ∃ Wparts : Finset (Finset V), IsAFKSTwoLevel G ε E Vparts Wparts := by
  classical
  refine ⟨Finset.univ.image (fun v => ({v} : Finset V)), ?_, ?_, ?_, ?_⟩
  · exact hcoarse
  · -- refinement: each singleton sits inside the coarse block containing its point
    intro W hW
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨A, hA, hvA⟩ := hVcover v
    exact ⟨A, hA, Finset.singleton_subset_iff.mpr hvA⟩
  · -- equitability: all parts are singletons
    intro P Q hP hQ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ
    simp
  · -- zero irregular pairs: singleton pairs are always regular
    have hempty : ((Finset.univ.image (fun v => ({v} : Finset V))).product
        (Finset.univ.image (fun v => ({v} : Finset V)))).filter
          (fun pq => pq.1 ≠ pq.2 ∧
            ¬IsEpsilonRegular G (E Vparts.card) pq.1 pq.2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro pq hpq
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpq
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h1
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h2
      rintro ⟨-, hirr⟩
      exact hirr (hp ▸ hq ▸ isEpsilonRegular_singleton G hE p q)
    rw [hempty]
    have hk : (0 : ℚ) ≤ ((Finset.univ.image (fun v => ({v} : Finset V))).card : ℚ)
        * (((Finset.univ.image (fun v => ({v} : Finset V))).card : ℚ) - 1) := by
      rcases Nat.eq_zero_or_pos (Finset.univ.image (fun v => ({v} : Finset V))).card
        with h | h
      · rw [h]; norm_num
      · have h1 : (1 : ℚ) ≤ ((Finset.univ.image (fun v => ({v} : Finset V))).card : ℚ) := by
          exact_mod_cast h
        nlinarith
    simpa using mul_nonneg hε hk

/-- **The corrected (bounded) two-level target.**  The AFKS strong lemma
(Lemma 3.2 of the paper) bounds the number of fine parts by a function
`L = L(ε, |Vparts|)` independent of the vertex count.  Adding that clause
restores the mathematical content that the unbounded statement lacks — the
discrete witness of `exists_afksTwoLevel_discrete` has `n` parts and is excluded
as soon as `L < n`.

The S12–S27 oracle machinery targets exactly this statement: its mass-floor-`m`
invariant keeps `|Wparts| ≤ n/m` throughout the chain.  Producing an
`n`-independent `L` additionally requires the amplified (summed, mass-weighted)
energy increment recorded as the S28 blocker in the problem tracker. -/
structure IsAFKSTwoLevelBounded (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (L : ℕ) (Vparts Wparts : Finset (Finset V)) : Prop
    extends IsAFKSTwoLevel G ε E Vparts Wparts where
  /-- The fine partition has at most `L` parts — the clause carrying the actual
      content of the strong lemma. -/
  sizeBound : Wparts.card ≤ L

end Szemeredi.RegularityOQ04Discrete
