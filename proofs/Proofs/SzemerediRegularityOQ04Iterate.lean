/-
  Szemerédi Regularity OQ04 — S27b-i: block-family iteration of the ambient re-cut

  S27a (`SzemerediRegularityOQ04Surgery.lean`) produced the per-block brick
  `exists_equitable_recut_within`: one fiber `S ⊆ Q₀` of an ambient family gets
  re-cut in place to exact sizes {m, m+1} at ambient energy cost
  `2·|S|·m/n + 2·m²/n`, without moving any vertex across blocks.

  The Chain oracle's successor must be re-equitized over EVERY coarse block of
  `Vparts` simultaneously.  This file supplies that iteration:

  * `exists_equitable_recut_blocks` — Finset induction over a pairwise-disjoint
    block family `T`.  Given the per-block fiber mass floor `m² ≤ |⋃ fiber(A)|`,
    the ambient family `Q₀` is rebuilt so that every piece lying inside a block
    of `T` has size in {m, m+1}, pieces outside the `T`-blocks are untouched
    (fiber preservation), ground set and pairwise disjointness survive, and the
    total ambient energy loss telescopes to
    `∑_{A ∈ T} (2·|fiber(A)|·m/n + 2·m²/n)`.
    The induction invariant that makes the iteration compose: processing block
    `A` only touches pieces contained in `A`, so the fibers of the remaining
    (pairwise-disjoint) blocks are preserved *as Finsets*, keeping both their
    mass floors and their cost terms anchored to the ORIGINAL family `Q₀`.

  * `sum_fiber_card_le` / `recut_blocks_cost_le` — bookkeeping: distinct blocks
    have disjoint fibers (pieces are nonempty), so the summed fiber cost is at
    most `2·|Q₀|·m/n + 2·|T|·m²/n` — the `2|q'|m/n + 2|Vparts|m²/n` budget of
    the S27 plan.

  S27b-ii residual (next session): apply this to the bare-split successor of
  `exists_energy_next_of_not_afksFineRegular` (blocks `T = Vparts`, fibers of
  the refining successor), choose parameters so the loss stays below a retained
  fraction of the `ε⁴m²/n²` energy gain, and feed the resulting maintaining
  oracle into `exists_afksTwoLevel_of_maintained_oracle`.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Surgery

namespace Szemeredi.RegularityOQ04Iterate

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04MergeLoss
open Szemeredi.RegularityOQ04Recut Szemeredi.RegularityOQ04Absorb
open Szemeredi.RegularityOQ04ChopRefine Szemeredi.RegularityOQ04FullRefine
open Szemeredi.RegularityOQ04Surgery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Block-family iteration of the ambient equitable re-cut (S27b-i).**

Let `T` be a pairwise-disjoint family of coarse blocks and `Q₀` a
pairwise-disjoint ambient family with nonempty pieces, such that the fiber of
every block `A ∈ T` (the pieces of `Q₀` contained in `A`) has ground mass at
least `m²`.  Then `Q₀` can be rebuilt into `Q₁` with:

* the same ground set and pairwise disjointness, all pieces nonempty;
* every piece inside a block of `T` has size `m` or `m + 1`;
* the fiber of any set disjoint from all `T`-blocks is untouched
  (in particular pieces outside `⋃ T` survive verbatim);
* ambient energy loss at most `∑_{A ∈ T} (2·|fiber(A)|·m/n + 2·m²/n)`,
  every cost term anchored to the ORIGINAL fibers of `Q₀`.

Each step applies `exists_equitable_recut_within` to the (preserved) fiber of
the next block; disjointness of the blocks and nonemptiness of the pieces are
what keep the untouched fibers frozen. -/
theorem exists_equitable_recut_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (T Q₀ : Finset (Finset V))
    (hTdisj : (↑T : Set (Finset V)).PairwiseDisjoint id)
    (hQdisj : (↑Q₀ : Set (Finset V)).PairwiseDisjoint id)
    (hQne : ∀ c ∈ Q₀, c.Nonempty)
    (hfloor : ∀ A ∈ T, m * m ≤ ((Q₀.filter (· ⊆ A)).biUnion id).card) :
    ∃ Q₁ : Finset (Finset V),
      Q₁.biUnion id = Q₀.biUnion id ∧
      (↑Q₁ : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ Q₁, c.Nonempty) ∧
      (∀ A ∈ T, ∀ c ∈ Q₁, c ⊆ A → (c.card = m ∨ c.card = m + 1)) ∧
      (∀ B : Finset V, (∀ A ∈ T, Disjoint A B) →
          Q₁.filter (· ⊆ B) = Q₀.filter (· ⊆ B)) ∧
      partitionEnergy G Q₀ -
          ∑ A ∈ T, (2 * ((Q₀.filter (· ⊆ A)).card * m : ℚ) / (Fintype.card V : ℚ)
            + 2 * (m * m : ℚ) / (Fintype.card V : ℚ)) ≤
        partitionEnergy G Q₁ := by
  classical
  revert hTdisj hfloor
  induction T using Finset.induction_on with
  | empty =>
      intro _ _
      refine ⟨Q₀, rfl, hQdisj, hQne, ?_, fun B _ => rfl, by simp⟩
      intro A hA
      exact absurd hA (by simp)
  | @insert A T' hA ih =>
      intro hTdisj hfloor
      have hsubT' : (↑T' : Set (Finset V)) ⊆ (↑(insert A T') : Set (Finset V)) :=
        Finset.coe_subset.mpr (Finset.subset_insert A T')
      obtain ⟨Q', hQ'cov, hQ'disj, hQ'ne, hQ'sized, hQ'fib, hQ'pe⟩ :=
        ih (hTdisj.subset hsubT')
          (fun A' hA' => hfloor A' (Finset.mem_insert_of_mem hA'))
      -- `A` is disjoint from every block of `T'`
      have hAdisjT' : ∀ A' ∈ T', Disjoint A' A := by
        intro A' hA'
        have hne : A' ≠ A := by
          intro h
          exact hA (h ▸ hA')
        have := hTdisj (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hA'))
          (Finset.mem_coe.mpr (Finset.mem_insert_self A T')) hne
        simpa [Function.onFun] using this
      -- the fiber of `A` in `Q'` is untouched, so its floor and cost transfer
      have hfibA : Q'.filter (· ⊆ A) = Q₀.filter (· ⊆ A) := hQ'fib A hAdisjT'
      have hground : m * m ≤ ((Q'.filter (· ⊆ A)).biUnion id).card := by
        rw [hfibA]
        exact hfloor A (Finset.mem_insert_self A T')
      obtain ⟨R, hRcov, hRsize, hcov, hdisj₂, hpe₂⟩ :=
        exists_equitable_recut_within G m hm Q' (Q'.filter (· ⊆ A))
          (Finset.filter_subset _ _) hQ'disj hground
      -- pieces of `R` live inside `A` and are nonempty
      have hSA : (Q'.filter (· ⊆ A)).biUnion id ⊆ A :=
        Finset.biUnion_subset.mpr (fun c hc => (Finset.mem_filter.mp hc).2)
      have hRunion_A : R.biUnion id ⊆ A := by
        rw [hRcov]
        exact hSA
      have hR_in_A : ∀ c ∈ R, c ⊆ A := fun c hc =>
        (Finset.subset_biUnion_of_mem id hc).trans hRunion_A
      have hRne : ∀ c ∈ R, c.Nonempty := by
        intro c hc
        have hpos : 0 < c.card := by
          rcases hRsize c hc with h | h <;> omega
        exact Finset.card_pos.mp hpos
      refine ⟨(Q' \ Q'.filter (· ⊆ A)) ∪ R, ?_, hdisj₂, ?_, ?_, ?_, ?_⟩
      · rw [hcov]
        exact hQ'cov
      · intro c hc
        rcases Finset.mem_union.mp hc with h | h
        · exact hQ'ne c (Finset.mem_sdiff.mp h).1
        · exact hRne c h
      · intro A' hA' c hc hcA'
        rcases Finset.mem_insert.mp hA' with rfl | hA'mem
        · -- `A' = A`: survivors of `Q'` inside `A` would have been in the fiber
          rcases Finset.mem_union.mp hc with h | h
          · exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1, hcA'⟩)
              (Finset.mem_sdiff.mp h).2
          · exact hRsize c h
        · rcases Finset.mem_union.mp hc with h | h
          · exact hQ'sized A' hA'mem c (Finset.mem_sdiff.mp h).1 hcA'
          · -- a piece of `R` sits inside `A`, hence not inside the disjoint `A'`
            obtain ⟨x, hx⟩ := hRne c h
            exact absurd (hcA' hx)
              (Finset.disjoint_right.mp (hAdisjT' A' hA'mem) (hR_in_A c h hx))
      · intro B hB
        have hAB : Disjoint A B := hB A (Finset.mem_insert_self A T')
        have hB' : Q'.filter (· ⊆ B) = Q₀.filter (· ⊆ B) :=
          hQ'fib B (fun A' hA' => hB A' (Finset.mem_insert_of_mem hA'))
        rw [← hB']
        ext c
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨h | h, hcB⟩
          · exact ⟨h.1, hcB⟩
          · obtain ⟨x, hx⟩ := hRne c h
            exact absurd (hcB hx) (Finset.disjoint_left.mp hAB (hR_in_A c h hx))
        · rintro ⟨hcQ', hcB⟩
          refine ⟨Or.inl ⟨hcQ', ?_⟩, hcB⟩
          rintro ⟨-, hcA⟩
          obtain ⟨x, hx⟩ := hQ'ne c hcQ'
          exact absurd (hcB hx) (Finset.disjoint_left.mp hAB (hcA hx))
      · rw [Finset.sum_insert hA]
        rw [show ((Q'.filter (· ⊆ A)).card : ℚ) = ((Q₀.filter (· ⊆ A)).card : ℚ) from
          by rw [hfibA]] at hpe₂
        linarith [hQ'pe, hpe₂]

omit [Fintype V] in
/-- **Disjoint blocks have disjoint fibers.**  Since pieces are nonempty and
the blocks of `T` are pairwise disjoint, a piece of `Q₀` lies in the fiber of
at most one block, so the fiber cardinalities sum to at most `|Q₀|`. -/
theorem sum_fiber_card_le (T Q₀ : Finset (Finset V))
    (hTdisj : (↑T : Set (Finset V)).PairwiseDisjoint id)
    (hQne : ∀ c ∈ Q₀, c.Nonempty) :
    ∑ A ∈ T, (Q₀.filter (· ⊆ A)).card ≤ Q₀.card := by
  classical
  have hdisj : ∀ A ∈ T, ∀ A' ∈ T, A ≠ A' →
      Disjoint (Q₀.filter (· ⊆ A)) (Q₀.filter (· ⊆ A')) := by
    intro A hAmem A' hA'mem hne
    rw [Finset.disjoint_left]
    intro c hc hc'
    have hcA : c ⊆ A := (Finset.mem_filter.mp hc).2
    have hcA' : c ⊆ A' := (Finset.mem_filter.mp hc').2
    obtain ⟨x, hx⟩ := hQne c (Finset.mem_filter.mp hc).1
    have hd : Disjoint A A' := by
      have := hTdisj (Finset.mem_coe.mpr hAmem) (Finset.mem_coe.mpr hA'mem) hne
      simpa [Function.onFun] using this
    exact absurd (hcA' hx) (Finset.disjoint_left.mp hd (hcA hx))
  calc ∑ A ∈ T, (Q₀.filter (· ⊆ A)).card
      = (T.biUnion (fun A => Q₀.filter (· ⊆ A))).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Q₀.card := Finset.card_le_card (Finset.biUnion_subset.mpr
        (fun A _ => Finset.filter_subset _ _))

/-- **Total cost budget (S27b-i bookkeeping).**  The summed per-block cost of
`exists_equitable_recut_blocks` is at most `2·|Q₀|·m/n + 2·|T|·m²/n` — the
`2|q'|m/n + 2|Vparts|m²/n` budget of the S27 plan. -/
theorem recut_blocks_cost_le (m : ℕ) (T Q₀ : Finset (Finset V))
    (hTdisj : (↑T : Set (Finset V)).PairwiseDisjoint id)
    (hQne : ∀ c ∈ Q₀, c.Nonempty) :
    ∑ A ∈ T, (2 * ((Q₀.filter (· ⊆ A)).card * m : ℚ) / (Fintype.card V : ℚ)
        + 2 * (m * m : ℚ) / (Fintype.card V : ℚ)) ≤
      2 * (Q₀.card * m : ℚ) / (Fintype.card V : ℚ)
        + 2 * (T.card * (m * m) : ℚ) / (Fintype.card V : ℚ) := by
  classical
  have hsumQ : (∑ A ∈ T, ((Q₀.filter (· ⊆ A)).card : ℚ)) ≤ (Q₀.card : ℚ) := by
    exact_mod_cast sum_fiber_card_le T Q₀ hTdisj hQne
  rw [Finset.sum_add_distrib]
  have h1 : ∑ A ∈ T, 2 * (((Q₀.filter (· ⊆ A)).card : ℚ) * m) / (Fintype.card V : ℚ)
      ≤ 2 * ((Q₀.card : ℚ) * m) / (Fintype.card V : ℚ) := by
    have hterm : ∀ A : Finset V,
        2 * (((Q₀.filter (· ⊆ A)).card : ℚ) * m) / (Fintype.card V : ℚ)
          = ((Q₀.filter (· ⊆ A)).card : ℚ) * (2 * (m : ℚ) / (Fintype.card V : ℚ)) := by
      intro A
      ring
    simp only [hterm]
    rw [← Finset.sum_mul]
    have h2m : (0 : ℚ) ≤ 2 * (m : ℚ) / (Fintype.card V : ℚ) := by positivity
    calc (∑ A ∈ T, ((Q₀.filter (· ⊆ A)).card : ℚ))
          * (2 * (m : ℚ) / (Fintype.card V : ℚ))
        ≤ (Q₀.card : ℚ) * (2 * (m : ℚ) / (Fintype.card V : ℚ)) :=
          mul_le_mul_of_nonneg_right hsumQ h2m
      _ = 2 * ((Q₀.card : ℚ) * m) / (Fintype.card V : ℚ) := by ring
  have h2 : (∑ _A ∈ T, 2 * (m * m : ℚ) / (Fintype.card V : ℚ))
      = 2 * ((T.card : ℚ) * ((m : ℚ) * m)) / (Fintype.card V : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h2]
  exact add_le_add h1 le_rfl

end Szemeredi.RegularityOQ04Iterate
