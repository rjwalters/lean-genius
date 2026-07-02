/-
  Caro–Wei Lower Bound for the Independence Number (verified, 0-axiom)

  Open Question OQ-03 from prob-method-alteration:
  "Prove the Caro–Wei bound α(G) ≥ ∑_v 1/(deg(v)+1) for a finite simple graph G,
   then deduce the Turán-type corollary α(G) ≥ n²/(2m+n) by convexity on the
   degree sequence."

  This DE-AXIOMATIZES the bound `α(G) ≥ n²/(2m+n)` that was previously stated as an
  `axiom caro_wei` in `ProbMethodAlterationOQ02.lean`.

  Rather than the usual random-permutation / expectation argument, we give the
  fully constructive **deterministic** proof:

    Induct on the vertex set W.  Pick a vertex v ∈ W of MINIMUM degree (within W),
    let N = N_W[v] be its closed neighbourhood in W (|N| = deg_W(v)+1), and delete N.
    A maximum independent set of W \ N, together with v, is independent in W, so
    α(W) ≥ 1 + α(W \ N).  The weight lost by deleting N is
        ∑_{u ∈ N} 1/(deg_W(u)+1) ≤ |N| · 1/(deg_W(v)+1) = 1,
    because every u ∈ N has deg_W(u) ≥ deg_W(v) (v is a minimum-degree vertex).
    Deleting a vertex can only lower the remaining degrees, so the surviving weights
    only increase.  Induction closes the bound.

  The Turán corollary follows from the Cauchy–Schwarz (AM–HM) inequality
        n² = (∑ 1)² ≤ (∑ (deg v + 1)) · (∑ 1/(deg v + 1)) = (2m + n) · S
  together with the handshake identity ∑ deg v = 2m.

  Status: verified, 0 axioms (only Lean/Mathlib foundations).
-/

import Mathlib

namespace ProbMethod.CaroWei

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independence number `α(G)`: the size of the largest independent set.
    (Identical to the definition in `ProbMethodAlterationOQ02`.) -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ s : Finset V, s.card = k ∧
    ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ¬G.Adj v w }

/-- Degree of `u` counted only within the finset `W`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (u : V) : ℕ :=
  (W.filter (fun w => G.Adj u w)).card

/-- Restricting to a smaller vertex set can only decrease the degree. -/
theorem degIn_mono (G : SimpleGraph V) [DecidableRel G.Adj] {W' W : Finset V}
    (h : W' ⊆ W) (u : V) : degIn G W' u ≤ degIn G W u :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Core existence lemma.**  For every finset `W`, there is an independent set
    `I ⊆ W` whose size is at least the Caro–Wei weight `∑_{u∈W} 1/(deg_W(u)+1)`. -/
theorem exists_indep_card_ge (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    ∃ I : Finset V, I ⊆ W ∧ (∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ G.Adj a b) ∧
      (∑ u ∈ W, (1 : ℝ) / ((degIn G W u : ℝ) + 1)) ≤ (I.card : ℝ) := by
  induction W using Finset.strongInductionOn with
  | _ W ih =>
    rcases W.eq_empty_or_nonempty with hW | hWne
    · exact ⟨∅, by simp [hW], by simp, by simp [hW]⟩
    · -- Pick a vertex `v` of minimum degree in `W`.
      obtain ⟨v, hvW, hvmin⟩ := W.exists_min_image (degIn G W) hWne
      -- Closed neighbourhood of `v` inside `W`.
      set Nb : Finset V := W.filter (fun w => G.Adj v w) with hNb
      set N : Finset V := insert v Nb with hN
      set W' : Finset V := W \ N with hW'
      have hv_notNb : v ∉ Nb := by
        rw [hNb, Finset.mem_filter]; rintro ⟨_, hadj⟩; exact (G.irrefl hadj)
      have hNb_sub : Nb ⊆ W := Finset.filter_subset _ _
      have hNW : N ⊆ W := by rw [hN]; exact Finset.insert_subset_iff.mpr ⟨hvW, hNb_sub⟩
      have hNcard : N.card = degIn G W v + 1 := by
        rw [hN, Finset.card_insert_of_not_mem hv_notNb, hNb]; rfl
      have hNne : N.Nonempty := ⟨v, by rw [hN]; exact Finset.mem_insert_self _ _⟩
      have hW'ss : W' ⊂ W := by rw [hW']; exact Finset.sdiff_ssubset hNW hNne
      -- Induction hypothesis on the strictly smaller `W'`.
      obtain ⟨I', hI'sub, hI'indep, hI'card⟩ := ih W' hW'ss
      -- Facts about members of `I'` (they lie in `W`, off `N`, hence not adjacent to `v`).
      have hI'W : I' ⊆ W := hI'sub.trans (by rw [hW']; exact Finset.sdiff_subset)
      have hmem : ∀ b ∈ I', b ∈ W ∧ ¬ G.Adj v b ∧ b ≠ v := by
        intro b hb
        have hbW' : b ∈ W' := hI'sub hb
        rw [hW', Finset.mem_sdiff, hN, Finset.mem_insert, not_or] at hbW'
        obtain ⟨hbW, hbne, hbNb⟩ := hbW'
        rw [hNb, Finset.mem_filter] at hbNb
        refine ⟨hbW, fun hadj => hbNb ⟨hbW, hadj⟩, hbne⟩
      -- `v ∉ I'`, so inserting `v` grows the card by exactly one.
      have hv_notI' : v ∉ I' := by
        intro h
        have hvW' := hI'sub h
        rw [hW', Finset.mem_sdiff] at hvW'
        exact hvW'.2 (hN ▸ Finset.mem_insert_self v Nb)
      refine ⟨insert v I', ?_, ?_, ?_⟩
      · -- `insert v I' ⊆ W`.
        exact Finset.insert_subset_iff.mpr ⟨hvW, hI'W⟩
      · -- `insert v I'` is independent.
        intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | haI'
        · rcases hb with rfl | hbI'
          · exact absurd rfl hab
          · exact (hmem b hbI').2.1
        · rcases hb with rfl | hbI'
          · exact fun hadj => (hmem a haI').2.1 (G.symm hadj)
          · exact hI'indep a haI' b hbI' hab
      · -- The weight bound.
        have hcard_eq : ((insert v I').card : ℝ) = (I'.card : ℝ) + 1 := by
          rw [Finset.card_insert_of_not_mem hv_notI']; push_cast; ring
        rw [hcard_eq]
        -- Split the sum over `W` as `W' + N`.
        have hsplit : (∑ u ∈ W, (1 : ℝ) / ((degIn G W u : ℝ) + 1))
            = (∑ u ∈ W', (1 : ℝ) / ((degIn G W u : ℝ) + 1))
              + (∑ u ∈ N, (1 : ℝ) / ((degIn G W u : ℝ) + 1)) := by
          rw [hW', ← Finset.sum_sdiff hNW]
        -- (a) Surviving weights only increase under deletion.
        have hstep2 : (∑ u ∈ W', (1 : ℝ) / ((degIn G W u : ℝ) + 1))
            ≤ (∑ u ∈ W', (1 : ℝ) / ((degIn G W' u : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro u _
          have hle : degIn G W' u ≤ degIn G W u :=
            degIn_mono G (by rw [hW']; exact Finset.sdiff_subset) u
          apply one_div_le_one_div_of_le
          · positivity
          · have : (degIn G W' u : ℝ) ≤ (degIn G W u : ℝ) := by exact_mod_cast hle
            linarith
        -- (b) The deleted weight is at most 1.
        have hstep3 : (∑ u ∈ N, (1 : ℝ) / ((degIn G W u : ℝ) + 1)) ≤ 1 := by
          have hbound : (∑ u ∈ N, (1 : ℝ) / ((degIn G W u : ℝ) + 1))
              ≤ (∑ _u ∈ N, (1 : ℝ) / ((degIn G W v : ℝ) + 1)) := by
            apply Finset.sum_le_sum
            intro u hu
            have huW : u ∈ W := hNW hu
            have : (degIn G W v : ℝ) ≤ (degIn G W u : ℝ) := by
              exact_mod_cast hvmin u huW
            apply one_div_le_one_div_of_le
            · positivity
            · linarith
          refine hbound.trans (le_of_eq ?_)
          rw [Finset.sum_const, hNcard, nsmul_eq_mul]
          have h1 : ((degIn G W v + 1 : ℕ) : ℝ) = (degIn G W v : ℝ) + 1 := by
            push_cast; ring
          rw [h1, mul_one_div, div_self (by positivity)]
        -- Combine (split) ≤ (a) + (b) ≤ I'.card + 1.
        calc (∑ u ∈ W, (1 : ℝ) / ((degIn G W u : ℝ) + 1))
            = (∑ u ∈ W', (1 : ℝ) / ((degIn G W u : ℝ) + 1))
              + (∑ u ∈ N, (1 : ℝ) / ((degIn G W u : ℝ) + 1)) := hsplit
          _ ≤ (∑ u ∈ W', (1 : ℝ) / ((degIn G W' u : ℝ) + 1)) + 1 := by
                gcongr
          _ ≤ (I'.card : ℝ) + 1 := by linarith [hI'card]

/-- `degIn G univ = G.degree`. -/
theorem degIn_univ (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    degIn G Finset.univ u = G.degree u := by
  rw [degIn, SimpleGraph.degree]
  congr 1
  ext w
  rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **Caro–Wei bound (weighted form).**  For any finite simple graph `G`,
    `∑_v 1/(deg(v)+1) ≤ α(G)`. -/
theorem caro_wei_weighted (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (independenceNumber G : ℝ) := by
  obtain ⟨I, hIsub, hIindep, hIcard⟩ := exists_indep_card_ge G Finset.univ
  -- Rewrite the sum using `degIn univ = degree`.
  have hsum : (∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1))
      = ∑ u ∈ Finset.univ, (1 : ℝ) / ((degIn G Finset.univ u : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro u _; rw [degIn_univ]
  rw [hsum]
  refine hIcard.trans ?_
  -- `I.card ≤ α(G)` since `I` is an independent set.
  have hbdd : BddAbove { k : ℕ | ∃ s : Finset V, s.card = k ∧
      ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ¬G.Adj v w } := by
    refine ⟨Fintype.card V, ?_⟩
    rintro k ⟨s, rfl, _⟩
    exact Finset.card_le_univ s
  have hmem : I.card ∈ { k : ℕ | ∃ s : Finset V, s.card = k ∧
      ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ¬G.Adj v w } := ⟨I, rfl, hIindep⟩
  have : I.card ≤ independenceNumber G := le_csSup hbdd hmem
  exact_mod_cast this

/-- **Caro–Wei / Turán bound.**  De-axiomatizes `ProbMethodAlterationOQ02.caro_wei`:
    for a finite simple graph `G` on `n` vertices with `m` edges,
    `n²/(2m+n) ≤ α(G)`. -/
theorem caro_wei {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (hm : m = G.edgeFinset.card) (hpos : 0 < 2 * m + n) :
    (n : ℝ) ^ 2 / (2 * m + n) ≤ (independenceNumber G : ℝ) := by
  set S : ℝ := ∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1) with hS
  -- Denominators are positive.
  have hpos' : ∀ v : Fin n, (0 : ℝ) < (G.degree v : ℝ) + 1 := fun v => by positivity
  -- ∑ (deg v + 1) = 2m + n  (handshake identity).
  have hsum_deg : (∑ v : Fin n, ((G.degree v : ℝ) + 1)) = 2 * m + n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hhand : ∑ v : Fin n, G.degree v = 2 * G.edgeFinset.card :=
      SimpleGraph.sum_degrees_eq_twice_card_edges G
    have : (∑ v : Fin n, (G.degree v : ℝ)) = 2 * (m : ℝ) := by
      rw [← Nat.cast_sum, hhand, hm]; push_cast; ring
    rw [this]; push_cast; ring
  -- Cauchy–Schwarz: n² ≤ (∑ (deg+1)) · S.
  have hCS : ((n : ℝ)) ^ 2 ≤ (2 * m + n) * S := by
    -- Use the Finset Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq`.
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v : Fin n => Real.sqrt ((G.degree v : ℝ) + 1))
      (fun v : Fin n => (Real.sqrt ((G.degree v : ℝ) + 1))⁻¹)
    -- Simplify the three sums appearing in `cs`.
    have hfg : ∀ v : Fin n,
        Real.sqrt ((G.degree v : ℝ) + 1) * (Real.sqrt ((G.degree v : ℝ) + 1))⁻¹ = 1 := by
      intro v
      have : Real.sqrt ((G.degree v : ℝ) + 1) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (hpos' v)
      field_simp
    have hf2 : ∀ v : Fin n,
        (Real.sqrt ((G.degree v : ℝ) + 1)) ^ 2 = (G.degree v : ℝ) + 1 := by
      intro v; rw [Real.sq_sqrt (hpos' v).le]
    have hg2 : ∀ v : Fin n,
        ((Real.sqrt ((G.degree v : ℝ) + 1))⁻¹) ^ 2 = (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
      intro v
      rw [inv_pow, Real.sq_sqrt (hpos' v).le, one_div]
    rw [Finset.sum_congr rfl (fun v _ => hfg v),
        Finset.sum_congr rfl (fun v _ => hf2 v),
        Finset.sum_congr rfl (fun v _ => hg2 v)] at cs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at cs
    rw [hsum_deg, ← hS] at cs
    exact cs
  -- Turn `n² ≤ (2m+n)·S` into the division form, then chain with the weighted bound.
  have hden : (0 : ℝ) < 2 * m + n := by exact_mod_cast hpos
  have hdiv : (n : ℝ) ^ 2 / (2 * m + n) ≤ S := by
    rw [div_le_iff₀ hden]; linarith [hCS]
  exact hdiv.trans (caro_wei_weighted G)

end ProbMethod.CaroWei
