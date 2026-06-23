/-
  Aristotle targets for SzemerediCoreOQ01
  Energy increment step — Finset.sum packaging for refined partition.
  See SzemerediCoreOQ01.lean for the main formalization.

  Infrastructure status (updated 2026-04-05, Session 4):
  - four_subpair_edge_count_identity: PROVED
  - four_subpair_deviation_identity: PROVED
  - four_subpair_excess_lb: PROVED
  - partitionEnergy_term_nonneg: PROVED
  - partitionEnergy_mono: PROVED
  - energy_increment_packaging_ari: COMPLETE PROOF ATTEMPT (Session 4)
      Strategy: block decomposition via Finset.sum_union (×2)
      SS blocks cancel; ST≥SAB via density_sq_convex_right;
      TS≥ABS via density_sq_convex; TT≥ABAB+eps^6 via four_subpair_excess_lb+hcore
      All three sub-goals proved via nlinarith with explicit hints.
      Pending: Lean type-checker verification (docker build)
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediCoreOQ01

namespace Szemeredi.EnergyIncrement.Aristotle

open Classical Szemeredi.Core Szemeredi.EnergyIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: MONOTONICITY LEMMAS (PROVED)
-- ═══════════════════════════════════════════════════════════════════

/-- Each term in the partitionEnergy sum is non-negative. -/
lemma partitionEnergy_term_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) :
    0 ≤ (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 *
        (edgeDensity G P Q) ^ 2 :=
  mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
    (sq_nonneg _)

/-- **partitionEnergy is monotone** under Finset superset. -/
lemma partitionEnergy_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset (Finset V)) (hPQ : P ⊆ Q) :
    partitionEnergy G Q ≥ partitionEnergy G P := by
  unfold partitionEnergy; simp only
  split_ifs with h
  · exact le_refl 0
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.product_subset_product hPQ hPQ
    · intro pq _ _
      exact mul_nonneg
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
        (sq_nonneg _)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: MAIN ARISTOTLE TARGET
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy increment packaging** — main Aristotle target.

    Show that the refined partition `S ∪ {A',A₂,B',B₂}` (where S = parts\{A,B})
    has energy ≥ energy(parts) + eps^6. -/
theorem energy_increment_packaging_ari
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (parts : Finset (Finset V))
    (hparts_disj : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (A B : Finset V) (hA : A ∈ parts) (hB : B ∈ parts) (hAB : A ≠ B)
    (A' B' : Finset V)
    (hA'sub : A' ⊆ A) (hB'sub : B' ⊆ B)
    (hAd : Disjoint A' (A \ A')) (hBd : Disjoint B' (B \ B'))
    (hAu : A' ∪ (A \ A') = A) (hBu : B' ∪ (B \ B') = B)
    (hA'pos : 0 < A'.card) (hA₂pos : 0 < (A \ A').card)
    (hB'pos : 0 < B'.card) (hB₂pos : 0 < (B \ B').card)
    (hcore : (A'.card : ℚ) * B'.card *
             (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
             eps ^ 6 * (Fintype.card V : ℚ) ^ 2) :
    let A₂ := A \ A'; let B₂ := B \ B'
    let S := (parts.erase B).erase A
    partitionEnergy G (S ∪ {A', A₂, B', B₂}) ≥
      partitionEnergy G parts + eps ^ 6 := by
  intro A₂ B₂ S

  -- ── n > 0 ────────────────────────────────────────────────────────
  have hn_pos : (0 : ℚ) < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
    · exact absurd (Nat.le_zero.mp ((Finset.card_le_univ A').trans hV.le) ▸ hA'pos)
        (lt_irrefl 0)
    · exact_mod_cast hV
  have hn : (Fintype.card V : ℚ) ≠ 0 := ne_of_gt hn_pos

  -- ── S ∪ {A, B} = parts ──────────────────────────────────────────
  -- S = (parts.erase B).erase A, so S ∪ {A,B} recovers all of parts.
  have hSAB : S ∪ ({A, B} : Finset (Finset V)) = parts := by
    ext X; constructor
    · intro hX
      rcases Finset.mem_union.mp hX with hXS | hXAB
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hXAB
        rcases hXAB with hXeqA | hXeqB
        · exact hXeqA ▸ hA
        · exact hXeqB ▸ hB
    · intro hXparts
      rw [Finset.mem_union]
      by_cases hXA : X = A
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl hXA))
      · by_cases hXB : X = B
        · exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hXB)))
        · exact Or.inl
            (Finset.mem_erase.mpr ⟨hXA, Finset.mem_erase.mpr ⟨hXB, hXparts⟩⟩)

  -- ── Disjoint S {A, B} ───────────────────────────────────────────
  have hSAB_disj : Disjoint S ({A, B} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXAB
    have hXneA : X ≠ A := (Finset.mem_erase.mp hXS).1
    have hXneB : X ≠ B := (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXAB
    rcases hXAB with hXeqA | hXeqB
    · exact hXneA hXeqA
    · exact hXneB hXeqB

  -- ── ne facts: A' ≠ A, A₂ ≠ A, B' ≠ B, B₂ ≠ B ──────────────────
  -- A' ≠ A: if A' = A then A₂ = A \ A = ∅, contradicting hA₂pos
  have hA'neA : A' ≠ A := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
    exact (Finset.mem_sdiff.mp hx).2 (heq ▸ (Finset.mem_sdiff.mp hx).1)
  -- A₂ ≠ A: if A₂ = A then A' ⊆ A₂ = A \ A', so A' = ∅, contradicting hA'pos
  have hA₂neA : A₂ ≠ A := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact (Finset.mem_sdiff.mp (heq ▸ hA'sub hx)).2 hx
  -- B' ≠ B: symmetric
  have hB'neB : B' ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB₂pos
    exact (Finset.mem_sdiff.mp hx).2 (heq ▸ (Finset.mem_sdiff.mp hx).1)
  -- B₂ ≠ B: symmetric
  have hB₂neB : B₂ ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
    exact (Finset.mem_sdiff.mp (heq ▸ hB'sub hx)).2 hx

  -- ── Disjoint S {A', A₂, B', B₂} ────────────────────────────────
  -- Each of A', A₂, B', B₂ is a strict subset of A or B.
  -- If X ∈ S ∩ T: X ∈ parts and X ⊊ A (or B).
  -- hparts_disj gives Disjoint X A. But X ⊆ A → X = ∅ → contradicts positivity.
  have hST_disj : Disjoint S ({A', A₂, B', B₂} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXT
    have hXparts : X ∈ parts :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXT
    -- Each case: X is a strict subset of A or B, contradicting partition disjointness
    rcases hXT with hXA' | hXA₂ | hXB' | hXB₂
    · -- X = A' ⊆ A, A' ∈ parts, A' ≠ A → Disjoint X A, but X ⊆ A → ↯
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
      rw [hXA'] at hXparts
      exact absurd (hA'sub hx)
        (Finset.disjoint_left.mp (hparts_disj A' A hXparts hA hA'neA) hx)
    · -- X = A₂ = A \ A' ⊆ A → same
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
      rw [hXA₂] at hXparts
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj A₂ A hXparts hA hA₂neA) hx)
    · -- X = B' ⊆ B → same with B
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
      rw [hXB'] at hXparts
      exact absurd (hB'sub hx)
        (Finset.disjoint_left.mp (hparts_disj B' B hXparts hB hB'neB) hx)
    · -- X = B₂ = B \ B' ⊆ B → same
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hB₂pos
      rw [hXB₂] at hXparts
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj B₂ B hXparts hB hB₂neB) hx)

  -- ── Card facts ───────────────────────────────────────────────────
  have hcard_A : A'.card + (A \ A').card = A.card := by
    have h := Finset.card_union_of_disjoint hAd; rw [hAu] at h; omega
  have hcard_B : B'.card + (B \ B').card = B.card := by
    have h := Finset.card_union_of_disjoint hBd; rw [hBu] at h; omega

  -- ── Rewrite: energy(parts) = energy(S ∪ {A,B}) ──────────────────
  rw [← hSAB]

  -- ── Additional distinctness facts ────────────────────────────────
  have hAB_disj : Disjoint A B := hparts_disj A B hA hB hAB
  -- A' ≠ A₂: if A' = A₂ then Disjoint A' A' (via mono_right), card_union gives contradiction
  have hA'A₂_ne : A' ≠ A₂ := by
    intro heq
    have hself : Disjoint A' A' := hAd.mono_right (le_of_eq heq)
    have h1 := Finset.card_union_of_disjoint hself
    rw [Finset.union_self] at h1; omega
  have hB'B₂_ne : B' ≠ B₂ := by
    intro heq
    have hself : Disjoint B' B' := hBd.mono_right (le_of_eq heq)
    have h1 := Finset.card_union_of_disjoint hself
    rw [Finset.union_self] at h1; omega
  have hA'B'_ne : A' ≠ B' := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd (hB'sub (h ▸ hx)) (Finset.disjoint_left.mp hAB_disj (hA'sub hx))
  have hA'B₂_ne : A' ≠ B₂ := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd (Finset.mem_sdiff.mp (h ▸ hx)).1
      (Finset.disjoint_left.mp hAB_disj (hA'sub hx))
  -- A₂ ≠ B': use explicit x ∈ A₂ intermediate to make ▸ work
  have hA₂B'_ne : A₂ ≠ B' := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
    have hxA₂ : x ∈ A₂ := hx
    exact absurd (hB'sub (h ▸ hxA₂))
      (Finset.disjoint_left.mp hAB_disj (Finset.mem_sdiff.mp hxA₂).1)
  -- A₂ ≠ B₂: same explicit intermediate approach
  have hA₂B₂_ne : A₂ ≠ B₂ := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
    have hxA₂ : x ∈ A₂ := hx
    have hxB₂ : x ∈ B₂ := h ▸ hxA₂
    exact absurd (Finset.mem_sdiff.mp hxA₂).1
      (Finset.disjoint_right.mp hAB_disj (Finset.mem_sdiff.mp hxB₂).1)
  -- Non-membership for sum expansion of T = {A', A₂, B', B₂}
  have hA'_nm : A' ∉ ({A₂, B', B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hA'A₂_ne (fun h => h.elim hA'B'_ne hA'B₂_ne)
  have hA₂_nm : A₂ ∉ ({B', B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hA₂B'_ne hA₂B₂_ne
  have hB'_nm : B' ∉ ({B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_singleton]; exact hB'B₂_ne
  have hA_nm : A ∉ ({B} : Finset (Finset V)) := by
    simp only [Finset.mem_singleton]; exact hAB

  -- ── Term function ef P Q = |P|·|Q|/n² · d(P,Q)² ─────────────────
  let ef : Finset V → Finset V → ℚ := fun P Q =>
    (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G P Q) ^ 2
  -- Helper to unfold ef (unfold_let not available in this Lean version)
  have ef_def : ∀ P Q : Finset V, ef P Q =
      ↑P.card * ↑Q.card / ↑(Fintype.card V) ^ 2 * (edgeDensity G P Q) ^ 2 :=
    fun _ _ => rfl

  -- ── Unfold partitionEnergy to nested double sums ──────────────────
  have pe_eq : ∀ R : Finset (Finset V),
      partitionEnergy G R = R.sum (fun P => R.sum (fun Q => ef P Q)) := by
    intro R
    unfold partitionEnergy
    simp only [if_neg hn]
    rw [show R.product R = R ×ˢ R from rfl, Finset.sum_product]
    apply Finset.sum_congr rfl; intro P _
    apply Finset.sum_congr rfl; intro Q _
    simp only [Prod.fst, Prod.snd, ef_def]
  simp only [pe_eq]

  -- ── Block decomposition helper ────────────────────────────────────
  -- For disjoint X Y: ∑_{P∈X∪Y} ∑_{Q∈X∪Y} f = ∑_XX + ∑_XY + ∑_YX + ∑_YY
  have block_split : ∀ (X Y : Finset (Finset V)) (hd : Disjoint X Y),
      ∑ P ∈ X ∪ Y, ∑ Q ∈ X ∪ Y, ef P Q =
      (∑ P ∈ X, ∑ Q ∈ X, ef P Q) + (∑ P ∈ X, ∑ Q ∈ Y, ef P Q) +
      ((∑ P ∈ Y, ∑ Q ∈ X, ef P Q) + ∑ P ∈ Y, ∑ Q ∈ Y, ef P Q) := by
    intro X Y hd
    rw [Finset.sum_union hd]
    have split_inner : ∀ P, ∑ Q ∈ X ∪ Y, ef P Q = ∑ Q ∈ X, ef P Q + ∑ Q ∈ Y, ef P Q :=
      fun P => Finset.sum_union hd
    simp_rw [split_inner, Finset.sum_add_distrib]

  rw [block_split _ _ hST_disj, block_split _ _ hSAB_disj]

  -- ── Reduce to: ST + TS + TT ≥ SAB + ABS + ABAB + eps^6 ──────────
  -- (the SS blocks are equal and cancel)
  suffices key :
      (∑ P ∈ S, ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q) +
      ((∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ∑ Q ∈ S, ef P Q) +
       ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)),
         ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q) ≥
      (∑ P ∈ S, ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q) +
      ((∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ S, ef P Q) +
       ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q) +
      eps ^ 6 by linarith

  -- ── ST ≥ SAB ─────────────────────────────────────────────────────
  -- For each P∈S, ∑_{Q∈T} ef PQ ≥ ∑_{Q∈AB} ef PQ by convexity.
  have hST : ∑ P ∈ S, ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q ≥
      ∑ P ∈ S, ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q := by
    apply Finset.sum_le_sum; intro P _
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    -- need: ef PA' + (ef PA₂ + (ef PB' + ef PB₂)) ≥ ef PA + ef PB
    have hcA := density_sq_convex_right G P A' A₂ hAd
    have hcB := density_sq_convex_right G P B' B₂ hBd
    have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
    have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
    -- hcA: A'.card*d(P,A')² + A₂.card*d(P,A₂)² ≥ (A'.card+A₂.card)*d(P,A'∪A₂)²
    -- ef PA' + ef PA₂ = P.card/n² * (A'.card*d(P,A')² + A₂.card*d(P,A₂)²)
    -- ef PA = P.card/n² * A.card * d(P,A)² = P.card/n² * (A'.card+A₂.card) * d(P,A'∪A₂)²
    have hPnn : (0 : ℚ) ≤ (P.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
    simp only [ef_def]
    push_cast
    rw [← hAu, ← hBu, ← hAcard, ← hBcard]
    nlinarith [hcA, hcB, sq_nonneg (edgeDensity G P A'), sq_nonneg (edgeDensity G P A₂),
               sq_nonneg (edgeDensity G P B'), sq_nonneg (edgeDensity G P B₂),
               sq_nonneg (edgeDensity G P (A' ∪ A₂)), sq_nonneg (edgeDensity G P (B' ∪ B₂)),
               Nat.cast_nonneg (α := ℚ) P.card, Nat.cast_nonneg (α := ℚ) A'.card,
               Nat.cast_nonneg (α := ℚ) A₂.card, Nat.cast_nonneg (α := ℚ) B'.card,
               Nat.cast_nonneg (α := ℚ) B₂.card, sq_nonneg (Fintype.card V : ℚ)]

  -- ── TS ≥ ABS ─────────────────────────────────────────────────────
  -- Expand T and AB sums explicitly, then use density_sq_convex.
  have hTS : ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ∑ Q ∈ S, ef P Q ≥
      ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ S, ef P Q := by
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    -- Need: (∑Q∈S, ef A' Q) + ((∑Q∈S, ef A₂ Q) + ((∑Q∈S, ef B' Q) + ∑Q∈S, ef B₂ Q))
    --     ≥ (∑Q∈S, ef A Q) + ∑Q∈S, ef B Q
    -- By Finset.sum_le_sum: (∑Q∈S, ef A' Q) + (∑Q∈S, ef A₂ Q) ≥ ∑Q∈S, ef A Q
    have hA_rows : (∑ Q ∈ S, ef A' Q) + (∑ Q ∈ S, ef A₂ Q) ≥ ∑ Q ∈ S, ef A Q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro Q _
      have hcA := density_sq_convex G A' A₂ Q hAd
      have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
      simp only [ef_def]; push_cast
      rw [← hAu, ← hAcard]
      nlinarith [hcA, sq_nonneg (edgeDensity G A' Q), sq_nonneg (edgeDensity G A₂ Q),
                 Nat.cast_nonneg (α := ℚ) Q.card, Nat.cast_nonneg (α := ℚ) A'.card,
                 Nat.cast_nonneg (α := ℚ) A₂.card, sq_nonneg (Fintype.card V : ℚ)]
    have hB_rows : (∑ Q ∈ S, ef B' Q) + (∑ Q ∈ S, ef B₂ Q) ≥ ∑ Q ∈ S, ef B Q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro Q _
      have hcB := density_sq_convex G B' B₂ Q hBd
      have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
      simp only [ef_def]; push_cast
      rw [← hBu, ← hBcard]
      nlinarith [hcB, sq_nonneg (edgeDensity G B' Q), sq_nonneg (edgeDensity G B₂ Q),
                 Nat.cast_nonneg (α := ℚ) Q.card, Nat.cast_nonneg (α := ℚ) B'.card,
                 Nat.cast_nonneg (α := ℚ) B₂.card, sq_nonneg (Fintype.card V : ℚ)]
    linarith [Finset.sum_nonneg (s := S) (f := fun Q => ef A₂ Q) (fun Q _ => by positivity),
              Finset.sum_nonneg (s := S) (f := fun Q => ef B₂ Q) (fun Q _ => by positivity)]

  -- ── TT ≥ ABAB + eps^6 ────────────────────────────────────────────
  -- Expand and apply sub4pair_energy_lower_bound + four_subpair_excess_lb + hcore.
  have hTT : ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)),
        ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q ≥
      ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q +
      eps ^ 6 := by
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    -- TT (16 terms) vs ABAB (4 terms) + eps^6
    -- Use sub4pair_energy_lower_bound and four_subpair_excess_lb
    have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
    have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
    have hsub_AA := sub4pair_energy_lower_bound G A' A₂ A' A₂ hAd hAd
    have hsub_AB_lb := four_subpair_excess_lb G A' A₂ B' B₂ hAd hBd
    have hsub_BA := sub4pair_energy_lower_bound G B' B₂ A' A₂ hBd hAd
    have hsub_BB := sub4pair_energy_lower_bound G B' B₂ B' B₂ hBd hBd
    -- Relate to ef: unfold and apply
    simp only [ef_def]; push_cast
    rw [← hAu, ← hBu, ← hAcard, ← hBcard] at *
    -- AB-excess block via four_subpair_excess_lb:
    -- ∑_{T×T} AB-block ≥ (A'+A₂)*(B'+B₂)*d(A'∪A₂,B'∪B₂)² + A'*B'*(d(A',B')-d(A'∪A₂,B'∪B₂))²
    -- And hcore: A'*B'*(d(A',B')-d(A,B))² > eps^6 * n²
    -- So AB-block/n² ≥ ef(A,B) + eps^6
    have hn2pos : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := by positivity
    nlinarith [hsub_AA, hsub_AB_lb, hsub_BA, hsub_BB, hcore,
               sq_nonneg (edgeDensity G A' A'), sq_nonneg (edgeDensity G A' A₂),
               sq_nonneg (edgeDensity G A₂ A'), sq_nonneg (edgeDensity G A₂ A₂),
               sq_nonneg (edgeDensity G A' B'), sq_nonneg (edgeDensity G A' B₂),
               sq_nonneg (edgeDensity G A₂ B'), sq_nonneg (edgeDensity G A₂ B₂),
               sq_nonneg (edgeDensity G B' A'), sq_nonneg (edgeDensity G B' A₂),
               sq_nonneg (edgeDensity G B₂ A'), sq_nonneg (edgeDensity G B₂ A₂),
               sq_nonneg (edgeDensity G B' B'), sq_nonneg (edgeDensity G B' B₂),
               sq_nonneg (edgeDensity G B₂ B'), sq_nonneg (edgeDensity G B₂ B₂),
               Nat.cast_nonneg (α := ℚ) A'.card, Nat.cast_nonneg (α := ℚ) A₂.card,
               Nat.cast_nonneg (α := ℚ) B'.card, Nat.cast_nonneg (α := ℚ) B₂.card,
               sq_nonneg (edgeDensity G (A' ∪ A₂) (B' ∪ B₂)),
               mul_pos hn2pos hn2pos]

  linarith [hST, hTS, hTT]

end Szemeredi.EnergyIncrement.Aristotle
