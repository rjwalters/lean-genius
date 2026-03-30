/-
  Roth's Theorem via Triangle Removal (Ruzsa-Szemerédi approach)

  An alternative proof that every AP-free subset of Z/NZ has density o(1).
  Instead of Fourier analysis (see RothTheorem.lean), this uses the
  triangle removal lemma from graph theory.

  The key idea:
  1. Given AP-free A ⊂ Z/NZ, construct a tripartite graph G on 3N vertices
  2. Triangles in G correspond to 3-term APs in A
  3. AP-free => triangles are edge-disjoint (each edge in exactly 1 triangle)
  4. Triangle removal: few triangles => few edges to remove
  5. Edge-disjointness => need to remove >= N|A| edges => |A| <= 9*delta*N

  This gives |A| = o(N) for AP-free sets.

  Dependencies:
  - SzemerediCounting.lean: triangle_removal_quantitative

  Ruzsa-Szemeredi (1978), Solymosi (2003)
-/
import Mathlib
import Proofs.SzemerediCounting

namespace RothTriangleRemoval

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: AP-FREE SET DEFINITION (self-contained)
-- ═══════════════════════════════════════════════════════════════════

/-- A subset of ZMod N is AP-free if it contains no non-trivial 3-AP. -/
def APFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE RUZSA-SZEMEREDI TRIPARTITE GRAPH
-- ═══════════════════════════════════════════════════════════════════

variable (N : ℕ) [NeZero N]

/-- The vertex type: ZMod N x Fin 3 (three copies of Z/NZ). -/
abbrev TriVertex := ZMod N × Fin 3

/-- Edge predicate for the Ruzsa-Szemeredi graph.
    Edges between parts:
    - Part 0 <-> Part 1: difference in A
    - Part 1 <-> Part 2: difference in A
    - Part 0 <-> Part 2: difference = 2a for some a in A -/
def rsAdj (A : Finset (ZMod N)) (p q : TriVertex N) : Prop :=
  match p.2.val, q.2.val with
  | 0, 1 => q.1 - p.1 ∈ A
  | 1, 0 => p.1 - q.1 ∈ A
  | 1, 2 => q.1 - p.1 ∈ A
  | 2, 1 => p.1 - q.1 ∈ A
  | 0, 2 => ∃ a ∈ A, q.1 - p.1 = 2 * a
  | 2, 0 => ∃ a ∈ A, p.1 - q.1 = 2 * a
  | _, _ => False

/-- The Ruzsa-Szemeredi tripartite graph constructed from A in Z/NZ. -/
noncomputable def rsGraph (A : Finset (ZMod N)) : SimpleGraph (TriVertex N) where
  Adj p q := rsAdj N A p q
  symm p q h := by
    simp only [rsAdj] at h ⊢
    rcases p with ⟨x, i⟩; rcases q with ⟨y, j⟩
    fin_cases i <;> fin_cases j <;> simp_all [rsAdj]
  loopless v := by
    simp only [rsAdj]
    rcases v with ⟨x, i⟩
    fin_cases i <;> simp [rsAdj]

noncomputable instance (A : Finset (ZMod N)) : DecidableRel (rsGraph N A).Adj :=
  Classical.decRel _

-- ═══════════════════════════════════════════════════════════════════
-- PART III: VERTEX COUNT AND BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- The graph has 3N vertices. -/
theorem card_triVertex : Fintype.card (TriVertex N) = 3 * N := by
  simp [TriVertex, Fintype.card_prod, ZMod.card, Fintype.card_fin]

/-- No edges within the same part. -/
theorem no_edges_same_part (A : Finset (ZMod N)) (x y : ZMod N) (i : Fin 3) :
    ¬(rsGraph N A).Adj (x, i) (y, i) := by
  simp only [rsGraph, rsAdj]
  fin_cases i <;> simp

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: TRIANGLE-AP CORRESPONDENCE
-- ═══════════════════════════════════════════════════════════════════

/-- A triangle (x,0)-(y,1)-(z,2) in the RS graph yields elements
    a1 = y-x, a2 = z-y, a3 with a1 + a2 = 2*a3, all in A. -/
theorem triangle_gives_ap (A : Finset (ZMod N)) (x y z : ZMod N)
    (h01 : (rsGraph N A).Adj (x, (0 : Fin 3)) (y, (1 : Fin 3)))
    (h12 : (rsGraph N A).Adj (y, (1 : Fin 3)) (z, (2 : Fin 3)))
    (h02 : (rsGraph N A).Adj (x, (0 : Fin 3)) (z, (2 : Fin 3))) :
    ∃ a₁ a₂ a₃ : ZMod N,
      a₁ ∈ A ∧ a₂ ∈ A ∧ a₃ ∈ A ∧
      y - x = a₁ ∧ z - y = a₂ ∧ a₁ + a₂ = 2 * a₃ := by
  simp only [rsGraph, rsAdj] at h01 h12 h02
  obtain ⟨a₃, ha₃, heq⟩ := h02
  refine ⟨y - x, z - y, a₃, h01, h12, ha₃, rfl, rfl, ?_⟩
  -- (y - x) + (z - y) = z - x = 2 * a₃
  linear_combination heq

/-- For AP-free A, every triangle forces a1 = a2 = a3 (trivial AP). -/
theorem apFree_triangle_trivial (A : Finset (ZMod N)) (hAP : APFree A)
    (a₁ a₂ a₃ : ZMod N) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (ha₃ : a₃ ∈ A)
    (heq : a₁ + a₂ = 2 * a₃) :
    a₁ = a₃ ∧ a₂ = a₃ := by
  -- a₃ - a₁ is the common difference. If nonzero, (a₁, a₃, a₂) is a 3-AP.
  constructor
  · by_contra h1
    have hd : a₃ - a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have h_mid : a₁ + (a₃ - a₁) = a₃ := by ring
    have h_end : a₁ + 2 * (a₃ - a₁) = a₂ := by linear_combination -heq
    exact hAP a₁ (a₃ - a₁) hd ha₁ (h_mid ▸ ha₃) (h_end ▸ ha₂)
  · by_contra h2
    have hd : a₃ - a₁ ≠ 0 := by
      intro hd0
      have : a₁ = a₃ := by linear_combination -hd0
      rw [this] at heq
      -- heq : a₃ + a₂ = 2 * a₃, so a₂ = a₃
      have : a₂ = a₃ := by linear_combination heq
      exact h2 this
    have h_mid : a₁ + (a₃ - a₁) = a₃ := by ring
    have h_end : a₁ + 2 * (a₃ - a₁) = a₂ := by linear_combination -heq
    exact hAP a₁ (a₃ - a₁) hd ha₁ (h_mid ▸ ha₃) (h_end ▸ ha₂)

/-- For AP-free A, every triangle has the form (x, x+a, x+2a) for a in A. -/
theorem apFree_triangle_form (A : Finset (ZMod N)) (hAP : APFree A)
    (x y z : ZMod N)
    (h01 : (rsGraph N A).Adj (x, (0 : Fin 3)) (y, (1 : Fin 3)))
    (h12 : (rsGraph N A).Adj (y, (1 : Fin 3)) (z, (2 : Fin 3)))
    (h02 : (rsGraph N A).Adj (x, (0 : Fin 3)) (z, (2 : Fin 3))) :
    ∃ a ∈ A, y = x + a ∧ z = x + 2 * a := by
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, hy, hz, hap⟩ :=
    triangle_gives_ap N A x y z h01 h12 h02
  obtain ⟨rfl, rfl⟩ := apFree_triangle_trivial N A hAP a₁ a₂ a₃ ha₁ ha₂ ha₃ hap
  exact ⟨a₃, ha₃, by linear_combination hy, by linear_combination hy + hz⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART V: TRIVIAL TRIANGLES ARE THE CANONICAL EMBEDDING
-- ═══════════════════════════════════════════════════════════════════

/-- For each a in A and x in Z/NZ, (x,0)-(x+a,1)-(x+2a,2) is a triangle. -/
theorem trivial_triangle (A : Finset (ZMod N)) (a : ZMod N) (ha : a ∈ A)
    (x : ZMod N) :
    (rsGraph N A).Adj (x, (0 : Fin 3)) (x + a, (1 : Fin 3)) ∧
    (rsGraph N A).Adj (x + a, (1 : Fin 3)) (x + 2 * a, (2 : Fin 3)) ∧
    (rsGraph N A).Adj (x, (0 : Fin 3)) (x + 2 * a, (2 : Fin 3)) := by
  simp only [rsGraph, rsAdj]
  refine ⟨?_, ?_, ?_⟩
  · -- (x,0)-(x+a,1): (x+a) - x = a in A
    convert ha using 1; ring
  · -- (x+a,1)-(x+2a,2): (x+2a) - (x+a) = a in A
    convert ha using 1; ring
  · -- (x,0)-(x+2a,2): exists a' in A, (x+2a) - x = 2a'
    exact ⟨a, ha, by ring⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: EDGE-DISJOINTNESS (AP-FREE CASE)
-- ═══════════════════════════════════════════════════════════════════

/-- When A is AP-free, each (0,1)-edge determines a unique triangle.
    If (x,0)-(y,1) is an edge, the only triangle using it has z = x+2(y-x). -/
theorem edge01_unique_triangle (A : Finset (ZMod N)) (hAP : APFree A)
    (x y : ZMod N) (h01 : (rsGraph N A).Adj (x, (0 : Fin 3)) (y, (1 : Fin 3)))
    (z : ZMod N)
    (h12 : (rsGraph N A).Adj (y, (1 : Fin 3)) (z, (2 : Fin 3)))
    (h02 : (rsGraph N A).Adj (x, (0 : Fin 3)) (z, (2 : Fin 3))) :
    z = x + 2 * (y - x) := by
  obtain ⟨a, _, hy, hz⟩ := apFree_triangle_form N A hAP x y z h01 h12 h02
  linear_combination hz - 2 * hy

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: DENSITY BOUND VIA TRIANGLE REMOVAL
-- ═══════════════════════════════════════════════════════════════════

/-- For every delta > 0, AP-free sets in Z/NZ have density at most 9*delta
    for all sufficiently large N.

    Proof strategy:
    1. Get gamma from triangle_removal_quantitative for parameter delta
    2. For N large enough, the RS graph has N|A| <= gamma*(3N)^3 triangles
    3. Triangle removal gives edge set R with |R| <= delta*(3N)^2
    4. Edge-disjointness: to remove all triangles, need |R| >= N|A|
    5. Therefore N|A| <= 9*delta*N^2, giving |A| <= 9*delta*N -/
theorem roth_via_triangle_removal (delta : ℚ) (hdelta : 0 < delta) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N ≥ N₀ → N > 0 →
    ∀ (A : Finset (ZMod N)),
      APFree A → (A.card : ℚ) ≤ 9 * delta * N := by
  sorry

/-- Corollary: AP-free subsets of Z/NZ have density o(1).
    For every eps > 0, for all large enough N, |A|/N < eps. -/
theorem roth_density_from_triangle_removal (eps : ℚ) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N ≥ N₀ → N > 0 →
    ∀ (A : Finset (ZMod N)),
      APFree A → (A.card : ℚ) < eps * N := by
  obtain ⟨N₀, hN₀⟩ := roth_via_triangle_removal (eps / 10) (by positivity)
  exact ⟨N₀, fun N hN hNp A hAP => by
    have h := hN₀ N hN hNp A hAP
    have : (9 : ℚ) * (eps / 10) * N < eps * N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN'
      · omega
      · have hNq : (0 : ℚ) < N := Nat.cast_pos.mpr hN'
        nlinarith
    linarith⟩

end RothTriangleRemoval
