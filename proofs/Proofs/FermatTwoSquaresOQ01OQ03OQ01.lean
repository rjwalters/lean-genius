/-
  Discharging the Hurwitz Euclidean Axiom
  Open Question: fermat-two-squares-oq-01-oq-03-oq-01

  The parent file `FermatTwoSquaresOQ01OQ03.lean` proves Lagrange's four-square
  theorem via the Hurwitz quaternions, but assumes ONE axiom:

      axiom hurwitz_euclidean :
        ∀ (a b : HurwitzQuat), b.normSq > 0 →
          ∃ (q r : HurwitzQuat),
            a.toQuat = b.toQuat * q.toQuat + r.toQuat ∧ r.normSq < b.normSq

  i.e. the Hurwitz integers admit *left Euclidean division* with strictly
  decreasing norm.  The open question asks: can this be formalized in Lean 4
  without new heavy machinery, just the elementary half-integer rounding
  argument?  **Answer: YES.**  This file proves `hurwitz_euclidean` as a
  THEOREM, with zero axioms (only propext / Classical.choice / Quot.sound).

  ## The mathematical content

  The crux is a *covering-radius* bound for the Hurwitz lattice:

      For every rational quaternion x there is a Hurwitz integer q with
          N(x - q) ≤ 1/2.

  This is the single property the Lipschitz integers ℤ⟨1,i,j,k⟩ lack
  (their covering radius² is 1, only ≤, giving N(r) ≤ N(b) — not strict).
  Adjoining ω = ½(1+i+j+k) lets us round each coordinate either to the
  nearest *integer* (giving an all-even Hurwitz point) or to the nearest
  *half-integer* (giving an all-odd Hurwitz point), and one of the two
  always has squared error ≤ 1/2.  Per coordinate,

      (x - ⌊x⌉)² + (x - ½ - ⌊x - ½⌉)² ≤ 1/4,

  so summing the four coordinates, the two squared errors total ≤ 1; hence
  the smaller is ≤ 1/2 < 1.  Then for the left quotient x = b⁻¹·a we get a
  Hurwitz q with N(a - b·q) = N(b)·N(x - q) ≤ N(b)/2 < N(b).

  Beyond rounding we need the Hurwitz integers to be closed under
  multiplication and subtraction (so that r = a - b·q is again Hurwitz);
  these are proved here directly from the equal-parity coordinate condition.

  References:
  - Hurwitz (1896): Über die Zahlentheorie der Quaternionen
  - Conway & Smith (2003): On Quaternions and Octonions, Ch. 5 (covering radius)
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic
import Proofs.FermatTwoSquaresOQ01OQ03

namespace FermatTwoSquaresOQ01OQ03OQ01

open FermatTwoSquaresOQ01OQ03 Quaternion

-- ============================================================================
-- Part I: Norm bridge  ℤ ↔ ℚ
-- ============================================================================

/-- The integer Hurwitz norm equals the rational quaternion norm of the image:
    `(N(q) : ℚ) = N(q.toQuat)`. -/
theorem normSq_cast (q : HurwitzQuat) :
    (q.normSq : ℚ) = Quaternion.normSq q.toQuat := by
  have h4 : (q.normSq4 : ℚ) = 4 * Quaternion.normSq q.toQuat :=
    hurwitz_normSq4_toQuat q
  have hspec : (q.normSq : ℚ) * 4 = (q.normSq4 : ℚ) := by
    exact_mod_cast (HurwitzQuat.normSq_spec q)
  have : (q.normSq : ℚ) * 4 = 4 * Quaternion.normSq q.toQuat := by rw [hspec, h4]
  linarith

-- ============================================================================
-- Part II: Closure of the Hurwitz integers under subtraction and multiplication
-- ============================================================================

/-- The Hurwitz integers are closed under subtraction:
    there is a Hurwitz quaternion whose image is `a.toQuat - b.toQuat`. -/
theorem hurwitz_sub_closed (a b : HurwitzQuat) :
    ∃ c : HurwitzQuat, c.toQuat = a.toQuat - b.toQuat := by
  refine ⟨⟨a.n₀ - b.n₀, a.n₁ - b.n₁, a.n₂ - b.n₂, a.n₃ - b.n₃, ?_⟩, ?_⟩
  · obtain ⟨ha01, ha12, ha23⟩ := a.parity
    obtain ⟨hb01, hb12, hb23⟩ := b.parity
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · apply Quaternion.ext <;>
      simp only [HurwitzQuat.toQuat, Quaternion.re_sub, Quaternion.imI_sub,
        Quaternion.imJ_sub, Quaternion.imK_sub] <;>
      push_cast <;> ring

/-- The Hurwitz integers are closed under multiplication:
    there is a Hurwitz quaternion whose image is `a.toQuat * b.toQuat`.

    Proof: split on the parity of `a` and of `b` (each is all-even or
    all-odd).  In each of the four cases substitute the explicit integer
    halves and exhibit the product coordinates as integers; the parity
    condition closes by `omega`, the coordinate identities by `ring`. -/
theorem hurwitz_mul_closed (a b : HurwitzQuat) :
    ∃ c : HurwitzQuat, c.toQuat = a.toQuat * b.toQuat := by
  obtain ⟨ha01, ha12, ha23⟩ := a.parity
  obtain ⟨hb01, hb12, hb23⟩ := b.parity
  -- name the eight coordinates
  rcases Int.emod_two_eq_zero_or_one a.n₀ with hA | hA <;>
  rcases Int.emod_two_eq_zero_or_one b.n₀ with hB | hB
  -- Case 1: a all even, b all even
  · have ha1 : a.n₁ % 2 = 0 := ha01 ▸ hA
    have ha2 : a.n₂ % 2 = 0 := ha12 ▸ ha1
    have ha3 : a.n₃ % 2 = 0 := ha23 ▸ ha2
    have hb1 : b.n₁ % 2 = 0 := hb01 ▸ hB
    have hb2 : b.n₂ % 2 = 0 := hb12 ▸ hb1
    have hb3 : b.n₃ % 2 = 0 := hb23 ▸ hb2
    obtain ⟨a0, ha0⟩ := Int.dvd_of_emod_eq_zero hA
    obtain ⟨a1, ha1'⟩ := Int.dvd_of_emod_eq_zero ha1
    obtain ⟨a2, ha2'⟩ := Int.dvd_of_emod_eq_zero ha2
    obtain ⟨a3, ha3'⟩ := Int.dvd_of_emod_eq_zero ha3
    obtain ⟨c0, hc0⟩ := Int.dvd_of_emod_eq_zero hB
    obtain ⟨c1, hc1⟩ := Int.dvd_of_emod_eq_zero hb1
    obtain ⟨c2, hc2⟩ := Int.dvd_of_emod_eq_zero hb2
    obtain ⟨c3, hc3⟩ := Int.dvd_of_emod_eq_zero hb3
    refine ⟨⟨ 2*(a0*c0 - a1*c1 - a2*c2 - a3*c3),
              2*(a0*c1 + a1*c0 + a2*c3 - a3*c2),
              2*(a0*c2 - a1*c3 + a2*c0 + a3*c1),
              2*(a0*c3 + a1*c2 - a2*c1 + a3*c0), ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · apply Quaternion.ext <;>
        simp only [HurwitzQuat.toQuat, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul] <;>
        rw [ha0, ha1', ha2', ha3', hc0, hc1, hc2, hc3] <;>
        push_cast <;> ring
  -- Case 2: a all even, b all odd
  · have ha1 : a.n₁ % 2 = 0 := ha01 ▸ hA
    have ha2 : a.n₂ % 2 = 0 := ha12 ▸ ha1
    have ha3 : a.n₃ % 2 = 0 := ha23 ▸ ha2
    have hb1 : b.n₁ % 2 = 1 := hb01 ▸ hB
    have hb2 : b.n₂ % 2 = 1 := hb12 ▸ hb1
    have hb3 : b.n₃ % 2 = 1 := hb23 ▸ hb2
    obtain ⟨a0, ha0⟩ := Int.dvd_of_emod_eq_zero hA
    obtain ⟨a1, ha1'⟩ := Int.dvd_of_emod_eq_zero ha1
    obtain ⟨a2, ha2'⟩ := Int.dvd_of_emod_eq_zero ha2
    obtain ⟨a3, ha3'⟩ := Int.dvd_of_emod_eq_zero ha3
    obtain ⟨c0, hc0⟩ : ∃ k : ℤ, b.n₀ = 2 * k + 1 := ⟨b.n₀ / 2, by omega⟩
    obtain ⟨c1, hc1⟩ : ∃ k : ℤ, b.n₁ = 2 * k + 1 := ⟨b.n₁ / 2, by omega⟩
    obtain ⟨c2, hc2⟩ : ∃ k : ℤ, b.n₂ = 2 * k + 1 := ⟨b.n₂ / 2, by omega⟩
    obtain ⟨c3, hc3⟩ : ∃ k : ℤ, b.n₃ = 2 * k + 1 := ⟨b.n₃ / 2, by omega⟩
    refine ⟨⟨ 2*(a0*c0 - a1*c1 - a2*c2 - a3*c3) + (a0 - a1 - a2 - a3),
              2*(a0*c1 + a1*c0 + a2*c3 - a3*c2) + (a0 + a1 + a2 - a3),
              2*(a0*c2 - a1*c3 + a2*c0 + a3*c1) + (a0 - a1 + a2 + a3),
              2*(a0*c3 + a1*c2 - a2*c1 + a3*c0) + (a0 + a1 - a2 + a3), ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · apply Quaternion.ext <;>
        simp only [HurwitzQuat.toQuat, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul] <;>
        rw [ha0, ha1', ha2', ha3', hc0, hc1, hc2, hc3] <;>
        push_cast <;> ring
  -- Case 3: a all odd, b all even
  · have ha1 : a.n₁ % 2 = 1 := ha01 ▸ hA
    have ha2 : a.n₂ % 2 = 1 := ha12 ▸ ha1
    have ha3 : a.n₃ % 2 = 1 := ha23 ▸ ha2
    have hb1 : b.n₁ % 2 = 0 := hb01 ▸ hB
    have hb2 : b.n₂ % 2 = 0 := hb12 ▸ hb1
    have hb3 : b.n₃ % 2 = 0 := hb23 ▸ hb2
    obtain ⟨a0, ha0⟩ : ∃ k : ℤ, a.n₀ = 2 * k + 1 := ⟨a.n₀ / 2, by omega⟩
    obtain ⟨a1, ha1'⟩ : ∃ k : ℤ, a.n₁ = 2 * k + 1 := ⟨a.n₁ / 2, by omega⟩
    obtain ⟨a2, ha2'⟩ : ∃ k : ℤ, a.n₂ = 2 * k + 1 := ⟨a.n₂ / 2, by omega⟩
    obtain ⟨a3, ha3'⟩ : ∃ k : ℤ, a.n₃ = 2 * k + 1 := ⟨a.n₃ / 2, by omega⟩
    obtain ⟨c0, hc0⟩ := Int.dvd_of_emod_eq_zero hB
    obtain ⟨c1, hc1⟩ := Int.dvd_of_emod_eq_zero hb1
    obtain ⟨c2, hc2⟩ := Int.dvd_of_emod_eq_zero hb2
    obtain ⟨c3, hc3⟩ := Int.dvd_of_emod_eq_zero hb3
    refine ⟨⟨ 2*(a0*c0 - a1*c1 - a2*c2 - a3*c3) + (c0 - c1 - c2 - c3),
              2*(a0*c1 + a1*c0 + a2*c3 - a3*c2) + (c1 + c0 + c3 - c2),
              2*(a0*c2 - a1*c3 + a2*c0 + a3*c1) + (c2 - c3 + c0 + c1),
              2*(a0*c3 + a1*c2 - a2*c1 + a3*c0) + (c3 + c2 - c1 + c0), ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · apply Quaternion.ext <;>
        simp only [HurwitzQuat.toQuat, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul] <;>
        rw [ha0, ha1', ha2', ha3', hc0, hc1, hc2, hc3] <;>
        push_cast <;> ring
  -- Case 4: a all odd, b all odd
  · have ha1 : a.n₁ % 2 = 1 := ha01 ▸ hA
    have ha2 : a.n₂ % 2 = 1 := ha12 ▸ ha1
    have ha3 : a.n₃ % 2 = 1 := ha23 ▸ ha2
    have hb1 : b.n₁ % 2 = 1 := hb01 ▸ hB
    have hb2 : b.n₂ % 2 = 1 := hb12 ▸ hb1
    have hb3 : b.n₃ % 2 = 1 := hb23 ▸ hb2
    obtain ⟨a0, ha0⟩ : ∃ k : ℤ, a.n₀ = 2 * k + 1 := ⟨a.n₀ / 2, by omega⟩
    obtain ⟨a1, ha1'⟩ : ∃ k : ℤ, a.n₁ = 2 * k + 1 := ⟨a.n₁ / 2, by omega⟩
    obtain ⟨a2, ha2'⟩ : ∃ k : ℤ, a.n₂ = 2 * k + 1 := ⟨a.n₂ / 2, by omega⟩
    obtain ⟨a3, ha3'⟩ : ∃ k : ℤ, a.n₃ = 2 * k + 1 := ⟨a.n₃ / 2, by omega⟩
    obtain ⟨c0, hc0⟩ : ∃ k : ℤ, b.n₀ = 2 * k + 1 := ⟨b.n₀ / 2, by omega⟩
    obtain ⟨c1, hc1⟩ : ∃ k : ℤ, b.n₁ = 2 * k + 1 := ⟨b.n₁ / 2, by omega⟩
    obtain ⟨c2, hc2⟩ : ∃ k : ℤ, b.n₂ = 2 * k + 1 := ⟨b.n₂ / 2, by omega⟩
    obtain ⟨c3, hc3⟩ : ∃ k : ℤ, b.n₃ = 2 * k + 1 := ⟨b.n₃ / 2, by omega⟩
    -- Each product coordinate cᵢ is even; we record half of it.
    -- c₀ = (2a₀+1)(2c₀+1) - Σ ... ; here we give cᵢ/2 directly.
    refine ⟨⟨ 2*(a0*c0 - a1*c1 - a2*c2 - a3*c3) + (a0 - a1 - a2 - a3)
                + (c0 - c1 - c2 - c3) - 1,
              2*(a0*c1 + a1*c0 + a2*c3 - a3*c2) + (a0 + a1 + a2 - a3)
                + (c1 + c0 + c3 - c2) + 1,
              2*(a0*c2 - a1*c3 + a2*c0 + a3*c1) + (a0 - a1 + a2 + a3)
                + (c2 - c3 + c0 + c1) + 1,
              2*(a0*c3 + a1*c2 - a2*c1 + a3*c0) + (a0 + a1 - a2 + a3)
                + (c3 + c2 - c1 + c0) + 1, ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · apply Quaternion.ext <;>
        simp only [HurwitzQuat.toQuat, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul] <;>
        rw [ha0, ha1', ha2', ha3', hc0, hc1, hc2, hc3] <;>
        push_cast <;> ring

-- ============================================================================
-- Part III: The covering-radius rounding lemma
-- ============================================================================

/-- Per-coordinate covering bound: for any rational `x`, the squared distance
    to the nearest integer plus the squared distance to the nearest
    half-integer is at most `1/4`. -/
theorem per_coord_bound (x : ℚ) :
    (x - (round x : ℚ))^2 + ((x - 1/2) - (round (x - 1/2) : ℚ))^2 ≤ 1/4 := by
  set δ : ℚ := x - (round x : ℚ) with hδdef
  set ε : ℚ := (x - 1/2) - (round (x - 1/2) : ℚ) with hεdef
  have hδ : |δ| ≤ 1/2 := abs_sub_round x
  have hε : |ε| ≤ 1/2 := abs_sub_round (x - 1/2)
  obtain ⟨hδl, hδr⟩ := abs_le.mp hδ
  obtain ⟨hεl, hεr⟩ := abs_le.mp hε
  set k : ℤ := round (x - 1/2) - round x with hkdef
  have hrel : δ - ε = 1/2 + (k : ℚ) := by
    rw [hδdef, hεdef, hkdef]; push_cast; ring
  -- k ∈ {-1, 0}
  have hk_lt1 : k < 1 := by
    have : (k : ℚ) < 1 := by linarith
    exact_mod_cast this
  have hk_gtm2 : -2 < k := by
    have : (-2 : ℚ) < (k : ℚ) := by linarith
    exact_mod_cast this
  have hk_le' : k ≤ 0 := by omega
  have hk_ge' : -1 ≤ k := by omega
  interval_cases k
  · -- k = -1 : ε = δ + 1/2
    have heq : ε = δ + 1/2 := by push_cast at hrel; linarith
    have hδ0 : δ ≤ 0 := by linarith [hεr, heq]
    rw [heq]
    nlinarith [hδl, hδ0, mul_nonneg (by linarith : (0:ℚ) ≤ -δ) (by linarith : (0:ℚ) ≤ 2*δ+1)]
  · -- k = 0 : ε = δ - 1/2
    have heq : ε = δ - 1/2 := by push_cast at hrel; linarith
    have hδ0 : 0 ≤ δ := by linarith [hεl, heq]
    rw [heq]
    nlinarith [hδr, hδ0, mul_nonneg (by linarith : (0:ℚ) ≤ δ) (by linarith : (0:ℚ) ≤ 1-2*δ)]

/-- **Covering radius bound for the Hurwitz lattice.**  For every rational
    quaternion `x` there is a Hurwitz integer `q` with `N(x - q.toQuat) ≤ 1/2`.

    Round each coordinate either all to the nearest integer (an all-even, i.e.
    Lipschitz, Hurwitz point) or all to the nearest half-integer (an all-odd
    Hurwitz point); the smaller of the two total squared errors is ≤ 1/2. -/
theorem exists_hurwitz_close (x : Quaternion ℚ) :
    ∃ q : HurwitzQuat, Quaternion.normSq (x - q.toQuat) ≤ 1/2 := by
  -- the integer-rounded Hurwitz point (all coordinates even)
  set qI : HurwitzQuat :=
    ⟨2 * round x.re, 2 * round x.imI, 2 * round x.imJ, 2 * round x.imK,
      by refine ⟨?_, ?_, ?_⟩ <;> omega⟩ with hqI
  -- the half-integer-rounded Hurwitz point (all coordinates odd)
  set qH : HurwitzQuat :=
    ⟨2 * round (x.re - 1/2) + 1, 2 * round (x.imI - 1/2) + 1,
      2 * round (x.imJ - 1/2) + 1, 2 * round (x.imK - 1/2) + 1,
      by refine ⟨?_, ?_, ?_⟩ <;> omega⟩ with hqH
  -- squared errors, computed coordinate-wise
  have eI : Quaternion.normSq (x - qI.toQuat) =
      (x.re - round x.re)^2 + (x.imI - round x.imI)^2
        + (x.imJ - round x.imJ)^2 + (x.imK - round x.imK)^2 := by
    rw [hqI, Quaternion.normSq_def']
    simp only [HurwitzQuat.toQuat, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub]
    push_cast; ring
  have eH : Quaternion.normSq (x - qH.toQuat) =
      ((x.re - 1/2) - round (x.re - 1/2))^2 + ((x.imI - 1/2) - round (x.imI - 1/2))^2
        + ((x.imJ - 1/2) - round (x.imJ - 1/2))^2 + ((x.imK - 1/2) - round (x.imK - 1/2))^2 := by
    rw [hqH, Quaternion.normSq_def']
    simp only [HurwitzQuat.toQuat, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub]
    push_cast; ring
  -- the two squared errors sum to ≤ 1
  have hsum : Quaternion.normSq (x - qI.toQuat) + Quaternion.normSq (x - qH.toQuat) ≤ 1 := by
    rw [eI, eH]
    have b0 := per_coord_bound x.re
    have b1 := per_coord_bound x.imI
    have b2 := per_coord_bound x.imJ
    have b3 := per_coord_bound x.imK
    linarith
  -- pick the smaller
  by_cases hcase : Quaternion.normSq (x - qI.toQuat) ≤ 1/2
  · exact ⟨qI, hcase⟩
  · exact ⟨qH, by linarith⟩

-- ============================================================================
-- Part IV: Discharging the Euclidean axiom
-- ============================================================================

/-- **The Hurwitz integers form a (left) Euclidean ring** — this is the
    statement declared as `axiom hurwitz_euclidean` in the parent file, now
    proved as a theorem.

    Given `a, b` with `N(b) > 0`, set `x = b⁻¹·a` in `ℍ(ℚ)`, round it to a
    Hurwitz integer `q` with `N(x - q) ≤ 1/2`, and let `r = a - b·q` (Hurwitz
    by closure).  Then
        `N(r) = N(b·(x - q)) = N(b)·N(x - q) ≤ N(b)/2 < N(b).` -/
theorem hurwitz_euclidean_thm :
    ∀ (a b : HurwitzQuat), b.normSq > 0 →
      ∃ (q r : HurwitzQuat),
        a.toQuat = b.toQuat * q.toQuat + r.toQuat ∧ r.normSq < b.normSq := by
  intro a b hb
  -- b.toQuat ≠ 0
  have hbQ : Quaternion.normSq b.toQuat > 0 := by
    rw [← normSq_cast b]; exact_mod_cast hb
  have hbne : b.toQuat ≠ 0 := by
    intro h; rw [h] at hbQ; simp at hbQ
  -- round the left quotient x = b⁻¹ * a
  set x : Quaternion ℚ := b.toQuat⁻¹ * a.toQuat with hxdef
  obtain ⟨q, hq⟩ := exists_hurwitz_close x
  -- r = a - b*q  is Hurwitz
  obtain ⟨bq, hbq⟩ := hurwitz_mul_closed b q
  obtain ⟨r, hr⟩ := hurwitz_sub_closed a bq
  have hr' : r.toQuat = a.toQuat - b.toQuat * q.toQuat := by rw [hr, hbq]
  refine ⟨q, r, ?_, ?_⟩
  · -- a = b*q + r  (additive identity in the noncommutative ring)
    rw [hr']; abel
  · -- N(r) < N(b)
    -- r.toQuat = b.toQuat * (x - q.toQuat)
    have hfactor : r.toQuat = b.toQuat * (x - q.toQuat) := by
      rw [hr', hxdef, mul_sub, mul_inv_cancel_left₀ hbne]
    have hnorm : Quaternion.normSq r.toQuat
        = Quaternion.normSq b.toQuat * Quaternion.normSq (x - q.toQuat) := by
      rw [hfactor, map_mul]
    have hbound : Quaternion.normSq r.toQuat ≤ Quaternion.normSq b.toQuat * (1/2) := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hq (le_of_lt hbQ)
    -- transfer to ℤ
    have hrlt : (r.normSq : ℚ) < (b.normSq : ℚ) := by
      rw [normSq_cast r, normSq_cast b]
      have : Quaternion.normSq b.toQuat * (1/2) < Quaternion.normSq b.toQuat := by
        nlinarith [hbQ]
      linarith [hbound]
    exact_mod_cast hrlt

-- A sanity check that the discharged statement matches the parent axiom's type.
example : ∀ (a b : HurwitzQuat), b.normSq > 0 →
    ∃ (q r : HurwitzQuat),
      a.toQuat = b.toQuat * q.toQuat + r.toQuat ∧ r.normSq < b.normSq :=
  hurwitz_euclidean_thm

end FermatTwoSquaresOQ01OQ03OQ01
