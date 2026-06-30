/-
  The 2D-slice Minkowski bound for the three-squares Dirichlet construction.

  This file isolates the remaining open step of `dirichlet_key_lemma`
  in `Proofs/ThreeSquares.lean`. Session researcher-11 (2026-06-16, recorded in
  `G2-minkowski-2p-gap.md`) pinned down that the 3D index-p² ellipsoid route
  CANNOT supply the required `Q < 2p` bound — the generic 2ⁿ Minkowski bound on
  the covolume-p² sublattice only gives `Q ≲ p^(4/3)`, too weak by a factor
  `~p^(1/3)`. The attainable route restricts to the slice `z = 0`, dropping to
  the index-p sublattice `{(x,y) ∈ ℤ² : x ≡ r·y (mod p)}` with the BINARY form
  `x² + d·y²`. Its 2D Hermite bound gives a nonzero point with
  `x² + d·y² ≤ (2/√3)·√d·p`, which is `< 2p` exactly when `d ≤ 2` — and the file's
  own case split uses only `d ∈ {1, 2}`.

  STATUS (researcher-2, 2026-06-18): the `d = 1` case is now FULLY PROVED by an
  elementary Thue/pigeonhole argument (no measure theory) — see
  `exists_slice_point_lt_two_mul_d1`. The `d = 2` case genuinely
  requires the area bound on the ellipse `x² + 2y² ≤ R` (the integer box is
  provably insufficient — 394 counterexamples were exhibited in
  `verify_slice_minkowski.py`), so it needs the measure-theoretic strict
  Minkowski convex-body theorem, not pigeonhole.

  UPDATE (researcher-12, 2026-06-18): the `d = 2` step now has a TURNKEY recipe
  (see its docstring below) — a near-verbatim port of the proved axiom-free
  `dirichlet_approximation` (`MinkowskiTheoremOQ02OQ01.lean`). Key simplification:
  keep the standard `ℤ²` lattice (covolume 1) and shear the *set* to
  `E' = {(a,b) | (p·a + r·b)² + 2b² < 2p}`; then `vol(E') = √2·π ≈ 4.443 > 4` is
  `p`-INDEPENDENT, so Minkowski applies uniformly, and the returned `(a,b)` yields
  `(x,y) = (a·p + b·r, b)` with `p ∣ (x − r·y)` automatic. The target lemma was
  re-verified true for all `p < 1500` (all `r`) and the two elementary shortcuts
  (box bound, strict small-ellipse count) re-confirmed insufficient. Remaining work
  is purely the measure-theory port (2D ellipse volume + the `Measure.map S` change
  of variables) — build-and-Aristotle-gated this session (Aristotle backend down).

  Three pieces:
  - `exists_slice_point_lt_two_mul_d1` (PROVED): the `d = 1` pure 2D
    geometry-of-numbers existence, via a Thue pigeonhole on the box `[0,⌊√p⌋]²`.
    The only subtlety is strictness when `p` is a perfect square `m²`: there the
    plain box can return the corner difference `(±m, ±m)` with `x²+y² = 2p`, so
    we run the pigeonhole on the box with the two corners `(m,m)`, `(m,0)`
    removed, which forces a non-corner collision and hence the strict bound.
  - `exists_slice_point_lt_two_mul_d2` (PROVED): the `d = 2` existence, via the
    arithmetic glue `slice_point_of_sheared_d2` plus the Minkowski core
    `exists_sheared_point_lt_two_mul_d2` (nonzero `ℤ²` point in the sheared
    ellipse), the latter discharged by Aristotle (project `8feb596c`).
  - `exists_slice_point_lt_two_mul` (PROVED): the original combined statement,
    dispatching on `d ∈ {1, 2}`.
  - `slice_point_to_dirichlet_vector` (PROVED): pure plumbing that lifts a 2D
    slice point `(x, y)` to the `Fin 3 → ℤ` vector `![x, y, 0]`.

  STATUS: the file now builds clean with **0 sorries** (researcher-1,
  2026-06-19; `Build completed successfully (7743 jobs)`). The `d = 2` Minkowski
  core was proved by the Aristotle proof search system and integrated/re-verified
  against the project's Mathlib. The `MinkowskiCore.*` declarations depend only on
  the standard `propext` / `Classical.choice` / `Quot.sound` axioms.
-/
import Mathlib

/-! ### Minkowski convex-body infrastructure for the `d = 2` core

Supporting geometry for `exists_sheared_point_lt_two_mul_d2`: the sheared open
ellipse `E' = {(u,v) : (p·u+r·v)² + 2v² < 2p}` is the preimage of the open unit
disc under a determinant-`1/√2` linear map, so `vol(E') = √2·π > 4` independently
of `p`, and Minkowski's strict convex-body theorem applies to `ℤ²` uniformly.

Discharged by the Aristotle proof search system (project `8feb596c`, submitted by
researcher-2); integrated and re-verified against the project's Mathlib by
researcher-1. -/
namespace MinkowskiCore

open MeasureTheory Module Set
open scoped ENNReal

/-- The linear map (a shear composed with diagonal scaling) on `Fin 2 → ℝ` whose matrix is
`!![p/√(2p), r/√(2p); 0, 1/√p]`. It sends the open unit disc onto the sheared open ellipse
`{(u,v) : (p·u + r·v)² + 2·v² < 2p}`. Its determinant is `1/√2`. -/
noncomputable def shearLin (p : ℕ) (r : ℤ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![(p : ℝ) / Real.sqrt (2 * p), (r : ℝ) / Real.sqrt (2 * p); 0, 1 / Real.sqrt p]

/-- The open unit disc in `Fin 2 → ℝ`. -/
def discBall : Set (Fin 2 → ℝ) := {w | (w 0) ^ 2 + (w 1) ^ 2 < 1}

/-- The sheared open ellipse `{(u,v) : (p·u + r·v)² + 2·v² < 2p}` in `Fin 2 → ℝ`. -/
def shearedEllipse (p : ℕ) (r : ℤ) : Set (Fin 2 → ℝ) :=
  {y | ((p : ℝ) * y 0 + (r : ℝ) * y 1) ^ 2 + 2 * (y 1) ^ 2 < 2 * p}

/-- The Lebesgue volume of the open unit disc in `Fin 2 → ℝ` is `π`. -/
lemma discBall_volume : volume discBall = ENNReal.ofReal Real.pi := by
  have h_unit_disc_eq : discBall = (WithLp.toLp 2) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext; simp [discBall, EuclideanSpace.norm_eq];
    rw [ Real.sqrt_lt' ] <;> norm_num;
  rw [ h_unit_disc_eq ];
  convert ( EuclideanSpace.volume_ball ( Fin 2 ) 0 1 ) using 1;
  · convert ( PiLp.volume_preserving_toLp ( Fin 2 ) ).measure_preimage ?_ using 1;
    exact measurableSet_ball.nullMeasurableSet;
  · norm_num [ Real.pi_pos.le ]

/-- The open unit disc is convex. -/
lemma discBall_convex : Convex ℝ discBall := by
  refine' convex_iff_forall_pos.mpr _;
  intro x hx y hy a b ha hb hab; simp_all +decide [ discBall ] ; ring_nf; (
  nlinarith [ sq_nonneg ( x 0 - y 0 ), sq_nonneg ( x 1 - y 1 ), mul_pos ha hb ]);

/-- The sheared ellipse is the preimage of the unit disc under `shearLin`. -/
lemma shearedEllipse_eq (p : ℕ) (hp : 0 < p) (r : ℤ) :
    shearedEllipse p r = (shearLin p r) ⁻¹' discBall := by
  ext y
  simp [shearedEllipse, shearLin, discBall];
  field_simp;
  norm_num [ hp.le ] ; ring_nf!

/-- The determinant of `shearLin` is `1/√2`. -/
lemma shearLin_det (p : ℕ) (hp : 0 < p) (r : ℤ) :
    LinearMap.det (shearLin p r) = 1 / Real.sqrt 2 := by
  have h_matrix : shearLin p r = Matrix.toLin' !![(p : ℝ) / Real.sqrt (2 * p), (r : ℝ) / Real.sqrt (2 * p); 0, 1 / Real.sqrt p] := by
    rfl;
  rw [ h_matrix, LinearMap.det_toLin' ] ; norm_num [ Real.sqrt_mul, hp ] ; ring_nf ;
  norm_num [ hp.ne', mul_assoc, mul_comm, mul_left_comm ]

/-- The sheared ellipse is symmetric about the origin. -/
lemma shearedEllipse_symm (p : ℕ) (r : ℤ) :
    ∀ y ∈ shearedEllipse p r, -y ∈ shearedEllipse p r := by
  intro y hy
  simp [shearedEllipse] at hy;
  exact show ( ( p : ℝ ) * ( -y 0 ) + ( r : ℝ ) * ( -y 1 ) ) ^ 2 + 2 * ( -y 1 ) ^ 2 < 2 * p from by linarith;

/-- The fundamental domain of the standard lattice `ℤ²` has volume `1`. -/
lemma fundDomain_volume :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))) = 1 := by
  convert MeasureTheory.volume_pi_pi _;
  any_goals exact fun _ => Set.Ico 0 1;
  · simp +decide [ Set.ext_iff, Fin.forall_fin_two ];
  · norm_num [ Real.volume_Ico ];
  · exact fun _ => inferInstance

/-- `√2 · π > 4`, the volume bound powering Minkowski's theorem in this setting. -/
lemma four_lt_sqrt2_pi : (4 : ℝ) < Real.sqrt 2 * Real.pi := by
  nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

end MinkowskiCore

namespace ThreeSquaresSlice

set_option maxHeartbeats 800000 in
/-- **The `d = 1` slice point (PROVED).**

For any `p > 0` and any `r : ℤ`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` of `ℤ²` contains a nonzero vector with
`x² + y² < 2p`.

Elementary proof: a Thue pigeonhole on the box of pairs `(a, b)` with
`0 ≤ a, b ≤ ⌊√p⌋`. The box has `(⌊√p⌋+1)² > p` points, so two collide under
`(a, b) ↦ a − r·b (mod p)`; their difference `(x, y)` satisfies `p ∣ (x − r·y)`
and `|x|, |y| ≤ ⌊√p⌋`. When `p` is not a perfect square this already gives
`x² + y² ≤ 2⌊√p⌋² < 2p`; when `p = m²` we instead pigeonhole on the box with the
corners `(m, m)`, `(m, 0)` deleted, which excludes the only `(±m, ±m)`
differences and so forces `x² + y² ≤ m² + (m−1)² < 2p`. -/
theorem exists_slice_point_lt_two_mul_d1
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + y ^ 2 < 2 * p := by
  set m : ℕ := Nat.sqrt p with hm
  have hle : m * m ≤ p := by rw [hm]; exact Nat.sqrt_le p
  have hlt : p < (m + 1) * (m + 1) := by
    rw [hm]; simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt p
  set box : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1) with hbox
  have hbox_card : box.card = (m + 1) * (m + 1) := by
    simp [hbox, Finset.card_range]
  have mem_box : ∀ a b : ℕ, a ≤ m → b ≤ m → (a, b) ∈ box := by
    intro a b ha hb
    rw [hbox]
    exact Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega))
  -- generic pigeonhole over any large-enough sub-box
  have pigeon : ∀ (B : Finset (ℕ × ℕ)), B ⊆ box → p < B.card →
      ∃ a₁ a₂ b₁ b₂ : ℕ, (a₁, b₁) ∈ B ∧ (a₂, b₂) ∈ B ∧ (a₁, b₁) ≠ (a₂, b₂) ∧
        a₁ ≤ m ∧ a₂ ≤ m ∧ b₁ ≤ m ∧ b₂ ≤ m ∧
        (p : ℤ) ∣ ((a₁ : ℤ) - a₂ - r * ((b₁ : ℤ) - b₂)) := by
    intro B hsub hcard
    obtain ⟨⟨a₁, b₁⟩, h1, ⟨a₂, b₂⟩, h2, hne, hfeq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := B) (t := Finset.range p)
        (f := fun ab => (((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ)).toNat)
        (by rw [Finset.card_range]; exact hcard)
        (by
          intro ab _
          simp only [Finset.coe_range, Set.mem_Iio]
          show (((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ)).toNat < p
          have h0 : (0 : ℤ) ≤ ((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ) :=
            Int.emod_nonneg _ (by exact_mod_cast hp.ne')
          have h1 : ((ab.1 : ℤ) - r * (ab.2 : ℤ)) % (p : ℤ) < (p : ℤ) :=
            Int.emod_lt_of_pos _ (by exact_mod_cast hp)
          omega)
    have hb1box := hsub h1
    have hb2box := hsub h2
    simp only [hbox, Finset.mem_product, Finset.mem_range] at hb1box hb2box
    refine ⟨a₁, a₂, b₁, b₂, h1, h2, hne, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · -- divisibility from residue equality
      have e0 : (0 : ℤ) ≤ ((a₁ : ℤ) - r * b₁) % (p : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have e1 : (0 : ℤ) ≤ ((a₂ : ℤ) - r * b₂) % (p : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have hfeq' : (((a₁ : ℤ) - r * (b₁ : ℤ)) % (p : ℤ)).toNat
          = (((a₂ : ℤ) - r * (b₂ : ℤ)) % (p : ℤ)).toNat := hfeq
      have huv : ((a₁ : ℤ) - r * b₁) % (p : ℤ) = ((a₂ : ℤ) - r * b₂) % (p : ℤ) := by
        rw [← Int.toNat_of_nonneg e0, ← Int.toNat_of_nonneg e1, hfeq']
      have hmod : ((a₁ : ℤ) - r * b₁) ≡ ((a₂ : ℤ) - r * b₂) [ZMOD (p : ℤ)] := huv
      have hd := Int.modEq_iff_dvd.mp hmod
      have hreq : ((a₁ : ℤ) - a₂ - r * ((b₁ : ℤ) - b₂))
          = -(((a₂ : ℤ) - r * b₂) - ((a₁ : ℤ) - r * b₁)) := by ring
      rw [hreq]
      exact (dvd_neg).mpr hd
  by_cases hsq : m * m = p
  · -- p is a perfect square; remove two corners so no (±m, ±m) difference survives
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h1
      · rw [h0] at hsq; simp at hsq; omega
      · exact h1
    set B : Finset (ℕ × ℕ) := box \ {(m, m), (m, 0)} with hB
    have hcorners_sub : ({(m, m), (m, 0)} : Finset (ℕ × ℕ)) ⊆ box := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨mem_box m m (le_refl m) (le_refl m), mem_box m 0 (le_refl m) (Nat.zero_le m)⟩
    have hcorners_card : ({(m, m), (m, 0)} : Finset (ℕ × ℕ)).card = 2 := by
      have hne_c : ((m, m) : ℕ × ℕ) ≠ (m, 0) := by
        intro h; rw [Prod.mk.injEq] at h; omega
      rw [Finset.card_pair hne_c]
    have hBcard : p < B.card := by
      have hinter : (({(m, m), (m, 0)} : Finset (ℕ × ℕ)) ∩ box) = {(m, m), (m, 0)} :=
        Finset.inter_eq_left.mpr hcorners_sub
      have h2 : B.card = (m + 1) * (m + 1) - 2 := by
        rw [hB, Finset.card_sdiff, hinter, hbox_card, hcorners_card]
      have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      rw [h2]
      omega
    have hBsub : B ⊆ box := by rw [hB]; exact Finset.sdiff_subset
    obtain ⟨a₁, a₂, b₁, b₂, hin1, hin2, hne, ha1, ha2, hb1, hb2, hdvd⟩ :=
      pigeon B hBsub hBcard
    refine ⟨(a₁ : ℤ) - a₂, (b₁ : ℤ) - b₂, ?_, hdvd, ?_⟩
    · intro hzero
      rw [Prod.mk.injEq] at hzero
      apply hne
      rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩
    · have hx2le : ((a₁ : ℤ) - a₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (a₁ : ℤ) - a₂ by omega,
          show (a₁ : ℤ) - a₂ ≤ (m : ℤ) by omega]
      have hy2le : ((b₁ : ℤ) - b₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (b₁ : ℤ) - b₂ by omega,
          show (b₁ : ℤ) - b₂ ≤ (m : ℤ) by omega]
      have hmm : (m : ℤ) ^ 2 = (p : ℤ) := by
        have : m ^ 2 = p := by rw [pow_two]; exact hsq
        exact_mod_cast this
      -- no surviving corner: at least one coordinate is strictly inside
      have hnot : ¬ (((a₁ = m ∧ a₂ = 0) ∨ (a₁ = 0 ∧ a₂ = m)) ∧
          ((b₁ = m ∧ b₂ = 0) ∨ (b₁ = 0 ∧ b₂ = m))) := by
        rintro ⟨ha, hb⟩
        rcases ha with ⟨ha1', ha2'⟩ | ⟨ha1', ha2'⟩ <;>
          rcases hb with ⟨hb1', hb2'⟩ | ⟨hb1', hb2'⟩ <;>
            subst_vars <;>
              simp_all [hB, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
                Prod.mk.injEq]
      have key : ((a₁ : ℤ) - a₂) ^ 2 < (m : ℤ) ^ 2 ∨ ((b₁ : ℤ) - b₂) ^ 2 < (m : ℤ) ^ 2 := by
        by_contra hc
        push_neg at hc
        have hx2 : ((a₁ : ℤ) - a₂) ^ 2 = (m : ℤ) ^ 2 := le_antisymm hx2le hc.1
        have hy2 : ((b₁ : ℤ) - b₂) ^ 2 = (m : ℤ) ^ 2 := le_antisymm hy2le hc.2
        have hx0 : (((a₁ : ℤ) - a₂) - m) * (((a₁ : ℤ) - a₂) + m) = 0 := by linear_combination hx2
        have hy0 : (((b₁ : ℤ) - b₂) - m) * (((b₁ : ℤ) - b₂) + m) = 0 := by linear_combination hy2
        apply hnot
        refine ⟨?_, ?_⟩
        · rcases mul_eq_zero.mp hx0 with h | h
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rcases mul_eq_zero.mp hy0 with h | h
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
      rcases key with h | h
      · nlinarith [h, hy2le, hmm]
      · nlinarith [h, hx2le, hmm]
  · -- p not a perfect square: m*m < p, so the plain box already gives the strict bound
    have hmm_lt : m * m < p := lt_of_le_of_ne hle hsq
    obtain ⟨a₁, a₂, b₁, b₂, hin1, hin2, hne, ha1, ha2, hb1, hb2, hdvd⟩ :=
      pigeon box (le_refl box) (by rw [hbox_card]; exact hlt)
    refine ⟨(a₁ : ℤ) - a₂, (b₁ : ℤ) - b₂, ?_, hdvd, ?_⟩
    · intro hzero
      rw [Prod.mk.injEq] at hzero
      apply hne
      rw [Prod.mk.injEq]; exact ⟨by omega, by omega⟩
    · have hx2le : ((a₁ : ℤ) - a₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (a₁ : ℤ) - a₂ by omega,
          show (a₁ : ℤ) - a₂ ≤ (m : ℤ) by omega]
      have hy2le : ((b₁ : ℤ) - b₂) ^ 2 ≤ (m : ℤ) ^ 2 := by
        nlinarith [show (-(m : ℤ)) ≤ (b₁ : ℤ) - b₂ by omega,
          show (b₁ : ℤ) - b₂ ≤ (m : ℤ) by omega]
      have hmm : (m : ℤ) ^ 2 < (p : ℤ) := by
        have : m ^ 2 < p := by rw [pow_two]; exact hmm_lt
        exact_mod_cast this
      nlinarith [hx2le, hy2le, hmm]

/-- **Arithmetic glue (proved): sheared lattice point → slice point.**

The `d = 2` Minkowski step reduces, via the turnkey "shear-the-set" recipe, to
producing a nonzero integer pair `(a, b)` on which the *sheared* binary form
`(a·p + b·r)² + 2·b²` is `< 2p` — this is exactly membership of the standard-lattice
point `(a, b)` in the sheared open ellipse `E' = S⁻¹ '' E`, `S = !![p, r; 0, 1]`
(see `exists_sheared_point_lt_two_mul_d2`). This lemma performs the remaining
purely-arithmetic conversion of such a pair into the required slice point
`(x, y) = (a·p + b·r, b)`:

  * `p ∣ (x − r·y)` because `x − r·y = a·p + b·r − r·b = a·p`;
  * `(x, y) ≠ (0, 0)` because `(a, b) ≠ (0, 0)` and `p > 0` (if `b = 0` then
    `x = a·p ≠ 0` since `a ≠ 0`);
  * `x² + 2y² < 2p` is the hypothesis verbatim.

No geometry of numbers here — pure `ring`/`omega` plumbing, so it is fully proved.
It isolates the irreducible Minkowski content from the arithmetic, de-risking the
eventual build. -/
theorem slice_point_of_sheared_d2
    (p : ℕ) (hp : 0 < p) (r : ℤ) (a b : ℤ)
    (hab : (a, b) ≠ (0, 0))
    (hlt : (a * p + b * r) ^ 2 + 2 * b ^ 2 < 2 * p) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + 2 * y ^ 2 < 2 * p := by
  refine ⟨a * p + b * r, b, ?_, ⟨a, by ring⟩, hlt⟩
  intro hzero
  rw [Prod.mk.injEq] at hzero
  obtain ⟨hx, hy⟩ := hzero
  apply hab
  rw [Prod.mk.injEq]
  refine ⟨?_, hy⟩
  -- from `b = 0` and `a·p + b·r = 0` we get `a·p = 0`, so `a = 0` (since `p ≠ 0`)
  rw [hy] at hx
  simp only [zero_mul, add_zero] at hx
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  rcases mul_eq_zero.mp hx with ha | hpz
  · exact ha
  · exact absurd hpz hpne

open MeasureTheory Module Set in
open scoped ENNReal in
/-- **The irreducible `d = 2` Minkowski core (PROVED).**

The sole geometry-of-numbers input remaining in the three-squares development: the
standard lattice `ℤ²` contains a nonzero point `(a, b)` inside the sheared open
ellipse `E' = { (u, v) : ℝ² | (p·u + r·v)² + 2·v² < 2p }`. Because the shear
`S = !![p, r; 0, 1]` has `det = p`, dividing out the `√2·π·p` area of the
axis-aligned ellipse `{w₀² + 2·w₁² < 2p}` leaves `vol(E') = √2·π ≈ 4.443 > 4`
*independently of `p`*, so Minkowski's strict convex-body theorem
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` applies uniformly
for every `p`.

Discharged by the Aristotle proof search system (project `8feb596c`, submitted by
researcher-2) via the `MinkowskiCore` infrastructure above; integrated and
re-verified against the project's Mathlib by researcher-1. -/
theorem exists_sheared_point_lt_two_mul_d2
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ a b : ℤ, (a, b) ≠ (0, 0) ∧ (a * p + b * r) ^ 2 + 2 * b ^ 2 < 2 * p := by
  haveI : Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 2)))).toAddSubgroup :=
    (inferInstance : Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 2)))))
  have det_ne : LinearMap.det (MinkowskiCore.shearLin p r) ≠ 0 := by
    rw [MinkowskiCore.shearLin_det p hp r]; positivity
  have vol_s : volume (MinkowskiCore.shearedEllipse p r)
      = ENNReal.ofReal (Real.sqrt 2 * Real.pi) := by
    rw [MinkowskiCore.shearedEllipse_eq p hp r,
      MeasureTheory.Measure.addHaar_preimage_linearMap volume det_ne,
      MinkowskiCore.discBall_volume, MinkowskiCore.shearLin_det p hp r,
      show |((1:ℝ) / Real.sqrt 2)⁻¹| = Real.sqrt 2 by
        rw [one_div, inv_inv, abs_of_nonneg (Real.sqrt_nonneg 2)],
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  have conv : Convex ℝ (MinkowskiCore.shearedEllipse p r) := by
    rw [MinkowskiCore.shearedEllipse_eq p hp r]
    exact MinkowskiCore.discBall_convex.linear_preimage (MinkowskiCore.shearLin p r)
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 2)) volume
  have hfr : finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  have key : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2)))
      * 2 ^ finrank ℝ (Fin 2 → ℝ) < volume (MinkowskiCore.shearedEllipse p r) := by
    rw [MinkowskiCore.fundDomain_volume, vol_s, hfr, one_mul]
    have h2 : (2:ℝ≥0∞)^2 = ENNReal.ofReal 4 := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num)]; norm_num
    rw [h2, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)]
    exact MinkowskiCore.four_lt_sqrt2_pi
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    fund (MinkowskiCore.shearedEllipse_symm p r) conv key
  have hxspan : (x : Fin 2 → ℝ) ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 2))) := x.2
  rw [Module.Basis.mem_span_iff_repr_mem ℤ] at hxspan
  simp only [Pi.basisFun_repr] at hxspan
  obtain ⟨a, ha⟩ := hxspan 0
  obtain ⟨bb, hbb⟩ := hxspan 1
  have hax : (x : Fin 2 → ℝ) 0 = (a : ℝ) := by rw [← ha]; simp
  have hbx : (x : Fin 2 → ℝ) 1 = (bb : ℝ) := by rw [← hbb]; simp
  have hmem : ((p:ℝ) * (x:Fin 2→ℝ) 0 + (r:ℝ) * (x:Fin 2→ℝ) 1)^2
      + 2 * ((x:Fin 2→ℝ) 1)^2 < 2*p := hxs
  rw [hax, hbx] at hmem
  refine ⟨a, bb, ?_, ?_⟩
  · intro hcontra
    rw [Prod.mk.injEq] at hcontra
    apply hx0
    have hxz : (x : Fin 2 → ℝ) = 0 := by
      funext i
      rw [Pi.zero_apply]
      fin_cases i
      · exact hax.trans (by exact_mod_cast hcontra.1)
      · exact hbx.trans (by exact_mod_cast hcontra.2)
    exact Subtype.ext hxz
  · have hgoal : (((a * p + bb * r) ^ 2 + 2 * bb ^ 2 : ℤ) : ℝ) < ((2 * p : ℤ) : ℝ) := by
      push_cast
      nlinarith [hmem]
    exact_mod_cast hgoal

/-- **The `d = 2` slice point (PROVED).**

For any `p > 0` and any `r : ℤ`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` contains a nonzero vector with `x² + 2y² < 2p`.

Unlike `d = 1`, the integer box `|x|, |y| ≤ ⌊√p⌋` does NOT suffice: the binary
form `x² + 2y²` has Hermite ratio `(2/√3)·√2 ≈ 1.633`, and `verify_slice_minkowski.py`
exhibits 394 `(p, r)` cases where every box point has `x² + 2y² ≥ 2p`. The proof
genuinely requires Minkowski's strict convex-body theorem on the ellipse
`x² + 2y² < 2p` (open, area `√2·π·p`); no elementary box/pigeonhole reduction works
(the best box bound is `2√2·p > 2p`, and the strict small-ellipse count
`#{x²+2y² < p/2} > p` fails for many `p` — both ruled out numerically, S-2026-06-18).
PROVED from the arithmetic glue `slice_point_of_sheared_d2` plus the Minkowski
core `exists_sheared_point_lt_two_mul_d2` (discharged by Aristotle, project
`8feb596c`); this was the last `sorry` in the three-squares slice development.

**REALIZED RECIPE (the route Aristotle's `MinkowskiCore` proof took).** A
near-verbatim port of the proved, axiom-free `dirichlet_approximation`
(`MinkowskiTheoremOQ02OQ01.lean:161`): keep the STANDARD lattice `ℤ²` (covolume `1`,
basis `Pi.basisFun ℝ (Fin 2)`) and shear the *set*, rather than building a
covolume-`p` sublattice. Concretely:

  * Let `S = !![(p:ℝ), r; 0, 1]` (det `= p`) and define the sheared open set
    `E' := { v : Fin 2 → ℝ | (p·v 0 + r·v 1)^2 + 2·(v 1)^2 < 2*p }`,
    i.e. `E' = S ⁻¹' E` where `E = {w | w 0 ^2 + 2·w 1 ^2 < 2p}` is the axis-aligned
    open ellipse.
  * `E'` is symmetric and convex (preimage of the symmetric convex `E` under the
    linear `S`; reuse the quadratic-form convexity argument of
    `dirichletEllipsoid_convex`, `ThreeSquares.lean`).
  * **Volume is `p`-INDEPENDENT**: `vol(E') = vol(E)/|det S| = (√2·π·p)/p = √2·π
    ≈ 4.443 > 4 = 2²·covol(ℤ²)`, so Minkowski's hypothesis holds for *every* `p`
    with a fixed margin. Compute `vol(E')` exactly as `dirichletSet_volume`
    (`MinkowskiTheoremOQ02OQ01.lean:96`) does — via `Measure.map S volume` and
    `map_matrix_volume_pi_eq_smul_volume_pi` — feeding in `vol(E) = √2·π·p` (the 2D
    analog of `dirichletEllipsoid_volume`, `ThreeSquares.lean`: ellipse `= T '' ball`
    with `T = diag(√(2p), √p)`, `EuclideanSpace.volume_ball` in dim 2 `= π`).
  * Apply `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to `ℤ²`,
    `E'`, exactly as in `dirichlet_approximation` (same `ZSpan.isAddFundamentalDomain'`,
    `Module.finrank_fin_fun`, coordinate-extraction block lines 188–215).
  * The returned nonzero integer `(a, b)` gives the slice point
    `(x, y) := (a·p + b·r, b)`: then `x - r·y = a·p` so `(p:ℤ) ∣ (x - r·y)`
    automatically, `(x,y) ≠ (0,0)` since `(a,b) ≠ 0` (if `b = 0` then `x = a·p ≠ 0`),
    and `x² + 2y² < 2p` is exactly membership in `E'`. (Numerically validated for all
    `p < 400`, all `r`.)

This is a KNOWN result (Minkowski applied to a binary form); it was discharged by
Aristotle along essentially this recipe and re-verified against the project's
Mathlib. -/
theorem exists_slice_point_lt_two_mul_d2
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + 2 * y ^ 2 < 2 * p := by
  obtain ⟨a, b, hab, hlt⟩ := exists_sheared_point_lt_two_mul_d2 p hp r
  exact slice_point_of_sheared_d2 p hp r a b hab hlt

/-- **The missing `Q < 2p` step (2D slice).**

For `d ∈ {1, 2}` and any `p > 0`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` of `ℤ²` contains a nonzero vector on which the
binary form `x² + d·y²` is strictly below `2p`.

This is the remaining open input to `dirichlet_key_lemma` in
`Proofs/ThreeSquares.lean`. The `d = 1` case is fully proved
(`exists_slice_point_lt_two_mul_d1`); only the `d = 2` case
(`exists_slice_point_lt_two_mul_d2`) is still open. -/
theorem exists_slice_point_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p := by
  interval_cases d
  · obtain ⟨x, y, h1, h2, h3⟩ := exists_slice_point_lt_two_mul_d1 p hp r
    exact ⟨x, y, h1, h2, by simpa using h3⟩
  · obtain ⟨x, y, h1, h2, h3⟩ := exists_slice_point_lt_two_mul_d2 p hp r
    exact ⟨x, y, h1, h2, by simpa using h3⟩

/-- **Bridge (proved): 2D slice point → Dirichlet sublattice vector.**

Lifts a 2D slice point `(x, y)` with `p ∣ (x − r·y)` and `x² + d·y² < 2p` to the
`Fin 3 → ℤ` vector `![x, y, 0]`. The third coordinate `0` makes the second
sublattice condition `p ∣ v 2` automatic, and the ternary form
`v 0² + d·v 1² + d·v 2²` collapses to the binary `x² + d·y²`. This is exactly the
input shape of `dirichletForm_dvd_of_in_sublattice` and
`dirichletForm_eq_p_of_lt_two_mul` (`ThreeSquares.lean`).

No geometry of numbers here — pure plumbing, so it is fully proved. -/
theorem slice_point_to_dirichlet_vector
    (p d : ℕ) (r x y : ℤ)
    (hxy : (x, y) ≠ (0, 0))
    (hdvd : (p : ℤ) ∣ (x - r * y))
    (hlt : x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  refine ⟨![x, y, 0], ?_, ⟨?_, ?_⟩, ?_⟩
  · -- ![x, y, 0] ≠ 0 since (x, y) ≠ (0, 0)
    intro h
    apply hxy
    have hx : x = 0 := by have := congrFun h 0; simpa using this
    have hy : y = 0 := by have := congrFun h 1; simpa using this
    simp [hx, hy]
  · simpa using hdvd
  · simp
  · simpa using hlt

/-- **Assembled existence**: composing the 2D Minkowski bound with the (proved)
bridge gives directly the `Fin 3 → ℤ` lattice point that `dirichlet_key_lemma`
consumes. Sorry-free once `exists_slice_point_lt_two_mul_d2` is closed. -/
theorem exists_dirichlet_vector_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  obtain ⟨x, y, hxy, hdvd, hlt⟩ := exists_slice_point_lt_two_mul p d hp hd hd2 r
  exact slice_point_to_dirichlet_vector p d r x y hxy hdvd hlt

end ThreeSquaresSlice
