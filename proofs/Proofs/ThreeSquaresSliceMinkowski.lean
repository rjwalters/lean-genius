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
  `exists_slice_point_lt_two_mul_d1`. The `d = 2` case
  (`exists_slice_point_lt_two_mul_d2`) remains the sole `sorry`: it genuinely
  requires the area bound on the ellipse `x² + 2y² ≤ R` (the integer box is
  provably insufficient — 394 counterexamples were exhibited in
  `verify_slice_minkowski.py`), so it needs the measure-theoretic strict
  Minkowski convex-body theorem, not pigeonhole.

  Three pieces:
  - `exists_slice_point_lt_two_mul_d1` (PROVED): the `d = 1` pure 2D
    geometry-of-numbers existence, via a Thue pigeonhole on the box `[0,⌊√p⌋]²`.
    The only subtlety is strictness when `p` is a perfect square `m²`: there the
    plain box can return the corner difference `(±m, ±m)` with `x²+y² = 2p`, so
    we run the pigeonhole on the box with the two corners `(m,m)`, `(m,0)`
    removed, which forces a non-corner collision and hence the strict bound.
  - `exists_slice_point_lt_two_mul_d2` (OPEN): the `d = 2` existence.
  - `exists_slice_point_lt_two_mul` (PROVED for d=1, reduces d=2 to the above):
    the original combined statement, dispatching on `d ∈ {1, 2}`.
  - `slice_point_to_dirichlet_vector` (PROVED): pure plumbing that lifts a 2D
    slice point `(x, y)` to the `Fin 3 → ℤ` vector `![x, y, 0]`.

  NOTE: build-pending and intentionally UNregistered in `Proofs.lean` — it
  carries one `sorry` (the `d = 2` target) and must not gate the deployer build.
-/
import Mathlib

namespace ThreeSquaresSlice

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
    rw [hbox, Finset.card_product, Finset.card_range, Finset.card_range]
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
          rw [Finset.mem_range]
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
      rw [Finset.card_insert_of_not_mem (by simp only [Finset.mem_singleton, Prod.mk.injEq];
        omega), Finset.card_singleton]
    have hBcard : p < B.card := by
      have h2 : B.card = (m + 1) * (m + 1) - 2 := by
        rw [hB, Finset.card_sdiff hcorners_sub, hbox_card, hcorners_card]
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

/-- **The `d = 2` slice point (OPEN).**

For any `p > 0` and any `r : ℤ`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` contains a nonzero vector with `x² + 2y² < 2p`.

Unlike `d = 1`, the integer box `|x|, |y| ≤ ⌊√p⌋` does NOT suffice: the binary
form `x² + 2y²` has Hermite ratio `(2/√3)·√2 ≈ 1.633`, and `verify_slice_minkowski.py`
exhibits 394 `(p, r)` cases where every box point has `x² + 2y² ≥ 2p`. The proof
genuinely requires Minkowski's strict convex-body theorem on the ellipse
`x² + 2y² ≤ R` (area `πR/√2`) with the covolume-`p` sublattice and `R ∈ (4√2·p/π, 2p)`.
This is the sole remaining `sorry` in the three-squares development. -/
theorem exists_slice_point_lt_two_mul_d2
    (p : ℕ) (hp : 0 < p) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + 2 * y ^ 2 < 2 * p := by
  sorry

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
