/-
  Structural Properties of the Discriminant, and the Discriminant–Derivative Formula
    (Open Question OQ-01 of `abel-ruffini-oq-07-discriminant-oq-01`)

  ## Background
  The parent entry `AbelRuffiniOQ07DiscriminantOQ01.lean` introduced the difference
  product `δ = ∏_{i<j}(rⱼ − rᵢ)` (as the Vandermonde determinant `diffProd`), proved
  its sign transformation `diffProd (r ∘ σ) = sign σ • diffProd r`, and used it to
  establish the Galois criterion `disc = δ² is a square ⟺ Gal ⊆ Aₙ`.

  That file left the *structural* properties of the discriminant `disc = δ²` itself
  unexamined.  This file records them, over an arbitrary commutative ring (and an
  integral domain where separability is discussed):

    * **Symmetry.**  `disc` is a symmetric function of the family: `disc (r ∘ σ) = disc r`.
      This is the conceptual foundation of the whole theory — being permutation-invariant,
      the discriminant is a polynomial in the elementary symmetric functions of the
      roots, hence in the coefficients.
    * **Antisymmetry of δ.**  A transposition negates the difference product,
      `diffProd (r ∘ swap i j) = − diffProd r`.
    * **Separability.**  Over a domain, `disc r = 0 ⟺ the family is not injective`
      (two roots coincide) — the discriminant detects repeated roots.
    * **Translation invariance.**  `disc` is unchanged by a common shift of all roots,
      `diffProd (r + c) = diffProd r`; this is the algebraic content of the reduction
      of a polynomial to depressed form.

  ## The centerpiece: the discriminant–derivative formula
  The classical identity connecting the discriminant to the derivative of the
  associated polynomial is

      δ² = (−1)^{n(n−1)/2} · ∏ᵢ ∏_{j ≠ i} (rᵢ − rⱼ).

  The inner product `∏_{j ≠ i}(rᵢ − rⱼ)` is exactly `f'(rᵢ)` for the monic polynomial
  `f = ∏ⱼ (X − rⱼ)`, so this is the standard bridge `disc = (−1)^{C(n,2)} ∏ᵢ f'(rᵢ)`
  from which one derives `disc = (−1)^{C(n,2)} Res(f, f')` (up to the leading coefficient).
  We prove it here purely as a Finset product identity, valid over any commutative ring.

  All results are fully machine-checked with 0 sorries and 0 axioms.
-/
import Proofs.AbelRuffiniOQ07DiscriminantOQ01
import Mathlib.Tactic

open Matrix Equiv Equiv.Perm Finset
open AbelRuffiniDiscriminantSquare

namespace AbelRuffiniDiscriminantStructure

variable {R : Type*} [CommRing R]

/-- The **discriminant** `disc r = δ²`, the square of the difference product. -/
noncomputable def disc {n : ℕ} (r : Fin n → R) : R := diffProd r ^ 2

theorem disc_eq_sq {n : ℕ} (r : Fin n → R) : disc r = diffProd r ^ 2 := rfl

/-! ## Symmetry of the discriminant -/

/-- **The discriminant is a symmetric function.**  Permuting the family leaves the
discriminant unchanged, because the difference product only changes by the sign of the
permutation and the sign squares to `1`.  This is the reason `disc` is a polynomial in
the coefficients of the associated polynomial. -/
theorem disc_comp_perm {n : ℕ} (r : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    disc (r ∘ σ) = disc r := by
  simp only [disc, diffProd_comp_perm, zsmul_eq_mul, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-- **A transposition negates the difference product.**  For `i ≠ j`, swapping the two
entries `rᵢ` and `rⱼ` flips the sign of `δ` — the antisymmetry of the Vandermonde
determinant, specialized to a transposition. -/
theorem diffProd_swap {n : ℕ} (r : Fin n → R) {i j : Fin n} (hij : i ≠ j) :
    diffProd (r ∘ Equiv.swap i j) = - diffProd r := by
  rw [diffProd_comp_perm, Equiv.Perm.sign_swap hij]
  simp

/-! ## Translation invariance -/

/-- **Translation invariance of the difference product.**  Adding a common constant `c`
to every entry leaves `δ` unchanged, since it cancels in every difference `rⱼ − rᵢ`.
This is the algebraic heart of the reduction of a polynomial to depressed form. -/
theorem diffProd_add_const {n : ℕ} (r : Fin n → R) (c : R) :
    diffProd (fun k => r k + c) = diffProd r := by
  simp only [diffProd_eq_prod]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  ring

/-- **Translation invariance of the discriminant.** -/
theorem disc_add_const {n : ℕ} (r : Fin n → R) (c : R) :
    disc (fun k => r k + c) = disc r := by
  simp only [disc, diffProd_add_const]

/-! ## Separability: the discriminant detects repeated roots -/

section Domain
variable {R : Type*} [CommRing R] [IsDomain R]

/-- The difference product is nonzero iff the family is injective (over a domain). -/
theorem diffProd_ne_zero_iff {n : ℕ} (r : Fin n → R) :
    diffProd r ≠ 0 ↔ Function.Injective r := by
  rw [diffProd]; exact Matrix.det_vandermonde_ne_zero_iff

/-- **The discriminant detects repeated roots.**  Over an integral domain, `disc r = 0`
exactly when two entries of the family coincide (the family is not injective).  This is
the separability criterion: a polynomial has a repeated root iff its discriminant
vanishes. -/
theorem disc_eq_zero_iff {n : ℕ} (r : Fin n → R) :
    disc r = 0 ↔ ¬ Function.Injective r := by
  rw [disc, pow_eq_zero_iff (two_ne_zero), ← diffProd_ne_zero_iff, not_not]

end Domain

/-! ## The discriminant–derivative formula -/

/-- The **off-diagonal product** `∏ᵢ ∏_{j ≠ i}(rᵢ − rⱼ)`.  Its inner factor
`∏_{j ≠ i}(rᵢ − rⱼ)` is `f'(rᵢ)` for `f = ∏ⱼ(X − rⱼ)`, so this equals `∏ᵢ f'(rᵢ)`. -/
noncomputable def offDiagProd {n : ℕ} (r : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ univ.erase i, (r i - r j)

/-- For a fixed `i`, the punctured index set `univ.erase i` splits as the disjoint union
of the strictly-smaller and strictly-larger indices. -/
theorem erase_eq_Iio_union_Ioi {n : ℕ} (i : Fin n) :
    univ.erase i = Iio i ∪ Ioi i := by
  ext x
  simp only [mem_erase, mem_union, mem_Iio, mem_Ioi, mem_univ, and_true]
  constructor
  · intro h; exact lt_or_gt_of_ne h
  · rintro (h | h)
    · exact ne_of_lt h
    · exact (ne_of_lt h).symm

/-- `Iio i` and `Ioi i` are disjoint. -/
theorem disjoint_Iio_Ioi {n : ℕ} (i : Fin n) : Disjoint (Iio i) (Ioi i) := by
  simp only [Finset.disjoint_left, mem_Iio, mem_Ioi]
  intro x hx hx'; exact absurd (hx.trans hx') (lt_irrefl x)

/-- The number of ordered upper-triangular pairs: `∑ᵢ #(Ioi i) = C(n, 2)`. -/
theorem sum_card_Ioi (n : ℕ) : ∑ i : Fin n, (Ioi i).card = n.choose 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n,
      show (∑ k ∈ Finset.range n, (n - 1 - k)) = ∑ k ∈ Finset.range n, k from
        Finset.sum_range_reflect (fun k => k) n,
      Finset.sum_range_id, Nat.choose_two_right]

/-- **The discriminant–derivative formula.**  The off-diagonal product equals
`(−1)^{C(n,2)}` times the discriminant:

    ∏ᵢ ∏_{j ≠ i}(rᵢ − rⱼ)  =  (−1)^{n(n−1)/2} · δ².

Pairing the ordered off-diagonal pairs `(i, j)` and `(j, i)` turns each unordered pair
into `(rᵢ − rⱼ)(rⱼ − rᵢ) = −(rⱼ − rᵢ)²`; collecting the `C(n,2)` signs and the squares
gives the result.  Since `∏_{j ≠ i}(rᵢ − rⱼ) = f'(rᵢ)` for `f = ∏ⱼ(X − rⱼ)`, this is the
classical `disc = (−1)^{C(n,2)} ∏ᵢ f'(rᵢ)`. -/
theorem offDiagProd_eq_sign_mul_disc {n : ℕ} (r : Fin n → R) :
    offDiagProd r = (-1) ^ (n.choose 2) * disc r := by
  -- Split each punctured product into its lower and upper parts.
  have hAB : offDiagProd r
      = (∏ i, ∏ j ∈ Iio i, (r i - r j)) * (∏ i, ∏ j ∈ Ioi i, (r i - r j)) := by
    unfold offDiagProd
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      rw [erase_eq_Iio_union_Ioi, Finset.prod_union (disjoint_Iio_Ioi i)]
  -- The lower-triangular product is `δ` itself (transpose the index of summation).
  have hA : (∏ i : Fin n, ∏ j ∈ Iio i, (r i - r j)) = diffProd r := by
    rw [diffProd_eq_prod]
    apply Finset.prod_comm'
    intro i j
    simp [mem_Iio, mem_Ioi]
  -- The upper-triangular product is `(−1)^{C(n,2)} · δ` (negate each factor).
  have hB : (∏ i : Fin n, ∏ j ∈ Ioi i, (r i - r j)) = (-1 : R) ^ (n.choose 2) * diffProd r := by
    have hneg : ∀ i : Fin n, (∏ j ∈ Ioi i, (r i - r j))
        = (-1 : R) ^ (Ioi i).card * ∏ j ∈ Ioi i, (r j - r i) := fun i => by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => by ring
    rw [Finset.prod_congr rfl fun i _ => hneg i, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, sum_card_Ioi, diffProd_eq_prod]
  rw [hAB, hA, hB, disc]; ring

/-- **The discriminant as a signed off-diagonal product.**  The mirror form of
`offDiagProd_eq_sign_mul_disc`: `δ² = (−1)^{C(n,2)} · ∏ᵢ ∏_{j ≠ i}(rᵢ − rⱼ)`. -/
theorem disc_eq_sign_mul_offDiagProd {n : ℕ} (r : Fin n → R) :
    disc r = (-1) ^ (n.choose 2) * offDiagProd r := by
  rw [offDiagProd_eq_sign_mul_disc, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_mul]

end AbelRuffiniDiscriminantStructure
