/-
# Primitive integer vectors and the `SLₙ(ℤ)` action

Research: bezout-identity-oq-01-oq-02-oq-02

The parent proof `bezout-identity-oq-01-oq-02` builds, for a coprime pair `(a, b)`,
an explicit `bezoutSL a b ∈ SL₂(ℤ)` carrying `(a, b)` to the first basis vector
`(1, 0)`.  The open question asks to generalize this to `n` coordinates:
construct a unimodular `n × n` matrix carrying an arbitrary **primitive** integer
vector to `e₁`, i.e. to establish transitivity of the `SLₙ(ℤ)`-action on
primitive vectors.

The full transitivity statement `∀ v primitive, ∃ U ∈ SLₙ(ℤ), U · v = e₁`
requires a Euclidean descent (an iterated Bézout reduction across coordinates).
This file builds the **invariant-theoretic foundation** that any such descent
must respect, all fully machine-checked with no new axioms:

* `IsPrimitive v` — the coordinate-free notion: `v` has an integer *dual*
  `w` with `w · v = 1` (dot product).  Over `ℤ` this is exactly the classical
  "entries generate the unit ideal" / "gcd of the entries is `1`"; see
  `isPrimitive_iff_span_eq_top`.
* `isPrimitive_single` — the target vector `eᵢ` is primitive.
* `IsPrimitive.mulVec` / `isPrimitive_mulVec_iff` — **`SLₙ(ℤ)` preserves
  primitivity**, in both directions.  This is the exact invariance the
  transitivity action lives inside: the `SLₙ(ℤ)`-orbit of `e₁` consists
  precisely of primitive vectors on the "reachable" side, and no unimodular move
  can leave the primitive locus.
* `transvectionSL` — the elementary generators: each transvection
  `I + c·Eᵢⱼ` (`i ≠ j`) is packaged as an element of `SLₙ(ℤ)`, with its explicit
  action `transvectionSL_mulVec` adding `c·vⱼ` to `vᵢ`.  These are the atomic
  moves of the Euclidean descent, and (being in `SLₙ(ℤ)`) they preserve
  primitivity by the general lemma.
* `orbit_e_isPrimitive` — the "easy half" of transitivity assembled from the
  above: everything in the `SLₙ(ℤ)`-orbit of `eᵢ` is primitive.  The converse
  (every primitive vector is in the orbit) is the remaining Euclidean-descent
  step recorded for future work.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

namespace BezoutPrimitive

open Matrix

variable {n : ℕ}

local notation:1024 "↑ₘ" A:1024 =>
  ((A : Matrix.SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)

/-! ### Primitive vectors -/

/-- An integer vector `v` is **primitive** if it has an integer *dual*: a vector
`w` with `w ⬝ᵥ v = 1`.  Equivalently (over `ℤ`, a Bézout domain) the entries of
`v` are setwise coprime, i.e. their gcd is `1`.  This dot-product form is
manifestly `SLₙ(ℤ)`-invariant, which is why it is the convenient notion for the
transitivity question. -/
def IsPrimitive (v : Fin n → ℤ) : Prop := ∃ w : Fin n → ℤ, w ⬝ᵥ v = 1

/-- **The standard basis vector `eᵢ` is primitive** — its own indicator is a dual
pairing to `1`.  This is the target of the transitivity reduction. -/
theorem isPrimitive_single (i : Fin n) : IsPrimitive (Pi.single i (1 : ℤ)) := by
  refine ⟨Pi.single i 1, ?_⟩
  simp [dotProduct, Pi.single_apply]

/-- **Bridge to the classical notion.**  `v` is primitive iff its entries
generate the unit ideal of `ℤ`, i.e. `Ideal.span (range v) = ⊤`.  Over `ℤ` the
right-hand side says exactly that the gcd of the entries is a unit. -/
theorem isPrimitive_iff_span_eq_top (v : Fin n → ℤ) :
    IsPrimitive v ↔ Ideal.span (Set.range v) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by simpa [dotProduct, smul_eq_mul, mul_comm] using hw⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa [dotProduct, smul_eq_mul, mul_comm] using hc⟩

/-- **The gcd characterization of primitivity.**  A vector `v` is primitive iff
every common divisor of its entries is a unit — i.e. `gcd(v₁, …, vₙ) = 1`, the
classical definition.  Forward: a dual `w` with `w ⬝ᵥ v = 1` divides `1` by any
common divisor `d` of the entries (`d ∣ ∑ wᵢvᵢ = 1`), so `d` is a unit.  Reverse
(over `ℤ`, a principal ideal ring): the generator `g` of `Ideal.span (range v)`
divides every entry, hence is a unit by hypothesis, so the ideal is `⊤` and
`isPrimitive_iff_span_eq_top` closes it.  This is the entry-level statement the
opening docstring names ("gcd of the entries is `1`"), complementing the ideal
form. -/
theorem isPrimitive_iff_forall_isUnit_of_dvd (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∀ d : ℤ, (∀ i, d ∣ v i) → IsUnit d := by
  constructor
  · rintro ⟨w, hw⟩ d hd
    apply isUnit_of_dvd_one
    rw [← hw, dotProduct]
    exact Finset.dvd_sum fun i _ => (hd i).mul_left (w i)
  · intro h
    rw [isPrimitive_iff_span_eq_top]
    haveI hP : (Ideal.span (Set.range v)).IsPrincipal :=
      IsPrincipalIdealRing.principal _
    set I := Ideal.span (Set.range v) with hI
    have hgen : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Submodule.IsPrincipal.span_singleton_generator I
    set g := Submodule.IsPrincipal.generator I with hg
    have hdvd : ∀ i, g ∣ v i := by
      intro i
      have hmem : v i ∈ I := Ideal.subset_span (Set.mem_range_self i)
      rw [← hgen] at hmem
      exact Ideal.mem_span_singleton.mp hmem
    have hu : IsUnit g := h g hdvd
    rw [← hgen]
    exact Ideal.span_singleton_eq_top.mpr hu

/-! ### `SLₙ(ℤ)` preserves primitivity -/

/-- **`SLₙ(ℤ)` sends primitive vectors to primitive vectors.**  If `w ⬝ᵥ v = 1`
then `(w ᵥ* ↑ₘA⁻¹) ⬝ᵥ (↑ₘA *ᵥ v) = 1`, because `↑ₘA⁻¹ * ↑ₘA = 1`.  So the
transformed dual `w ᵥ* ↑ₘA⁻¹` witnesses primitivity of `↑ₘA *ᵥ v`. -/
theorem IsPrimitive.mulVec (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    {v : Fin n → ℤ} (h : IsPrimitive v) : IsPrimitive (↑ₘA *ᵥ v) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w ᵥ* ↑ₘ(A⁻¹), ?_⟩
  have hinv : ↑ₘ(A⁻¹) * ↑ₘA = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  rw [dotProduct_mulVec, vecMul_vecMul, hinv, vecMul_one, hw]

/-- **`SLₙ(ℤ)` preserves primitivity, both directions.**  Since `↑ₘA⁻¹ *ᵥ (↑ₘA *ᵥ v) = v`,
the forward lemma applied to `A⁻¹` gives the reverse implication. -/
theorem isPrimitive_mulVec_iff (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : Fin n → ℤ) : IsPrimitive (↑ₘA *ᵥ v) ↔ IsPrimitive v := by
  refine ⟨fun h => ?_, fun h => h.mulVec A⟩
  have h2 := h.mulVec A⁻¹
  rwa [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, one_mulVec] at h2

/-! ### Elementary generators: transvections in `SLₙ(ℤ)` -/

/-- The **transvection** `I + c·Eᵢⱼ` (`i ≠ j`), packaged as an element of
`SLₙ(ℤ)`.  These are the elementary Bézout moves of the Euclidean descent that
proves transitivity; each has determinant `1`. -/
def transvectionSL (i j : Fin n) (h : i ≠ j) (c : ℤ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j h c⟩

/-- **Action of a transvection on a vector.**  `transvectionSL i j h c` adds
`c · vⱼ` to the `i`-th coordinate of `v` and leaves the others fixed — one
elementary step of Bézout reduction. -/
theorem transvectionSL_mulVec (i j : Fin n) (h : i ≠ j) (c : ℤ) (v : Fin n → ℤ) :
    ↑ₘ(transvectionSL i j h c) *ᵥ v = Function.update v i (v i + c * v j) := by
  show Matrix.transvection i j c *ᵥ v = _
  rw [Matrix.transvection, add_mulVec, one_mulVec, single_mulVec]
  funext k
  rcases eq_or_ne k i with rfl | hk
  · simp
  · simp [Function.update_of_ne hk]

/-- **A transvection preserves primitivity** — a special case of
`IsPrimitive.mulVec`, recorded because transvections are the atomic moves of the
descent. -/
theorem IsPrimitive.transvection (i j : Fin n) (h : i ≠ j) (c : ℤ) {v : Fin n → ℤ}
    (hv : IsPrimitive v) : IsPrimitive (Function.update v i (v i + c * v j)) := by
  rw [← transvectionSL_mulVec i j h c v]
  exact hv.mulVec _

/-! ### The easy half of transitivity -/

/-- **Every vector in the `SLₙ(ℤ)`-orbit of a basis vector is primitive.**  This
is the "necessity" half of the transitivity characterization: primitivity is a
necessary condition for a vector to be `SLₙ(ℤ)`-equivalent to `eᵢ`.  The converse
— that primitivity is also *sufficient* (every primitive vector is in the orbit)
— is the remaining Euclidean-descent construction. -/
theorem orbit_e_isPrimitive (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (i : Fin n) :
    IsPrimitive (↑ₘA *ᵥ Pi.single i (1 : ℤ)) :=
  (isPrimitive_single i).mulVec A

/-! ### Closure properties and the one-dimensional base case -/

/-- **A primitive vector is nonzero.**  If `v = 0` then `w ⬝ᵥ v = 0 ≠ 1` for every
`w`, contradicting primitivity.  (In particular there are no primitive vectors in
the empty dimension `n = 0`.)  Any Euclidean descent needs this to know the pivot
coordinate can be made nonzero. -/
theorem IsPrimitive.ne_zero {v : Fin n → ℤ} (h : IsPrimitive v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨w, hw⟩ := h
  rw [dotProduct_zero] at hw
  exact one_ne_zero hw.symm

/-- **A unit coordinate makes the whole vector primitive.**  If some entry `vᵢ` is
a unit (over `ℤ`, `vᵢ = ±1`) then `v` is primitive: the single dual
`w = (vᵢ)⁻¹ · eᵢ` pairs `v` to `1`.  This is the *termination test* of the
Euclidean descent — the moment a Bézout reduction drives one coordinate down to a
unit, primitivity (hence reachability of `e₁`) is already certified, no further
reduction required.  It is the sufficient-condition companion to
`IsPrimitive.ne_zero`. -/
theorem isPrimitive_of_isUnit_apply {v : Fin n → ℤ} {i : Fin n}
    (hi : IsUnit (v i)) : IsPrimitive v := by
  obtain ⟨u, hu⟩ := hi
  refine ⟨Pi.single i ((u⁻¹ : ℤˣ) : ℤ), ?_⟩
  rw [dotProduct, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Primitivity is preserved under negation.**  If `w ⬝ᵥ v = 1` then
`(-w) ⬝ᵥ (-v) = 1`, so `-v` is primitive with dual `-w`.  A sign flip is an
`SLₙ`-move only in even dimension, but primitivity is sign-invariant in every
dimension. -/
theorem IsPrimitive.neg {v : Fin n → ℤ} (h : IsPrimitive v) : IsPrimitive (-v) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  rw [neg_dotProduct, dotProduct_neg, neg_neg]
  exact hw

/-- **Primitivity is preserved under coordinate permutation.**  Reindexing the
entries of `v` by any permutation `σ` of the coordinates keeps it primitive: if
`w ⬝ᵥ v = 1` then `(w ∘ σ) ⬝ᵥ (v ∘ σ) = 1`, since a permutation only reorders the
terms of the dot-product sum.  A permutation matrix lies in `SLₙ(ℤ)` only when the
permutation is even (its determinant is the sign), so — exactly like
`IsPrimitive.neg` — this invariance holds in every dimension beyond the `SLₙ`-orbit
itself.  The Euclidean descent uses it to bring a chosen pivot coordinate into
position without disturbing primitivity. -/
theorem IsPrimitive.comp_perm (σ : Equiv.Perm (Fin n)) {v : Fin n → ℤ}
    (h : IsPrimitive v) : IsPrimitive (v ∘ σ) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w ∘ σ, ?_⟩
  have hsum : (w ∘ σ) ⬝ᵥ (v ∘ σ) = w ⬝ᵥ v := by
    simp only [dotProduct, Function.comp_apply]
    exact Equiv.sum_comp σ (fun i => w i * v i)
  rw [hsum, hw]

/-- **One-dimensional base case of the descent.**  A vector `v : Fin 1 → ℤ` is
primitive iff its single entry is a unit, i.e. `v 0 = 1` or `v 0 = -1`.  So in
dimension `1` the primitive vectors are exactly `±e₁` — the descent has nothing
left to do, which is the base case of the Euclidean reduction proving transitivity
of the `SLₙ(ℤ)`-action. -/
theorem isPrimitive_fin_one_iff (v : Fin 1 → ℤ) :
    IsPrimitive v ↔ v 0 = 1 ∨ v 0 = -1 := by
  have hdot : ∀ x y : Fin 1 → ℤ, x ⬝ᵥ y = x 0 * y 0 := fun x y => by
    simp [dotProduct]
  constructor
  · rintro ⟨w, hw⟩
    rw [hdot] at hw
    have hu : IsUnit (v 0) :=
      IsUnit.of_mul_eq_one (w 0) (by rw [mul_comm]; exact hw)
    rwa [Int.isUnit_iff] at hu
  · intro h
    refine ⟨v, ?_⟩
    rw [hdot]
    rcases h with h | h <;> rw [h] <;> norm_num

/-- **The empty dimension has no primitive vectors.**  When `n = 0` every vector is
`0` (there are no coordinates to distinguish), and `0` is never primitive
(`IsPrimitive.ne_zero`).  This is the degenerate floor below the `Fin 1` base case:
there is nothing to reduce and no target `e₁` to reach, so the descent is vacuous. -/
theorem not_isPrimitive_fin_zero (v : Fin 0 → ℤ) : ¬ IsPrimitive v :=
  fun h => h.ne_zero (Subsingleton.elim v 0)

/-! ### The first nontrivial case of transitivity: dimension 2 -/

/-- **Transitivity of the `SL₂(ℤ)`-action, base case.**  Every primitive vector
`v : Fin 2 → ℤ` is carried to `e₁ = (1, 0)` by an *explicit* unimodular matrix.
Given a dual `w` with `w ⬝ᵥ v = 1`, the matrix
`![![w 0, w 1], ![-v 1, v 0]]` has determinant `w 0 · v 0 + w 1 · v 1 = 1`,
so it lies in `SL₂(ℤ)`, and its first row `w` pairs `v` to `1` while its second
row `(-v 1, v 0)` pairs `v` to `0`.  This is the `n = 2` instance of the
Euclidean-descent step that `orbit_e_isPrimitive` records as remaining work — here
the descent is a single Bézout move, so the construction is closed form.  Together
with the easy half it upgrades to the full characterization
`isPrimitive_fin_two_iff_orbit`. -/
theorem isPrimitive_fin_two_orbit {v : Fin 2 → ℤ} (hv : IsPrimitive v) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (A : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v = Pi.single 0 1 := by
  obtain ⟨w, hw⟩ := hv
  have hwv : w 0 * v 0 + w 1 * v 1 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two] using hw
  refine ⟨⟨!![w 0, w 1; -v 1, v 0], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hwv
  · funext k
    fin_cases k <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      linarith [hwv]

/-- **Full transitivity in dimension 2.**  A vector `v : Fin 2 → ℤ` is primitive
iff it is `SL₂(ℤ)`-equivalent to `e₁`.  The forward direction is the closed-form
Bézout reduction `isPrimitive_fin_two_orbit`; the reverse is the invariance
`isPrimitive_mulVec_iff` applied to the primitive target `e₁`.  This is the
converse (sufficiency) half of the transitivity characterization, established in
full for `n = 2`. -/
theorem isPrimitive_fin_two_iff_orbit (v : Fin 2 → ℤ) :
    IsPrimitive v ↔ ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (A : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v = Pi.single 0 1 := by
  refine ⟨isPrimitive_fin_two_orbit, ?_⟩
  rintro ⟨A, hA⟩
  have h : IsPrimitive ((A : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) := by
    rw [hA]; exact isPrimitive_single 0
  exact (isPrimitive_mulVec_iff A v).mp h

end BezoutPrimitive
