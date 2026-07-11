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
  above: everything in the `SLₙ(ℤ)`-orbit of `eᵢ` is primitive.
* `exists_sl_mulVec_single_of_isPrimitive` — the **converse (hard) half in every
  dimension**: a strong induction on the ℓ¹ measure `∑ₖ |vₖ|`, via the transvection
  Euclidean-reduction step `sum_natAbs_update_emod_lt`, carries any primitive vector
  to a unit multiple `c · eₖ` of a basis vector.  Combined with the easy half this
  gives `isPrimitive_iff_exists_sl_single`, the coordinate-free description of the
  `SLₙ(ℤ)`-orbits on primitive vectors.
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
— that primitivity is also *sufficient* — is discharged in every dimension by the
Euclidean descent `exists_sl_mulVec_single_of_isPrimitive` below. -/
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

/-! ### The Euclidean descent in arbitrary dimension

The `n = 2` argument above is a *single* closed-form Bézout move.  For general `n`
the reduction is iterated: repeatedly apply a transvection that replaces the larger
of two nonzero coordinates by its remainder modulo the smaller, driving the ℓ¹ size
`∑ₖ |vₖ|` strictly down until a single unit coordinate remains.  The two ingredients
below package that descent.  Together they discharge the converse (sufficiency) half
of transitivity that `orbit_e_isPrimitive` recorded as remaining work, in **every**
dimension: a primitive vector is exactly one that is `SLₙ(ℤ)`-equivalent to a unit
multiple of a basis vector. -/

/-- **The Euclidean reduction step strictly decreases the ℓ¹ measure.**  Replacing
the `i`-th coordinate of `v` by the remainder `v i % v j` — the effect of the
transvection with `c = -(v i / v j)`, see `transvectionSL_mulVec` — lowers the total
`∑ₖ |vₖ|`, provided the reducing coordinate `v j` is nonzero and no larger in absolute
value than the pivot `v i`.  This is the well-founded measure that makes the descent
terminate: `0 ≤ v i % v j < |v j| ≤ |v i|`, so exactly the `i`-th summand shrinks. -/
theorem sum_natAbs_update_emod_lt {v : Fin n → ℤ} {i j : Fin n}
    (hj : v j ≠ 0) (hle : (v j).natAbs ≤ (v i).natAbs) :
    (∑ k, (Function.update v i (v i % v j) k).natAbs) < ∑ k, (v k).natAbs := by
  have h0 : 0 ≤ v i % v j := Int.emod_nonneg (v i) hj
  have hlt : (v i % v j).natAbs < (v i).natAbs := by
    have h1 : ((v i % v j).natAbs : ℤ) < ((v j).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg h0, ← Int.abs_eq_natAbs]
      exact Int.emod_lt_abs (v i) hj
    exact lt_of_lt_of_le (by exact_mod_cast h1) hle
  apply Finset.sum_lt_sum
  · intro k _
    rcases eq_or_ne k i with rfl | hk
    · simpa using hlt.le
    · simp [Function.update_of_ne hk]
  · exact ⟨i, Finset.mem_univ i, by rw [Function.update_self]; exact hlt⟩

/-- **Transitivity of the `SLₙ(ℤ)`-action, converse (sufficiency) half — every
dimension.**  Every primitive vector `v` is carried by some `A ∈ SLₙ(ℤ)` to a unit
multiple `c · eₖ` of a standard basis vector.  This is the general-`n` Euclidean
descent that `orbit_e_isPrimitive` recorded as remaining work: proved by strong
induction on the ℓ¹ measure `∑ₖ |vₖ|`.

*Descent (`≥ 2` nonzero coordinates).*  Pick two distinct nonzero coordinates and let
`i` be the one of larger absolute value.  A single transvection replaces `v i` by
`v i % v j`, strictly lowering the measure (`sum_natAbs_update_emod_lt`) while
preserving primitivity (`IsPrimitive.mulVec`); the inductive hypothesis handles the
smaller vector and we prepend the transvection.

*Base (`1` nonzero coordinate).*  The vector is `v = (v k) · eₖ`; primitivity forces
its single entry `v k` to be a unit, and `A = 1` already exhibits it as `Pi.single k
(v k)`.

For `n ≥ 2` this immediately upgrades to the full orbit statement (a unit multiple of
a basis vector is `SLₙ(ℤ)`-equivalent to `e₀`); the `n = 1` case genuinely stops here,
since `SL₁(ℤ) = {1}` fixes `-e₀ ≠ e₀`, both primitive. -/
theorem exists_sl_mulVec_single_of_isPrimitive (v : Fin n → ℤ) (hv : IsPrimitive v) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) (c : ℤ),
      IsUnit c ∧ ↑ₘA *ᵥ v = Pi.single k c := by
  -- Strong induction on the ℓ¹ measure `∑ₖ |vₖ|`.
  suffices H : ∀ N, ∀ v : Fin n → ℤ, IsPrimitive v → (∑ k, (v k).natAbs) = N →
      ∃ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) (c : ℤ),
        IsUnit c ∧ ↑ₘA *ᵥ v = Pi.single k c by
    exact H _ v hv rfl
  intro N
  induction' N using Nat.strong_induction_on with N ih
  intro v hv hN
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0) with hS
  by_cases hcard : 1 < S.card
  · -- Descent: at least two nonzero coordinates.
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    have hva : v a ≠ 0 := (Finset.mem_filter.mp ha).2
    have hvb : v b ≠ 0 := (Finset.mem_filter.mp hb).2
    -- One reduction step, applied to the appropriately ordered pair.
    have step : ∀ i j : Fin n, i ≠ j → v j ≠ 0 → (v j).natAbs ≤ (v i).natAbs →
        ∃ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) (c : ℤ),
          IsUnit c ∧ ↑ₘA *ᵥ v = Pi.single k c := by
      intro i j hij hjne hle
      have hval : v i + -(v i / v j) * v j = v i % v j := by
        linear_combination -Int.emod_add_mul_ediv (v i) (v j)
      have hTact : ↑ₘ(transvectionSL i j hij (-(v i / v j))) *ᵥ v
          = Function.update v i (v i % v j) := by
        rw [transvectionSL_mulVec, hval]
      have hprim' : IsPrimitive (Function.update v i (v i % v j)) := by
        rw [← hTact]; exact hv.mulVec _
      have hmeas : (∑ k, (Function.update v i (v i % v j) k).natAbs) < N := by
        have hstep := sum_natAbs_update_emod_lt hjne hle
        rw [hN] at hstep; exact hstep
      obtain ⟨A', k, c', hc'unit, hA'eq⟩ :=
        ih _ hmeas (Function.update v i (v i % v j)) hprim' rfl
      refine ⟨A' * transvectionSL i j hij (-(v i / v j)), k, c', hc'unit, ?_⟩
      rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hTact, hA'eq]
    rcases le_total (v a).natAbs (v b).natAbs with hle | hle
    · exact step b a (fun h => hab h.symm) hva hle
    · exact step a b hab hvb hle
  · -- Base case: exactly one nonzero coordinate.
    have hne : S.Nonempty := by
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv.ne_zero
      exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩
    have hcard1 : S.card = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp (lt_of_not_ge (fun h => hcard h)))
        (Finset.card_pos.mpr hne)
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard1
    have hvk : v k ≠ 0 := by
      have hmem : k ∈ S := hk ▸ Finset.mem_singleton_self k
      exact (Finset.mem_filter.mp hmem).2
    have hzero : ∀ j, j ≠ k → v j = 0 := by
      intro j hjk
      by_contra hj0
      have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj0⟩
      rw [hk, Finset.mem_singleton] at hmem
      exact hjk hmem
    have hvsingle : v = Pi.single k (v k) := by
      funext j
      rcases eq_or_ne j k with rfl | hjk
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hjk]; exact hzero j hjk
    obtain ⟨w, hw⟩ := hv
    rw [hvsingle, dotProduct_single] at hw
    have hvw : v k * w k = 1 := by rw [mul_comm]; exact hw
    have hunit : IsUnit (v k) := IsUnit.of_mul_eq_one (w k) hvw
    refine ⟨1, k, v k, hunit, ?_⟩
    rw [SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact hvsingle

/-- **Primitivity ⇔ `SLₙ(ℤ)`-reducibility to a unit basis multiple.**  Combining the
descent `exists_sl_mulVec_single_of_isPrimitive` (forward) with `SLₙ(ℤ)`-invariance of
primitivity (`isPrimitive_mulVec_iff`, backward), a vector is primitive exactly when
some unimodular matrix carries it to `c · eₖ` for a unit `c`.  This is the
coordinate-count-free characterization of the `SLₙ(ℤ)`-orbits on primitive vectors,
valid in every dimension. -/
theorem isPrimitive_iff_exists_sl_single (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∃ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) (c : ℤ),
      IsUnit c ∧ ↑ₘA *ᵥ v = Pi.single k c := by
  refine ⟨exists_sl_mulVec_single_of_isPrimitive v, ?_⟩
  rintro ⟨A, k, c, hc, hAv⟩
  have hp : IsPrimitive (↑ₘA *ᵥ v) := by
    rw [hAv]
    exact isPrimitive_of_isUnit_apply (i := k) (by rw [Pi.single_eq_same]; exact hc)
  exact (isPrimitive_mulVec_iff A v).mp hp

/-! ### Sharp transitivity for `n ≥ 2`

`isPrimitive_iff_exists_sl_single` reaches only a *unit multiple* `c · eₖ` of a
basis vector, and this weaker form is the best possible *uniformly in `n`*.  For
`n ≥ 2` it sharpens to the classical statement of the open question: `SLₙ(ℤ)` acts
**transitively** on primitive vectors, so any primitive vector is carried onto any
other — in particular onto the first basis vector `e₁ = (1, 0, …, 0)`, exactly as
the parent 2×2 `bezoutSL` does for a coprime pair.

The dimension hypothesis is genuinely necessary, not an artefact of the proof.  For
`n = 1` the only unimodular matrix is the identity (`SL₁(ℤ) = {1}`), so the two
primitive vectors `(1)` and `(-1)` lie in *distinct* orbits — no `SL₁(ℤ)` move
connects them.  That is precisely the sign ambiguity the uniform `c · eₖ`
description is forced to leave open. -/

/-- **Core normalizing move.**  For distinct coordinates `k ≠ t` and signs
`c, d` (units, i.e. `±1`), the two-transvection product
`T_{k,t}(-cd) · T_{t,k}(dc)` carries `c · eₖ` to `d · eₜ`.  No lower bound on `n`
is needed here: the two coordinates `k` and `t` already supply the scratch space
for the `2×2` rotation.  This is the atomic step that reshuffles sign and position
after the descent has collapsed a primitive vector onto one coordinate. -/
theorem exists_sl_single_orbit_ne {c d : ℤ} (hc : IsUnit c) (hd : IsUnit d)
    {k t : Fin n} (hkt : k ≠ t) :
    ∃ B : Matrix.SpecialLinearGroup (Fin n) ℤ,
      ↑ₘB *ᵥ Pi.single k c = Pi.single t d := by
  classical
  refine ⟨transvectionSL k t hkt (-(c * d)) * transvectionSL t k hkt.symm (d * c), ?_⟩
  rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, transvectionSL_mulVec,
    transvectionSL_mulVec]
  funext i
  simp only [Function.update_apply, Pi.single_apply]
  rcases Int.isUnit_iff.mp hc with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hd with rfl | rfl <;>
      by_cases hik : i = k <;> by_cases hit : i = t <;>
        simp_all [Fin.ext_iff] <;> omega

/-- **Reduction to any signed basis vector (`n ≥ 2`).**  Any signed basis vector
`c · eₖ` (`c` a unit) is `SLₙ(ℤ)`-equivalent to any other signed basis vector
`d · eₜ`.  When `k ≠ t` this is one core move; when `k = t` a second coordinate —
available because `n ≥ 2` — is used as a scratch register to flip the sign. -/
theorem exists_sl_single_to_single (hn : 1 < n) {c d : ℤ} (hc : IsUnit c)
    (hd : IsUnit d) (k t : Fin n) :
    ∃ B : Matrix.SpecialLinearGroup (Fin n) ℤ,
      ↑ₘB *ᵥ Pi.single k c = Pi.single t d := by
  rcases eq_or_ne k t with rfl | hkt
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j, hj⟩ := exists_ne k
    obtain ⟨B₁, hB₁⟩ :=
      exists_sl_single_orbit_ne hc isUnit_one (k := k) (t := j) (Ne.symm hj)
    obtain ⟨B₂, hB₂⟩ :=
      exists_sl_single_orbit_ne isUnit_one hd (k := j) (t := k) hj
    refine ⟨B₂ * B₁, ?_⟩
    rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₁, hB₂]
  · exact exists_sl_single_orbit_ne hc hd hkt

/-- **`SLₙ(ℤ)` acts transitively on primitive vectors (`n ≥ 2`).**  Any two
primitive integer vectors are related by a unimodular matrix.  Together with
`orbit_e_isPrimitive` (primitivity is *necessary* to be `SLₙ(ℤ)`-equivalent to a
basis vector), this pins down the orbit structure completely: for `n ≥ 2` the
primitive vectors form a **single** `SLₙ(ℤ)`-orbit. -/
theorem exists_sl_mulVec_eq_of_isPrimitive (hn : 1 < n) {v w : Fin n → ℤ}
    (hv : IsPrimitive v) (hw : IsPrimitive w) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) ℤ, ↑ₘA *ᵥ v = w := by
  obtain ⟨A, k, c, hc, hAv⟩ := exists_sl_mulVec_single_of_isPrimitive v hv
  obtain ⟨A', k', c', hc', hA'w⟩ := exists_sl_mulVec_single_of_isPrimitive w hw
  obtain ⟨B, hB⟩ := exists_sl_single_to_single hn hc hc' k k'
  refine ⟨A'⁻¹ * (B * A), ?_⟩
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hAv, hB, ← hA'w, Matrix.mulVec_mulVec,
    ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, one_mulVec]

/-- **Transitivity onto a basis vector, matching the open-question statement.**  For
`n ≥ 2`, every primitive vector is carried by some `U ∈ SLₙ(ℤ)` exactly onto the
basis vector `eₜ`.  Taking `t = 0` gives `U · v = e₁ = (1, 0, …, 0)`, the
`n`-dimensional generalization of the parent `bezoutSL` construction — now with the
sign fully pinned down, which the uniform `c · eₖ` statement cannot do. -/
theorem exists_sl_mulVec_basis_of_isPrimitive (hn : 1 < n) {v : Fin n → ℤ}
    (hv : IsPrimitive v) (t : Fin n) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) ℤ, ↑ₘA *ᵥ v = Pi.single t (1 : ℤ) :=
  exists_sl_mulVec_eq_of_isPrimitive hn hv (isPrimitive_single t)

/-- **Unimodular column completion (`n ≥ 2`).**  A vector is primitive **iff** it is a
column of some matrix in `SLₙ(ℤ)`: `IsPrimitive v ↔ ∃ A k, ↑ₘA *ᵥ eₖ = v` — the right side
says `v` is the `k`-th column of `A` (`↑ₘA *ᵥ Pi.single k 1` extracts that column).  The
backward direction is `orbit_e_isPrimitive` (any column of a unimodular matrix is
primitive); the forward direction inverts `exists_sl_mulVec_basis_of_isPrimitive` — the `U`
carrying `v` onto `e₀` has `U⁻¹` with `v` as its `0`-th column.  This is the classical
statement that a primitive integer vector **extends to a `ℤ`-basis** (unimodular
completion): the columns of `SLₙ(ℤ)` are *exactly* the primitive vectors.

The dimension hypothesis `1 < n` is essential and not an artefact: for `n = 1` the only
unimodular matrix is the identity, whose sole column is `e₀ = (1)`, so the primitive vector
`(-1)` is *not* a column of any `SL₁(ℤ)` matrix — the same sign obstruction that keeps the
uniform `c · eₖ` normal form (`isPrimitive_iff_exists_sl_single`) from sharpening at `n = 1`. -/
theorem isPrimitive_iff_exists_sl_column (hn : 1 < n) (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∃ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n),
      ↑ₘA *ᵥ Pi.single k (1 : ℤ) = v := by
  refine ⟨fun hv => ?_, ?_⟩
  · obtain ⟨A, hA⟩ := exists_sl_mulVec_basis_of_isPrimitive hn hv ⟨0, by omega⟩
    refine ⟨A⁻¹, ⟨0, by omega⟩, ?_⟩
    rw [← hA, Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, one_mulVec]
  · rintro ⟨A, k, rfl⟩
    exact orbit_e_isPrimitive A k

end BezoutPrimitive
