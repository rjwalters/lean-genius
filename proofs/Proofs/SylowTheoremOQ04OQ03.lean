/-
  Toward the simplicity of PSL(2, p) for primes p ≥ 5 (Sylow OQ-04 OQ-03)

  Parent open question sylow-theorem-oq-04-oq-03: prove that PSL(2, p) is simple
  for every prime p ≥ 5, generalizing the parent entry's A₅ = PSL(2,5) result to
  the first infinite family of finite simple groups.

  The full theorem is genuinely blocked on a large body of missing Mathlib
  infrastructure (the action of PSL(2,p) on the projective line P¹(𝔽_p), its
  2-transitivity, an Iwasawa structure, and perfectness for p ≥ 5). The standard
  modern route is *not* a raw Sylow count but Iwasawa's criterion applied to that
  action; see the research knowledge file for the full assessment.

  This file builds one clean, fully verified piece of that infrastructure: the
  **unipotent one-parameter subgroup**

      U = { [[1, t], [0, 1]] : t ∈ 𝔽_p } ⊆ SL(2, 𝔽_p).

  U is exactly the abelian normal subgroup of the Borel (stabilizer of ∞) that the
  Iwasawa criterion requires, and it is the order-p Sylow subgroup of SL(2, p).
  We show:

  * `unipotentUpper t` is a genuine element of `SL(2, ZMod p)` (determinant 1);
  * `t ↦ unipotentUpper t` is an injective group homomorphism from the additive
    group `(ZMod p, +)` (written multiplicatively) into `SL(2, ZMod p)`
    (`unipotentHom`), so its image is abelian and isomorphic to `ZMod p`;
  * the image has cardinality exactly `p` (the order-p Sylow / unipotent subgroup).

  We then build the **split diagonal torus**

      T = { [[a, 0], [0, a⁻¹]] : a ∈ 𝔽_pˣ } ⊆ SL(2, 𝔽_p),

  the second factor of the Borel `B = U ⋊ T`, and prove the two facts Iwasawa's
  criterion needs about the pair `(U, T)`:

  * `t ↦ torusDiag a` is an injective group homomorphism `(ZMod p)ˣ →* SL(2, ZMod p)`
    (`torusHom`), so its image is the abelian torus of cardinality exactly `p − 1`
    (`card_torus_range`);
  * **T normalizes U** with the conjugation acting through the square map: for every
    `a ∈ 𝔽_pˣ` and `t ∈ 𝔽_p`,

        diag(a) · [[1, t], [0, 1]] · diag(a)⁻¹ = [[1, a²·t], [0, 1]]

    (`torusHom_conj_unipotent`), so each `T`-conjugate of a unipotent element is
    again unipotent (`torus_normalizes_unipotent`). This is precisely the
    `U ⊴ B` normality that makes `B = U ⋊ T` the point stabiliser required by
    Iwasawa's lemma, and it exhibits the `a ↦ a²` action of the torus on the root
    group that governs the whole SL(2) structure theory.

  Everything here is `sorry`-free and axiom-free; the deep simplicity theorem
  remains open.

  References:
  - Rotman, An Introduction to the Theory of Groups (4th ed.), §9.
  - Dixon & Mortimer, Permutation Groups, §3.3 (Iwasawa's lemma), §2.8.

  Tags: group-theory, sylow, PSL, special-linear-group, unipotent, iwasawa,
        borel, torus, normalizer
-/

import Mathlib

open Matrix

namespace SylowOQ04OQ03

variable {p : ℕ} [Fact p.Prime]

/-!
## The unipotent one-parameter subgroup of `SL(2, ZMod p)`

We embed `(ZMod p, +)` into `SL(2, ZMod p)` via the upper-triangular unipotent
matrices `[[1, t], [0, 1]]`.
-/

/-- The upper unipotent matrix `[[1, t], [0, 1]]`, viewed as an element of
`SL(2, ZMod p)`. Its determinant is `1 · 1 − t · 0 = 1`. -/
def unipotentUpper (t : ZMod p) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem val_unipotentUpper (t : ZMod p) :
    (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, t; 0, 1] := rfl

/-- The unipotent embedding is additive: `[[1,s],[0,1]] · [[1,t],[0,1]] = [[1,s+t],[0,1]]`. -/
theorem unipotentUpper_mul (s t : ZMod p) :
    unipotentUpper s * unipotentUpper t = unipotentUpper (s + t) := by
  apply Subtype.ext
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, t; 0, 1]
      = !![1, s + t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The unipotent embedding sends `0` to the identity matrix. -/
theorem unipotentUpper_zero : unipotentUpper (0 : ZMod p) = 1 := by
  apply Subtype.ext
  show (!![1, (0 : ZMod p); 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
  rw [Matrix.one_fin_two]

/-- Elements of the unipotent subgroup commute (it is abelian). -/
theorem unipotentUpper_comm (s t : ZMod p) :
    unipotentUpper s * unipotentUpper t = unipotentUpper t * unipotentUpper s := by
  rw [unipotentUpper_mul, unipotentUpper_mul, add_comm]

/-- The unipotent embedding is injective (read off the top-right entry). -/
theorem unipotentUpper_injective :
    Function.Injective (unipotentUpper (p := p)) := by
  intro s t h
  have h' : (unipotentUpper s : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
      = (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 := by rw [h]
  simpa using h'

/-- The unipotent one-parameter subgroup packaged as a group homomorphism from the
additive group `(ZMod p, +)` (written multiplicatively) into `SL(2, ZMod p)`.

This is the abelian normal subgroup of the Borel stabilizer required by Iwasawa's
simplicity criterion for `PSL(2, p)`. -/
def unipotentHom :
    Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun t := unipotentUpper (Multiplicative.toAdd t)
  map_one' := by simpa using unipotentUpper_zero
  map_mul' s t := by
    simpa using
      (unipotentUpper_mul (Multiplicative.toAdd s) (Multiplicative.toAdd t)).symm

@[simp] theorem unipotentHom_apply (t : Multiplicative (ZMod p)) :
    unipotentHom t = unipotentUpper (Multiplicative.toAdd t) := rfl

/-- `unipotentHom` is injective, so its range is a subgroup of `SL(2, ZMod p)`
isomorphic to `(ZMod p, +)`. -/
theorem unipotentHom_injective : Function.Injective (unipotentHom (p := p)) := by
  intro s t h
  exact Multiplicative.toAdd.injective (unipotentUpper_injective h)

/-- The unipotent subgroup has cardinality exactly `p`: it is the order-`p`
Sylow-`p` subgroup of `SL(2, p)`. -/
theorem card_unipotent_range :
    Nat.card (Set.range (unipotentUpper (p := p))) = p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have e : ZMod p ≃ Set.range (unipotentUpper (p := p)) :=
    Equiv.ofInjective _ unipotentUpper_injective
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card]

/-!
## The split diagonal torus and its normalizing action on `U`

We now build the split maximal torus

    T = { [[a, 0], [0, a⁻¹]] : a ∈ (ZMod p)ˣ } ⊆ SL(2, ZMod p),

the second factor of the Borel `B = U ⋊ T`, and prove that `T` normalizes the
unipotent subgroup `U` by conjugation through the square map `a ↦ a²`.
-/

/-- The split diagonal matrix `[[a, 0], [0, a⁻¹]]` for a unit `a`, viewed as an
element of `SL(2, ZMod p)`. Its determinant is `a · a⁻¹ − 0 · 0 = 1`. -/
def torusDiag (a : (ZMod p)ˣ) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)], by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]; exact Units.mul_inv a⟩

@[simp] theorem val_torusDiag (a : (ZMod p)ˣ) :
    (torusDiag a : Matrix (Fin 2) (Fin 2) (ZMod p))
      = !![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)] := rfl

/-- The diagonal embedding is multiplicative:
`[[a,0],[0,a⁻¹]] · [[b,0],[0,b⁻¹]] = [[ab,0],[0,(ab)⁻¹]]`. -/
theorem torusDiag_mul (a b : (ZMod p)ˣ) :
    torusDiag a * torusDiag b = torusDiag (a * b) := by
  apply Subtype.ext
  have hab : (((a * b)⁻¹ : (ZMod p)ˣ) : ZMod p)
      = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    rw [mul_inv, Units.val_mul]
  show ((!![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)]
        : Matrix (Fin 2) (Fin 2) (ZMod p))
        * !![(b : ZMod p), 0; 0, ((b⁻¹ : (ZMod p)ˣ) : ZMod p)])
      = !![((a * b : (ZMod p)ˣ) : ZMod p), 0; 0, (((a * b)⁻¹ : (ZMod p)ˣ) : ZMod p)]
  rw [Units.val_mul, hab]
  set x := (a : ZMod p)
  set y := (b : ZMod p)
  set xi := ((a⁻¹ : (ZMod p)ˣ) : ZMod p)
  set yi := ((b⁻¹ : (ZMod p)ˣ) : ZMod p)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The diagonal embedding sends the unit `1` to the identity matrix. -/
theorem torusDiag_one : torusDiag (1 : (ZMod p)ˣ) = 1 := by
  apply Subtype.ext
  show (!![((1 : (ZMod p)ˣ) : ZMod p), 0; 0, (((1 : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)]
      : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
  rw [Matrix.one_fin_two]
  simp

/-- The split torus packaged as a group homomorphism from the unit group
`(ZMod p)ˣ` into `SL(2, ZMod p)`. Its image is the split maximal torus `T`. -/
def torusHom : (ZMod p)ˣ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun := torusDiag
  map_one' := torusDiag_one
  map_mul' a b := (torusDiag_mul a b).symm

@[simp] theorem torusHom_apply (a : (ZMod p)ˣ) : torusHom a = torusDiag a := rfl

/-- The diagonal embedding is injective (read off the top-left entry). -/
theorem torusDiag_injective : Function.Injective (torusDiag (p := p)) := by
  intro a b h
  apply Units.ext
  -- `↑(torusDiag a) 0 0` reduces definitionally to `↑a`, so the top-left entry
  -- gives `↑a = ↑b` directly.
  exact congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h

/-- `torusHom` is injective, so its range is a subgroup of `SL(2, ZMod p)`
isomorphic to `(ZMod p)ˣ`. -/
theorem torusHom_injective : Function.Injective (torusHom (p := p)) :=
  torusDiag_injective

/-- The split torus has cardinality exactly `p − 1`: it is the maximal split
torus `T`, the complement of `U` in the Borel `B = U ⋊ T`. -/
theorem card_torus_range :
    Nat.card (Set.range (torusDiag (p := p))) = p - 1 := by
  have e : (ZMod p)ˣ ≃ Set.range (torusDiag (p := p)) :=
    Equiv.ofInjective _ torusDiag_injective
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **The torus normalizes the unipotent subgroup, acting by squares.** For every
unit `a` and every `t`, conjugating the unipotent element `[[1, t], [0, 1]]` by the
diagonal `diag(a) = [[a, 0], [0, a⁻¹]]` returns the unipotent element `[[1, a²t],
[0, 1]]`:

    diag(a) · [[1, t], [0, 1]] · diag(a)⁻¹ = [[1, a²·t], [0, 1]].

This is the `U ⊴ B` normality that makes the Borel `B = U ⋊ T` the point
stabiliser required by Iwasawa's simplicity criterion, and exhibits the `a ↦ a²`
action of the split torus on the root group `U`. -/
theorem torusHom_conj_unipotent (a : (ZMod p)ˣ) (t : ZMod p) :
    torusHom a * unipotentUpper t * (torusHom a)⁻¹
      = unipotentUpper ((a : ZMod p) ^ 2 * t) := by
  have ha : (a : ZMod p) * ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv a
  have ha' : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p) = 1 := Units.inv_mul a
  have haa : (((a⁻¹ : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) = (a : ZMod p) := by
    rw [inv_inv]
  rw [← map_inv torusHom]
  apply Subtype.ext
  show (((!![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)]
        : Matrix (Fin 2) (Fin 2) (ZMod p))
        * !![1, t; 0, 1])
        * !![((a⁻¹ : (ZMod p)ˣ) : ZMod p), 0; 0,
            (((a⁻¹ : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)])
      = !![1, (a : ZMod p) ^ 2 * t; 0, 1]
  rw [haa]
  set x := (a : ZMod p)
  set xi := ((a⁻¹ : (ZMod p)ˣ) : ZMod p)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ha'] <;> ring

/-- Each `T`-conjugate of a unipotent element is again unipotent: the torus maps
the unipotent subgroup `U` into itself under conjugation. -/
theorem torus_normalizes_unipotent (a : (ZMod p)ˣ) (t : ZMod p) :
    torusHom a * unipotentUpper t * (torusHom a)⁻¹
      ∈ Set.range (unipotentUpper (p := p)) :=
  ⟨(a : ZMod p) ^ 2 * t, (torusHom_conj_unipotent a t).symm⟩

/-!
## The Weyl element and the Bruhat ingredients

Beyond the Borel `B = U ⋊ T`, the Iwasawa/Bruhat structure of `SL(2, p)` needs the
non-trivial coset representative of the Weyl group `W = N(T)/T ≅ ℤ/2`, the
**Weyl element**

    w = [[0, -1], [1, 0]] ∈ SL(2, 𝔽_p).

On the projective line `P¹(𝔽_p)` it is the involution swapping `0 ↔ ∞`; together with
`B` it produces the Bruhat decomposition `SL(2,p) = B ⊔ B w B`.  We record the two
structural facts that drive the whole SL(2) theory:

* `w` reflects the torus, `w · diag(a) · w⁻¹ = diag(a⁻¹)` (`weylW_conj_torus`), so
  `w` normalises `T` and acts as the non-trivial Weyl reflection `a ↦ a⁻¹`;
* `w` conjugates the **upper** unipotent subgroup `U` onto the **lower** (opposite)
  unipotent subgroup `U⁻`, `w · [[1,t],[0,1]] · w⁻¹ = [[1,0],[-t,1]]`
  (`weylW_conj_unipotent`).  Since `⟨U, U⁻⟩ = SL(2,p)`, this is exactly the step by
  which the conjugates of the abelian normal `U` fill out the whole group — the
  generation hypothesis of Iwasawa's criterion.

Finally `unipotent_inter_torus_trivial` shows `U ∩ T = 1`, so `B = U ⋊ T` is a genuine
(internal) semidirect product with `|B| = |U| · |T| = p(p-1)`.
-/

/-- The **Weyl element** `w = [[0, -1], [1, 0]]`, viewed as an element of
`SL(2, ZMod p)`.  Its determinant is `0 · 0 − (−1) · 1 = 1`. -/
def weylW : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp] theorem val_weylW :
    (weylW (p := p) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![0, -1; 1, 0] := rfl

/-- The inverse Weyl element `w⁻¹ = [[0, 1], [-1, 0]] = −w`.  Its determinant is
`0 · 0 − 1 · (−1) = 1`. -/
def weylWinv : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp] theorem val_weylWinv :
    (weylWinv (p := p) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![0, 1; -1, 0] := rfl

/-- `w · w⁻¹ = 1`, identifying `weylWinv` as the group inverse of `weylW`. -/
theorem weylW_mul_weylWinv :
    weylW * weylWinv = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  apply Subtype.ext
  show (!![(0 : ZMod p), -1; 1, 0] * !![(0 : ZMod p), 1; -1, 0])
      = (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The group inverse of the Weyl element is `weylWinv = [[0, 1], [-1, 0]]`. -/
@[simp] theorem weylW_inv : (weylW (p := p))⁻¹ = weylWinv :=
  inv_eq_of_mul_eq_one_right weylW_mul_weylWinv

/-- **The Weyl element reflects the split torus.**  Conjugation by `w` inverts the
diagonal parameter:

    w · diag(a) · w⁻¹ = diag(a⁻¹).

Hence `w` normalises `T` and realises the non-trivial element of the Weyl group
`W = N(T)/T ≅ ℤ/2`, acting on `T` by the reflection `a ↦ a⁻¹`. -/
theorem weylW_conj_torus (a : (ZMod p)ˣ) :
    weylW * torusDiag a * weylW⁻¹ = torusDiag a⁻¹ := by
  rw [weylW_inv]
  apply Subtype.ext
  have haa : (((a⁻¹ : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) = (a : ZMod p) := by
    rw [inv_inv]
  show ((!![(0 : ZMod p), -1; 1, 0]
          * !![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)])
          * !![(0 : ZMod p), 1; -1, 0])
      = !![((a⁻¹ : (ZMod p)ˣ) : ZMod p), 0; 0,
          (((a⁻¹ : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)]
  rw [haa]
  set x := (a : ZMod p)
  set xi := ((a⁻¹ : (ZMod p)ˣ) : ZMod p)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The **lower** (opposite) unipotent matrix `[[1, 0], [t, 1]]`, viewed as an
element of `SL(2, ZMod p)`.  Its determinant is `1 · 1 − 0 · t = 1`.  This is the
root group `U⁻` opposite to `U`; together `⟨U, U⁻⟩` generate `SL(2, p)`. -/
def lowerUnipotent (t : ZMod p) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![1, 0; t, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp] theorem val_lowerUnipotent (t : ZMod p) :
    (lowerUnipotent t : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; t, 1] := rfl

/-- **The Weyl element sends the upper unipotent subgroup to the lower one.**
Conjugation by `w` turns `[[1, t], [0, 1]] ∈ U` into `[[1, 0], [-t, 1]] ∈ U⁻`:

    w · [[1, t], [0, 1]] · w⁻¹ = [[1, 0], [-t, 1]].

Because `⟨U, U⁻⟩ = SL(2, p)`, this exhibits `U⁻` as a `w`-conjugate of `U`, the step
that makes the conjugates of the abelian normal subgroup `U` generate the whole
group — precisely the generation hypothesis of Iwasawa's simplicity criterion. -/
theorem weylW_conj_unipotent (t : ZMod p) :
    weylW * unipotentUpper t * weylW⁻¹ = lowerUnipotent (-t) := by
  rw [weylW_inv]
  apply Subtype.ext
  show ((!![(0 : ZMod p), -1; 1, 0] * !![1, t; 0, 1]) * !![(0 : ZMod p), 1; -1, 0])
      = !![1, 0; -t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The Weyl element sends the lower unipotent subgroup back to the upper one.**
The reverse of `weylW_conj_unipotent`: conjugation by `w` turns `[[1, 0], [t, 1]] ∈ U⁻`
into `[[1, -t], [0, 1]] ∈ U`:

    w · [[1, 0], [t, 1]] · w⁻¹ = [[1, -t], [0, 1]].

Together with `weylW_conj_unipotent` this shows `w` interchanges the two opposite root
groups `U ↔ U⁻`; in particular the subgroup `⟨U, U⁻⟩` is stable under conjugation by
`w`, one of the closure facts behind `⟨U, U⁻⟩ = SL(2, p)`. -/
theorem weylW_conj_lowerUnipotent (t : ZMod p) :
    weylW * lowerUnipotent t * weylW⁻¹ = unipotentUpper (-t) := by
  rw [weylW_inv]
  apply Subtype.ext
  show ((!![(0 : ZMod p), -1; 1, 0] * !![1, 0; t, 1]) * !![(0 : ZMod p), 1; -1, 0])
      = !![1, -t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **`w² = −1`.**  The square of the Weyl element is the central scalar `−1`:

    w² = [[0, -1], [1, 0]]² = [[-1, 0], [0, -1]] = −I.

Since `−I` is the non-trivial central element of `SL(2, p)` (for `p > 2`), `w` has
order `4` in `SL(2, p)` and order `2` in `PSL(2, p)`.  This pins down the Weyl group
`W = N(T)/T ≅ ℤ/2`, whose non-trivial element acts on the torus by the reflection
`a ↦ a⁻¹` of `weylW_conj_torus`. -/
theorem val_weylW_sq :
    ((weylW * weylW : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = !![-1, 0; 0, -1] := by
  show (!![(0 : ZMod p), -1; 1, 0] * !![(0 : ZMod p), -1; 1, 0]) = !![-1, 0; 0, -1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **`w⁴ = 1`.**  A direct consequence of `w² = −1`: the Weyl element has order
dividing `4` in `SL(2, p)`. -/
theorem weylW_pow_four :
    weylW * weylW * weylW * weylW = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  apply Subtype.ext
  show (((!![(0 : ZMod p), -1; 1, 0] * !![(0 : ZMod p), -1; 1, 0])
          * !![(0 : ZMod p), -1; 1, 0]) * !![(0 : ZMod p), -1; 1, 0])
      = (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`U ∩ T = 1`.**  The only matrix that is simultaneously upper unipotent
`[[1, t], [0, 1]]` and diagonal `[[a, 0], [0, a⁻¹]]` is the identity: `t = 0` and
`a = 1`.  Combined with `card_unipotent_range` and `card_torus_range`, this makes
`B = U ⋊ T` a genuine internal semidirect product with `|B| = p(p − 1)`. -/
theorem unipotent_inter_torus_trivial (t : ZMod p) (a : (ZMod p)ˣ)
    (h : unipotentUpper t = torusDiag a) : t = 0 ∧ a = 1 := by
  have h01 : (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
      = (torusDiag a : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 := by rw [h]
  have h00 : (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0
      = (torusDiag a : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by rw [h]
  simp only [val_unipotentUpper, val_torusDiag, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h01 h00
  refine ⟨h01, ?_⟩
  exact Units.ext (by rw [Units.val_one]; exact h00.symm)

/-!
## The commutator `[T, U]` and perfectness of the root group

The complementary Iwasawa ingredient is **perfectness**: for `p ≥ 5` every
unipotent element is a commutator, hence lies in the derived subgroup
`[SL(2,p), SL(2,p)]`.  The engine is the single identity

    [diag(a), u(t)] = diag(a)·u(t)·diag(a)⁻¹·u(t)⁻¹ = u((a² − 1)·t),

obtained by composing the torus-conjugation law `torusHom_conj_unipotent`
(`diag(a)·u(t)·diag(a)⁻¹ = u(a²t)`) with the addition law
`u(a²t)·u(−t) = u((a² − 1)t)`.  When the scalar `a² − 1` is a unit of `𝔽_p` the
map `t ↦ [diag(a), u(t)]` covers the whole root group `U`, so every `u(s)` is a
commutator.  This happens for `a = 2` exactly when `p ≥ 5` (then `a² − 1 = 3 ≠ 0`,
while it fails for `p = 2, 3` — precisely the primes for which `PSL(2, p)` is
*not* simple).
-/

/-- The group inverse of a unipotent element: `[[1, t], [0, 1]]⁻¹ = [[1, -t], [0, 1]]`. -/
@[simp] theorem unipotentUpper_inv (t : ZMod p) :
    (unipotentUpper t)⁻¹ = unipotentUpper (-t) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, unipotentUpper_mul, neg_add_cancel, unipotentUpper_zero]

/-- **The commutator of a torus element and a root-group element.**  Conjugating
`u(t)` by `diag(a)` and multiplying by `u(t)⁻¹` scales the unipotent parameter by
`a² − 1`:

    [diag(a), u(t)] = diag(a)·u(t)·diag(a)⁻¹·u(t)⁻¹ = u((a² − 1)·t).

This is the root-group form of the SL(2) commutator relation; iterating it over a
generating unit `a` is what makes `SL(2, p)` perfect for `p ≥ 5`. -/
theorem torus_unipotent_commutator (a : (ZMod p)ˣ) (t : ZMod p) :
    torusHom a * unipotentUpper t * (torusHom a)⁻¹ * (unipotentUpper t)⁻¹
      = unipotentUpper (((a : ZMod p) ^ 2 - 1) * t) := by
  rw [torusHom_conj_unipotent, unipotentUpper_inv, unipotentUpper_mul]
  congr 1
  ring

/-- **Every unipotent element is a commutator when `a² − 1` is a unit.**  If the
scalar `a² − 1` is invertible in `𝔽_p`, then for every `s` the unipotent `u(s)` is
the commutator `[diag(a), u(t)]` with `t = (a² − 1)⁻¹ · s`.  This is the
derived-subgroup membership that feeds the perfectness hypothesis of Iwasawa's
criterion. -/
theorem unipotent_isCommutator_of_isUnit {a : (ZMod p)ˣ}
    (ha : IsUnit ((a : ZMod p) ^ 2 - 1)) (s : ZMod p) :
    ∃ t : ZMod p,
      torusHom a * unipotentUpper t * (torusHom a)⁻¹ * (unipotentUpper t)⁻¹
        = unipotentUpper s := by
  obtain ⟨u, hu⟩ := ha
  refine ⟨((u⁻¹ : (ZMod p)ˣ) : ZMod p) * s, ?_⟩
  rw [torus_unipotent_commutator]
  congr 1
  rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

/-- **For every prime `p ≥ 5`, every unipotent element is a commutator.**  Taking
`a = 2` (a unit since `p ≠ 2`) gives `a² − 1 = 3`, a unit since `p ≠ 3`, so
`unipotent_isCommutator_of_isUnit` applies: each `u(s)` equals `[diag(2), u(t)]`
for a suitable `t`.  Hence the whole root group `U` lies in the derived subgroup —
the perfectness input to Iwasawa's simplicity criterion, valid exactly on the
range `p ≥ 5` where `PSL(2, p)` is simple. -/
theorem exists_unipotent_isCommutator (hp : 5 ≤ p) (s : ZMod p) :
    ∃ (a : (ZMod p)ˣ) (t : ZMod p),
      torusHom a * unipotentUpper t * (torusHom a)⁻¹ * (unipotentUpper t)⁻¹
        = unipotentUpper s := by
  have hp2 : ¬ (p ∣ 2) := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ (p ∣ 3) := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]; exact hp2
    simpa using h
  have h3 : (3 : ZMod p) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]; exact hp3
    simpa using h
  refine ⟨(isUnit_iff_ne_zero.mpr h2).unit, ?_⟩
  have ha_val : (((isUnit_iff_ne_zero.mpr h2).unit : (ZMod p)ˣ) : ZMod p) = 2 :=
    IsUnit.unit_spec _
  have haU : IsUnit ((((isUnit_iff_ne_zero.mpr h2).unit : (ZMod p)ˣ) : ZMod p) ^ 2 - 1) := by
    rw [ha_val]
    have h : (2 : ZMod p) ^ 2 - 1 = 3 := by ring
    rw [h]
    exact isUnit_iff_ne_zero.mpr h3
  exact unipotent_isCommutator_of_isUnit haU s

/-- **For every prime `p ≥ 5`, every *lower* unipotent element is also a commutator.**
Conjugating the upper-unipotent identity by the Weyl element `w` transports it to the
opposite root group: since `w` sends `u(−s) ∈ U` to `lowerUnipotent s ∈ U⁻`
(`weylW_conj_unipotent`) and conjugation carries a commutator `g·h·g⁻¹·h⁻¹` to the
commutator of the conjugates, `lowerUnipotent s` is the commutator of
`w·diag(a)·w⁻¹` and `w·u(t)·w⁻¹`.  Together with `exists_unipotent_isCommutator` this
places **both** root groups `U` and `U⁻` inside the derived subgroup
`[SL(2,p), SL(2,p)]` — the two halves of the perfectness input to Iwasawa's criterion
(recall `⟨U, U⁻⟩ = SL(2,p)`). -/
theorem exists_lowerUnipotent_isCommutator (hp : 5 ≤ p) (s : ZMod p) :
    ∃ g h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
      g * h * g⁻¹ * h⁻¹ = lowerUnipotent s := by
  obtain ⟨a, t, hc⟩ := exists_unipotent_isCommutator hp (-s)
  refine ⟨weylW * torusHom a * weylW⁻¹, weylW * unipotentUpper t * weylW⁻¹, ?_⟩
  -- Conjugation by `w` is a homomorphism, so it distributes over the commutator word;
  -- the interior collapses to the upper-unipotent commutator identity `hc`.
  have key : (weylW * torusHom a * weylW⁻¹) * (weylW * unipotentUpper t * weylW⁻¹)
        * (weylW * torusHom a * weylW⁻¹)⁻¹ * (weylW * unipotentUpper t * weylW⁻¹)⁻¹
      = weylW *
          (torusHom a * unipotentUpper t * (torusHom a)⁻¹ * (unipotentUpper t)⁻¹)
          * weylW⁻¹ := by
    group
  rw [key, hc, weylW_conj_unipotent, neg_neg]

/-!
## Bruhat generation: `⟨U, U⁻⟩ = SL(2, p)`

The final structural input to Iwasawa's criterion is the **generation hypothesis**:
the two opposite root groups generate the whole group,

    ⟨U, U⁻⟩ = SL(2, 𝔽_p).

Combined with the perfectness lemmas above (`exists_unipotent_isCommutator` and
`exists_lowerUnipotent_isCommutator`, which place `U` and `U⁻` inside the derived
subgroup for `p ≥ 5`), this makes `SL(2, p)` perfect — the perfectness half of
Iwasawa — and it is also the generation clause of Iwasawa's lemma itself.

The proof is the concrete **Bruhat/Gauss decomposition** of `SL(2)`.  Two
elementary factorizations feed it:

* the Weyl element is a word in the root groups,
  `w = u(-1) · l(1) · u(-1)` (`weylW_eq_root_word`);
* every torus element is a word in the root groups,
  `diag(a) = u(a) · l(-a⁻¹) · u(a) · w` (`torusDiag_eq_root_word`), so the whole
  split torus `T` lies in `⟨U, U⁻⟩`.

With `w, T ⊆ ⟨U, U⁻⟩` (and `U, U⁻` there by definition) the Bruhat cell
`u(x)·w·diag(c)·u(y)` covers every matrix with nonzero lower-left entry
(`mem_closure_of_lowerLeft_ne_zero`); a single lower transvection `l(1)` moves the
remaining `c = 0` matrices into that cell, giving
`closure_rootGroups_eq_top`.
-/

/-- The lower unipotent embedding is additive:
`[[1,0],[s,1]] · [[1,0],[t,1]] = [[1,0],[s+t,1]]`. -/
theorem lowerUnipotent_mul (s t : ZMod p) :
    lowerUnipotent s * lowerUnipotent t = lowerUnipotent (s + t) := by
  apply Subtype.ext
  show (!![1, 0; s, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, 0; t, 1]
      = !![1, 0; s + t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The lower unipotent embedding sends `0` to the identity matrix. -/
theorem lowerUnipotent_zero : lowerUnipotent (0 : ZMod p) = 1 := by
  apply Subtype.ext
  show (!![1, (0 : ZMod p); 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
  rw [Matrix.one_fin_two]

/-- **The Weyl element is a word in the two root groups.**  `w = u(-1)·l(1)·u(-1)`:

    [[0, -1], [1, 0]] = [[1, -1], [0, 1]] · [[1, 0], [1, 1]] · [[1, -1], [0, 1]].

This exhibits `w ∈ ⟨U, U⁻⟩`, the Bruhat generator that swaps the two root groups. -/
theorem weylW_eq_root_word :
    weylW (p := p)
      = unipotentUpper (-1) * lowerUnipotent 1 * unipotentUpper (-1) := by
  apply Subtype.ext
  show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      = !![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

set_option maxHeartbeats 800000 in
/-- **Every torus element is a word in the two root groups.**
`diag(a) = u(a)·l(-a⁻¹)·u(a)·w`:

    [[a, 0], [0, a⁻¹]]
      = [[1, a], [0, 1]] · [[1, 0], [-a⁻¹, 1]] · [[1, a], [0, 1]] · [[0, -1], [1, 0]].

Hence the whole split torus `T` lies in `⟨U, U⁻⟩`. -/
theorem torusDiag_eq_root_word (a : (ZMod p)ˣ) :
    torusDiag a
      = unipotentUpper (a : ZMod p) * lowerUnipotent (-((a : ZMod p)⁻¹))
          * unipotentUpper (a : ZMod p) * weylW := by
  have hc : (a : ZMod p) ≠ 0 := a.ne_zero
  have hinv : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = (a : ZMod p)⁻¹ :=
    Units.val_inv_eq_inv_val a
  have hab : (a : ZMod p) * (a : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hc
  apply Subtype.ext
  show (!![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)]
        : Matrix (Fin 2) (Fin 2) (ZMod p))
      = !![1, (a : ZMod p); 0, 1] * !![1, 0; -((a : ZMod p)⁻¹), 1]
          * !![1, (a : ZMod p); 0, 1] * !![0, -1; 1, 0]
  rw [hinv]
  -- Generalise the inverse to an opaque atom `b` so `simp` cannot loop on inverse
  -- lemmas while reducing the `4`-fold matrix product; the single relation
  -- `a * b = 1` (`hab`) then discharges every entry.
  set b := (a : ZMod p)⁻¹ with hb
  clear_value b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination hab
      | linear_combination -hab

/-- The two opposite root groups `U ∪ U⁻`, the Bruhat generators of `SL(2, p)`. -/
def rootGroups : Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  Set.range (unipotentUpper (p := p)) ∪ Set.range (lowerUnipotent (p := p))

theorem unipotentUpper_mem_closure_rootGroups (t : ZMod p) :
    unipotentUpper t ∈ Subgroup.closure (rootGroups (p := p)) :=
  Subgroup.subset_closure (Set.mem_union_left _ ⟨t, rfl⟩)

theorem lowerUnipotent_mem_closure_rootGroups (t : ZMod p) :
    lowerUnipotent t ∈ Subgroup.closure (rootGroups (p := p)) :=
  Subgroup.subset_closure (Set.mem_union_right _ ⟨t, rfl⟩)

/-- The Weyl element lies in `⟨U, U⁻⟩`. -/
theorem weylW_mem_closure_rootGroups :
    weylW ∈ Subgroup.closure (rootGroups (p := p)) := by
  rw [weylW_eq_root_word]
  exact mul_mem (mul_mem (unipotentUpper_mem_closure_rootGroups _)
    (lowerUnipotent_mem_closure_rootGroups _)) (unipotentUpper_mem_closure_rootGroups _)

/-- The whole split torus `T` lies in `⟨U, U⁻⟩`. -/
theorem torusDiag_mem_closure_rootGroups (a : (ZMod p)ˣ) :
    torusDiag a ∈ Subgroup.closure (rootGroups (p := p)) := by
  rw [torusDiag_eq_root_word]
  exact mul_mem (mul_mem (mul_mem (unipotentUpper_mem_closure_rootGroups _)
    (lowerUnipotent_mem_closure_rootGroups _)) (unipotentUpper_mem_closure_rootGroups _))
    weylW_mem_closure_rootGroups

set_option maxHeartbeats 800000 in
/-- **Bruhat cell membership.**  Every `g ∈ SL(2, p)` whose lower-left entry `c` is
nonzero lies in `⟨U, U⁻⟩`, via the Bruhat factorization

    g = u(a·c⁻¹) · w · diag(c) · u(d·c⁻¹),

where `a = g₀₀`, `d = g₁₁`.  (The top-right entry checks out because
`ad − bc = 1`.)  Since `u(·), w, diag(c)` all lie in `⟨U, U⁻⟩`, so does `g`. -/
theorem mem_closure_of_lowerLeft_ne_zero
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 ≠ 0) :
    g ∈ Subgroup.closure (rootGroups (p := p)) := by
  set A := (g : Matrix (Fin 2) (Fin 2) (ZMod p)) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h : A.det = 1 := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  have hv2 : (((Units.mk0 (A 1 0) hc)⁻¹ : (ZMod p)ˣ) : ZMod p) = (A 1 0)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  have key : ((unipotentUpper (A 0 0 * (A 1 0)⁻¹) * weylW * torusDiag (Units.mk0 (A 1 0) hc)
        * unipotentUpper (A 1 1 * (A 1 0)⁻¹) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        : Matrix (Fin 2) (Fin 2) (ZMod p)) = A := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, val_unipotentUpper, val_weylW,
      val_torusDiag, Units.val_mk0, hv2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (try field_simp) <;>
      first
        | linear_combination hdet
        | linear_combination -hdet
        | linear_combination (A 1 0) * hdet
        | linear_combination -(A 1 0) * hdet
        | ring
  have hword : g = unipotentUpper (A 0 0 * (A 1 0)⁻¹) * weylW * torusDiag (Units.mk0 (A 1 0) hc)
      * unipotentUpper (A 1 1 * (A 1 0)⁻¹) := by
    apply Subtype.ext
    exact key.symm
  rw [hword]
  exact mul_mem (mul_mem (mul_mem (unipotentUpper_mem_closure_rootGroups _)
    weylW_mem_closure_rootGroups) (torusDiag_mem_closure_rootGroups _))
    (unipotentUpper_mem_closure_rootGroups _)

/-- **`⟨U, U⁻⟩ = SL(2, p)`.**  The two opposite root groups generate the whole
special linear group.  This is the Bruhat generation theorem: matrices with a
nonzero lower-left entry are covered by the big Bruhat cell
(`mem_closure_of_lowerLeft_ne_zero`), and the remaining matrices — those with
lower-left entry `0`, forcing the top-left entry to be a unit — are pulled into
that cell by one lower transvection `l(1)`.

Together with `exists_unipotent_isCommutator` / `exists_lowerUnipotent_isCommutator`
(both root groups lie in the derived subgroup for `p ≥ 5`) this yields perfectness
of `SL(2, p)` for `p ≥ 5`, and it is the generation hypothesis of Iwasawa's
simplicity criterion for `PSL(2, p)`. -/
theorem closure_rootGroups_eq_top :
    Subgroup.closure (rootGroups (p := p)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0
  · -- lower-left entry `0`: `det = 1` forces the top-left entry `g₀₀ ≠ 0`.
    have hane : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 := by
      intro ha0
      have h : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 :=
        Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two, ha0, hc] at h
      simp at h
    -- `l(1) · g` then has lower-left entry `g₀₀ + g₁₀ = g₀₀ ≠ 0`.
    have hbl : ((lowerUnipotent 1 * g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, val_lowerUnipotent]
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc] using hane
    have hmem : lowerUnipotent 1 * g ∈ Subgroup.closure (rootGroups (p := p)) :=
      mem_closure_of_lowerLeft_ne_zero _ hbl
    have hinv : lowerUnipotent (-1 : ZMod p) * lowerUnipotent 1 = 1 := by
      rw [lowerUnipotent_mul, neg_add_cancel, lowerUnipotent_zero]
    have hg : g = lowerUnipotent (-1) * (lowerUnipotent 1 * g) := by
      rw [← mul_assoc, hinv, one_mul]
    rw [hg]
    exact mul_mem (lowerUnipotent_mem_closure_rootGroups _) hmem
  · exact mem_closure_of_lowerLeft_ne_zero g hc

/-!
## Perfectness of `SL(2, p)` for `p ≥ 5`

The two structural inputs are now in place:
* every root-group element is a commutator (`exists_unipotent_isCommutator` and
  `exists_lowerUnipotent_isCommutator`), so `U ∪ U⁻ ⊆ [SL(2,p), SL(2,p)]`;
* the root groups generate the whole group (`closure_rootGroups_eq_top`).

A subgroup containing a generating set is the whole group, so the derived subgroup is
everything: `SL(2, p)` is **perfect** for `p ≥ 5`.  This is exactly the perfectness
hypothesis of Iwasawa's simplicity criterion for `PSL(2, p)`, whose validity range
`p ≥ 5` matches the range on which `PSL(2, p)` is simple. -/

/-- **`SL(2, p)` is perfect for `p ≥ 5`**: `[SL(2,p), SL(2,p)] = SL(2, p)`.

Both root groups lie in the derived subgroup — every upper unipotent is a commutator
(`exists_unipotent_isCommutator`, taking `[diag(2), u(t)]`) and every lower unipotent is
a commutator (`exists_lowerUnipotent_isCommutator`, the Weyl-conjugate). Since the root
groups generate `SL(2, p)` (`closure_rootGroups_eq_top`), the derived subgroup contains a
generating set and hence is all of `SL(2, p)`. -/
theorem commutator_eq_top (hp : 5 ≤ p) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = ⊤ := by
  apply top_le_iff.mp
  rw [← closure_rootGroups_eq_top (p := p), Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe]
  simp only [rootGroups, Set.mem_union, Set.mem_range] at hg
  rcases hg with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · obtain ⟨a, t, hc⟩ := exists_unipotent_isCommutator hp s
    rw [← hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · obtain ⟨x, y, hc⟩ := exists_lowerUnipotent_isCommutator hp s
    rw [← hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **Perfectness of `PSL(2, p)` for `p ≥ 5`.**  The projective special linear group
`PSL(2, p) = SL(2, p)/Z` is perfect: its own commutator subgroup is the whole group.

This transports `commutator_eq_top` (perfectness of the cover `SL(2, p)`) across the
central quotient homomorphism `mk' : SL(2, p) ↠ PSL(2, p)`.  Since that map is
surjective it carries `⊤` onto `⊤` and commutes with the commutator bracket
(`Subgroup.map_commutator`), so the image of the derived subgroup of `SL(2, p)` is the
derived subgroup of `PSL(2, p)`; as the former is all of `SL(2, p)`, the latter is all
of `PSL(2, p)`.

Perfectness is one of the two hypotheses of Iwasawa's simplicity criterion (the other
being a primitive faithful action, here the `2`-transitive action on `P¹(𝔽_p)`).  It is
exactly the side condition that fails at `p = 2, 3`: `PSL(2,2) ≅ S₃` and
`PSL(2,3) ≅ A₄` are *not* perfect, which is why the simplicity statement is restricted
to `p ≥ 5`. -/
theorem commutator_PSL_eq_top (hp : 5 ≤ p) :
    commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = ⊤ := by
  set N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) with hN
  have hsurj := QuotientGroup.mk'_surjective N
  -- The central quotient map sends the derived subgroup of `SL` onto that of `PSL`.
  have key :
      Subgroup.map (QuotientGroup.mk' N)
          (commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
        = commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    show Subgroup.map (QuotientGroup.mk' N)
          ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))), ⊤⁆
        = ⁅(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
  rw [← key, commutator_eq_top hp, Subgroup.map_top_of_surjective _ hsurj]

/-!
## The Iwasawa generation hypothesis: `⟪U⟫ᴳ = SL(2, p)`

The Bruhat theorem `closure_rootGroups_eq_top` shows the *two* opposite root groups
`U ∪ U⁻` generate `SL(2, p)`.  Iwasawa's criterion, however, asks for something
sharper about the *single* abelian subgroup `U`: that the **normal closure** of `U`
— the subgroup generated by all `SL(2, p)`-conjugates of `U` — is the whole group.

This is immediate from the Bruhat theorem together with `weylW_conj_unipotent`
(`w · u(t) · w⁻¹ = l(-t)`): the normal closure of `U` already contains every Weyl
conjugate of a `U`-element, i.e. all of the opposite root group `U⁻`, so it contains
`U ∪ U⁻` and hence the group `⟨U, U⁻⟩ = SL(2, p)` they generate.

Combined with `unipotentUpper_comm` (`U` is abelian) and `torus_normalizes_unipotent`
(`U` is normalised by the torus, so `U ⊴ B`), this is exactly the "abelian normal
subgroup of a point stabiliser whose conjugates generate `G`" hypothesis of Iwasawa's
simplicity lemma for `PSL(2, p)`.
-/

/-- **The normal closure of the unipotent subgroup `U` is all of `SL(2, p)`.**
Every conjugate of a `U`-element lies in the normal closure `⟪U⟫ᴳ`; in particular the
Weyl conjugate `w · u(t) · w⁻¹ = l(-t)` shows the entire opposite root group `U⁻` lies
in `⟪U⟫ᴳ`.  Hence `⟪U⟫ᴳ` contains the generating set `U ∪ U⁻` of `closure_rootGroups_eq_top`,
so it is everything.  This is the generation half of Iwasawa's criterion, phrased for
the single abelian subgroup `U` rather than the symmetric pair `⟨U, U⁻⟩`. -/
theorem unipotent_normalClosure_eq_top :
    Subgroup.normalClosure (Set.range (unipotentUpper (p := p))) = ⊤ := by
  rw [eq_top_iff, ← closure_rootGroups_eq_top (p := p), Subgroup.closure_le]
  intro g hg
  simp only [rootGroups, Set.mem_union, Set.mem_range] at hg
  rcases hg with ⟨t, rfl⟩ | ⟨s, rfl⟩
  · -- `u(t) ∈ U ⊆ ⟪U⟫ᴳ`.
    exact Subgroup.subset_normalClosure ⟨t, rfl⟩
  · -- `l(s) = w · u(-s) · w⁻¹` is a conjugate of a `U`-element, hence in `⟪U⟫ᴳ`.
    have h : weylW * unipotentUpper (-s) * weylW⁻¹ = lowerUnipotent s := by
      have := weylW_conj_unipotent (p := p) (-s)
      rwa [neg_neg] at this
    have hu : unipotentUpper (-s) ∈
        Subgroup.normalClosure (Set.range (unipotentUpper (p := p))) :=
      Subgroup.subset_normalClosure (Set.mem_range_self _)
    rw [SetLike.mem_coe, ← h]
    exact Subgroup.normalClosure_normal.conj_mem _ hu weylW

/-!
## The order `|SL(2, p)| = p·(p² − 1)`

The remaining Iwasawa/order ingredient toward `|PSL(2, p)|` is the cardinality of
`SL(2, 𝔽_p)`, absent from Mathlib.  We obtain it from Mathlib's `Matrix.card_GL_field`
(`|GL(2, 𝔽_p)| = (p² − 1)(p² − p)`) via the short exact sequence
`1 → SL(2, p) → GL(2, p) --det--> 𝔽_pˣ → 1`.  The determinant is a **surjective**
homomorphism (`diag(u, 1)` realizes any unit `u`) whose kernel is the image of
`SL(2, p)` (`Matrix.SpecialLinearGroup.range_toGL`), so by Lagrange
`|SL| · (p − 1) = |GL| = (p² − 1)(p² − p)` and hence `|SL| = p·(p² − 1)`.
-/

/-- **The determinant `GL(2, 𝔽_p) → 𝔽_pˣ` is surjective.**  Every unit `u` is the
determinant of the diagonal matrix `diag(u, 1)`. -/
theorem generalLinearGroup_det_surjective :
    Function.Surjective
      (GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ) := by
  intro u
  have hdet : (!![(u : ZMod p), 0; 0, 1] :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det = (u : ZMod p) := by
    rw [Matrix.det_fin_two_of]; ring
  refine ⟨GeneralLinearGroup.mkOfDetNeZero !![(u : ZMod p), 0; 0, 1] ?_, ?_⟩
  · rw [hdet]; exact u.ne_zero
  · apply Units.ext
    simp [Matrix.det_fin_two_of]

/-- **Order of `SL(2, p)`:** `|SL(2, 𝔽_p)| = p·(p² − 1)`.

Proof via the determinant short exact sequence `1 → SL → GL --det--> 𝔽_pˣ → 1`:
the determinant is a surjective homomorphism whose kernel is (the image of) `SL`,
so `|SL| = |GL| / |𝔽_pˣ| = (p² − 1)(p² − p)/(p − 1) = p·(p² − 1)`. -/
theorem card_SL2 :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set D : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ := GeneralLinearGroup.det with hD
  have hsurj : Function.Surjective D := generalLinearGroup_det_surjective
  -- (1) `SL ≃* ker(det)`, so the cardinalities agree.
  have hrangeker :
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).range = D.ker := by
    ext g
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, hD]
    constructor
    · rintro ⟨A, rfl⟩
      exact Matrix.SpecialLinearGroup.coeToGL_det A
    · intro hg
      have hmem : g ∈ Set.range (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod p) → GL (Fin 2) (ZMod p)) := by
        rw [Matrix.SpecialLinearGroup.range_toGL]
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact hg
      exact hmem
  have hcardSL :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = Nat.card D.ker := by
    rw [← hrangeker]
    exact Nat.card_congr
      (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv
  -- (2) Lagrange: `|ker| · index = |GL|`.
  have hmulindex : Nat.card D.ker * D.ker.index = Nat.card (GL (Fin 2) (ZMod p)) :=
    D.ker.card_mul_index
  -- (3) `index = |range(det)| = |𝔽_pˣ| = p − 1`.
  have hindex : D.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Nat.card_congr (Subgroup.topEquiv (G := (ZMod p)ˣ)).toEquiv, Nat.card_eq_fintype_card,
      ZMod.card_units]
  -- (4) `|GL(2, p)| = (p² − 1)(p² − p)`.
  have hcardGL : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    have h := Matrix.card_GL_field (n := 2) (𝔽 := ZMod p)
    rw [h, Fin.prod_univ_two]
    simp [ZMod.card]
  -- Assemble: `|SL| · (p − 1) = (p² − 1)(p² − p) = (p·(p² − 1))·(p − 1)`, then cancel.
  have hpos : 0 < p - 1 := by omega
  have key : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1)
      = (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [hcardSL, ← hindex, hmulindex, hcardGL]
  have hfact : (p ^ 2 - 1) * (p ^ 2 - p) = p * (p ^ 2 - 1) * (p - 1) := by
    have e1 : p ^ 2 - p = p * (p - 1) := by
      rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
    rw [e1, ← mul_assoc, mul_comm (p ^ 2 - 1) p]
  rw [hfact] at key
  exact Nat.eq_of_mul_eq_mul_right hpos key

/-!
## The unipotent subgroup is a Sylow `p`-subgroup of `SL(2, p)`

Combining the order formula `|SL(2, p)| = p·(p² − 1)` (`card_SL2`) with the coprimality
`p ∤ (p² − 1)` (modulo `p`, `p² − 1 ≡ −1`), the `p`-part of the group order is exactly `p`.
The unipotent one-parameter subgroup `U = range unipotentHom` has order exactly `p`
(`card_unipotentHom_range`), so `U` realises the whole `p`-part and is a Sylow `p`-subgroup
of `SL(2, p)` (`unipotentSylow`).  This makes precise the header's description of `U` as
"the order-`p` Sylow-`p` subgroup", and is the concrete Sylow-theoretic anchor of the
"Sylow counting" framing: the unipotent radical of the Borel is a full Sylow `p`-subgroup.
-/

/-- The unipotent subgroup `U = range unipotentHom` has cardinality exactly `p`. This is the
subgroup form of `card_unipotent_range`: `unipotentHom` is an injective homomorphism out of
`Multiplicative (ZMod p)`, so its range is equinumerous with `ZMod p`. -/
theorem card_unipotentHom_range :
    Nat.card (unipotentHom (p := p)).range = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have e : Multiplicative (ZMod p) ≃* (unipotentHom (p := p)).range :=
    MonoidHom.ofInjective unipotentHom_injective
  rw [← Nat.card_congr e.toEquiv]
  show Nat.card (ZMod p) = p
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-- `p` does not divide `p² − 1`.  Modulo `p`, `p² − 1 ≡ −1`; concretely, `p ∣ p²` and
`p ∣ (p² − 1)` would force `p ∣ p² − (p² − 1) = 1`. -/
theorem not_dvd_sq_sub_one : ¬ (p ∣ p ^ 2 - 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsq : 1 ≤ p ^ 2 := by nlinarith
  intro hdvd
  have hp_sq : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have h1 : p ∣ 1 := by
    have hd := Nat.dvd_sub hp_sq hdvd
    rwa [Nat.sub_sub_self hsq] at hd
  have := Nat.le_of_dvd one_pos h1
  omega

/-- The `p`-part of `|SL(2, p)|` is exactly `p`: `(|SL(2, p)|).factorization p = 1`.
From `card_SL2`, `|SL(2, p)| = p·(p² − 1)` with `p ∤ (p² − 1)` (`not_dvd_sq_sub_one`). -/
theorem factorization_card_SL2 :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).factorization p = 1 := by
  have hp : Nat.Prime p := Fact.out
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hq0 : p ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
    omega
  rw [card_SL2, Nat.factorization_mul hp0 hq0, Finsupp.add_apply,
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd not_dvd_sq_sub_one,
    add_zero]

/-- **The unipotent subgroup `U` is a Sylow `p`-subgroup of `SL(2, p)`.**  Its order is
exactly `p` (`card_unipotentHom_range`), which equals the full `p`-part `p ^ 1` of the group
order `|SL(2, p)| = p·(p² − 1)` (`factorization_card_SL2`).  This realises the abelian
normal-in-Borel unipotent radical `U` as a genuine Sylow `p`-subgroup — the concrete object
underlying the "Sylow counting" route to the structure of `SL(2, p)`. -/
noncomputable def unipotentSylow :
    Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  Sylow.ofCard (unipotentHom (p := p)).range <| by
    rw [card_unipotentHom_range, factorization_card_SL2, pow_one]

/-!
## `SL(2, p)` is not solvable for `p ≥ 5`

Perfectness (`commutator_eq_top`) rules out solvability outright: a *nontrivial
solvable* group has a **proper** commutator subgroup
(`IsSolvable.commutator_lt_top_of_nontrivial`), whereas `SL(2, p)` equals its own
commutator subgroup for `p ≥ 5`.  Non-solvability is the group-theoretic heart of
the simplicity of `PSL(2, p)`: `SL(2, p)` (and hence its central quotient
`PSL(2, p)`) escapes the entire solvable hierarchy exactly when `p ≥ 5`, the same
threshold at which the simplicity theorem turns on.
-/

/-- **`SL(2, p)` is not solvable for `p ≥ 5`.**  It is perfect
(`commutator_eq_top`) and nontrivial (the unipotent `[[1, 1], [0, 1]] ≠ 1`), and a
nontrivial solvable group would have a proper commutator subgroup
(`IsSolvable.commutator_lt_top_of_nontrivial`), contradicting
`commutator (SL(2, p)) = ⊤`.  This is the non-solvability obstruction underlying the
simplicity of `PSL(2, p)`. -/
theorem not_isSolvable (hp : 5 ≤ p) :
    ¬ IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  intro hsolv
  haveI := hsolv
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    refine ⟨unipotentUpper 1, 1, ?_⟩
    rw [← unipotentUpper_zero (p := p)]
    intro h
    exact one_ne_zero (unipotentUpper_injective h)
  have hlt : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) < ⊤ :=
    IsSolvable.commutator_lt_top_of_nontrivial _
  rw [commutator_eq_top hp] at hlt
  exact lt_irrefl _ hlt

/-- **`PSL(2, p)` is not solvable for `p ≥ 5`.**  Non-solvability descends from the
cover `SL(2, p)` to the projective quotient through the central extension

    `1 → Z → SL(2, p) → PSL(2, p) → 1`.

The kernel `Z = Z(SL(2, p))` is abelian, hence solvable, and if `PSL(2, p)` were
solvable then — with a solvable kernel *and* a solvable quotient — the middle group
`SL(2, p)` would be solvable too (`solvable_of_ker_le_range`).  That contradicts
`not_isSolvable`, so `PSL(2, p)` is not solvable.

This is the non-solvability of the target group itself, one step past the
non-solvability of its cover; together with `commutator_PSL_eq_top` (perfectness of
`PSL(2, p)`) it records that `PSL(2, p)` escapes the entire solvable hierarchy exactly
on the range `p ≥ 5` where the simplicity theorem turns on. -/
theorem not_isSolvable_PSL (hp : 5 ≤ p) :
    ¬ IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  intro hsolv
  haveI := hsolv
  -- `Subgroup.center` no longer bundles a `CommGroup` instance in this Mathlib version,
  -- only the mixin `IsMulCommutative`; derive `IsSolvable` from it explicitly.
  haveI : IsSolvable (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
    isSolvable_of_comm mul_comm'
  -- A solvable quotient and (now explicitly) solvable central kernel force the middle
  -- group `SL(2, p)` to be solvable via the central extension.
  haveI : IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    solvable_of_ker_le_range
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).subtype
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
      (by rw [QuotientGroup.ker_mk']; exact (Subgroup.range_subtype _).ge)
  exact not_isSolvable hp this

/-!
## Triviality of the abelianizations for `p ≥ 5`

Perfectness (`commutator_eq_top`, `commutator_PSL_eq_top`) says the derived subgroup is
the whole group.  In the standard `G^{ab} = 1` language this is the statement that the
*abelianization* — the universal abelian quotient `G ⧸ ⁅G, G⁆` — is trivial.  Recording
it in this form makes the perfectness of both the cover `SL(2, p)` and the target
`PSL(2, p)` available as `Subsingleton (Abelianization …)`, the shape most facts about
abelian quotients consume: every homomorphism from a perfect group to an abelian group is
trivial, and the first integral homology `H₁(G; ℤ) ≅ G^{ab}` vanishes.
-/

/-- **The abelianization of `SL(2, p)` is trivial for `p ≥ 5`.**  Since
`Abelianization G = G ⧸ commutator G` and `SL(2, p)` is perfect (`commutator_eq_top`), the
abelianization is a quotient by the whole group, hence a subsingleton.  Equivalently, every
group homomorphism from `SL(2, p)` into an abelian group is trivial. -/
theorem subsingleton_abelianization (hp : 5 ≤ p) :
    Subsingleton (Abelianization (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
  show Subsingleton (_ ⧸ commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  rw [commutator_eq_top hp]
  exact QuotientGroup.subsingleton_quotient_top

/-- **The abelianization of `PSL(2, p)` is trivial for `p ≥ 5`.**  The target group is
perfect (`commutator_PSL_eq_top`), so its abelianization `PSL(2, p) ⧸ commutator` is a
quotient by the whole group and therefore a subsingleton.  This is the `G^{ab} = 1` form of
perfectness for the simple-group candidate itself. -/
theorem subsingleton_abelianization_PSL (hp : 5 ≤ p) :
    Subsingleton
      (Abelianization (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) := by
  show Subsingleton
    (_ ⧸ commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
  rw [commutator_PSL_eq_top hp]
  exact QuotientGroup.subsingleton_quotient_top

/-!
## The center of `SL(2, p)` and the order of `PSL(2, p)`

`card_SL2` gives `|SL(2, p)| = p(p²−1)`; passing to the projective quotient
`PSL(2, p) = SL(2, p)/Z` divides this by the order of the center.  For odd `p` the
center is exactly the two scalar matrices `{I, −I}`: by `mem_center_iff` every central
element is a scalar `r·I` with `r² = 1`, and over the field `ZMod p` (odd characteristic)
the only square roots of unity are `r = ±1` — and `I ≠ −I` because `p ≠ 2`.  Hence
`|Z(SL(2, p))| = 2` and Lagrange gives `|PSL(2, p)| = p(p²−1)/2`, the classical order of
the projective group.
-/

/-- **The center of `SL(2, p)` has order `2` for odd `p`.**  Via
`SpecialLinearGroup.mem_center_iff` the central elements are the scalar matrices
`scalar (Fin 2) r` with `r ^ 2 = 1`; over the field `ZMod p` (odd `p`) the only square
roots of unity are `r = ±1` (`mul_self_eq_one_iff`), so the center is exactly the pair
`{1, -1}`, which has two elements because `1 ≠ -1` when `p ≠ 2`. -/
theorem card_center_SL2 (hp : 3 ≤ p) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = 2 := by
  -- `1 ≠ -1` in `SL(2, p)`, because otherwise `2 = 0` in `ZMod p`, forcing `p ∣ 2`.
  have hne : (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ≠ -1 := by
    intro h
    have h00 := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
        (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.one_apply_eq, Matrix.neg_apply] at h00
    have hdvd : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h00
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- The center is exactly the pair `{1, -1}`.
  have hset : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = {1, -1} := by
    ext A
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hA
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      rw [Fintype.card_fin] at hr
      have hrr : r * r = 1 := by rw [← pow_two]; exact hr
      rcases mul_self_eq_one_iff.mp hrr with h1 | h1
      · left
        apply Subtype.ext
        rw [← hrA, h1]
        simp [Matrix.SpecialLinearGroup.coe_one]
      · right
        apply Subtype.ext
        rw [← hrA, h1]
        simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · rw [Matrix.SpecialLinearGroup.mem_center_iff]
        refine ⟨-1, by rw [Fintype.card_fin]; ring, ?_⟩
        simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair hne]

/-- **`|PSL(2, p)| = p(p²−1)/2` for odd `p`.**  The projective group is the central
quotient `PSL(2, p) = SL(2, p)/Z(SL(2, p))`, so by Lagrange
`|Z| · |PSL| = |SL| = p(p²−1)` (`Subgroup.card_mul_index`, with `|PSL|` the index of the
center).  Since `|Z| = 2` for odd `p` (`card_center_SL2`) and `|SL| = p(p²−1)`
(`card_SL2`), the order of `PSL(2, p)` is `p(p²−1)/2` — the classical formula. -/
theorem card_PSL2 (hp : 3 ≤ p) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      = p * (p ^ 2 - 1) / 2 := by
  have hmul :=
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).card_mul_index
  rw [card_center_SL2 hp, card_SL2] at hmul
  -- `hmul : 2 * (center).index = p*(p²−1)`, and `(center).index = |PSL|` by definition.
  have hidx : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).index
      = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := rfl
  rw [hidx] at hmul
  omega

/-- **`|PSL(2, p)| ≥ 60` for `p ≥ 5`.**  Evaluating `card_PSL2 = p(p²−1)/2` at `p ≥ 5`
gives `p(p²−1) ≥ 5·24 = 120`, so `|PSL(2, p)| ≥ 60` — matching the classical fact that
`PSL(2, 5) ≅ A₅` (order `60`) is the smallest member of the family, the smallest nonabelian
simple group.  A concrete order floor on the target group of the simplicity theorem. -/
theorem card_PSL2_ge_sixty (hp : 5 ≤ p) :
    60 ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  rw [card_PSL2 (by omega)]
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  have hq : 24 ≤ p ^ 2 - 1 := by omega
  have hpq : 120 ≤ p * (p ^ 2 - 1) := by
    calc 120 = 5 * 24 := by norm_num
      _ ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp hq
  omega

/-- **`|PSL(2, p)| > 1` for `p ≥ 5`.**  The nontriviality floor, immediate from
`card_PSL2_ge_sixty`. -/
theorem one_lt_card_PSL2 (hp : 5 ≤ p) :
    1 < Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  lt_of_lt_of_le (by norm_num) (card_PSL2_ge_sixty hp)

/-- **`PSL(2, p)` is nontrivial for `p ≥ 5`.**  A prerequisite of the simplicity statement
(a simple group is by definition nontrivial): since `|PSL(2, p)| ≥ 60 > 1`, the group has more
than one element (`Finite.one_lt_card_iff_nontrivial`). -/
theorem nontrivial_PSL2 (hp : 5 ≤ p) :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  Finite.one_lt_card_iff_nontrivial.mp (one_lt_card_PSL2 hp)

/-!
## The unipotent Sylow `p`-subgroup is cyclic of order `p`

`card_unipotentHom_range` and `unipotentSylow` record that `U = range unipotentHom`
has order exactly `p` and is a Sylow `p`-subgroup.  We add the missing *structural*
refinement: `U` is **cyclic** — indeed `U ≅ ℤ/p` — with the single generator
`[[1, 1], [0, 1]]` of order exactly `p`.  Any group of prime order is cyclic
(`isCyclic_of_prime_card`), so the Sylow `p`-subgroup of `SL(2, p)` is `ℤ/p`; this
is the base case (`p ∥ |SL(2, p)|`, exponent one) of the general fact that the
`p`-Sylow of `SL(2, p)` is the elementary-abelian unipotent radical.  The generator
order is read off from `unipotentHom` being an injective homomorphism out of
`(ZMod p, +)`, in which `1` has additive order `p`. -/

/-- **The unipotent generator `[[1, 1], [0, 1]]` has order exactly `p`.**
`unipotentUpper 1 = unipotentHom (ofAdd 1)`, and `unipotentHom` is an injective
homomorphism, so its order equals that of `Multiplicative.ofAdd (1 : ZMod p)`, which
is the additive order of `1` in `ZMod p`, namely `p` (`ZMod.addOrderOf_one`). -/
theorem orderOf_unipotentUpper_one :
    orderOf (unipotentUpper (1 : ZMod p)) = p := by
  have h := orderOf_injective (unipotentHom (p := p)) unipotentHom_injective
      (Multiplicative.ofAdd (1 : ZMod p))
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at h
  simpa using h

/-- **The unipotent subgroup `U` is cyclic.**  `U = range unipotentHom` has order the
prime `p` (`card_unipotentHom_range`), and every finite group of prime order is cyclic
(`isCyclic_of_prime_card`).  Thus the Sylow `p`-subgroup `unipotentSylow` of `SL(2, p)`
is `ℤ/p`, generated by `[[1, 1], [0, 1]]` (`orderOf_unipotentUpper_one`). -/
theorem isCyclic_unipotentHom_range :
    IsCyclic (unipotentHom (p := p)).range :=
  isCyclic_of_prime_card card_unipotentHom_range

/-- **The unipotent Sylow `p`-subgroup is cyclic.**  Restatement of
`isCyclic_unipotentHom_range` for the packaged Sylow subgroup `unipotentSylow`, whose
underlying subgroup is exactly `range unipotentHom` (`Sylow.coe_ofCard`).  So the
`p`-Sylow of `SL(2, p)` is cyclic of order `p`, i.e. `≅ ℤ/p`. -/
theorem isCyclic_unipotentSylow :
    IsCyclic (unipotentSylow (p := p) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
  isCyclic_unipotentHom_range

/-!
## Sylow counting: at least `p + 1` Sylow `p`-subgroups of `SL(2, p)`

The unipotent subgroup `U = range unipotentHom` is a Sylow `p`-subgroup
(`unipotentSylow`), but it is **not normal**: its normal closure is all of
`SL(2, p)` (`unipotent_normalClosure_eq_top`), whereas `|U| = p < |SL(2, p)|`.
A group with a *unique* Sylow `p`-subgroup would have it normal
(`Sylow.normal_of_subsingleton`), so `SL(2, p)` has more than one Sylow
`p`-subgroup.  Sylow's third theorem forces the number `n_p` to be `≡ 1 (mod p)`
(`card_sylow_modEq_one`); together with `n_p ≠ 1` this jumps the count straight
to `n_p ≥ p + 1` — the classical value `n_p = p + 1 = |P¹(𝔽_p)|`, obtained here as
a lower bound *purely by Sylow counting*, the very route named in the problem
statement.  (The Sylow `p`-subgroups of `SL(2, p)` are exactly the conjugates of
`U`, i.e. the unipotent radicals of the `p + 1` Borel subgroups / points of the
projective line, so this bound is in fact sharp.)
-/

/-- **The unipotent Sylow subgroup `U` is not normal in `SL(2, p)` for `p ≥ 5`.**
If `U = range unipotentHom` were normal, the normal closure of its underlying set
would be contained in `U`; but `unipotent_normalClosure_eq_top` shows that closure
is the whole group, forcing `U = ⊤` and hence the absurdity
`p = |U| = |SL(2, p)| = p·(p² − 1)` (impossible since `p² − 1 ≥ 24 > 1`).  This is
the non-normality that makes the Sylow count `n_p > 1`. -/
theorem unipotent_range_not_normal (hp : 5 ≤ p) :
    ¬ ((unipotentHom (p := p)).range).Normal := by
  intro hN
  -- The carrier of `U` sits inside the normal subgroup, so its normal closure does too.
  have hsub : Set.range (unipotentUpper (p := p)) ⊆
      ((unipotentHom (p := p)).range : Set _) := by
    rintro _ ⟨t, rfl⟩
    rw [MonoidHom.coe_range]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  have hle := Subgroup.normalClosure_le_normal hsub
  rw [unipotent_normalClosure_eq_top] at hle
  have htop : (unipotentHom (p := p)).range = ⊤ := top_le_iff.mp hle
  -- Cardinalities collide: `|U| = p` but `|⊤| = |SL(2, p)| = p·(p² − 1)`.
  have hcard : Nat.card ((unipotentHom (p := p)).range) = p := card_unipotentHom_range
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv, card_SL2] at hcard
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h1 : p * (p ^ 2 - 1) = p * 1 := by rw [mul_one]; exact hcard
  have h2 : p ^ 2 - 1 = 1 := Nat.eq_of_mul_eq_mul_left hp0 h1
  have hsq : 4 ≤ p ^ 2 := by nlinarith [(Fact.out : p.Prime).two_le]
  omega

/-- **Sylow counting bound: `SL(2, p)` has at least `p + 1` Sylow `p`-subgroups for
`p ≥ 5`.**  The unipotent Sylow `U` is not normal (`unipotent_range_not_normal`), so
the number `n_p` of Sylow `p`-subgroups is not `1` (a unique Sylow would be normal,
`Sylow.normal_of_subsingleton`).  Sylow's third theorem gives `n_p ≡ 1 (mod p)`
(`card_sylow_modEq_one`), and `n_p ≠ 1` then forces `n_p ≥ p + 1`.  This realises the
"Sylow counting argument" of the problem statement: the lower bound matches the
`p + 1` points of the projective line `P¹(𝔽_p)` on which `PSL(2, p)` acts. -/
theorem card_sylow_ge (hp : 5 ≤ p) :
    p + 1 ≤ Nat.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := Finite.of_fintype _
  set n := Nat.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) with hn
  -- Sylow III congruence: `n_p ≡ 1 (mod p)`.
  have hmod : n ≡ 1 [MOD p] :=
    card_sylow_modEq_one p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
  -- `n_p ≠ 1`: a single Sylow subgroup would be normal, but `U` is not.
  have hne : n ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    have hnorm : ((unipotentHom (p := p)).range).Normal :=
      Sylow.normal_of_subsingleton (unipotentSylow (p := p))
    exact unipotent_range_not_normal hp hnorm
  -- Sylow subgroups exist, so `n_p ≥ 1`.
  have hpos : 1 ≤ n := Nat.card_pos
  -- `p ∣ n_p − 1` from the congruence; with `n_p − 1 ≥ 1` this gives `p ≤ n_p − 1`.
  have hdvd : p ∣ n - 1 := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  have hle : p ≤ n - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

omit [Fact (Nat.Prime p)] in
/-- **Arithmetic core of the exact Sylow count.**  A divisor `n` of `p² − 1` that is
`≡ 1 (mod p)` and `≥ p + 1` equals `p + 1` exactly (for `p ≥ 5`).  This is the purely
number-theoretic step that turns the Sylow *lower* bound `card_sylow_ge` into an
*equality*, avoiding the explicit normalizer/Borel matrix computation.

Proof sketch: write `n = p·a + 1` (from `n ≡ 1`) and `p² − 1 = n·m`.  The equation
`p² = p·(a·m) + (m + 1)` forces `p ∣ m + 1`, hence `m + 1 ≥ p`.  If `a ≥ 2` then
`n ≥ 2p + 1`, so `(2p + 1)·p ≤ n·(m + 1) = (p² − 1) + n ≤ 2(p² − 1)`, i.e.
`2p² + p + 1 ≤ 2p²`, impossible.  Thus `a = 1` and `n = p + 1`. -/
theorem sylow_count_arith (hp : 5 ≤ p) {n : ℕ}
    (hdvd : n ∣ p ^ 2 - 1) (hmod : n ≡ 1 [MOD p]) (hge : p + 1 ≤ n) :
    n = p + 1 := by
  have hpsq : 25 ≤ p ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ := hdvd
  have hn1 : 1 ≤ n := by omega
  have hdvd1 : p ∣ n - 1 := (Nat.modEq_iff_dvd' hn1).mp hmod.symm
  obtain ⟨a, ha⟩ := hdvd1
  have hn : n = p * a + 1 := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  have hpm : p ^ 2 = n * m + 1 := by omega
  have hkey : p ^ 2 = p * (a * m) + (m + 1) := by rw [hpm, hn]; ring
  have hdvdm : p ∣ m + 1 := by
    have h1 : p ∣ p ^ 2 := ⟨p, by ring⟩
    have h2 : p ∣ p * (a * m) := ⟨a * m, rfl⟩
    have h3 : m + 1 = p ^ 2 - p * (a * m) := by omega
    rw [h3]; exact Nat.dvd_sub h1 h2
  have hmp : p ≤ m + 1 := Nat.le_of_dvd (by omega) hdvdm
  by_contra hne
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp only [Nat.mul_zero, Nat.zero_add] at hn; omega
    · exact h
  have ha2 : 2 ≤ a := by
    rcases lt_or_ge a 2 with h | h
    · have hai : a = 1 := by omega
      exact absurd (show n = p + 1 by rw [hn, hai]; ring) hne
    · exact h
  have hn2p : 2 * p + 1 ≤ n := by rw [hn]; nlinarith [ha2, hp]
  have hnle : n ≤ p ^ 2 - 1 := Nat.le_of_dvd (by omega) ⟨m, hm⟩
  have hlow : (2 * p + 1) * p ≤ n * (m + 1) := Nat.mul_le_mul hn2p hmp
  have heq : n * (m + 1) = (p ^ 2 - 1) + n := by rw [mul_add_one, ← hm]
  rw [heq] at hlow
  have hexp : (2 * p + 1) * p = 2 * p ^ 2 + p := by ring
  rw [hexp] at hlow
  omega

/-- **The index of the unipotent Sylow subgroup is `p² − 1`.**  From
`|U|·[SL : U] = |SL|` (`Subgroup.card_mul_index`) with `|U| = p`
(`card_unipotentHom_range`) and `|SL(2, p)| = p·(p² − 1)` (`card_SL2`). -/
theorem index_unipotentSylow :
    (↑(unipotentSylow (p := p)) :
        Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).index = p ^ 2 - 1 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hcard : Nat.card (↑(unipotentSylow (p := p)) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = p :=
    card_unipotentHom_range
  have hmul := Subgroup.card_mul_index
    (↑(unipotentSylow (p := p)) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  rw [hcard, card_SL2] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp0 hmul

/-- **Exact Sylow count: `SL(2, p)` has exactly `p + 1` Sylow `p`-subgroups for
`p ≥ 5`.**  Sharpens the lower bound `card_sylow_ge` to an equality.  Sylow's theorem
gives `n_p ∣ [SL : U] = p² − 1` (`Sylow.card_dvd_index` + `index_unipotentSylow`) and
`n_p ≡ 1 (mod p)` (`card_sylow_modEq_one`); together with `n_p ≥ p + 1`
(`card_sylow_ge`) the arithmetic lemma `sylow_count_arith` forces `n_p = p + 1`.
This matches the classical `n_p = |P¹(𝔽_p)| = p + 1` — the number of Borel subgroups /
points of the projective line on which `PSL(2, p)` acts — obtained here without the
explicit normalizer-is-Borel matrix computation. -/
theorem card_sylow_eq (hp : 5 ≤ p) :
    Nat.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = p + 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := Finite.of_fintype _
  have hdvd : Nat.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
      ∣ p ^ 2 - 1 := by
    have h := Sylow.card_dvd_index (unipotentSylow (p := p))
    rwa [index_unipotentSylow] at h
  have hmod : Nat.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ≡ 1 [MOD p] :=
    card_sylow_modEq_one p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
  have hge := card_sylow_ge hp
  exact sylow_count_arith hp hdvd hmod hge

/-! ### Every Sylow `p`-subgroup is a copy of `ℤ/p`, and distinct ones meet trivially

`unipotentSylow` is one explicit Sylow `p`-subgroup, cyclic of order `p`
(`isCyclic_unipotentSylow`).  Since all Sylow `p`-subgroups are conjugate they share these
properties: **every** Sylow `p`-subgroup of `SL(2, p)` has order exactly `p` (`card_sylowP`)
and is therefore cyclic `≅ ℤ/p` (`isCyclic_sylowP`).  As subgroups of prime order, two
*distinct* Sylow `p`-subgroups intersect trivially (`sylowP_inf_eq_bot`): the `p + 1` Sylow
`p`-subgroups (`card_sylow_eq`) overlap only in the identity.  These are the exact
ingredients of the classical count "`SL(2, p)` has `(p+1)(p-1) = p² - 1` elements of order
`p`". -/

/-- **Every Sylow `p`-subgroup of `SL(2, p)` has order exactly `p`.**  The `p`-part of the
group order is `p ^ 1` (`factorization_card_SL2`), and a Sylow `p`-subgroup realises the full
`p`-part (`Sylow.card_eq_multiplicity`).  Generalises `card_unipotentHom_range` from the one
explicit unipotent Sylow to every Sylow `p`-subgroup. -/
theorem card_sylowP (P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :
    Nat.card (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = p := by
  rw [P.card_eq_multiplicity, factorization_card_SL2, pow_one]

/-- **Every Sylow `p`-subgroup of `SL(2, p)` is cyclic `≅ ℤ/p`.**  It has prime order `p`
(`card_sylowP`), and any group of prime order is cyclic (`isCyclic_of_prime_card`).  This
generalises `isCyclic_unipotentSylow` from the one explicit unipotent Sylow to *all* of them. -/
theorem isCyclic_sylowP (P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :
    IsCyclic (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
  isCyclic_of_prime_card (card_sylowP P)

/-- **Distinct Sylow `p`-subgroups of `SL(2, p)` intersect trivially.**  Each has prime order
`p` (`card_sylowP`), so `P ⊓ Q ≤ P` has order dividing `p`: either `1` (giving `P ⊓ Q = ⊥`)
or `p`, in which case `P ⊓ Q = P` and, by symmetry, `= Q`, forcing `P = Q` and contradicting
`P ≠ Q`.  Hence the `p + 1` Sylow `p`-subgroups pairwise meet only in the identity — the
disjointness underlying the classical order-`p` element count. -/
theorem sylowP_inf_eq_bot {P Q : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))}
    (hPQ : P ≠ Q) :
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
      ⊓ (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = ⊥ := by
  have hp : Nat.Prime p := Fact.out
  set G := Matrix.SpecialLinearGroup (Fin 2) (ZMod p) with hG
  have hle : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ (P : Subgroup G) := inf_le_left
  -- `|P ⊓ Q|` divides `|P| = p`.
  have hdvd : Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) ∣ p := by
    have h := Subgroup.card_subgroup_dvd_card
      (((P : Subgroup G) ⊓ (Q : Subgroup G)).subgroupOf (P : Subgroup G))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_sylowP] at h
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpc
  · -- order 1 ⟹ trivial
    exact Subgroup.card_eq_one.mp h1
  · -- order p ⟹ `P ⊓ Q = P` and `= Q`, so `P = Q`, contradiction
    exfalso
    have hPeq : (P : Subgroup G) ⊓ (Q : Subgroup G) = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_sylowP, hpc]))
    have hQeq : (P : Subgroup G) ⊓ (Q : Subgroup G) = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [card_sylowP, hpc]))
    exact hPQ (Sylow.ext (hPeq.symm.trans hQeq))

/-- **A non-identity element lies in a unique Sylow `p`-subgroup.**  If `g ≠ 1` lies in two
Sylow `p`-subgroups `P` and `Q`, then `g ∈ P ⊓ Q`, which is `⊥` unless `P = Q`
(`sylowP_inf_eq_bot`); as `g ≠ 1` this forces `P = Q`.  This is the injectivity fact behind the
classical order-`p` element count: the `p + 1` Sylow `p`-subgroups partition the non-identity
`p`-elements. -/
theorem sylowP_eq_of_mem
    {P Q : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))}
    {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (hg : g ≠ 1)
    (hP : g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
    (hQ : g ∈ (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) :
    P = Q := by
  by_contra h
  have hmem : g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
      ⊓ (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
    Subgroup.mem_inf.mpr ⟨hP, hQ⟩
  rw [sylowP_inf_eq_bot h] at hmem
  exact hg (Subgroup.mem_bot.mp hmem)

/-! ### The classical order-`p` element count: `SL(2, p)` has exactly `p² − 1` elements of order `p`

The `p + 1` Sylow `p`-subgroups (`card_sylow_eq`) each have order `p` (`card_sylowP`), meet only in
the identity (`sylowP_inf_eq_bot`), and jointly exhaust the elements of order `p` (a non-identity
element generates a cyclic group of order `p`, a `p`-subgroup, hence sits inside some Sylow, and by
`sylowP_eq_of_mem` inside a *unique* one).  So the elements of order `p` are partitioned into
`p + 1` blocks of `p − 1` non-identity elements each, giving `(p + 1)(p − 1) = p² − 1`.  This is the
classical count underlying the original Sylow-counting approach to the simplicity of `PSL(2, p)`. -/

/-- **`SL(2, p)` has exactly `p² − 1` elements of order `p`** (for `p ≥ 5`).  The elements of order
`p` are exactly the non-identity elements of the Sylow `p`-subgroups, and the `p + 1` Sylow
`p`-subgroups (`card_sylow_eq`), each of order `p` (`card_sylowP`), partition them (distinct Sylows
meet only in `1`, `sylowP_eq_of_mem`).  Counting: `(p + 1) · (p − 1) = p² − 1`. -/
theorem card_orderOf_eq_p (hp : 5 ≤ p) :
    (Finset.univ.filter
        (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) => orderOf g = p)).card
      = p ^ 2 - 1 := by
  classical
  have hp' : Nat.Prime p := Fact.out
  -- the elementary arithmetic `(p + 1)(p − 1) = p² − 1`
  have harith : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e : (n + 1 + 1) * n + 1 = (n + 1) ^ 2 := by ring
    omega
  -- for each Sylow `P`, the non-identity elements of `P`
  set f : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      → Finset (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    fun P => (Finset.univ.filter
        (fun g => g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))).erase 1
    with hf
  -- (a) each block has `p − 1` elements
  have hmemcard : ∀ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      (Finset.univ.filter
        (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
          g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))).card = p := by
    intro P
    have hsub : (Finset.univ.filter
        (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
          g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))).card
        = Fintype.card {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)
            // x ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))} :=
      (Fintype.card_subtype _).symm
    rw [hsub, ← Nat.card_eq_fintype_card]
    exact card_sylowP P
  have hcardf : ∀ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      (f P).card = p - 1 := by
    intro P
    have h1 : (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        ∈ Finset.univ.filter
          (fun g => g ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) := by
      simp [Subgroup.one_mem]
    simp only [hf]
    rw [Finset.card_erase_of_mem h1, hmemcard P]
  -- (b) distinct Sylows give disjoint blocks
  have hdisj : (↑(Finset.univ : Finset (Sylow p
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) :
      Set (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))).PairwiseDisjoint f := by
    intro P _ Q _ hPQ
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro g hgP hgQ
    simp only [hf, Finset.mem_erase, Finset.mem_filter] at hgP hgQ
    exact hPQ (sylowP_eq_of_mem hgP.1 hgP.2.2 hgQ.2.2)
  -- (c) the order-`p` elements are exactly the union of the blocks
  have hset : Finset.univ.filter
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) => orderOf g = p)
      = Finset.univ.biUnion f := by
    ext g
    simp only [hf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_erase]
    constructor
    · intro hord
      have hg1 : g ≠ 1 := by
        intro h; rw [h, orderOf_one] at hord; omega
      have hpg : IsPGroup p (Subgroup.zpowers g) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, hord, pow_one]
      obtain ⟨P, hP⟩ := hpg.exists_le_sylow
      exact ⟨P, hg1, hP (Subgroup.mem_zpowers g)⟩
    · rintro ⟨P, hg1, hgP⟩
      have hdvd : orderOf g ∣ p := by
        have h := orderOf_dvd_natCard
          (⟨g, hgP⟩ : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
        rw [← Subgroup.orderOf_coe, card_sylowP] at h
        exact h
      rcases (Nat.dvd_prime hp').mp hdvd with h1 | hpp
      · exact absurd (orderOf_eq_one_iff.mp h1) hg1
      · exact hpp
  -- assemble the count
  have hfc : Fintype.card (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = p + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact card_sylow_eq hp
  have hsum : ∑ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)), (f P).card
      = ∑ _P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)), (p - 1) :=
    Finset.sum_congr rfl (fun P _ => hcardf P)
  rw [hset, Finset.card_biUnion hdisj, hsum, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, hfc, harith]
/-!
## The Borel subgroup `B = U ⋊ T` and the normality `U ⊴ B`

The Iwasawa criterion takes as its point stabiliser the **Borel subgroup**
`B = ⟨U, T⟩`, and requires its unipotent radical `U` to be an *abelian normal*
subgroup of `B`.  So far `U` has appeared only as the `Set.range` of the embedding
`unipotentUpper`, and `torus_normalizes_unipotent` recorded the normalising action
only pointwise.  We now package `U` as an honest `Subgroup`, exhibit `B` as the
subgroup generated by `U` and `T`, and upgrade the pointwise conjugation law into
the genuine subgroup-level statements Iwasawa needs:

* `unipotentSubgroup` — `U` as a `Subgroup` of `SL(2, p)` (the range of `unipotentHom`);
* `unipotentSubgroup_mul_comm` — `U` is **abelian**;
* `torusDiag_mem_normalizer_unipotent` — every torus element normalises `U`
  (both directions of the biconditional, via the `a` and `a⁻¹` conjugation laws);
* `borel_le_normalizer_unipotent` — the whole Borel `B` lies in the normaliser of `U`;
* `unipotentSubgroup_normal_in_borel` — hence **`U ⊴ B`** in the precise Mathlib
  sense (`(U.subgroupOf B).Normal`).

Together with `card_unipotent_range` (`|U| = p`), `card_torus_range` (`|T| = p − 1`)
and `unipotent_inter_torus_trivial` (`U ∩ T = 1`), this is exactly the abelian
normal point-stabiliser radical required by Iwasawa's simplicity criterion for
`PSL(2, p)`; only the action on the projective line `P¹(𝔽_p)` remains to be built.
-/

/-- The **unipotent subgroup** `U`, packaged as a `Subgroup` of `SL(2, ZMod p)`:
the range of the one-parameter homomorphism `unipotentHom`.  Its elements are exactly
the upper unipotent matrices `[[1, t], [0, 1]]`. -/
def unipotentSubgroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  (unipotentHom (p := p)).range

/-- Membership in `unipotentSubgroup` is exactly being an upper unipotent matrix. -/
theorem mem_unipotentSubgroup {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} :
    g ∈ unipotentSubgroup (p := p) ↔ ∃ t : ZMod p, unipotentUpper t = g := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hg
    exact ⟨Multiplicative.toAdd x, hx⟩
  · rintro ⟨t, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd t, rfl⟩

/-- **`U` is abelian.**  Any two elements of the unipotent subgroup commute, since
they are images under `unipotentUpper` of the additive group `(ZMod p, +)`. -/
theorem unipotentSubgroup_mul_comm
    {x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)}
    (hx : x ∈ unipotentSubgroup (p := p)) (hy : y ∈ unipotentSubgroup (p := p)) :
    x * y = y * x := by
  rw [mem_unipotentSubgroup] at hx hy
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact unipotentUpper_comm s t

/-- The group inverse of a diagonal torus element is again diagonal:
`[[a, 0], [0, a⁻¹]]⁻¹ = [[a⁻¹, 0], [0, a]]`.  (`torusHom` is a homomorphism.) -/
theorem torusDiag_inv (a : (ZMod p)ˣ) : (torusDiag a)⁻¹ = torusDiag a⁻¹ := by
  rw [← torusHom_apply, ← map_inv torusHom, torusHom_apply]

/-- The torus-conjugation law stated directly in terms of `torusDiag` (no `torusHom`
wrapper): `diag(a) · u(t) · diag(a)⁻¹ = u(a²·t)`. -/
theorem torusDiag_conj_unipotentUpper (a : (ZMod p)ˣ) (t : ZMod p) :
    torusDiag a * unipotentUpper t * (torusDiag a)⁻¹
      = unipotentUpper ((a : ZMod p) ^ 2 * t) := by
  have h := torusHom_conj_unipotent a t
  rwa [torusHom_apply] at h

/-- The reverse torus-conjugation law: conjugation by `diag(a)⁻¹` scales the unipotent
parameter by `(a⁻¹)²`, `diag(a)⁻¹ · u(t) · diag(a) = u((a⁻¹)²·t)`.  This is
`torusDiag_conj_unipotentUpper` applied to `a⁻¹`, using `diag(a)⁻¹ = diag(a⁻¹)`. -/
theorem torusDiag_inv_conj_unipotentUpper (a : (ZMod p)ˣ) (t : ZMod p) :
    (torusDiag a)⁻¹ * unipotentUpper t * torusDiag a
      = unipotentUpper (((a⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2 * t) := by
  have h := torusDiag_conj_unipotentUpper a⁻¹ t
  rw [torusDiag_inv, inv_inv] at h
  rw [torusDiag_inv]
  exact h

/-- **Every torus element normalises `U`.**  Conjugation by `diag(a)` maps the
unipotent subgroup onto itself (both directions), so `diag(a) ∈ N(U)`.  This is the
subgroup-level form of `torus_normalizes_unipotent`. -/
theorem torusDiag_mem_normalizer_unipotent (a : (ZMod p)ˣ) :
    torusDiag a ∈ Subgroup.normalizer (unipotentSubgroup (p := p)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [mem_unipotentSubgroup] at hn ⊢
    obtain ⟨t, rfl⟩ := hn
    exact ⟨(a : ZMod p) ^ 2 * t, (torusDiag_conj_unipotentUpper a t).symm⟩
  · intro hn
    rw [mem_unipotentSubgroup] at hn ⊢
    obtain ⟨s, hs⟩ := hn
    refine ⟨((a⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2 * s, ?_⟩
    have hconj : (torusDiag a)⁻¹ * unipotentUpper s * torusDiag a = n := by
      rw [hs]; group
    rwa [torusDiag_inv_conj_unipotentUpper] at hconj

/-- The **Borel subgroup** `B = ⟨U, T⟩`, generated by the upper unipotent subgroup
`U` and the split torus `T`.  It is the stabiliser of `∞ ∈ P¹(𝔽_p)` and the point
stabiliser required by Iwasawa's criterion. -/
def borel : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  Subgroup.closure
    (Set.range (unipotentUpper (p := p)) ∪ Set.range (torusDiag (p := p)))

/-- `U ≤ B`: the unipotent subgroup is contained in the Borel it generates. -/
theorem unipotentSubgroup_le_borel : unipotentSubgroup (p := p) ≤ borel := by
  intro g hg
  rw [mem_unipotentSubgroup] at hg
  obtain ⟨t, rfl⟩ := hg
  exact Subgroup.subset_closure (Set.mem_union_left _ ⟨t, rfl⟩)

/-- **The whole Borel `B` normalises `U`.**  Both generating families lie in the
normaliser of `U`: `U` normalises itself, and every torus element normalises `U`
(`torusDiag_mem_normalizer_unipotent`).  Since the normaliser is a subgroup, the
generated subgroup `B` is contained in it. -/
theorem borel_le_normalizer_unipotent :
    borel (p := p) ≤ Subgroup.normalizer (unipotentSubgroup (p := p)) := by
  have hb : borel (p := p) = Subgroup.closure
      (Set.range (unipotentUpper (p := p)) ∪ Set.range (torusDiag (p := p))) := rfl
  rw [hb, Subgroup.closure_le]
  rintro g (⟨t, rfl⟩ | ⟨a, rfl⟩)
  · exact unipotentSubgroup.le_normalizer (mem_unipotentSubgroup.mpr ⟨t, rfl⟩)
  · exact torusDiag_mem_normalizer_unipotent a

/-- **`U ⊴ B`.**  The unipotent radical is a normal subgroup of the Borel, in the
precise Mathlib sense that `U.subgroupOf B` is normal.  This is the abelian normal
point-stabiliser radical demanded by Iwasawa's simplicity criterion for `PSL(2, p)`;
combined with `unipotentSubgroup_mul_comm` (`U` abelian), `card_unipotent_range`,
`card_torus_range` and `unipotent_inter_torus_trivial`, it completes the internal
structure `B = U ⋊ T` with `|B| = p(p − 1)`. -/
theorem unipotentSubgroup_normal_in_borel :
    ((unipotentSubgroup (p := p)).subgroupOf borel).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer unipotentSubgroup_le_borel).mpr
    borel_le_normalizer_unipotent

/-! ### The Iwasawa structure on the Sylow-conjugation action

`SL(2, p)` acts on its set `Sylow p (SL(2, p))` of Sylow `p`-subgroups by conjugation
(`Sylow.mulAction`).  Sending each Sylow subgroup to its underlying subgroup packages the
"abelian normal subgroups whose conjugates generate the group" half of **Iwasawa's simplicity
criterion** into Mathlib's `MulAction.IwasawaStructure`:

* each Sylow `p`-subgroup is abelian — indeed cyclic of order `p` (`isCyclic_sylowP`), so
  `IsMulCommutative`;
* the assignment is equivariant: `↑(g • P) = conj g • ↑P` (`Sylow.coe_subgroup_smul`, definitionally);
* the Sylow subgroups generate `SL(2, p)` (`iSup_sylowP_eq_top`), because the join of the
  conjugation-closed family `{↑P}` is a normal subgroup containing the unipotent Sylow, whose
  normal closure is already everything (`unipotent_normalClosure_eq_top`).

This is the concrete `IwasawaStructure` object the "Sylow-counting" route calls for.  The two
ingredients still missing before `MulAction.IwasawaStructure.isSimpleGroup` yields simplicity are
`[IsQuasiPreprimitive (SL(2,p)) (Sylow p (SL(2,p)))]` (primitivity of the conjugation action —
equivalently `2`-transitivity of `PSL(2,p)` on `P¹(𝔽_p)`) and faithfulness (which forces passage
to the central quotient `PSL(2,p)`, since the centre `{±1}` acts trivially on the Sylow set).
With quasi-preprimitivity alone, `IwasawaStructure.commutator_le` already yields
`eq_top_of_normal_of_acts_nontrivially` below: every normal subgroup acting nontrivially on the
Sylow set contains `commutator (SL(2,p)) = ⊤` (`commutator_eq_top`, `p ≥ 5`).
-/

/-- **The Sylow `p`-subgroups of `SL(2, p)` generate the whole group:** their supremum is `⊤`.

The join `⨆ P, ↑P` is *normal* — the family `{↑P}` is closed under conjugation
(`↑(g • P) = conj g • ↑P`), so conjugation permutes the joined subgroups.  As a normal subgroup it
contains the unipotent Sylow `U`, hence the normal closure `⟪U⟫ᴳ`, which is already `⊤`
(`unipotent_normalClosure_eq_top`).  This is the generation hypothesis of Iwasawa's criterion. -/
theorem iSup_sylowP_eq_top :
    (⨆ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
        (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) = ⊤ := by
  set G := Matrix.SpecialLinearGroup (Fin 2) (ZMod p) with hG
  -- The join of the conjugation-closed family `{↑P}` is a normal subgroup.
  have hnormal : (⨆ P : Sylow p G, (P : Subgroup G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    -- Conjugation `g * · * g⁻¹` is the monoid hom `MulAut.conj g`.
    have key : ∀ z : G, g * z * g⁻¹ = (MulAut.conj g) z := fun z => (MulAut.conj_apply g z).symm
    -- Induct on membership in the join, showing conjugation stays inside it.
    refine Subgroup.iSup_induction (fun P : Sylow p G => (P : Subgroup G))
      (C := fun z => g * z * g⁻¹ ∈ ⨆ P : Sylow p G, (P : Subgroup G)) hn ?_ ?_ ?_
    · -- generator: `x ∈ ↑P ⟹ g * x * g⁻¹ ∈ ↑(g • P) ≤ ⨆`
      intro P x hx
      refine Subgroup.mem_iSup_of_mem (g • P) ?_
      rw [Sylow.coe_subgroup_smul, key, ← MulAut.smul_def]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
    · -- identity
      show g * (1 : G) * g⁻¹ ∈ ⨆ P : Sylow p G, (P : Subgroup G)
      rw [key, map_one]; exact one_mem _
    · -- multiplicativity
      intro x y ihx ihy
      show g * (x * y) * g⁻¹ ∈ ⨆ P : Sylow p G, (P : Subgroup G)
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
        rw [key (x * y), key x, key y, map_mul]
      rw [e]; exact mul_mem ihx ihy
  haveI := hnormal
  rw [eq_top_iff, ← unipotent_normalClosure_eq_top (p := p)]
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  rw [SetLike.mem_coe]
  refine Subgroup.mem_iSup_of_mem (unipotentSylow (p := p)) ?_
  show unipotentUpper t ∈ (unipotentHom (p := p)).range
  exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd t, rfl⟩

/-- **The Iwasawa structure on the conjugation action of `SL(2, p)` on its Sylow `p`-subgroups.**

Assigns to each Sylow `p`-subgroup `P` its underlying subgroup `↑P`.  The three axioms of
`MulAction.IwasawaStructure` hold:

* `is_comm` — every Sylow `p`-subgroup is cyclic of order `p` (`isCyclic_sylowP`), hence abelian;
* `is_conj` — the assignment is equivariant, `↑(g • P) = conj g • ↑P` (`Sylow.coe_subgroup_smul`);
* `is_generator` — the Sylow `p`-subgroups generate `SL(2, p)` (`iSup_sylowP_eq_top`).

This packages the abelian-normal-generating half of Iwasawa's simplicity criterion for `PSL(2, p)`
as a genuine Mathlib `IwasawaStructure` object; see `eq_top_of_normal_of_acts_nontrivially` for the
structural payoff available from it. -/
noncomputable def sylowIwasawaStructure :
    MulAction.IwasawaStructure (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) where
  T P := (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  is_comm P := by
    haveI := isCyclic_sylowP P
    infer_instance
  is_conj _ _ := Sylow.coe_subgroup_smul
  is_generator := iSup_sylowP_eq_top

/-- **Conditional structural consequence (Iwasawa's criterion, generation half supplied).**

*If* the conjugation action of `SL(2, p)` on its Sylow `p`-subgroups is quasi-preprimitive, then
every normal subgroup `N` that acts **nontrivially** on the Sylow set is the whole group.

Indeed `sylowIwasawaStructure` together with `IwasawaStructure.commutator_le` gives
`commutator (SL(2,p)) ≤ N`, and `commutator (SL(2,p)) = ⊤` by perfectness for `p ≥ 5`
(`commutator_eq_top`).  Equivalently: any proper normal subgroup of `SL(2, p)` acts trivially,
i.e. lies in the kernel of the action (the centre `{±1}`) — the precise quasi-simplicity statement
modulo the still-open primitivity hypothesis `[IsQuasiPreprimitive …]`. -/
theorem eq_top_of_normal_of_acts_nontrivially (hp : 5 ≤ p)
    [MulAction.IsQuasiPreprimitive (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))]
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) [N.Normal]
    (hN : MulAction.fixedPoints N
        (Sylow p (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ≠ Set.univ) :
    N = ⊤ := by
  have h := (sylowIwasawaStructure (p := p)).commutator_le N hN
  rw [commutator_eq_top hp] at h
  exact top_le_iff.mp h

/-! ### The Borel is the normalizer of `U`: `[SL : B] = p + 1` and `|B| = p(p − 1)`

Sylow's theorem pins the normalizer of the unipotent Sylow `p`-subgroup `U` *without* the
explicit "normaliser-is-upper-triangular" matrix computation.  The conjugation action of
`SL(2, p)` on its `p + 1` Sylow `p`-subgroups (`card_sylow_eq`) is transitive with point
stabiliser `N(U)`, so

* `[SL : N(U)] = n_p = p + 1`  (`Sylow.card_eq_index_normalizer`), and hence
* `|N(U)| = |SL| / (p + 1) = p(p² − 1)/(p + 1) = p(p − 1)`  (`Subgroup.card_mul_index`).

Combined with `borel ≤ N(U)` (`borel_le_normalizer_unipotent`) and the reverse cardinality
bound `|B| ≥ |U| · |T| = p(p − 1)` — the injection `ZMod p × (ZMod p)ˣ ↪ B`,
`(a, b) ↦ u(a)·diag(b)`, is injective because `U ∩ T = 1`
(`unipotent_inter_torus_trivial`) — this identifies the Borel exactly:

    B = N(U),   |B| = p(p − 1),   [SL : B] = p + 1.

`B` is the point stabiliser of the `(p + 1)`-point conjugation action — the concrete
`|P¹(𝔽_p)| = p + 1` on which the Iwasawa route to simplicity of `PSL(2, p)` runs.  This
discharges the `|B| = p(p − 1)` claim previously only *asserted* in the `B = U ⋊ T`
docstrings. -/

/-- **The unipotent Sylow subgroup coincides with the unipotent radical `U`.**  `unipotentSylow`
is built from `unipotentHom.range = unipotentSubgroup` via `Sylow.ofCard`, so the two agree
definitionally.  This bridges the Sylow-theoretic normalizer facts (stated for `↑unipotentSylow`)
and the Borel infrastructure (stated for `unipotentSubgroup`). -/
theorem coe_unipotentSylow :
    ((unipotentSylow (p := p) :
        Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) = unipotentSubgroup :=
  rfl

/-- **`[SL(2, p) : N(U)] = p + 1`.**  The index of the normalizer of the unipotent Sylow
subgroup is the number of Sylow `p`-subgroups `n_p = p + 1` (`card_sylow_eq`), by the
Sylow orbit–stabiliser identity `Sylow.card_eq_index_normalizer`. -/
theorem index_normalizer_unipotent (hp : 5 ≤ p) :
    (Subgroup.normalizer
        (↑(unipotentSubgroup (p := p)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))).index = p + 1 := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := Finite.of_fintype _
  have h := (unipotentSylow (p := p)).card_eq_index_normalizer
  rw [card_sylow_eq hp] at h
  exact h.symm

/-- **`|N(U)| = p(p − 1)`.**  From `|N(U)| · [SL : N(U)] = |SL| = p(p² − 1)`
(`Subgroup.card_mul_index`, `card_SL2`) and `[SL : N(U)] = p + 1`
(`index_normalizer_unipotent`), cancelling the common factor `p + 1 = (p² − 1)/(p − 1)`. -/
theorem card_normalizer_unipotent (hp : 5 ≤ p) :
    Nat.card (Subgroup.normalizer
        (↑(unipotentSubgroup (p := p)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) = p * (p - 1) := by
  have hmul := Subgroup.card_mul_index
    (Subgroup.normalizer
      (↑(unipotentSubgroup (p := p)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
  rw [index_normalizer_unipotent hp, card_SL2] at hmul
  -- hmul : Nat.card (N U) * (p + 1) = p * (p ^ 2 - 1)
  have hpsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have h2 : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have key : Nat.card (Subgroup.normalizer
      (↑(unipotentSubgroup (p := p)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))) * (p + 1)
      = (p * (p - 1)) * (p + 1) := by
    rw [hmul, hpsq]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) key

/-- **Lower bound `p(p − 1) ≤ |B|`.**  The map `ZMod p × (ZMod p)ˣ → B`,
`(a, b) ↦ u(a)·diag(b)`, lands in the Borel (both factors are among its generators) and is
injective: if `u(a₁)·diag(b₁) = u(a₂)·diag(b₂)` then `u(a₁ − a₂) = u(a₂)⁻¹u(a₁) =
diag(b₂)diag(b₁)⁻¹ = diag(b₂b₁⁻¹) ∈ U ∩ T = 1` (`unipotent_inter_torus_trivial`), forcing
`a₁ = a₂`, `b₁ = b₂`.  Hence `|B| ≥ |ZMod p × (ZMod p)ˣ| = p(p − 1)`. -/
theorem card_borel_ge :
    p * (p - 1) ≤ Nat.card (borel (p := p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := Finite.of_fintype _
  set f : ZMod p × (ZMod p)ˣ → borel (p := p) := fun q =>
    ⟨unipotentUpper q.1 * torusDiag q.2,
      mul_mem
        (Subgroup.subset_closure (Set.mem_union_left _ ⟨q.1, rfl⟩))
        (Subgroup.subset_closure (Set.mem_union_right _ ⟨q.2, rfl⟩))⟩ with hf_def
  have hf : Function.Injective f := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hq
    rw [hf_def] at hq
    simp only [Subtype.mk_eq_mk] at hq
    -- hq : u(a₁) * diag(b₁) = u(a₂) * diag(b₂)
    have hu : (unipotentUpper a₂)⁻¹ * unipotentUpper a₁ = unipotentUpper (a₁ - a₂) := by
      rw [unipotentUpper_inv, unipotentUpper_mul]; ring_nf
    have ht : torusDiag b₂ * (torusDiag b₁)⁻¹ = torusDiag (b₂ * b₁⁻¹) := by
      rw [torusDiag_inv, ← torusHom_apply, ← torusHom_apply, ← torusHom_apply, ← map_mul]
    have key' : (unipotentUpper a₂)⁻¹ * unipotentUpper a₁
        = torusDiag b₂ * (torusDiag b₁)⁻¹ := by
      have h2 : unipotentUpper a₁
          = unipotentUpper a₂ * torusDiag b₂ * (torusDiag b₁)⁻¹ := by
        rw [← hq]; group
      rw [h2]; group
    rw [hu, ht] at key'
    obtain ⟨ha, hb⟩ := unipotent_inter_torus_trivial _ _ key'
    have hae : a₁ = a₂ := by rwa [sub_eq_zero] at ha
    have hbe : b₁ = b₂ := by rw [mul_inv_eq_one] at hb; exact hb.symm
    exact Prod.ext hae hbe
  have hdom : Nat.card (ZMod p × (ZMod p)ˣ) = p * (p - 1) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card,
      ZMod.card_units]
  have hle := Nat.card_le_card_of_injective f hf
  rwa [hdom] at hle

/-- **The Borel equals the normalizer of `U`.**  `borel ≤ N(U)` (`borel_le_normalizer_unipotent`)
and `|N(U)| = p(p − 1) ≤ |B|` (`card_normalizer_unipotent`, `card_borel_ge`), so the two finite
subgroups coincide (`Subgroup.eq_of_le_of_card_ge`).  This upgrades the containment
`B ⊆ N(U)` to an identity, giving the exact matrix-free description of the Borel as the Sylow
normalizer. -/
theorem borel_eq_normalizer_unipotent (hp : 5 ≤ p) :
    borel (p := p) = Subgroup.normalizer
      (↑(unipotentSubgroup (p := p)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := Finite.of_fintype _
  refine Subgroup.eq_of_le_of_card_ge borel_le_normalizer_unipotent ?_
  rw [card_normalizer_unipotent hp]
  exact card_borel_ge

/-- **`|B| = p(p − 1)`.**  Immediate from `B = N(U)` (`borel_eq_normalizer_unipotent`) and
`|N(U)| = p(p − 1)` (`card_normalizer_unipotent`).  This discharges the internal
`B = U ⋊ T`, `|B| = p(p − 1)` claim of the Borel docstrings. -/
theorem card_borel (hp : 5 ≤ p) :
    Nat.card (borel (p := p)) = p * (p - 1) := by
  rw [borel_eq_normalizer_unipotent hp, card_normalizer_unipotent hp]

/-- **`[SL(2, p) : B] = p + 1`.**  From `B = N(U)` (`borel_eq_normalizer_unipotent`) and
`[SL : N(U)] = p + 1` (`index_normalizer_unipotent`).  So the Borel has exactly `p + 1`
cosets — the `p + 1` points of `P¹(𝔽_p)` / the `p + 1` Sylow `p`-subgroups on which the
conjugation action is realised. -/
theorem index_borel (hp : 5 ≤ p) :
    (borel (p := p)).index = p + 1 := by
  rw [borel_eq_normalizer_unipotent hp, index_normalizer_unipotent hp]


end SylowOQ04OQ03

#print axioms SylowOQ04OQ03.sylow_count_arith
#print axioms SylowOQ04OQ03.index_unipotentSylow
#print axioms SylowOQ04OQ03.card_sylow_eq
#print axioms SylowOQ04OQ03.card_orderOf_eq_p
#print axioms SylowOQ04OQ03.iSup_sylowP_eq_top
#print axioms SylowOQ04OQ03.sylowIwasawaStructure
#print axioms SylowOQ04OQ03.eq_top_of_normal_of_acts_nontrivially
#print axioms SylowOQ04OQ03.index_normalizer_unipotent
#print axioms SylowOQ04OQ03.card_normalizer_unipotent
#print axioms SylowOQ04OQ03.card_borel_ge
#print axioms SylowOQ04OQ03.borel_eq_normalizer_unipotent
#print axioms SylowOQ04OQ03.card_borel
#print axioms SylowOQ04OQ03.index_borel
