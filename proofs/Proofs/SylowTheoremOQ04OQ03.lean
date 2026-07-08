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

end SylowOQ04OQ03
