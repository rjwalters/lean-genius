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

/-- **Every torus element is a word in the two root groups.**
`diag(a) = u(a)·l(-a⁻¹)·u(a)·w`:

    [[a, 0], [0, a⁻¹]]
      = [[1, a], [0, 1]] · [[1, 0], [-a⁻¹, 1]] · [[1, a], [0, 1]] · [[0, -1], [1, 0]].

Hence the whole split torus `T` lies in `⟨U, U⁻⟩`. -/
set_option maxHeartbeats 800000 in
theorem torusDiag_eq_root_word (a : (ZMod p)ˣ) :
    torusDiag a
      = unipotentUpper (a : ZMod p) * lowerUnipotent (-((a : ZMod p)⁻¹))
          * unipotentUpper (a : ZMod p) * weylW := by
  have hc : (a : ZMod p) ≠ 0 := a.ne_zero
  have hinv : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = (a : ZMod p)⁻¹ :=
    Units.val_inv_eq_inv_val a
  apply Subtype.ext
  show (!![(a : ZMod p), 0; 0, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)]
        : Matrix (Fin 2) (Fin 2) (ZMod p))
      = !![1, (a : ZMod p); 0, 1] * !![1, 0; -((a : ZMod p)⁻¹), 1]
          * !![1, (a : ZMod p); 0, 1] * !![0, -1; 1, 0]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

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

/-- **Bruhat cell membership.**  Every `g ∈ SL(2, p)` whose lower-left entry `c` is
nonzero lies in `⟨U, U⁻⟩`, via the Bruhat factorization

    g = u(a·c⁻¹) · w · diag(c) · u(d·c⁻¹),

where `a = g₀₀`, `d = g₁₁`.  (The top-right entry checks out because
`ad − bc = 1`.)  Since `u(·), w, diag(c)` all lie in `⟨U, U⁻⟩`, so does `g`. -/
set_option maxHeartbeats 800000 in
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
      field_simp <;>
      first
        | ring
        | linear_combination hdet
        | linear_combination -hdet
        | linear_combination (A 1 0) * hdet
        | linear_combination -(A 1 0) * hdet
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
      (MulEquiv.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv
  -- (2) Lagrange: `|ker| · index = |GL|`.
  have hmulindex : Nat.card D.ker * D.ker.index = Nat.card (GL (Fin 2) (ZMod p)) :=
    D.ker.card_mul_index
  -- (3) `index = |range(det)| = |𝔽_pˣ| = p − 1`.
  have hindex : D.ker.index = p - 1 := by
    rw [MonoidHom.index_ker, MonoidHom.range_eq_top.mpr hsurj,
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
  -- A solvable quotient and (automatically) solvable central kernel force the middle
  -- group `SL(2, p)` to be solvable via the central extension.
  haveI : IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    solvable_of_ker_le_range
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).subtype
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))
      (by rw [QuotientGroup.ker_mk']; exact (Subgroup.range_subtype _).ge)
  exact not_isSolvable hp this

end SylowOQ04OQ03
