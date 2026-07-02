import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# The `{±1}`-quotient of generators is in bijection with primitive triples
  (pythagorean-theorem-oq-04-oq-01)

## What this proves

The parent entry `PythagoreanTheoremOQ04` shows that squaring in the Gaussian
integers `ℤ[i]` parameterizes Pythagorean triples,
`(m + ni)² ↦ (m² - n², 2mn, m² + n²)`, and that the generating pair `(m, n)` is
determined by its triple *only up to the sign `±1`*
(`generator_unique_up_to_sign`): squaring is two-to-one, `g² = (-g)²`.

This follow-up **packages that `{±1}` ambiguity as an honest quotient** and turns
the up-to-sign uniqueness into a genuine injection, then a bijection.

* **The sign relation.** On generator pairs `ℤ × ℤ` we identify `(m, n)` with
  `(-m, -n)`. This `SignRel` is exactly the orbit relation of the sign subgroup
  `{±1} ⊆ ℤ[i]ˣ` acting by multiplication (`(-1)·(m + ni) = -m - ni`), and it is an
  equivalence relation (`signSetoid`).

* **Descent.** The triple map `genTriple (m, n) = (m² - n², 2mn, m² + n²)` is
  constant on sign-orbits (`genTriple_neg`), so it descends to the quotient
  `GenClass := (ℤ × ℤ) / SignRel` as `classTriple`.

* **Injectivity (the point).** On the quotient the parameterization becomes
  **injective** (`classTriple_injective`): distinct sign-classes give distinct
  triples. This is the up-to-sign uniqueness of the parent, now with the `±1`
  redundancy quotiented away — no chosen representative, no sign normalization,
  and the `m = 0` degenerate case is handled uniformly because `(0, 1)` and
  `(0, -1)` are *already the same class*.

* **Surjectivity / bijection.** Every primitive triple with `x` odd and `z > 0` is
  the image of a generator class (`classTriple_surj_onto_primitive`, from Mathlib's
  `coprime_classification'`). Together with injectivity this is the genuine
  bijection the open question asked for: sign-classes of coprime opposite-parity
  generators correspond bijectively to primitive triples.

## Status

- [x] Complete proof, no sorries
- [x] 0 `axiom` declarations, no structure-encoded assumptions
- [x] `SignRel` proven to be an equivalence relation (`signSetoid`)
- [x] `classTriple` well-defined on the quotient (descent via `genTriple_neg`)
- [x] `classTriple` injective — the `{±1}` ambiguity is fully quotiented
- [x] Surjective onto primitive triples (`x` odd, `z > 0`)
-/

namespace PythagoreanTheoremOQ04OQ01

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-! ## Reused Gaussian-integer facts (self-contained copies from the parent entry) -/

/-- Squaring in `ℤ[i]` realizes the parameterization map:
`(m + ni)² = (m² - n²) + (2mn)i`. -/
theorem gaussianInt_sq (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]) ^ 2 = ⟨m * m - n * n, 2 * m * n⟩ := by
  rw [sq]
  apply Zsqrtd.ext <;> simp <;> ring

/-- The norm of a Gaussian integer is the sum of squares of its components. -/
theorem gaussianInt_norm (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]).norm = m * m + n * n := by
  simp [Zsqrtd.norm_def]

/-- Two Gaussian integers with equal squares are equal or negatives (the domain
`ℤ[i]` has no zero divisors). Coordinatewise: `(m,n)` is `(m',n')` or `(-m',-n')`. -/
theorem gen_coords_unique_up_to_sign {m n m' n' : ℤ}
    (h : (⟨m, n⟩ : ℤ[i]) ^ 2 = (⟨m', n'⟩ : ℤ[i]) ^ 2) :
    (m = m' ∧ n = n') ∨ (m = -m' ∧ n = -n') := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with heq | hneg
  · exact Or.inl ⟨congrArg Zsqrtd.re heq, congrArg Zsqrtd.im heq⟩
  · have hre := congrArg Zsqrtd.re hneg
    have him := congrArg Zsqrtd.im hneg
    simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hre him
    exact Or.inr ⟨hre, him⟩

/-! ## The triple map and its `{±1}` invariance -/

/-- The parameterization on raw coordinate pairs:
`(m, n) ↦ (m² - n², 2mn, m² + n²)`. -/
def genTriple (p : ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (p.1 * p.1 - p.2 * p.2, 2 * p.1 * p.2, p.1 * p.1 + p.2 * p.2)

@[simp] theorem genTriple_mk (m n : ℤ) :
    genTriple (m, n) = (m * m - n * n, 2 * m * n, m * m + n * n) := rfl

/-- `genTriple` is invariant under the sign flip `(m, n) ↦ (-m, -n)`: squares and the
doubled product are unchanged. This is what makes squaring two-to-one. -/
theorem genTriple_neg (p : ℤ × ℤ) : genTriple (-p.1, -p.2) = genTriple p := by
  simp only [genTriple]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

/-! ## The sign relation as an equivalence -/

/-- Two generator pairs are `SignRel`-related when they are equal or exact
negatives — the orbit relation of the sign subgroup `{±1}` of units. -/
def SignRel (p q : ℤ × ℤ) : Prop := p = q ∨ p = (-q.1, -q.2)

theorem SignRel.refl (p : ℤ × ℤ) : SignRel p p := Or.inl rfl

theorem SignRel.symm {p q : ℤ × ℤ} (h : SignRel p q) : SignRel q p := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2]

theorem SignRel.trans {p q r : ℤ × ℤ} (hpq : SignRel p q) (hqr : SignRel q r) :
    SignRel p r := by
  rcases hpq with rfl | hpq
  · exact hqr
  · rcases hqr with rfl | hqr
    · exact Or.inr hpq
    · left
      obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r
      simp only [Prod.mk.injEq] at hpq hqr
      obtain ⟨ha, hb⟩ := hpq; obtain ⟨hc, hd⟩ := hqr
      subst hc; subst hd
      rw [neg_neg] at ha hb
      simp [ha, hb]

/-- The `{±1}` sign relation on generator pairs, as a `Setoid`. -/
def signSetoid : Setoid (ℤ × ℤ) where
  r := SignRel
  iseqv := ⟨SignRel.refl, SignRel.symm, SignRel.trans⟩

/-- Sign-classes of generator pairs. -/
def GenClass : Type := Quotient signSetoid

/-! ## Injectivity of the raw map up to sign -/

/-- **Up-to-sign injectivity.** If two generator pairs produce the *same* triple,
they are `SignRel`-related. Proof: equal triple coordinates force equal Gaussian
squares, and equal squares differ only by a sign (`gen_coords_unique_up_to_sign`). -/
theorem genTriple_inj (p q : ℤ × ℤ) (h : genTriple p = genTriple q) : SignRel p q := by
  obtain ⟨m, n⟩ := p
  obtain ⟨m', n'⟩ := q
  simp only [genTriple_mk, Prod.mk.injEq] at h
  obtain ⟨hre, him, _⟩ := h
  have hsq : (⟨m, n⟩ : ℤ[i]) ^ 2 = (⟨m', n'⟩ : ℤ[i]) ^ 2 := by
    rw [gaussianInt_sq, gaussianInt_sq]
    apply Zsqrtd.ext
    · exact hre
    · exact him
  rcases gen_coords_unique_up_to_sign hsq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl (by simp [e1, e2])
  · exact Or.inr (by simp [e1, e2])

/-! ## The descended map on the quotient -/

/-- The triple map descends to the quotient by the sign relation. -/
def classTriple : GenClass → ℤ × ℤ × ℤ :=
  Quotient.lift genTriple (by
    intro p q h
    rcases h with rfl | h
    · rfl
    · obtain ⟨q1, q2⟩ := q
      subst h
      exact genTriple_neg (q1, q2))

@[simp] theorem classTriple_mk (p : ℤ × ℤ) :
    classTriple (Quotient.mk signSetoid p) = genTriple p := rfl

/-- **Main result: the parameterization is injective once the `{±1}` ambiguity is
quotiented away.** Distinct sign-classes of generators give distinct Pythagorean
triples — the up-to-sign uniqueness of the parent, now with no chosen sign. -/
theorem classTriple_injective : Function.Injective classTriple := by
  intro a b hab
  induction a using Quotient.ind with
  | _ p =>
    induction b using Quotient.ind with
    | _ q =>
      have h : genTriple p = genTriple q := hab
      exact Quotient.sound (genTriple_inj p q h)

/-! ## Surjectivity onto primitive triples -/

/-- **Surjectivity.** Every primitive Pythagorean triple `(x, y, z)` with `x` odd and
`z > 0` is `classTriple` of some generator class — via Mathlib's
`coprime_classification'`. With `classTriple_injective` this is the genuine bijection
between sign-classes of coprime opposite-parity generators and primitive triples. -/
theorem classTriple_surj_onto_primitive {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hpos : 0 < z) :
    ∃ c : GenClass, classTriple c = (x, y, z) := by
  obtain ⟨m, n, hx, hy, hz, _, _, _⟩ := h.coprime_classification' hco hodd hpos
  refine ⟨Quotient.mk signSetoid (m, n), ?_⟩
  rw [classTriple_mk, genTriple_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; rw [hx]; ring
  · simp only; rw [hy]
  · simp only; rw [hz]; ring

/-! ## Worked examples: the quotient collapses the sign ambiguity -/

/-- `(3, 4, 5)` from the class of `(2, 1)`. -/
example : classTriple (Quotient.mk signSetoid (2, 1)) = (3, 4, 5) := by
  rw [classTriple_mk]; decide

/-- The opposite-sign generator `(-2, -1)` is the *same class*, hence the same triple:
the `{±1}` ambiguity has been quotiented away. -/
example : Quotient.mk signSetoid (-2, -1) = Quotient.mk signSetoid (2, 1) := by
  apply Quotient.sound
  right
  rfl

/-- `(5, 12, 13)` from the class of `(3, 2)`. -/
example : classTriple (Quotient.mk signSetoid (3, 2)) = (5, 12, 13) := by
  rw [classTriple_mk]; decide

end PythagoreanTheoremOQ04OQ01
