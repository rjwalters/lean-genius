/-
# CRT for 3 Non-Coprime Moduli in PIDs (OQ-02-OQ-01)

The classical Chinese Remainder Theorem covers coprime moduli.  The parent entry
`chinese-remainder-non-coprime-oq-02` settled the **two-modulus** non-coprime case
in PIDs / Euclidean domains: the system

  x ≡ a (mod m),   x ≡ b (mod n)

is solvable iff `gcd m n ∣ a - b`, and solutions are unique mod `lcm m n`.

For **three or more** moduli the natural conjecture is *pairwise compatibility*:

  x ≡ aᵢ (mod mᵢ),  i = 1, 2, 3      solvable  ⟺  gcd mᵢ mⱼ ∣ aᵢ - aⱼ for all i,j.

The forward (necessity) direction holds in any commutative ring.  The converse
(pairwise compatibility ⟹ a global solution) is the subtle part: it is **false**
in a general commutative ring and becomes true exactly when the lattice of ideals
is distributive.  In a PID / Bézout domain that distributivity is automatic, and
this file makes the whole argument precise.

## The mathematical heart: distributivity of the divisibility lattice

The reduction of three moduli to two needs the identity

  gcd (lcm m₁ m₂) m₃  ∣  lcm (gcd m₁ m₃) (gcd m₂ m₃).            (★)

Translated to ideals this is the *distributive* inequality

  (I₁ ⊔ I₃) ⊓ (I₂ ⊔ I₃)  ≤  (I₁ ⊓ I₂) ⊔ I₃,

whose reverse holds in every lattice; the displayed direction is what
distinguishes the divisibility lattice of a UFD/Bézout domain.  We prove (★) by
transporting the goal through `Associates.factors` to the genuinely distributive
lattice `FactorSet R` (a `WithTop (Multiset _)`), where it is `inf_sup_right`.

With (★) in hand the three-modulus CRT follows by solving `m₁, m₂` first and then
combining with `m₃` over the modulus `lcm m₁ m₂`.

## Main results

* `gcd_lcm_distrib`        — the distributive law (★) for a UFD / GCD domain.
* `crt2_iff`              — two-modulus CRT: solvable ↔ `gcd m n ∣ a - b`.
* `crt3_necessary`        — pairwise gcd conditions are necessary.
* `crt3_sufficient`       — pairwise compatibility ⟹ a global solution (uses ★).
* `crt3_iff`             — the full characterization for three moduli.
* `crt3_unique`           — solutions are unique mod `lcm (lcm m₁ m₂) m₃`.
* `crt3_solution_set`     — combined existence + uniqueness statement.

All results are stated for a commutative domain that is simultaneously a Bézout
ring and a UFD — i.e. a PID such as `ℤ`, `k[X]`, or `ℤ[i]` (see the closing
`example`s instantiating `ℤ`).

The sibling gallery entry `chinese-remainder-non-coprime-oq-03-oq-01` proves the
same distributive law (★) by an elementary coprime-cofactor argument over Euclidean
domains; the factorization-model proof given here (`gcd_lcm_distrib`) is shorter and
holds in any UFD.

References:
- Hungerford (1974), *Algebra*, Ch. III (CRT and ideal arithmetic).
- Cohn (1968), *Bezout rings and their subrings* (distributivity of f.g. ideals).
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderNonCoprimeOQ02OQ01

open Associates

/-
## Part I: Distributivity of the divisibility lattice

We work in a UFD; the divisibility order on `Associates R` is then a lattice, and
we transport distributivity from the `FactorSet` (multiset) model.
-/

section Distrib

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- The lattice `Associates R` of a UFD is distributive (the nontrivial direction
`(A ⊔ B) ⊓ C ≤ (A ⊓ C) ⊔ (B ⊓ C)`).  Proved by pushing the inequality through the
order isomorphism `Associates.factors` onto the distributive lattice `FactorSet R`. -/
theorem associates_inf_sup_le [Nontrivial R] (A B C : Associates R) :
    (A ⊔ B) ⊓ C ≤ (A ⊓ C) ⊔ (B ⊓ C) := by
  classical
  have hsup : ∀ x y : Associates R, (x ⊔ y).factors = x.factors ⊔ y.factors := by
    intro x y
    show ((x.factors ⊔ y.factors).prod).factors = _
    rw [prod_factors]
  have hinf : ∀ x y : Associates R, (x ⊓ y).factors = x.factors ⊓ y.factors := by
    intro x y
    show ((x.factors ⊓ y.factors).prod).factors = _
    rw [prod_factors]
  rw [← Associates.factors_le, hinf, hsup, hsup, hinf, hinf]
  exact (inf_sup_right _ _ _).le

variable [GCDMonoid R]

/-- `mk (gcd a b)` is the lattice meet of `mk a` and `mk b` in `Associates R`. -/
theorem mk_gcd_eq_inf (a b : R) :
    Associates.mk (gcd a b) = Associates.mk a ⊓ Associates.mk b := by
  refine le_antisymm (le_inf (mk_le_mk_of_dvd (gcd_dvd_left a b))
    (mk_le_mk_of_dvd (gcd_dvd_right a b))) ?_
  obtain ⟨e, he⟩ := Associates.mk_surjective (Associates.mk a ⊓ Associates.mk b)
  rw [← he]
  exact mk_le_mk_of_dvd (dvd_gcd (dvd_of_mk_le_mk (he ▸ inf_le_left))
    (dvd_of_mk_le_mk (he ▸ inf_le_right)))

/-- `mk (lcm a b)` is the lattice join of `mk a` and `mk b` in `Associates R`. -/
theorem mk_lcm_eq_sup (a b : R) :
    Associates.mk (lcm a b) = Associates.mk a ⊔ Associates.mk b := by
  refine le_antisymm ?_ (sup_le (mk_le_mk_of_dvd (dvd_lcm_left a b))
    (mk_le_mk_of_dvd (dvd_lcm_right a b)))
  obtain ⟨e, he⟩ := Associates.mk_surjective (Associates.mk a ⊔ Associates.mk b)
  rw [← he]
  exact mk_le_mk_of_dvd (lcm_dvd (dvd_of_mk_le_mk (he ▸ le_sup_left))
    (dvd_of_mk_le_mk (he ▸ le_sup_right)))

/-- **Distributive law of divisibility (★).** In a UFD / GCD domain,
`gcd (lcm a b) c ∣ lcm (gcd a c) (gcd b c)`.

The reverse divisibility `lcm (gcd a c) (gcd b c) ∣ gcd (lcm a b) c` holds in any
GCD monoid; this direction is the distributive one and is the engine of the
three-modulus CRT. -/
theorem gcd_lcm_distrib [Nontrivial R] (a b c : R) :
    gcd (lcm a b) c ∣ lcm (gcd a c) (gcd b c) := by
  rw [← Associates.mk_dvd_mk, mk_gcd_eq_inf, mk_lcm_eq_sup, mk_lcm_eq_sup,
    mk_gcd_eq_inf, mk_gcd_eq_inf]
  exact associates_inf_sup_le _ _ _

/-- The easy (always-true) reverse direction, recorded for contrast with (★). -/
theorem lcm_gcd_dvd (a b c : R) :
    lcm (gcd a c) (gcd b c) ∣ gcd (lcm a b) c := by
  refine lcm_dvd (dvd_gcd ?_ (gcd_dvd_right a c)) (dvd_gcd ?_ (gcd_dvd_right b c))
  · exact (gcd_dvd_left a c).trans (dvd_lcm_left a b)
  · exact (gcd_dvd_left b c).trans (dvd_lcm_right a b)

end Distrib

/-
## Part II: Two-modulus CRT in a Bézout domain

`gcd m n ∣ a - b` is necessary and sufficient; this is the parent result, reproved
here through Bézout's identity (`gcd_dvd_iff_exists`) so the file is self-contained.
-/

section CRT

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [GCDMonoid R]
  [UniqueFactorizationMonoid R]

/-- Necessity for two moduli: a common solution forces `gcd m n ∣ a - b`. -/
theorem crt2_necessary {m n a b : R} (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) :
    gcd m n ∣ a - b := by
  obtain ⟨x, hm, hn⟩ := h
  have := dvd_sub ((gcd_dvd_right m n).trans hn) ((gcd_dvd_left m n).trans hm)
  rwa [show (x - b) - (x - a) = a - b by ring] at this

/-- Sufficiency for two moduli, via Bézout: if `gcd m n ∣ a - b` then the system
`x ≡ a (mod m)`, `x ≡ b (mod n)` has a solution. -/
theorem crt2_sufficient {m n a b : R} (h : gcd m n ∣ a - b) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨s, t, hst⟩ := (gcd_dvd_iff_exists m n).mp h
  exact ⟨a - m * s, ⟨-s, by ring⟩, ⟨t, by linear_combination hst⟩⟩

/-- **Two-modulus non-coprime CRT.** -/
theorem crt2_iff {m n a b : R} :
    (∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) ↔ gcd m n ∣ a - b :=
  ⟨crt2_necessary, crt2_sufficient⟩

/-- Two-modulus uniqueness: any two solutions agree mod `lcm m n`. -/
theorem crt2_unique {m n a b x y : R}
    (hx : m ∣ (x - a) ∧ n ∣ (x - b)) (hy : m ∣ (y - a) ∧ n ∣ (y - b)) :
    lcm m n ∣ x - y := by
  refine lcm_dvd ?_ ?_
  · have := dvd_sub hx.1 hy.1; rwa [show (x - a) - (y - a) = x - y by ring] at this
  · have := dvd_sub hx.2 hy.2; rwa [show (x - b) - (y - b) = x - y by ring] at this

/-
## Part III: Three-modulus CRT
-/

/-- **Necessity** for three moduli: pairwise gcd-compatibility of the residues. -/
theorem crt3_necessary {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h : ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) :
    gcd m₁ m₂ ∣ a₁ - a₂ ∧ gcd m₁ m₃ ∣ a₁ - a₃ ∧ gcd m₂ m₃ ∣ a₂ - a₃ := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨crt2_necessary ⟨x, h1, h2⟩, crt2_necessary ⟨x, h1, h3⟩, crt2_necessary ⟨x, h2, h3⟩⟩

/-- **Sufficiency** for three moduli: pairwise compatibility yields a global
solution.  This is the main new result; the distributive law `gcd_lcm_distrib` (★)
is exactly what lets us combine the solution of the first two congruences with the
third over the modulus `lcm m₁ m₂`. -/
theorem crt3_sufficient {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h12 : gcd m₁ m₂ ∣ a₁ - a₂)
    (h13 : gcd m₁ m₃ ∣ a₁ - a₃)
    (h23 : gcd m₂ m₃ ∣ a₂ - a₃) :
    ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃) := by
  -- Solve the first two congruences.
  obtain ⟨y, hy1, hy2⟩ := crt2_sufficient h12
  -- The combined residue `y` is compatible with `a₃` modulo each of `m₁`, `m₂`.
  have hd1 : gcd m₁ m₃ ∣ y - a₃ := by
    have h := dvd_add ((gcd_dvd_left m₁ m₃).trans hy1) h13
    rwa [show (y - a₁) + (a₁ - a₃) = y - a₃ by ring] at h
  have hd2 : gcd m₂ m₃ ∣ y - a₃ := by
    have h := dvd_add ((gcd_dvd_left m₂ m₃).trans hy2) h23
    rwa [show (y - a₂) + (a₂ - a₃) = y - a₃ by ring] at h
  -- Distributivity (★): `gcd (lcm m₁ m₂) m₃` divides `y - a₃`.
  have hkey : gcd (lcm m₁ m₂) m₃ ∣ y - a₃ :=
    (gcd_lcm_distrib m₁ m₂ m₃).trans (lcm_dvd hd1 hd2)
  -- Solve `lcm m₁ m₂` and `m₃` with targets `y` and `a₃`.
  obtain ⟨x, hx1, hx2⟩ := crt2_sufficient hkey
  refine ⟨x, ?_, ?_, hx2⟩
  · have h := dvd_add ((dvd_lcm_left m₁ m₂).trans hx1) hy1
    rwa [show (x - y) + (y - a₁) = x - a₁ by ring] at h
  · have h := dvd_add ((dvd_lcm_right m₁ m₂).trans hx1) hy2
    rwa [show (x - y) + (y - a₂) = x - a₂ by ring] at h

/-- **Three-modulus non-coprime CRT.**  The system is solvable iff the residues are
pairwise compatible. -/
theorem crt3_iff {m₁ m₂ m₃ a₁ a₂ a₃ : R} :
    (∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) ↔
      (gcd m₁ m₂ ∣ a₁ - a₂ ∧ gcd m₁ m₃ ∣ a₁ - a₃ ∧ gcd m₂ m₃ ∣ a₂ - a₃) :=
  ⟨crt3_necessary, fun ⟨h12, h13, h23⟩ => crt3_sufficient h12 h13 h23⟩

/-- **Uniqueness** for three moduli: solutions agree mod `lcm (lcm m₁ m₂) m₃`,
the lcm of the three moduli (the generator of `⟨m₁⟩ ∩ ⟨m₂⟩ ∩ ⟨m₃⟩`). -/
theorem crt3_unique {m₁ m₂ m₃ a₁ a₂ a₃ x y : R}
    (hx : m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃))
    (hy : m₁ ∣ (y - a₁) ∧ m₂ ∣ (y - a₂) ∧ m₃ ∣ (y - a₃)) :
    lcm (lcm m₁ m₂) m₃ ∣ x - y := by
  refine lcm_dvd (lcm_dvd ?_ ?_) ?_
  · have := dvd_sub hx.1 hy.1; rwa [show (x - a₁) - (y - a₁) = x - y by ring] at this
  · have := dvd_sub hx.2.1 hy.2.1; rwa [show (x - a₂) - (y - a₂) = x - y by ring] at this
  · have := dvd_sub hx.2.2 hy.2.2; rwa [show (x - a₃) - (y - a₃) = x - y by ring] at this

/-- Combined existence-and-uniqueness statement for three pairwise-compatible
moduli: a solution exists and is unique modulo `lcm (lcm m₁ m₂) m₃`. -/
theorem crt3_solution_set {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h12 : gcd m₁ m₂ ∣ a₁ - a₂) (h13 : gcd m₁ m₃ ∣ a₁ - a₃)
    (h23 : gcd m₂ m₃ ∣ a₂ - a₃) :
    (∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) ∧
      (∀ x y : R, (m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) →
        (m₁ ∣ (y - a₁) ∧ m₂ ∣ (y - a₂) ∧ m₃ ∣ (y - a₃)) →
        lcm (lcm m₁ m₂) m₃ ∣ x - y) :=
  ⟨crt3_sufficient h12 h13 h23, fun _ _ hx hy => crt3_unique hx hy⟩

end CRT

/-
## Part IV: Concrete instantiations

`ℤ` is a PID, hence simultaneously Bézout and a UFD, so every result above applies.
-/

section Examples

/-- The distributive law (★) holds in `ℤ`. -/
example (a b c : ℤ) : gcd (lcm a b) c ∣ lcm (gcd a c) (gcd b c) :=
  gcd_lcm_distrib a b c

/-- Three-modulus solvability in `ℤ` is exactly pairwise compatibility. -/
example {m₁ m₂ m₃ a₁ a₂ a₃ : ℤ} :
    (∃ x : ℤ, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) ↔
      (gcd m₁ m₂ ∣ a₁ - a₂ ∧ gcd m₁ m₃ ∣ a₁ - a₃ ∧ gcd m₂ m₃ ∣ a₂ - a₃) :=
  crt3_iff

end Examples

end ChineseRemainderNonCoprimeOQ02OQ01
