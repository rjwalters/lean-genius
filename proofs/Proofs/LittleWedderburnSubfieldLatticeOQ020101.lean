import Mathlib

/-
# The subfield lattice of a finite field: `GF(p^m) ⊆ GF(p^n) ⟺ m ∣ n`

The parent proof (`LittleWedderburnOQ02`) classifies finite fields: for every prime
power `q = p ^ n` there is a field of that order (`GaloisField p n`), unique up to
isomorphism. The first open question recorded there asks to **formalize the subfield
lattice**:

> The subfields of `GF(p^n)` are exactly the `GF(p^m)` for the divisors `m ∣ n`, and
> the inclusion `GF(p^a) ⊆ GF(p^b)` holds iff `a ∣ b`.

This file answers it on two complementary levels.

* **Abstract embedding form.** There is a `ZMod p`-algebra embedding
  `GaloisField p m →ₐ[ZMod p] GaloisField p n` **iff** `m ∣ n`
  (`embeds_iff_dvd`). This is the "lattice of abstract finite fields ordered by
  embeddability ≅ divisor lattice of exponents" statement; it follows by combining
  Mathlib's `FiniteField.nonempty_algHom_iff_finrank_dvd` with the dimension
  `finrank_{ZMod p} GF(p^k) = k`.

* **Concrete subfield form, inside a fixed `GF(p^n)`.** Working in an arbitrary
  finite field `K` with `|K| = p ^ n`, for each `m ∣ n` the set of fixed points of
  the `m`-fold Frobenius,
  `{ x : K | x ^ p ^ m = x }`,
  is a genuine `Subfield K` (`subfieldFix`, realised as the equaliser locus of the
  iterated Frobenius and the identity), and it has **exactly `p ^ m` elements**
  (`card_subfieldFix`). These subfields are nested according to divisibility:
  `a ∣ b → subfieldFix a ≤ subfieldFix b` (`subfieldFix_mono`). Counting the fixed
  points is the genuinely new content: `card_subfieldFix` says `GF(p^n)` contains a
  subfield of order `p ^ m` for every divisor `m ∣ n`, which Mathlib records only in
  the abstract `algHom` form, not as a concrete subfield-with-cardinality.

The cardinality count is the heart: the fixed points of `x ↦ x ^ p ^ m` are exactly
the roots of the separable polynomial `X ^ p ^ m - X`, which divides
`X ^ p ^ n - X = X ^ |K| - X` (because `m ∣ n`); the latter splits in `K` with all
`|K|` field elements as simple roots, so the divisor splits too and contributes
`deg = p ^ m` distinct roots.

Everything is fully machine-checked with no axioms or sorries.
-/

open Polynomial

namespace LittleWedderburnOQ02OQ01

/-! ## Abstract embedding lattice: `GF(p^m) ↪ GF(p^n) ⟺ m ∣ n` -/

/-- **Embedding characterization.** For a prime `p` and exponents `m, n ≥ 1`, there is
a `ZMod p`-algebra embedding `GF(p^m) → GF(p^n)` iff `m ∣ n`. Equivalently: the
poset of canonical finite fields `GF(p^k)` ordered by embeddability is isomorphic to
the divisor poset of the exponents. -/
theorem embeds_iff_dvd (p m n : ℕ) [Fact p.Prime] (hm : m ≠ 0) (hn : n ≠ 0) :
    Nonempty (GaloisField p m →ₐ[ZMod p] GaloisField p n) ↔ m ∣ n := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd, GaloisField.finrank p hm,
    GaloisField.finrank p hn]

/-- The constructive direction: `m ∣ n` produces an embedding `GF(p^m) ↪ GF(p^n)`. -/
theorem nonempty_algHom_of_dvd (p m n : ℕ) [Fact p.Prime] (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) : Nonempty (GaloisField p m →ₐ[ZMod p] GaloisField p n) :=
  (embeds_iff_dvd p m n hm hn).2 hmn

/-! ## Concrete fixed-point subfield inside a fixed finite field -/

variable {K : Type*} [Field K]

/-- The subfield of fixed points of the `m`-fold Frobenius `x ↦ x ^ p ^ m`, realised
as the equaliser locus of `iterateFrobenius K p m` and the identity ring map. Its
elements are exactly the `x` with `x ^ p ^ m = x`. When `|K| = p ^ n` and `m ∣ n`
this is the unique subfield of `K` of order `p ^ m` (see `card_subfieldFix`). -/
def subfieldFix (p m : ℕ) [ExpChar K p] : Subfield K :=
  (iterateFrobenius K p m).eqLocusField (RingHom.id K)

@[simp]
theorem mem_subfieldFix (p m : ℕ) [ExpChar K p] {x : K} :
    x ∈ subfieldFix (K := K) p m ↔ x ^ p ^ m = x := Iff.rfl

/-- **Inclusion lattice.** If `a ∣ b` then the `a`-th fixed subfield is contained in
the `b`-th one: `GF(p^a) ⊆ GF(p^b)` whenever `a ∣ b`. -/
theorem subfieldFix_mono (p : ℕ) [ExpChar K p] {a b : ℕ} (hab : a ∣ b) :
    subfieldFix (K := K) p a ≤ subfieldFix (K := K) p b := by
  intro x hx
  rw [mem_subfieldFix] at hx ⊢
  -- `x ^ p ^ a - x ∣ x ^ p ^ b - x`; the left side is `0`, forcing the right to be `0`.
  have hdvd : (x ^ p ^ a - x) ∣ (x ^ p ^ b - x) := dvd_pow_pow_sub_self_of_dvd hab
  rw [sub_eq_zero.mpr hx, zero_dvd_iff, sub_eq_zero] at hdvd
  exact hdvd

/-- **Cardinality of the fixed subfield.** In a finite field `K` of order `p ^ n`,
for every divisor `m ∣ n` the subfield of fixed points of the `m`-fold Frobenius has
exactly `p ^ m` elements. Equivalently: `GF(p^n)` contains a subfield of order `p ^ m`
for each `m ∣ n`. -/
theorem card_subfieldFix [Fintype K] (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hcard : Fintype.card K = p ^ n) {m : ℕ} (hm : m ≠ 0) (hmn : m ∣ n) :
    Nat.card (subfieldFix (K := K) p m) = p ^ m := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpm1 : 1 < p ^ m := Nat.one_lt_pow hm hp
  -- The fixing polynomial.
  set f : K[X] := X ^ p ^ m - X with hf
  have hf_ne : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hpm1
  -- Separability of `X ^ p ^ m - X`.
  have hsep : f.Separable := galois_poly_separable p (p ^ m) (dvd_pow_self p hm)
  -- `X ^ p ^ n - X = X ^ |K| - X` splits in `K` (every element is a simple root).
  have h1lt : 1 < Fintype.card K := Fintype.one_lt_card
  have hbig : (X ^ Fintype.card K - X : K[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K h1lt, ← Finset.card_def, Finset.card_univ]
  -- `f ∣ X ^ p ^ n - X` because `m ∣ n`.
  have hdvd : f ∣ (X ^ Fintype.card K - X : K[X]) := by
    rw [hf, hcard]
    exact dvd_pow_pow_sub_self_of_dvd hmn
  -- Hence `f` splits, with `deg f = p ^ m` simple roots.
  have hfsplit : f.Splits :=
    hbig.splits_of_dvd (FiniteField.X_pow_card_sub_X_ne_zero K h1lt) hdvd
  have hcardRoot : Fintype.card (f.rootSet K) = p ^ m := by
    have h := card_rootSet_eq_natDegree (F := K) (K := K) hsep (by simpa using hfsplit)
    rw [h, hf, FiniteField.X_pow_card_sub_X_natDegree_eq K hpm1]
  -- The carrier of `subfieldFix p m` is exactly the root set of `f`.
  have e : (subfieldFix (K := K) p m) ≃ (f.rootSet K) := by
    refine Equiv.subtypeEquivRight (fun x => ?_)
    rw [mem_subfieldFix, mem_rootSet, and_iff_right hf_ne, hf]
    simp [sub_eq_zero]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, hcardRoot]

/-! ## Worked instances -/

/-- `GF(2^2) = GF(4)` embeds into `GF(2^6) = GF(64)` since `2 ∣ 6`. -/
theorem gf4_embeds_gf64 :
    Nonempty (GaloisField 2 2 →ₐ[ZMod 2] GaloisField 2 6) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact nonempty_algHom_of_dvd 2 2 6 (by norm_num) (by norm_num) (by norm_num)

/-- `GF(2^2) = GF(4)` does **not** embed into `GF(2^3) = GF(8)`, since `2 ∤ 3`. -/
theorem gf4_not_embeds_gf8 :
    ¬ Nonempty (GaloisField 2 2 →ₐ[ZMod 2] GaloisField 2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [embeds_iff_dvd 2 2 3 (by norm_num) (by norm_num)]
  decide

end LittleWedderburnOQ02OQ01
