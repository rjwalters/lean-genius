import Mathlib

/-
Explicit Factorization over Finite Fields and ℚ
(bezout-identity-oq-02-oq-01-oq-01-oq-02)

Open question from BezoutIdentityOQ02OQ01OQ01 (unique factorization in
polynomial rings): make the abstract factorization *explicit* over the two
concrete settings the parent advertises — `ℚ` and `𝔽_p`.

Mathlib records the **root set** of `X^q - X` over a finite field
(`roots (X^q - X) = univ.val`, i.e. every field element is a simple root),
but it does not package the corresponding **product factorization**
`X^q - X = ∏_{a} (X - a)`. That explicit closed form is the centerpiece here.

**Main Results**:
1. `fermat_factorization` — over any finite field `K`,
     `X^|K| - X = ∏_{a : K} (X - a)`  (complete split into distinct linear factors).
2. `fermat_factorization_zmod` — the `𝔽_p` specialization `X^p - X = ∏_{a} (X - a)`.
3. `frobenius_factorization` — over `𝔽_p`, the binomial collapses to a perfect
     `p`-th power of a single linear factor: `X^p - a = (X - a)^p`.
4. `frobenius_one` — corollary `X^p - 1 = (X - 1)^p`.
5. Explicit `ℚ` vs `𝔽_p` contrast: `2` is a root of `X^5 - X` over `𝔽_5`
     (Fermat) but not over `ℚ` (where it evaluates to `30`).

**Why this is new (not a Mathlib re-export)**: Mathlib has the *multiset of
roots* of `X^q - X`; the equational product form here is assembled from it via
`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`. The Frobenius collapse is a
direct `sub_pow_char` + `ZMod.pow_card` computation. The two together exhibit
the qualitative split between separable (distinct-root) factorization over a
finite field and the inseparable single-root factorization of `X^p - a`.

**Status**: 0 sorries, 0 axioms.
-/

open Polynomial

namespace BezoutFactorizationFp

/-!
## Section I: Fermat factorization over a finite field

The polynomial `X^|K| - X` has every element of `K` as a simple root, so it
splits into the product of all the linear factors `X - a`.
-/

/-- **Fermat factorization**: over any finite field `K`, the polynomial
    `X^|K| - X` is the product of all linear factors `X - a`, `a ∈ K`.
    This is the explicit polynomial form of Fermat's little theorem
    (`a^|K| = a` for every `a`): each element is a root, with multiplicity one. -/
theorem fermat_factorization (K : Type*) [Field K] [Fintype K] :
    (X ^ (Fintype.card K) - X : K[X]) = ∏ a : K, (X - C a) := by
  classical
  -- `X^q - X` is monic (its top term `X^q` dominates `X` since `q = |K| ≥ 2`).
  have hmonic : (X ^ (Fintype.card K) - X : K[X]).Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast Fintype.one_lt_card
  -- It has degree `q` and exactly `q` roots, namely all of `K`.
  have hdeg : (X ^ (Fintype.card K) - X : K[X]).natDegree = Fintype.card K :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
  have hroots : roots (X ^ (Fintype.card K) - X : K[X]) = Finset.univ.val :=
    FiniteField.roots_X_pow_card_sub_X K
  have hcard : Multiset.card (roots (X ^ (Fintype.card K) - X : K[X]))
      = (X ^ (Fintype.card K) - X : K[X]).natDegree := by
    rw [hroots, hdeg]; rfl
  -- A monic polynomial with `deg`-many roots equals `∏ (X - root)`.
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at hprod
  rw [← hprod]
  rfl

/-- **Fermat factorization over `𝔽_p`**: for a prime `p`,
    `X^p - X = ∏_{a : 𝔽_p} (X - a)` in `(ZMod p)[X]`. -/
theorem fermat_factorization_zmod (p : ℕ) [Fact p.Prime] :
    (X ^ p - X : (ZMod p)[X]) = ∏ a : ZMod p, (X - C a) := by
  have h := fermat_factorization (ZMod p)
  rwa [ZMod.card p] at h

/-!
## Section II: Frobenius (Artin–Schreier) collapse over `𝔽_p`

In characteristic `p` the Frobenius endomorphism makes `X^p - a` an exact
`p`-th power. So `X^p - a` has the single root `a` with multiplicity `p` —
the opposite extreme from the squarefree split of `X^p - X`.
-/

/-- **Frobenius factorization**: over `𝔽_p`, the binomial `X^p - a` is a perfect
    `p`-th power of one linear factor: `X^p - a = (X - a)^p`.
    (`(X - a)^p = X^p - a^p` by the freshman's dream, and `a^p = a` by Fermat.) -/
theorem frobenius_factorization (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    (X ^ p - C a : (ZMod p)[X]) = (X - C a) ^ p := by
  rw [sub_pow_char, ← C_pow, ZMod.pow_card]

/-- Corollary `X^p - 1 = (X - 1)^p` over `𝔽_p`: the binomial whose roots are the
    `p`-th roots of unity collapses to a single root at `1` in characteristic `p`. -/
theorem frobenius_one (p : ℕ) [Fact p.Prime] :
    (X ^ p - 1 : (ZMod p)[X]) = (X - 1) ^ p := by
  have h := frobenius_factorization p 1
  simpa using h

/-!
## Section III: Explicit factorization over `ℚ` and the `ℚ` vs `𝔽_p` contrast

Over a field of characteristic `0`, Fermat factorization fails: `X^q - X` no
longer has every scalar as a root, so it does not split into linear factors.
The discriminating witness below is `2`.
-/

/-- Over `ℚ`, the small case `X^3 - X` happens to split completely into the
    distinct linear factors `X · (X - 1) · (X + 1)` (roots `0, 1, -1 ∈ ℚ`). -/
example : (X ^ 3 - X : ℚ[X]) = X * (X - 1) * (X + 1) := by ring

/-- Over `ℚ`, `2` is **not** a root of `X^5 - X`: it evaluates to `30`.
    Hence `X^5 - X` does not split into linear factors over `ℚ`. -/
theorem not_root_two_Q : (X ^ 5 - X : ℚ[X]).eval 2 = 30 := by
  simp only [eval_sub, eval_pow, eval_X]
  norm_num

/-- Over `𝔽_5`, by contrast, `2` **is** a root of `X^5 - X` (Fermat: `2^5 = 2`).
    Every element of `𝔽_5` is a root — that is exactly `fermat_factorization_zmod`. -/
theorem root_two_F5 : (X ^ 5 - X : (ZMod 5)[X]).IsRoot 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X]
  rw [ZMod.pow_card]
  ring

end BezoutFactorizationFp
