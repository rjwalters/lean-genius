import Mathlib

/-
# Stirling numbers of the first and second kind are inverse triangular matrices

The signed Stirling numbers of the first kind `s(n,k) = (−1)ⁿ⁻ᵏ c(n,k)` (where
`c(n,k) = Nat.stirlingFirst n k` is the unsigned count) are the connection
coefficients writing the **falling factorial** in the monomial basis,

  `x(x−1)⋯(x−n+1) = descPochhammer ℤ n = ∑ₖ s(n,k) xᵏ`,            (♭)

while the Stirling numbers of the second kind `S(n,k) = Nat.stirlingSecond n k`
run the substitution the other way, writing each **monomial** in the falling-
factorial basis,

  `xⁿ = ∑ₖ S(n,k) · x(x−1)⋯(x−k+1)`.                              (♯)

Composing (♭) and (♯) shows the two triangular arrays are **mutually inverse**:

  `∑ₖ S(n,k) · s(k,m) = δₙₘ`            (Stirling orthogonality)   (★)

— the fundamental relation that makes the first- and second-kind Stirling
transforms invert one another (Graham–Knuth–Patashnik, *Concrete Mathematics*
§6.1, eq. 6.32).  The sibling entry `stirling-first-kind-oq-01-oq-02` recorded the
falling-factorial identity (♭) and its alternating row sum; the gallery's
`combinations-formula` chain recorded the *numeric* second-kind bridge
`mᵖ = ∑ᵣ S(p,r)·(m)ᵣ`.  Neither places the two kinds in the same file, and the
**orthogonality** (★) — the statement that they are inverse matrices — is new to
the gallery: no existing entry mentions both `Nat.stirlingFirst` and
`Nat.stirlingSecond`.

## What is proved

1. `stirlingFirst_signed_eq_descPochhammer_coeff` — the per-coefficient form of
   (♭): `(descPochhammer ℤ n).coeff k = (−1)^{n+k} c(n,k)` (subtraction-free
   exponent, equal to `(−1)^{n−k}` mod `2`).  Proved by induction on `n` from the
   recurrence `descPochhammer (n+1) = descPochhammer n · (X − n)`.
2. `pow_X_eq_sum_stirlingSecond_descPochhammer` — the **polynomial** second-kind
   expansion (♯) over `ℤ[X]`: `Xⁿ = ∑ₖ S(n,k) · descPochhammer ℤ k`.  Proved by
   induction using `X · (x)ₖ = (x)_{k+1} + k·(x)ₖ` and the second-kind Pascal
   recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`.  (Mathlib and the gallery
   carry only the *evaluated* numeric form `mⁿ = ∑ₖ S(n,k)·(m)ₖ`.)
3. `stirlingSecond_mul_signed_stirlingFirst_orthogonal` — the orthogonality (★),
   obtained by extracting the `Xᵐ`-coefficient of (♯) and substituting the
   coefficient form (♭): the left side reads off `∑ₖ S(n,k)·s(k,m)`, the right
   side `(Xⁿ).coeff m = δₙₘ`.

Everything is over `ℤ` / `ℤ[X]`.  No axioms, no `sorry`, no `native_decide`.
-/

open Nat Polynomial

namespace StirlingFirstKindOQ02OQ01

/-- **Per-coefficient form of the signed falling-factorial identity.** The signed
Stirling number `(−1)^{n−k} c(n,k)` is the coefficient of `Xᵏ` in the falling
factorial `X(X−1)⋯(X−n+1) = descPochhammer ℤ n`.  Stated with the subtraction-free
exponent `n + k` (equal to `n − k` modulo `2`).

Proof by induction on `n` using
`descPochhammer ℤ (n+1) = descPochhammer ℤ n · (X − n)` (`descPochhammer_succ_right`):
extracting the `Xᵏ`-coefficient of the product — `coeff_mul_X` for the `X` factor
(an index shift) and `coeff_mul_C` for the constant `−n` — reproduces the Pascal
recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)` with the alternating sign carried
through; the `k = 0` case yields `c(n+1,0) = 0`. -/
theorem stirlingFirst_signed_eq_descPochhammer_coeff (n k : ℕ) :
    (descPochhammer ℤ n).coeff k = (-1 : ℤ) ^ (n + k) * (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    rw [descPochhammer_zero, Polynomial.coeff_one]
    cases k with
    | zero => simp [Nat.stirlingFirst_zero]
    | succ k => simp [Nat.stirlingFirst_zero_succ]
  | succ n ih =>
    rw [descPochhammer_succ_right, ← Polynomial.C_eq_natCast, mul_sub,
      Polynomial.coeff_sub, Polynomial.coeff_mul_C]
    cases k with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, zero_sub, ih, Nat.stirlingFirst_succ_zero]
      have hz : (Nat.stirlingFirst n 0 : ℤ) * (n : ℤ) = 0 := by
        cases n with
        | zero => simp
        | succ m => simp [Nat.stirlingFirst_succ_zero]
      rw [mul_assoc, hz]
      simp
    | succ j =>
      rw [Polynomial.coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

/-- **Polynomial second-kind expansion (♯).** Over `ℤ[X]`,

  `Xⁿ = ∑_{k=0}^{n} S(n,k) · descPochhammer ℤ k`,

i.e. each monomial is the corresponding combination of falling factorials with
Stirling-second-kind coefficients.  Mathlib and the gallery record only the
*evaluated* numeric form `mⁿ = ∑ₖ S(n,k)·(m)ₖ`; this is the polynomial identity.

Proof by induction on `n`.  Multiply the inductive hypothesis by `X` and use
`X · (x)ₖ = (x)_{k+1} + k·(x)ₖ` (from `descPochhammer_succ_right`).  Re-indexing
the two resulting sums and applying the second-kind recurrence
`S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)` (with the edge values `S(n+1,0) = 0` and
`S(n,n+1) = 0`) reassembles `∑ₖ S(n+1,k)·(x)ₖ`. -/
theorem pow_X_eq_sum_stirlingSecond_descPochhammer (n : ℕ) :
    (X : ℤ[X]) ^ n
      = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℤ[X]) * descPochhammer ℤ k := by
  induction n with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    -- Each term `S(p,k)·(x)ₖ·X` splits via `(x)ₖ·X = (x)_{k+1} + k·(x)ₖ`.
    have hterm : ∀ k ∈ Finset.range (p + 1),
        (Nat.stirlingSecond p k : ℤ[X]) * descPochhammer ℤ k * X
          = (Nat.stirlingSecond p k : ℤ[X]) * descPochhammer ℤ (k + 1)
            + (k : ℤ[X]) * ((Nat.stirlingSecond p k : ℤ[X]) * descPochhammer ℤ k) := by
      intro k _
      rw [descPochhammer_succ_right]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    -- The goal is now `A + B = ∑_{k<p+2} S(p+1,k)·(x)ₖ`, with
    --   A = ∑_{k<p+1} S(p,k)·(x)_{k+1},   B = ∑_{k<p+1} k·(S(p,k)·(x)ₖ).
    -- Expand the right-hand side and match.
    rw [Finset.sum_range_succ'
      (fun k => (Nat.stirlingSecond (p + 1) k : ℤ[X]) * descPochhammer ℤ k) (p + 1)]
    rw [stirlingSecond_succ_zero]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    -- RHS: `∑_{k<p+1} S(p+1,k+1)·(x)_{k+1}`. Split via the second-kind recurrence.
    have hsplit : ∀ k ∈ Finset.range (p + 1),
        (Nat.stirlingSecond (p + 1) (k + 1) : ℤ[X]) * descPochhammer ℤ (k + 1)
          = (Nat.stirlingSecond p k : ℤ[X]) * descPochhammer ℤ (k + 1)
            + ((k : ℤ[X]) + 1)
                * ((Nat.stirlingSecond p (k + 1) : ℤ[X]) * descPochhammer ℤ (k + 1)) := by
      intro k _
      rw [stirlingSecond_succ_succ]
      push_cast
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- Goal: `A + B = A + C`, where C = ∑_{k<p+1} (k+1)·(S(p,k+1)·(x)_{k+1}). Show B = C.
    congr 1
    -- B = ∑_{k<p+1} k·(S(p,k)·(x)ₖ); its k=0 term vanishes, then re-index.
    rw [Finset.sum_range_succ'
      (fun k => (k : ℤ[X]) * ((Nat.stirlingSecond p k : ℤ[X]) * descPochhammer ℤ k)) p]
    -- C = ∑_{k<p+1} (k+1)·(S(p,k+1)·(x)_{k+1}); its top term has S(p,p+1)=0.
    rw [Finset.sum_range_succ
      (fun k => ((k : ℤ[X]) + 1)
        * ((Nat.stirlingSecond p (k + 1) : ℤ[X]) * descPochhammer ℤ (k + 1))) p]
    rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self p)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring

/-- **Stirling orthogonality (★): first and second kind are inverse matrices.**
For all `n m`,

  `∑_{k=0}^{n} S(n,k) · (−1)^{k+m} c(k,m) = [m = n]`,

i.e. `∑ₖ S(n,k)·s(k,m) = δₙₘ` with signed first-kind `s(k,m) = (−1)^{k−m} c(k,m)`.

Proof: take the `Xᵐ`-coefficient of the polynomial second-kind expansion (♯)
`Xⁿ = ∑ₖ S(n,k)·descPochhammer ℤ k`.  The left side is `(Xⁿ).coeff m = [m = n]`
(`coeff_X_pow`); on the right, `coeff` is `ℤ`-linear and
`(descPochhammer ℤ k).coeff m = (−1)^{k+m} c(k,m)`
(`stirlingFirst_signed_eq_descPochhammer_coeff`), giving the stated sum. -/
theorem stirlingSecond_mul_signed_stirlingFirst_orthogonal (n m : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : ℤ) * ((-1 : ℤ) ^ (k + m) * (Nat.stirlingFirst k m : ℤ))
      = if m = n then 1 else 0 := by
  have hco := congrArg (fun q : ℤ[X] => q.coeff m) (pow_X_eq_sum_stirlingSecond_descPochhammer n)
  simp only [Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff] at hco
  rw [hco]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul,
    stirlingFirst_signed_eq_descPochhammer_coeff]

/-- **Numeric sanity check** (`n = 3`, `m = 1`).  With second-kind row
`S(3,·) = 0, 1, 3, 1` and signed first-kind column
`s(·,1) = (−1)^{k+1} c(k,1) = 0, 1, −1, 2`, orthogonality gives
`1·1 + 3·(−1) + 1·2 = 0 = [1 = 3]`, matching
`stirlingSecond_mul_signed_stirlingFirst_orthogonal 3 1`. -/
theorem stirlingSecond_signed_stirlingFirst_three_one :
    ∑ k ∈ Finset.range 4,
        (Nat.stirlingSecond 3 k : ℤ) * ((-1 : ℤ) ^ (k + 1) * (Nat.stirlingFirst k 1 : ℤ))
      = 0 := by
  simp [Finset.sum_range_succ, Nat.stirlingSecond, Nat.stirlingFirst]

/-- **Diagonal case.** Specialising orthogonality to `m = n` gives `∑ₖ S(n,k)·s(k,n) = 1`;
since `S(n,k)·c(k,n) = 0` unless `k = n` (both vanish off the diagonal), this is the
self-product `S(n,n)·s(n,n) = 1·1`. -/
theorem stirlingSecond_mul_signed_stirlingFirst_diag (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : ℤ) * ((-1 : ℤ) ^ (k + n) * (Nat.stirlingFirst k n : ℤ)) = 1 := by
  rw [stirlingSecond_mul_signed_stirlingFirst_orthogonal, if_pos rfl]

end StirlingFirstKindOQ02OQ01
