import Proofs.CombinationsFormulaOQ0302
import Mathlib

/-
# Combinations Formula OQ-01-OQ-03: q-binomial analogues of the extended identities

The parent entry `combinations-formula-oq-01` collected several classical
extensions of the binomial coefficients (Vandermonde's convolution, the hockey
stick identity, the *subset-of-a-subset* product rule, and the alternating row
sum). Its q-analogue framework lives in `combinations-formula-oq-03`
(namespace `QBinomialCoefficients`), which already lifts Vandermonde and the
hockey stick identity to Gaussian binomial coefficients `[n choose k]_q`.

This file closes the two remaining gaps in that program:

* **Subset-of-a-subset (trinomial revision):**
  `[n,k]_q · [k,j]_q = [n,j]_q · [n-j, k-j]_q` for `j ≤ k ≤ n`.
  The classical identity `C(n,k)·C(k,j) = C(n,j)·C(n-j,k-j)` is proved by
  cancelling factorials, which is illegitimate over a general ring where the
  q-factorials may vanish (e.g. `q` a root of unity). We give two forms:
  - `qBinom_subset_of_subset_mul` — the honest *multiplied* form, valid over
    **any** commutative ring, obtained directly from the q-factorial product
    formula with no division.
  - `qBinom_subset_of_subset` — the clean *cancelled* form, also valid over any
    commutative ring, proved by the **universal polynomial identity** method:
    the identity is established over the integral domain `ℤ[X]` (where the
    q-factorials are genuinely nonzero, so cancellation is legal) and then
    transported to an arbitrary `(R, q)` by the ring homomorphism `X ↦ q`.

* **Alternating q-row sum:** `∑_k [n,k]_q · q^{C(k,2)} · (-1)^k = 0` for `n ≥ 1`,
  the q-analogue of `∑_k (-1)^k C(n,k) = 0`. This is the value at `x = -1` of the
  finite q-binomial theorem `∏ (1 + q^i x) = ∑ [n,k]_q q^{C(k,2)} x^k`
  (`qBinom_gauss` from OQ-03-02): the `i = 0` factor becomes `1 - 1 = 0`.

To transport the cancelled identity we develop the (reusable) fact that the
q-number, q-factorial and q-binomial all **commute with ring homomorphisms** —
a small but general piece of infrastructure absent from the earlier files.

Each q-identity is accompanied by its `q = 1` specialization recovering the
classical statement over `ℤ`.
-/

open Nat Finset
open QBinomialCoefficients

namespace CombinationsFormulaOQ01OQ03

-- ============================================================
-- Part I: q-quantities commute with ring homomorphisms
-- ============================================================

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Ring homomorphisms commute with the q-number: `f [n]_q = [n]_{f q}`. -/
theorem qNumber_map (f : R →+* S) (q : R) :
    ∀ n : ℕ, f (qNumber q n) = qNumber (f q) n
  | 0 => by simp [qNumber]
  | n + 1 => by
    rw [qNumber_succ, map_add, map_one, map_mul, qNumber_map f q n, qNumber_succ]

/-- Ring homomorphisms commute with the q-factorial: `f [n]_q! = [n]_{f q}!`. -/
theorem qFactorial_map (f : R →+* S) (q : R) :
    ∀ n : ℕ, f (qFactorial q n) = qFactorial (f q) n
  | 0 => by simp [qFactorial]
  | n + 1 => by
    rw [qFactorial_succ, map_mul, qNumber_map f q (n + 1), qFactorial_map f q n,
        qFactorial_succ]

/-- Ring homomorphisms commute with the q-binomial: `f [n,k]_q = [n,k]_{f q}`.
    This is the transport lemma powering the universal polynomial identity
    method below: an identity in `[n,k]_q` proved over one ring pushes forward
    along any ring hom. -/
theorem qBinom_map (f : R →+* S) (q : R) :
    ∀ (n k : ℕ), f (qBinom q n k) = qBinom (f q) n k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    rw [qBinom_pascal, map_add, map_mul, map_pow, qBinom_map f q n k,
        qBinom_map f q n (k + 1), qBinom_pascal]

-- ============================================================
-- Part II: Subset-of-a-subset (trinomial revision), multiplied form
-- ============================================================

variable {T : Type*} [CommRing T]

/-- **Subset-of-a-subset, multiplied form** (valid over any commutative ring).

    For `j ≤ k ≤ n`,
    `[n,k]_q · [k,j]_q · M = [n,j]_q · [n-j,k-j]_q · M`,
    where `M = [j]_q! · [k-j]_q! · [n-k]_q!`. Both sides equal `[n]_q!`.

    This is the honest statement over an arbitrary ring: no cancellation is
    performed, so it holds even when the q-factorials `M` vanish. -/
theorem qBinom_subset_of_subset_mul (q : T) {n k j : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    qBinom q n k * qBinom q k j
        * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k))
      = qBinom q n j * qBinom q (n - j) (k - j)
        * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k)) := by
  have hjn : j ≤ n := le_trans hjk hkn
  have hkjnj : k - j ≤ n - j := by omega
  have hsub : (n - j) - (k - j) = n - k := by omega
  -- Left side collapses to [n]_q! via the product formula applied twice.
  have hLHS :
      qBinom q n k * qBinom q k j
          * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k))
        = qFactorial q n := by
    calc
      qBinom q n k * qBinom q k j
          * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k))
          = qBinom q n k
              * (qBinom q k j * qFactorial q j * qFactorial q (k - j))
              * qFactorial q (n - k) := by ring
      _ = qBinom q n k * qFactorial q k * qFactorial q (n - k) := by
              rw [qBinom_product q k j hjk]
      _ = qFactorial q n := qBinom_product q n k hkn
  -- Right side also collapses to [n]_q!.
  have hRHS :
      qBinom q n j * qBinom q (n - j) (k - j)
          * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k))
        = qFactorial q n := by
    calc
      qBinom q n j * qBinom q (n - j) (k - j)
          * (qFactorial q j * qFactorial q (k - j) * qFactorial q (n - k))
          = qBinom q n j * qFactorial q j
              * (qBinom q (n - j) (k - j) * qFactorial q (k - j)
                 * qFactorial q ((n - j) - (k - j))) := by rw [hsub]; ring
      _ = qBinom q n j * qFactorial q j * qFactorial q (n - j) := by
              rw [qBinom_product q (n - j) (k - j) hkjnj]
      _ = qFactorial q n := qBinom_product q n j hjn
  rw [hLHS, hRHS]

-- ============================================================
-- Part III: Subset-of-a-subset, cancelled form (universal identity)
-- ============================================================

/-- **Subset-of-a-subset (trinomial revision)** for Gaussian binomials.

    For `j ≤ k ≤ n` and any `q` in any commutative ring,
    `[n,k]_q · [k,j]_q = [n,j]_q · [n-j, k-j]_q`.

    Since the q-factorials can vanish, this cancelled form is **not** deducible
    from `qBinom_subset_of_subset_mul` by dividing. Instead it is proved once and
    for all over the integral domain `ℤ[X]` — where the q-factorials
    `[j]_X!·[k-j]_X!·[n-k]_X!` are nonzero, so cancellation is valid — and then
    transported to `(T, q)` along the evaluation homomorphism `X ↦ q` using
    `qBinom_map`. -/
theorem qBinom_subset_of_subset (q : T) {n k j : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    qBinom q n k * qBinom q k j = qBinom q n j * qBinom q (n - j) (k - j) := by
  -- Work over the polynomial ring ℤ[X], an integral domain.
  set X : Polynomial ℤ := Polynomial.X with hXdef
  have hmul := qBinom_subset_of_subset_mul X hjk hkn
  set F : Polynomial ℤ :=
      qFactorial X j * qFactorial X (k - j) * qFactorial X (n - k) with hF
  -- F ≠ 0: evaluating at 1 sends it to the (positive) product of factorials.
  have hev : (Polynomial.evalRingHom (1 : ℤ)) X = 1 := by simp [hXdef]
  have hFeval : (Polynomial.evalRingHom (1 : ℤ)) F
      = ((j.factorial : ℤ) * (k - j).factorial * (n - k).factorial) := by
    rw [hF]
    simp only [map_mul, qFactorial_map, hev, qFactorial_at_one]
  have hFne : F ≠ 0 := by
    have h1 : (0 : ℤ) < (j.factorial : ℤ) := by exact_mod_cast Nat.factorial_pos j
    have h2 : (0 : ℤ) < ((k - j).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos _
    have h3 : (0 : ℤ) < ((n - k).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos _
    intro h0
    have hz : ((j.factorial : ℤ) * (k - j).factorial * (n - k).factorial) = 0 := by
      rw [← hFeval, h0, map_zero]
    nlinarith [mul_pos (mul_pos h1 h2) h3]
  -- Cancel F to get the identity over ℤ[X].
  have hcancel :
      qBinom X n k * qBinom X k j = qBinom X n j * qBinom X (n - j) (k - j) :=
    mul_right_cancel₀ hFne hmul
  -- Transport along the evaluation map X ↦ q.
  have hφX : (Polynomial.eval₂RingHom (Int.castRingHom T) q) X = q := by simp [hXdef]
  have := congrArg (Polynomial.eval₂RingHom (Int.castRingHom T) q) hcancel
  simpa only [map_mul, qBinom_map, hφX] using this

/-- **Classical subset-of-a-subset at `q = 1`**:
    `C(n,k)·C(k,j) = C(n,j)·C(n-j,k-j)` for `j ≤ k ≤ n`, recovered from the
    q-identity by specializing `q = 1` over `ℚ`. -/
theorem choose_subset_of_subset {n k j : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
  have h := qBinom_subset_of_subset (1 : ℚ) hjk hkn
  simp only [qBinom_at_one] at h
  exact_mod_cast h

-- ============================================================
-- Part IV: Alternating q-row sum
-- ============================================================

/-- **Alternating q-row sum**: for `n ≥ 1` and any `q`,
    `∑_{k=0}^{n} [n,k]_q · q^{C(k,2)} · (-1)^k = 0`.

    This is the q-analogue of the classical alternating row sum
    `∑ (-1)^k C(n,k) = 0`. It is the value at `x = -1` of the finite q-binomial
    theorem `∏_{i<n} (1 + q^i x) = ∑_k [n,k]_q q^{C(k,2)} x^k`: the factor at
    `i = 0` becomes `1 + q^0·(-1) = 0`, so the whole product vanishes. -/
theorem qBinom_alternating_sum (q : T) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        qBinom q n k * q ^ (Nat.choose k 2) * (-1 : T) ^ k = 0 := by
  rw [← qBinom_gauss q (-1) n]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by ring)

/-- **Classical alternating row sum at `q = 1`**: `∑_{k=0}^{n} (-1)^k C(n,k) = 0`
    for `n ≥ 1`, recovered from the q-identity by specializing `q = 1`. -/
theorem choose_alternating_sum {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (-1) ^ k = 0 := by
  have h := qBinom_alternating_sum (1 : ℤ) hn
  simpa only [qBinom_at_one, one_pow, mul_one] using h

end CombinationsFormulaOQ01OQ03
