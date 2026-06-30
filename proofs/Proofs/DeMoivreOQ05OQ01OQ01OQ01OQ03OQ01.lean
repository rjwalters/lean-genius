/-
The normalised DFT has order four: U⁴ = 1, with U² the index reflection

Source: Open question from the de-moivre gallery family
        (de-moivre-oq-05-oq-01-oq-01-oq-01, fourth open question — the order of
         the unitary discrete Fourier transform)
Status: VERIFIED (0 axioms, 0 sorries)

The grandparent entry (de-moivre-oq-05-oq-01-oq-01-oq-01) packaged the normalised
discrete Fourier transform `U(j,k) = exp(2πi·jk/n)/√n` as a *matrix* and proved it
is unitary, `U ∈ Matrix.unitaryGroup (Fin n) ℂ`; its third open question upgraded
this to a genuine isometric isomorphism `dftLIE` of `ℂⁿ`.  A unitary operator on a
finite-dimensional Hilbert space has a well-defined order, and the discrete Fourier
transform is famous for a remarkably small one:

      U² = R,    U⁴ = 1,

where `R` is the **index-reflection** permutation `R(j,l) = [j + l ≡ 0 (mod n)]`,
i.e. `R` sends a sequence to its reversal `x(k) ↦ x(-k mod n)`.  This is the
discrete shadow of the classical fact that the (suitably normalised) continuous
Fourier transform satisfies `𝓕⁴ = id`, with `𝓕²` the parity operator `f(x) ↦ f(-x)`
— the structural reason the Hermite functions are Fourier eigenfunctions and the
spectrum of `𝓕` is contained in the fourth roots of unity `{1, -1, i, -i}`.

This file proves the discrete statement from scratch over the grandparent's kernel
`char n j k = exp(2πi·jk/n)`:

* `char_mul`  — the kernel is multiplicative in its frequency index:
                `char n j k · char n k l = char n (j+l) k`;
* `char_mod`  — the kernel is `n`-periodic in its first index (because
                `(exp(2πi·k/n))ⁿ = 1`): `char n m k = char n (m % n) k`;
* `sum_char`  — the geometric/orthogonality sum `∑_{k<n} char n m k = n·[n ∣ m]`;
* `dftMatrix_sq` — `U² = R`, the reflection matrix, via the above;
* `reflMatrix_mul_self` — `R² = 1` (`R` is an involutive permutation: reversal
                twice is the identity), proved through the additive group `Fin n`;
* `dftMatrix_pow_four` — `U⁴ = 1`, the order-four law;
* `reflMatrix_ne_one` / `dftMatrix_sq_ne_one` — for `n ≥ 3` the reflection is
                nontrivial, so `U² ≠ 1` and the order of `U` is *exactly* four.

Only the grandparent's `char`, `char_symm`, `char_inner` and `dftMatrix` are used;
no Mathlib Fourier or representation-theory machinery is invoked.
-/

import Mathlib
import Proofs.DeMoivreOQ05OQ01OQ01OQ01

open Matrix Finset DeMoivreOQ05OQ01OQ01 DeMoivreOQ05OQ01OQ01OQ01

namespace DeMoivreOQ05OQ01OQ01OQ01OQ03OQ01

/-- **The DFT kernel is multiplicative in the frequency index.**
`char n j k · char n k l = char n (j+l) k`, because the exponents add:
`exp(2πi·jk/n)·exp(2πi·kl/n) = exp(2πi·(j+l)k/n)`.  This is the algebraic engine
behind `U² = R`: the inner sum of `U²` telescopes the two kernels into one. -/
theorem char_mul (n j k l : ℕ) :
    char n j k * char n k l = char n (j + l) k := by
  simp only [char, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The DFT kernel is `n`-periodic in its first index.**
`char n m k = char n (m % n) k`.  Writing `char n m k = ζ^m` with
`ζ = exp(2πi·k/n)`, periodicity is the statement `ζⁿ = exp(2πi·k) = 1`, so only
`m mod n` matters.  This is what reduces the geometric sum below to a residue. -/
theorem char_mod {n : ℕ} (hn : 0 < n) (m k : ℕ) :
    char n m k = char n (m % n) k := by
  set z : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (n : ℂ) with hzdef
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz : ∀ a : ℕ, char n a k = Complex.exp z ^ a := by
    intro a
    simp only [char, ← Complex.exp_nat_mul]
    congr 1
    rw [hzdef]; ring
  have hzn : Complex.exp z ^ n = 1 := by
    rw [← Complex.exp_nat_mul]
    have hexp : ((n : ℂ) * z) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hzdef]; field_simp
    rw [hexp, Complex.exp_nat_mul_two_pi_mul_I]
  rw [hz m, hz (m % n)]
  conv_lhs => rw [show m = n * (m / n) + m % n from (Nat.div_add_mod m n).symm]
  rw [pow_add, pow_mul, hzn, one_pow, one_mul]

/-- **The discrete orthogonality / geometric sum.**
`∑_{k<n} char n m k = n` if `n ∣ m` and `0` otherwise.  For `m % n = 0` the kernel
is identically `1`; otherwise the `n`-th roots of unity sum to zero.  Obtained by
reducing `m` modulo `n` (`char_mod`) and specialising the grandparent's character
orthonormality `char_inner` at the trivial character `b = 0`. -/
theorem sum_char {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ∑ k ∈ Finset.range n, char n m k = if m % n = 0 then (n : ℂ) else 0 := by
  have hconj : ∀ k, (starRingEnd ℂ) (char n 0 k) = 1 := by
    intro k; simp [char]
  calc ∑ k ∈ Finset.range n, char n m k
      = ∑ k ∈ Finset.range n, char n (m % n) k * (starRingEnd ℂ) (char n 0 k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hconj, mul_one, char_mod hn m k]
    _ = if (m % n) = 0 then (n : ℂ) else 0 :=
        char_inner hn (Nat.mod_lt m hn) hn

/-- The **index-reflection matrix** `R(j,l) = [j + l ≡ 0 (mod n)]`.  It is the
permutation matrix of the reversal `k ↦ -k (mod n)` on `Fin n`; `U² = R`. -/
def reflMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j l => if ((j : ℕ) + (l : ℕ)) % n = 0 then 1 else 0

/-- **The square of the normalised DFT is the index reflection: `U² = R`.**
Entry `(j,l)` of `U²` is `(1/n)∑_{k<n} char n j k · char n k l`; the kernels combine
to `char n (j+l) k` (`char_mul`) and the geometric sum (`sum_char`) collapses to
`n·[j+l ≡ 0]`, leaving `[j+l ≡ 0 (mod n)] = R(j,l)`.  Concretely the DFT applied
twice reverses a sequence. -/
theorem dftMatrix_sq {n : ℕ} (hn : 0 < n) :
    dftMatrix n * dftMatrix n = reflMatrix n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin n,
      dftMatrix n j k * dftMatrix n k l = char n ((j : ℕ) + (l : ℕ)) (k : ℕ) / (n : ℂ) := by
    intro k
    simp only [dftMatrix]
    rw [div_mul_div_comm, char_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hn'.le, Complex.ofReal_natCast]
  simp only [hterm]
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun k => char n ((j : ℕ) + (l : ℕ)) k) n,
    sum_char hn]
  show (if ((j : ℕ) + (l : ℕ)) % n = 0 then (n : ℂ) else 0) / (n : ℂ) = reflMatrix n j l
  unfold reflMatrix
  by_cases h : ((j : ℕ) + (l : ℕ)) % n = 0
  · rw [if_pos h, if_pos h, div_self hnz]
  · rw [if_neg h, if_neg h, zero_div]

/-- **The reflection is an involution: `R² = 1`.**
Reversing a sequence twice is the identity.  Working in the additive group
`Fin n`, the condition `j + m ≡ 0` is exactly `m = -j`, so for each `j` there is a
unique nonzero contribution `m = -j`; it survives iff `(-j) + l ≡ 0`, i.e. `l = j`. -/
theorem reflMatrix_mul_self {n : ℕ} (hn : 0 < n) :
    reflMatrix n * reflMatrix n = 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcond : ∀ a b : Fin n, (((a : ℕ) + (b : ℕ)) % n = 0) ↔ b = -a := by
    intro a b
    rw [← Fin.val_add, Fin.val_eq_zero_iff]
    constructor
    · intro h; exact (neg_eq_of_add_eq_zero_right h).symm
    · rintro rfl; exact add_neg_cancel a
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [reflMatrix]
  rw [Finset.sum_eq_single (-j)]
  · rw [if_pos ((hcond j (-j)).mpr rfl), one_mul]
    by_cases hjl : j = l
    · subst hjl
      rw [if_pos ((hcond (-j) j).mpr (neg_neg j).symm), if_pos rfl]
    · rw [if_neg (by rw [hcond, neg_neg]; exact fun h => hjl h.symm), if_neg hjl]
  · intro m _ hm
    rw [if_neg (by rw [hcond]; exact hm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ (-j)) h

/-- **The order-four law of the discrete Fourier transform: `U⁴ = 1`.**
Since `U² = R` and `R² = 1`, the fourth power of the normalised DFT is the
identity.  Thus `U` is a unitary of order dividing four — the discrete analogue of
`𝓕⁴ = id` for the continuous Fourier transform, and the reason the DFT's spectrum
lies in the fourth roots of unity. -/
theorem dftMatrix_pow_four {n : ℕ} (hn : 0 < n) :
    dftMatrix n ^ 4 = 1 := by
  have h2 : dftMatrix n ^ 2 = reflMatrix n := by
    rw [pow_two]; exact dftMatrix_sq hn
  calc dftMatrix n ^ 4 = (dftMatrix n ^ 2) ^ 2 := by rw [← pow_mul]
    _ = reflMatrix n * reflMatrix n := by rw [h2, pow_two]
    _ = 1 := reflMatrix_mul_self hn

/-- **The reflection is nontrivial once `n ≥ 3`.**
For `n ≥ 3` the index `1` is its own reflection only if `2 ≡ 0 (mod n)`, which
fails, so `R(1,1) = 0 ≠ 1`.  (For `n = 1, 2` reversal *is* the identity, so this
sharpness genuinely needs `n ≥ 3`.) -/
theorem reflMatrix_ne_one {n : ℕ} (hn : 3 ≤ n) : reflMatrix n ≠ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have h2 : (2 : ℕ) % n = 2 := Nat.mod_eq_of_lt (by omega)
  have key : reflMatrix n ⟨1, by omega⟩ ⟨1, by omega⟩
      = (1 : Matrix (Fin n) (Fin n) ℂ) ⟨1, by omega⟩ ⟨1, by omega⟩ := by rw [h]
  simp only [reflMatrix, Matrix.one_apply_eq] at key
  rw [show (1 + 1) % n = 2 % n by norm_num, h2] at key
  simp only [OfNat.ofNat_ne_zero, if_false] at key
  exact zero_ne_one key

/-- **The order of the DFT is exactly four for `n ≥ 3`: `U² ≠ 1`.**
Combined with `dftMatrix_pow_four` (`U⁴ = 1`) and `U ≠ 1`, this pins the order of
the normalised discrete Fourier transform at precisely `4` whenever `n ≥ 3`. -/
theorem dftMatrix_sq_ne_one {n : ℕ} (hn : 3 ≤ n) :
    dftMatrix n ^ 2 ≠ 1 := by
  rw [pow_two, dftMatrix_sq (by omega)]
  exact reflMatrix_ne_one hn

end DeMoivreOQ05OQ01OQ01OQ01OQ03OQ01
