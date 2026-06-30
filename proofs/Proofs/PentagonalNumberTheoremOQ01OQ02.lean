/-
# Euler's partition recurrence from the generating-function reciprocal
  (`pentagonal-number-theorem-oq-01-oq-02`)

This entry cashes in the parent's pentagonal development
(`Proofs/PentagonalNumberTheoremOQ01.lean`) into the **reciprocal identity**

  `P(X) · ∏_{m≥1}(1 - Xᵐ) = 1`,        where `P(X) = ∑_{n≥0} p(n) Xⁿ`

and reads off the resulting **convolution recurrence** for the partition
function `p(n) = #(Nat.Partition n)`.

The headline `partition_genFun_mul_euler_eq_one` is exactly the statement that
the partition generating function `∑ p(n) Xⁿ` is the multiplicative inverse of
Euler's product `∏(1-Xᵐ)` — i.e. `∑ p(n) Xⁿ = ∏ 1/(1-Xᵐ)`.  This product form
is a stated `TODO` in Mathlib's `Combinatorics.Enumerative.Partition.GenFun`
(Weiyi Wang, 2025); we prove the equivalent multiplicative reciprocal here.

  * `factor_telescope`  — the per-factor geometric telescoping
    `(∑_j X^{m·j}) · (1 - Xᵐ) = 1` in `ℤ⟦X⟧` (Mathlib's
    `tsum_pow_mul_one_sub_of_constantCoeff_eq_zero`);
  * `partition_genFun_mul_euler_eq_one` — multiply the two convergent products
    factor-by-factor (`Multipliable.tprod_mul`), each combined factor collapsing
    to `1`, so the whole product is `1`;
  * `euler_convolution` — extract the `n`-th coefficient of `P·E = 1`
    (`PowerSeries.coeff_mul`): a Cauchy convolution equal to `[n = 0]`;
  * `partition_recurrence` — solve the convolution for `p(n)`, the explicit
    recurrence `p(n) = -∑_{k<n} p(k)·c_{n-k}`.

Here the Euler coefficients `c_b = [Xᵇ]∏(1-Xᵐ) = ∑_{q∈distincts b}(-1)^{#parts}`
are supplied by the parent's verified `coeff_tprod_pent`.

## Relation to the famous pentagonal form

Euler's celebrated form indexes the recurrence by the *generalized pentagonal
numbers* `g_k = k(3k-1)/2`:
`p(n) = ∑_{k≥1}(-1)^{k-1}(p(n-g_k)+p(n-g_{-k}))`.  Obtaining that form from the
convolution proved here requires the identity
`∑_{q∈distincts b}(-1)^{#parts} = pentSeriesCoeff b` — the **pentagonal number
theorem** (Franklin's sign-reversing involution), which is precisely the parent
entry's stated OPEN CORE and is still absent from Mathlib.  So this entry proves
the generating-function half (the `A·B = 1 ⟹` recurrence extraction)
unconditionally; the pentagonal indexing remains gated on Franklin's involution.

Results: 0 axioms, 0 sorries.  Original (the reciprocal `P·E = 1` is a Mathlib
`TODO`; the convolution recurrence is not in the gallery).
-/
import Mathlib
import Proofs.PentagonalNumberTheoremOQ01

namespace PentagonalNumberTheoremOQ01OQ02

open PowerSeries Finset
open PowerSeries.WithPiTopology
open scoped PowerSeries.WithPiTopology

/-- The partition generating function `P(X) = ∑_{n≥0} p(n) Xⁿ` over `ℤ`,
realised as Mathlib's `genFun` with the trivial character `f ≡ 1`. -/
noncomputable def P : ℤ⟦X⟧ := Nat.Partition.genFun (fun _ _ => (1 : ℤ))

/-- Euler's product `E(X) = ∏_{m≥1}(1 - Xᵐ)` over `ℤ`. -/
noncomputable def E : ℤ⟦X⟧ := ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))

/-- The `n`-th coefficient of `P` is the partition number `p(n) = #(Partition n)`.
With the trivial character every `Finsupp.prod` factor is `1`, so the inner sum
counts the partitions of `n`. -/
theorem coeff_P (n : ℕ) : P.coeff n = (Fintype.card (Nat.Partition n) : ℤ) := by
  have hone : ∀ p : Nat.Partition n,
      p.parts.toFinsupp.prod (fun _ _ => (1 : ℤ)) = 1 := fun p => by simp [Finsupp.prod]
  simp only [P, Nat.Partition.coeff_genFun, hone, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- The `n`-th coefficient of `E` is the signed count of partitions of `n` into
distinct parts, `∑_{q∈distincts n}(-1)^{#parts}` — the parent's `coeff_tprod_pent`. -/
theorem coeff_E (n : ℕ) :
    E.coeff n = ∑ q ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ q.parts.card := by
  rw [E]; exact PentagonalNumberTheoremOQ01.coeff_tprod_pent n

/-- **Per-factor geometric telescoping.**  For each `i`, the `i`-th factor of `P`
(the geometric series in `X^{i+1}`, with `1 + ∑_{j≥1} X^{(i+1)(j+1)} = ∑_j
(X^{i+1})ʲ`) times the `i`-th factor of `E` (namely `1 - X^{i+1}`) is `1`. -/
private theorem factor_telescope (i : ℕ) :
    (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1)))
        * (1 - (X : ℤ⟦X⟧) ^ (i + 1)) = 1 := by
  set f : ℤ⟦X⟧ := (X : ℤ⟦X⟧) ^ (i + 1) with hf
  have hcc : constantCoeff f = 0 := by
    rw [hf, map_pow, constantCoeff_X, zero_pow (Nat.succ_ne_zero i)]
  have hsum : Summable (f ^ ·) := summable_pow_of_constantCoeff_eq_zero hcc
  have hsplit : ∑' n : ℕ, f ^ n = 1 + ∑' j : ℕ, f ^ (j + 1) := by
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hsum)]; simp
  have hrw : (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1)))
      = ∑' n : ℕ, f ^ n := by
    rw [hsplit]; congr 1
    refine tsum_congr (fun j => ?_)
    rw [one_smul, hf, ← pow_mul]
  rw [hrw]
  exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hcc

/-- **The reciprocal identity (headline).**  The partition generating function is
the multiplicative inverse of Euler's product:
`P(X) · ∏_{m≥1}(1 - Xᵐ) = 1`, equivalently `∑ p(n) Xⁿ = ∏ 1/(1-Xᵐ)`.
Proof: both products converge (`Multipliable.tprod_mul`), and each combined
factor telescopes to `1` (`factor_telescope`), so the whole product is `1`. -/
theorem partition_genFun_mul_euler_eq_one : P * E = 1 := by
  have hmul := Multipliable.tprod_mul
      (Nat.Partition.multipliable_genFun (fun _ _ => (1 : ℤ)))
      (multipliable_one_sub_X_pow ℤ)
  rw [P, E, Nat.Partition.genFun_eq_tprod, ← hmul]
  refine (tprod_congr fun i => ?_).trans tprod_one
  exact factor_telescope i

/-- **The Euler convolution.**  Extracting the `n`-th coefficient of `P·E = 1`
gives a Cauchy convolution of the partition numbers against the Euler
coefficients, equal to `1` if `n = 0` and `0` otherwise. -/
theorem euler_convolution (n : ℕ) :
    ∑ ab ∈ Finset.antidiagonal n,
        (Fintype.card (Nat.Partition ab.1) : ℤ)
          * ∑ q ∈ Nat.Partition.distincts ab.2, (-1 : ℤ) ^ q.parts.card
      = if n = 0 then 1 else 0 := by
  have h : (P * E).coeff n = (1 : ℤ⟦X⟧).coeff n := by
    rw [partition_genFun_mul_euler_eq_one]
  rw [coeff_mul, coeff_one] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  rw [coeff_P, coeff_E]

/-- The Euler coefficient at `0` is `1` (the empty partition contributes `(-1)⁰`).
Read off from the constant term of `P·E = 1`. -/
theorem distinctsSum_zero :
    ∑ q ∈ Nat.Partition.distincts 0, (-1 : ℤ) ^ q.parts.card = 1 := by
  have h := euler_convolution 0
  simp only [Finset.antidiagonal_zero, Finset.sum_singleton,
    Fintype.card_unique, Nat.cast_one, one_mul] at h
  exact h

/-- **Euler's partition recurrence (generating-function form).**  For `n ≥ 1`,
`p(n) = -∑_{k<n} p(k)·c_{n-k}`, where `c_b = ∑_{q∈distincts b}(-1)^{#parts}` is
the Euler coefficient `[Xᵇ]∏(1-Xᵐ)`.  Solved from `euler_convolution` by
isolating the `k = n` term (whose Euler factor `c_0 = 1`). -/
theorem partition_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (Nat.Partition n) : ℤ)
      = - ∑ k ∈ Finset.range n,
          (Fintype.card (Nat.Partition k) : ℤ)
            * ∑ q ∈ Nat.Partition.distincts (n - k), (-1 : ℤ) ^ q.parts.card := by
  have h := euler_convolution n
  rw [if_neg (by omega : ¬ n = 0)] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ab : ℕ × ℕ => (Fintype.card (Nat.Partition ab.1) : ℤ)
          * ∑ q ∈ Nat.Partition.distincts ab.2, (-1 : ℤ) ^ q.parts.card) n] at h
  simp only [Finset.sum_range_succ] at h
  rw [Nat.sub_self, distinctsSum_zero, mul_one] at h
  linarith [h]

end PentagonalNumberTheoremOQ01OQ02
