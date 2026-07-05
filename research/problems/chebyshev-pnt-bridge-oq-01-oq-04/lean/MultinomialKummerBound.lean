import Mathlib

/-
# Multinomial Kummer carry bound — the conjectured `p^{v_p} ≤ kn` is FALSE;
  the correct bound is `p^{v_p} ≤ (kn)^{k-1}`.

## Research problem: chebyshev-pnt-bridge-oq-01-oq-04

The parent gallery entry `chebyshev-pnt-bridge-oq-01` proves the binomial bound
  `p^{v_p(C(2n,n))} ≤ 2n`
and the pool task proposed the "obvious" multinomial generalization
  `p^{v_p(C(kn; n,…,n))} ≤ kn`   (k blocks of size n).

**This generalization is false for every k ≥ 3.**  The binomial proof works only
because each Kummer carry digit `⌊2n/p^i⌋ − 2⌊n/p^i⌋ ∈ {0,1}`.  For `k` blocks the
per-digit carry lies in `{0,1,…,k−1}`, so the valuation can be as large as
`(k−1)·log_p(kn)`, giving the sharp clean bound

  `p^{v_p(C(kn; n,…,n))} ≤ (kn)^{k-1}`.

### Explicit counterexamples to the naive `≤ kn` bound
* k=3, n=2 (N=6):  C(6;2,2,2) = 90 = 2·3²·5, so 3^{v_3} = 9 > 6.
* k=4, n=1 (N=4):  C(4;1,1,1,1) = 24 = 2³·3,  so 2^{v_2} = 8 > 4.
In fact the bound fails for k≥3 at essentially every n (checked k≤7, n≤14).

### The corrected bound (verified numerically for k≤7, n≤14, all p ≤ N)
  `p^{v_p} ≤ (kn)^{k-1}`,   with `v_p ≤ (k-1)·⌊log_p(kn)⌋`.

This still yields a Chebyshev-type lower bound on π(kn):
  `C(kn;n,…,n) = ∏_{p≤kn} p^{v_p} ≤ (kn)^{(k-1)·π(kn)}`,
and `C(kn;n,…,n) ≥ k^{kn}/(poly)`, so `π(kn) ≥ (kn)·log k / ((k-1)·log(kn)) − o(1)`.
For k=2 this recovers the parent's Chebyshev bound.

Companion verified infrastructure already in the gallery:
`Erdos729LegendreMultinomial.lean` proves the multinomial Legendre/Kummer identity
`(p-1)·v_p(multinomial) + s_p(N) = Σ s_p(aᵢ)` (0 sorries, 0 axioms).

Tags: number-theory, analytic-number-theory, Kummer, Chebyshev
-/

namespace ChebyshevPNTBridgeOQ01OQ04

open Nat Finset

-- ============================================================
-- Part I: The conjectured bound `p^{v_p} ≤ kn` is FALSE (k ≥ 3)
-- ============================================================

/-- The central multinomial coefficient C(6;2,2,2) = 6!/(2!)³ = 90. -/
theorem multinomial_range3_two :
    Nat.multinomial (Finset.range 3) (fun _ => 2) = 90 := by
  native_decide

/-- Its 3-adic prime power is `3² = 9`, which already exceeds `kn = 6`. -/
theorem pow_val_multinomial_range3_two :
    3 ^ ((Nat.multinomial (Finset.range 3) (fun _ => 2)).factorization 3) = 9 := by
  native_decide

/-- **The naive multinomial bound is false.**  There exist a prime `p`, a block
size `n > 0`, and a block count `k > 0` with
`p^{v_p(C(kn;n,…,n))} > kn`.  Witness: `p = 3, n = 2, k = 3` (value `9 > 6`). -/
theorem naive_multinomial_bound_false :
    ¬ ∀ (p n k : ℕ), p.Prime → 0 < n → 0 < k →
        p ^ ((Nat.multinomial (Finset.range k) (fun _ => n)).factorization p) ≤ k * n := by
  intro h
  have hle := h 3 2 3 (by norm_num) (by norm_num) (by norm_num)
  rw [pow_val_multinomial_range3_two] at hle
  omega

/-- A second, minimal counterexample: C(4;1,1,1,1) = 24, `2^{v_2} = 8 > 4`. -/
theorem multinomial_range4_one :
    Nat.multinomial (Finset.range 4) (fun _ => 1) = 24 := by
  native_decide

theorem pow_val_multinomial_range4_one :
    2 ^ ((Nat.multinomial (Finset.range 4) (fun _ => 1)).factorization 2) = 8 := by
  native_decide

-- ============================================================
-- Part II: The corrected bound `p^{v_p} ≤ (kn)^{k-1}`
-- ============================================================

/-- Legendre's formula (copied from the verified parent `ChebyshevPNTBridgeOQ01`):
    `v_p(m!) = ∑_{i=1}^{m} ⌊m/p^i⌋`. -/
theorem legendre_factorial_val (p m : ℕ) (hp : p.Prime) :
    (m !).factorization p = ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Nat.factorial_zero, Nat.factorization_one]
  · have h_ico : (m !).factorization p =
        ∑ i ∈ Finset.Ico 1 (Nat.log p m + 2), m / p ^ i := by
      have h1 : (↑((m !).factorization p) : PartENat) = multiplicity p (m !) :=
        (multiplicity_eq_factorization hp (Nat.factorial_ne_zero m)).symm
      have h2 : multiplicity p (m !) =
          (↑(∑ i ∈ Finset.Ico 1 (Nat.log p m + 2), m / p ^ i) : PartENat) :=
        hp.multiplicity_factorial (by omega)
      exact_mod_cast h1.trans h2
    rw [h_ico]
    apply Finset.sum_subset (Finset.Ico_subset_Ico_right _)
    · have hlog_lt : Nat.log p m < m := by
        rw [Nat.log_lt hp.one_lt hm.ne']
        exact (Nat.lt_two_pow m).trans_le (Nat.pow_le_pow_left hp.two_le m)
      omega
    · intro i hi hni
      rw [Finset.mem_Ico] at hi hni
      push_neg at hni
      have : m < p ^ i := by
        calc m < p ^ (Nat.log p m + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
          _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      exact Nat.div_eq_of_lt this

/-- The factorization of the central multinomial equals
    `v_p((kn)!) − k·v_p(n!)`.  Follows from `Nat.multinomial_spec`:
    `(n!)^k · multinomial = (kn)!`, taking `p`-adic valuations. -/
theorem central_multinomial_factorization (p n k : ℕ) (hp : p.Prime) :
    (Nat.multinomial (Finset.range k) (fun _ => n)).factorization p
      = ((k * n)!).factorization p - k * ((n !).factorization p) := by
  -- `(∏ i ∈ range k, n!) * multinomial = (∑ i ∈ range k, n)!`
  have hspec := Nat.multinomial_spec (Finset.range k) (fun _ : ℕ => n)
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, smul_eq_mul] at hspec
  -- hspec : (n!)^k * multinomial = (k*n)!
  have hmul : ((n !) ^ k * Nat.multinomial (Finset.range k) (fun _ => n)).factorization p
      = ((k * n)!).factorization p := by rw [hspec]
  rw [Nat.factorization_mul (pow_ne_zero k (Nat.factorial_ne_zero n))
        (Nat.multinomial_pos _ _).ne', Nat.factorization_pow] at hmul
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hmul
  omega

/-- **Per-digit carry bound.**  For `N = k·n`, each Legendre term is `≤ k-1`:
    `⌊kn/p^i⌋ − k·⌊n/p^i⌋ ≤ k − 1`.
    Key identity: writing `d = p^i`, `⌊kn/d⌋ = k·⌊n/d⌋ + ⌊k·(n mod d)/d⌋`, and
    `k·(n mod d) < k·d` forces `⌊k·(n mod d)/d⌋ ≤ k-1`. -/
theorem carry_digit_le (p n k i : ℕ) (hp : p.Prime) :
    (k * n) / p ^ i - k * (n / p ^ i) ≤ k - 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hdpos : 0 < p ^ i := pow_pos hp.pos i
  set d := p ^ i with hd
  -- k*n = d * (k*(n/d)) + k*(n%d)
  have hkn : k * n = d * (k * (n / d)) + k * (n % d) := by
    conv_lhs => rw [← Nat.div_add_mod n d]
    ring
  have hdiv : (k * n) / d = k * (n / d) + (k * (n % d)) / d := by
    rw [hkn, Nat.mul_add_div hdpos]
  have hlt : (k * (n % d)) / d < k := by
    rw [Nat.div_lt_iff_lt_mul hdpos]
    exact mul_lt_mul_of_pos_left (Nat.mod_lt n hdpos) hk
  omega

/-- The non-vanishing Legendre terms occur only for `p^i ≤ kn`, and there are at
    most `⌊log_p(kn)⌋` of them, so `v_p ≤ (k-1)·⌊log_p(kn)⌋`.

    BLUEPRINT (the single remaining grind lemma; ideal for Aristotle):
    1. `central_multinomial_factorization` : v_p(mult) = v_p((kn)!) − k·v_p(n!).
    2. `legendre_factorial_val` for both factorials, then extend the `n!` sum from
       `Ico 1 (n+1)` to `Ico 1 (kn+1)`: the added terms `n/p^i` vanish because
       `p^i ≥ 2^i > n` for `i ≥ n+1` (`Finset.sum_subset`, as in `legendre_factorial_val`).
    3. Combine into one sum: `v_p(mult) = ∑_{i ∈ Ico 1 (kn+1)} (kn/p^i − k·(n/p^i))`
       via `Finset.sum_tsub_distrib` (termwise `k·(n/p^i) ≤ kn/p^i`, from
       `Nat.mul_div_le` / floor superadditivity).
    4. Bound each summand by `(k-1) · (if p^i ≤ kn then 1 else 0)`:
       `carry_digit_le` gives `≤ k-1`, and the term is `0` once `p^i > kn`
       (`Nat.div_eq_of_lt`).
    5. `∑ indicator ≤ card {i ∈ Ico 1 (kn+1) : p^i ≤ kn} ≤ Nat.log p (kn)`
       (`Nat.pow_le_iff_le_log` / `Nat.lt_pow_succ_log_self`). -/
theorem central_multinomial_val_le_log (p n k : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hk : 0 < k) :
    (Nat.multinomial (Finset.range k) (fun _ => n)).factorization p
      ≤ (k - 1) * Nat.log p (k * n) := by
  sorry

/-- **Corrected multinomial Kummer bound.**  For a prime `p`, block size `n ≥ 1`
    and block count `k ≥ 1`,
      `p^{v_p(C(kn; n,…,n))} ≤ (kn)^{k-1}`.
    Proof: `v_p ≤ (k-1)·log_p(kn)` (`central_multinomial_val_le_log`), hence
    `p^{v_p} ≤ (p^{log_p(kn)})^{k-1} ≤ (kn)^{k-1}` via `Nat.pow_log_le_self`. -/
theorem pow_factorization_central_multinomial_le (p n k : ℕ) (hp : p.Prime)
    (hn : 0 < n) (hk : 0 < k) :
    p ^ ((Nat.multinomial (Finset.range k) (fun _ => n)).factorization p)
      ≤ (k * n) ^ (k - 1) := by
  have hkn : 0 < k * n := Nat.mul_pos hk hn
  calc p ^ ((Nat.multinomial (Finset.range k) (fun _ => n)).factorization p)
      ≤ p ^ ((k - 1) * Nat.log p (k * n)) :=
        Nat.pow_le_pow_right hp.pos (central_multinomial_val_le_log p n k hp hn hk)
    _ = (p ^ Nat.log p (k * n)) ^ (k - 1) := by rw [Nat.mul_comm, pow_mul]
    _ ≤ (k * n) ^ (k - 1) :=
        Nat.pow_le_pow_left (Nat.pow_log_le_self p hkn.ne') (k - 1)

end ChebyshevPNTBridgeOQ01OQ04
