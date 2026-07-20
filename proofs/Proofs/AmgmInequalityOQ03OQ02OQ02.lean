/-
# AM-GM / Maclaurin OQ-03-OQ-02-OQ-02: the abstract log-concavity engine

## What This Proves

The heart of the derivation "Newton's inequalities ⟹ Maclaurin's inequalities" is a
purely combinatorial fact about **log-concave sequences** that has nothing to do with
symmetric polynomials. This file isolates that fact as a general, reusable tool.

Let `p : ℕ → ℝ` be a positive sequence with `p 0 = 1` that is **log-concave**:

  `p m · p (m+2) ≤ (p (m+1))²   for all m.`

Then:

1. `logConcave_pow_antitone` — the log-free, product-free multiplicative core:
   `p (k+1)^k ≤ (p k)^(k+1)` for all `k`.

2. `logConcave_root_antitone` — the "power means" `p_k^{1/k}` are non-increasing:
   `p (k+1)^{1/(k+1)} ≤ p k^{1/k}`.

Specialised to `p k = eₖ / C(n,k)` (whose log-concavity is exactly Newton's
inequality `newton_log_concavity` in `AmgmInequalityOQ02.lean`), statement 2 is
precisely Maclaurin's step `Mₖ ≥ Mₖ₊₁`. Stated abstractly here, the same engine
applies to *any* log-concave positive sequence — binomial coefficients, coefficients
of real-rooted polynomials, unimodal probability sequences, etc.

## Proof Strategy

`logConcave_pow_antitone` is proved by induction on `k`. The successor step raises the
log-concavity inequality `p m · p (m+2) ≤ p(m+1)²` to the power `m+1`, splits
`p(m+1)^{2(m+1)} = p(m+1)^m · p(m+1)^{m+2}`, feeds in the induction hypothesis
`p(m+1)^m ≤ (p m)^{m+1}` on one factor, and cancels the common positive factor
`(p m)^{m+1}`. Everything uses only `ℕ`-powers; no logarithms appear.

`logConcave_root_antitone` extracts the crossed roots via `rpow_cross`
(`b^s ≤ a^t ⟹ b^{1/t} ≤ a^{1/s}`).

No `sorry`, no axioms.
-/
import Mathlib

namespace MaclaurinLogConcave

open scoped Nat

/-- **The multiplicative log-concavity core.** For a positive log-concave sequence
`p` with `p 0 = 1`, one has `p (k+1)^k ≤ (p k)^(k+1)`. Proved by induction on `k` using
only natural-number powers (log- and product-free). -/
theorem logConcave_pow_antitone (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    ∀ k : ℕ, (∀ j, j ≤ k + 1 → 0 < p j) →
      p (k + 1) ^ k ≤ p k ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [hp0]
  | succ m ih =>
    intro hpos
    have IH := ih (fun j hj => hpos j (by omega))
    have hA : 0 < p m := hpos m (by omega)
    have hB : 0 < p (m + 1) := hpos (m + 1) (by omega)
    have hC : 0 < p (m + 2) := hpos (m + 2) (by omega)
    have hNewton : p m * p (m + 2) ≤ p (m + 1) ^ 2 := hlc m
    have hAC : (p m * p (m + 2)) ^ (m + 1) ≤ (p (m + 1) ^ 2) ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hA.le hC.le) hNewton (m + 1)
    rw [mul_pow, ← pow_mul] at hAC
    have hsplit : p (m + 1) ^ (2 * (m + 1))
        = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := by
      rw [← pow_add]; congr 1; omega
    have hIH2 : p (m + 1) ^ m * p (m + 1) ^ (m + 2)
        ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) :=
      mul_le_mul_of_nonneg_right IH (pow_nonneg hB.le _)
    have hcomb : p m ^ (m + 1) * p (m + 2) ^ (m + 1)
        ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) := by
      calc p m ^ (m + 1) * p (m + 2) ^ (m + 1)
            ≤ p (m + 1) ^ (2 * (m + 1)) := hAC
        _ = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := hsplit
        _ ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) := hIH2
    exact le_of_mul_le_mul_left hcomb (pow_pos hA _)

/-- If `b^s ≤ a^t` for positive reals and positive naturals, then taking the
appropriate crossed roots gives `b^(1/t) ≤ a^(1/s)`. -/
theorem rpow_cross {a b : ℝ} {s t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) (h : b ^ s ≤ a ^ t) :
    b ^ ((1 : ℝ) / t) ≤ a ^ ((1 : ℝ) / s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : (b ^ s) ^ ((1 : ℝ) / (s * t)) ≤ (a ^ t) ^ ((1 : ℝ) / (s * t)) :=
    Real.rpow_le_rpow (pow_nonneg hb.le s) h (by positivity)
  have lhs : (b ^ s) ^ ((1 : ℝ) / (s * t)) = b ^ ((1 : ℝ) / t) := by
    rw [← Real.rpow_natCast b s, ← Real.rpow_mul hb.le]
    congr 1
    field_simp
  have rhs : (a ^ t) ^ ((1 : ℝ) / (s * t)) = a ^ ((1 : ℝ) / s) := by
    rw [← Real.rpow_natCast a t, ← Real.rpow_mul ha.le]
    congr 1
    field_simp
  rwa [lhs, rhs] at key

/-- **The root form (abstract Maclaurin monotonicity).** For a positive log-concave
sequence `p` with `p 0 = 1`, the `k`-th-root sequence `p_k^{1/k}` is non-increasing:
`p (k+1)^{1/(k+1)} ≤ p k^{1/k}` for every `k ≥ 1`.

Specialised to `p k = eₖ/C(n,k)`, this is Maclaurin's inequality `Mₖ ≥ Mₖ₊₁`. -/
theorem logConcave_root_antitone (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) (hk : 0 < k) :
    p (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ p k ^ ((1 : ℝ) / k) := by
  have hcore : p (k + 1) ^ k ≤ p k ^ (k + 1) :=
    logConcave_pow_antitone p hp0 hlc k (fun j _ => hpos j)
  have h1 : (0 : ℕ) < k + 1 := by omega
  simpa using rpow_cross (hpos k) (hpos (k + 1)) hk h1 hcore

/-- **The full Maclaurin chain (abstract).** The shifted root sequence
`k ↦ p_(k+1)^{1/(k+1)}` is `Antitone`. This upgrades the *consecutive* step
`logConcave_root_antitone` to the *global* non-increasing chain
`p_1^{1/1} ≥ p_2^{1/2} ≥ p_3^{1/3} ≥ ⋯`: for any `j ≤ k` one gets
`p_(k+1)^{1/(k+1)} ≤ p_(j+1)^{1/(j+1)}`, not merely adjacent indices.

Specialised to `p k = eₖ/C(n,k)`, this is Maclaurin's inequality in its usual
full form `M_1 ≥ M_2 ≥ ⋯ ≥ M_n` — the statement one actually cites, of which the
one-step lemma is only the inductive ingredient. The shift by one keeps the
exponent `1/(k+1)` well-defined (avoiding the `k = 0`, `1/0` degeneracy). -/
theorem logConcave_root_antitone_seq (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    Antitone (fun k : ℕ => p (k + 1) ^ ((1 : ℝ) / (k + 1))) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa using logConcave_root_antitone p hp0 hpos hlc (k + 1) (Nat.succ_pos k)

/-! ## Sharpness: geometric sequences are the equality case

The engine above proves the root sequence `p_k^{1/k}` is *non-increasing*. The natural
question is whether the bound is tight. It is: a **geometric** sequence `p k = r^k` (`r > 0`)
is positive with `p 0 = 1`, log-concave *with equality*, and its root sequence is the
**constant** `r`, so every step of `logConcave_root_antitone` holds with equality.

Specialised to Maclaurin (`p k = eₖ/C(n,k)`), the geometric case corresponds exactly to all
inputs being equal — the classical AM-GM/Maclaurin equality case — confirming the abstract
monotonicity cannot be improved to a strict inequality without a strict-log-concavity
hypothesis. -/

/-- **`k`-th root of `r^k` is `r`.** For `r > 0` and `k ≥ 1`, `(r^k)^{1/k} = r`. The basic
identity making geometric root sequences constant. -/
theorem rpow_pow_root_self {r : ℝ} (hr : 0 < r) {k : ℕ} (hk : 0 < k) :
    (r ^ k) ^ ((1 : ℝ) / k) = r := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_natCast r k, ← Real.rpow_mul hr.le, mul_one_div, div_self hk0,
    Real.rpow_one]

/-- **Geometric sequences are log-concave with equality.** `r^m · r^(m+2) = (r^(m+1))²` for
every `r` and `m`: the log-concavity inequality `hlc` is saturated at every index. -/
theorem geometric_logConcave_eq (r : ℝ) (m : ℕ) :
    r ^ m * r ^ (m + 2) = (r ^ (m + 1)) ^ 2 := by
  rw [← pow_add, ← pow_mul]; congr 1; omega

/-- **Sharpness of `logConcave_root_antitone`.** For `r > 0` the geometric root sequence is
the constant `r`, so the antitone bound
`p (k+1)^{1/(k+1)} ≤ p k^{1/k}` of `logConcave_root_antitone` holds with **equality** at every
`k ≥ 1` when `p k = r^k`. Hence the monotonicity in the log-concavity engine is sharp: it
cannot be strengthened to `<` without assuming strict log-concavity. -/
theorem geometric_root_antitone_eq {r : ℝ} (hr : 0 < r) (k : ℕ) (hk : 0 < k) :
    (r ^ (k + 1)) ^ ((1 : ℝ) / (k + 1)) = (r ^ k) ^ ((1 : ℝ) / k) := by
  rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    rpow_pow_root_self hr (by omega : 0 < k + 1), rpow_pow_root_self hr hk]

/-- **The geometric root sequence is constant (hence the abstract chain is flat).** For
`r > 0`, `logConcave_root_antitone_seq`'s sequence `k ↦ (r^(k+1))^{1/(k+1)}` is the constant
function `r`. Combined with `geometric_logConcave_eq` (the hypotheses hold with equality), this
exhibits the equality case of the whole Maclaurin chain `M_1 ≥ M_2 ≥ ⋯`. -/
theorem geometric_root_seq_const {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (r ^ (k + 1)) ^ ((1 : ℝ) / (k + 1)) = r := by
  rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
  exact rpow_pow_root_self hr (by omega : 0 < k + 1)

/-- **The geometric ratio sequence is constant.** For `r > 0` the consecutive-ratio
sequence `m ↦ r^(m+1) / r^m` of a geometric sequence is the constant `r`. This is the
ratio-form companion of `geometric_root_seq_const`: on the geometric sequence both the
root means and the consecutive ratios collapse to `r`, so the ratio-antitone
characterisation `logConcave_iff_ratio_antitone` is saturated (flat) exactly as the
root-mean chain is. -/
theorem geometric_ratio_const {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ (m + 1) / r ^ m = r := by
  have h : r ^ m ≠ 0 := pow_ne_zero m hr.ne'
  rw [pow_succ, mul_comm, mul_div_assoc, div_self h, mul_one]

/-! ## Strict monotonicity under strict log-concavity

The sharpness section shows the abstract chain is *flat* exactly on geometric sequences
(equality throughout). Its converse is the following: if the log-concavity is **strict**
at every index — `p m · p (m+2) < (p (m+1))²` — then the root sequence `p_k^{1/k}` is
**strictly** decreasing, never flat. This is precisely the strict-log-concavity
hypothesis whose necessity the sharpness section points to. -/

/-- **Strict multiplicative core.** If `p` is positive with `p 0 = 1`, log-concave, and
*strictly* log-concave (`p m · p (m+2) < (p (m+1))²` for all `m`), then
`p (k+1)^k < p k^{k+1}` for every `k ≥ 1`.  The proof reuses the non-strict core
`logConcave_pow_antitone` (at index `k-1`) as the inductive ingredient and injects a
single strict Newton inequality, so no separate strict induction is needed. -/
theorem logConcave_pow_antitone_strict (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2)
    (k : ℕ) (hk : 0 < k) :
    p (k + 1) ^ k < p k ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- Goal: `p (m+2)^(m+1) < p (m+1)^(m+2)`.
  have hA : 0 < p m := hpos m
  have hB : 0 < p (m + 1) := hpos (m + 1)
  have hC : 0 < p (m + 2) := hpos (m + 2)
  -- Strict Newton at `m`, raised to the `(m+1)`-th power.
  have hAC : (p m * p (m + 2)) ^ (m + 1) < (p (m + 1) ^ 2) ^ (m + 1) :=
    pow_lt_pow_left₀ (hstrict m) (mul_nonneg hA.le hC.le) (by omega)
  rw [mul_pow, ← pow_mul] at hAC
  have hsplit : p (m + 1) ^ (2 * (m + 1))
      = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := by
    rw [← pow_add]; congr 1; omega
  -- Non-strict core at index `m`: `p (m+1)^m ≤ p m^(m+1)`.
  have IH : p (m + 1) ^ m ≤ p m ^ (m + 1) :=
    logConcave_pow_antitone p hp0 hlc m (fun j _ => hpos j)
  have hIH2 : p (m + 1) ^ m * p (m + 1) ^ (m + 2)
      ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) :=
    mul_le_mul_of_nonneg_right IH (pow_nonneg hB.le _)
  have hchain : p m ^ (m + 1) * p (m + 2) ^ (m + 1)
      < p m ^ (m + 1) * p (m + 1) ^ (m + 2) := by
    calc p m ^ (m + 1) * p (m + 2) ^ (m + 1)
          < p (m + 1) ^ (2 * (m + 1)) := hAC
      _ = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := hsplit
      _ ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) := hIH2
  exact lt_of_mul_lt_mul_left hchain (pow_nonneg hA.le _)

/-- Strict crossed-root comparison: if `b^s < a^t` for positive reals and positive
naturals, then `b^(1/t) < a^(1/s)`.  The strict analogue of `rpow_cross`. -/
theorem rpow_cross_strict {a b : ℝ} {s t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) (h : b ^ s < a ^ t) :
    b ^ ((1 : ℝ) / t) < a ^ ((1 : ℝ) / s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : (b ^ s) ^ ((1 : ℝ) / (s * t)) < (a ^ t) ^ ((1 : ℝ) / (s * t)) :=
    Real.rpow_lt_rpow (pow_nonneg hb.le s) h (by positivity)
  have lhs : (b ^ s) ^ ((1 : ℝ) / (s * t)) = b ^ ((1 : ℝ) / t) := by
    rw [← Real.rpow_natCast b s, ← Real.rpow_mul hb.le]
    congr 1
    field_simp
  have rhs : (a ^ t) ^ ((1 : ℝ) / (s * t)) = a ^ ((1 : ℝ) / s) := by
    rw [← Real.rpow_natCast a t, ← Real.rpow_mul ha.le]
    congr 1
    field_simp
  rwa [lhs, rhs] at key

/-- **Strict root form.** For a positive, strictly log-concave sequence `p` with
`p 0 = 1`, the root sequence is *strictly* decreasing:
`p (k+1)^{1/(k+1)} < p k^{1/k}` for every `k ≥ 1`.  The strict analogue of
`logConcave_root_antitone`. -/
theorem logConcave_root_antitone_strict (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2)
    (k : ℕ) (hk : 0 < k) :
    p (k + 1) ^ ((1 : ℝ) / (k + 1)) < p k ^ ((1 : ℝ) / k) := by
  have hcore : p (k + 1) ^ k < p k ^ (k + 1) :=
    logConcave_pow_antitone_strict p hp0 hpos hlc hstrict k hk
  have h1 : (0 : ℕ) < k + 1 := by omega
  simpa using rpow_cross_strict (hpos k) (hpos (k + 1)) hk h1 hcore

/-- **The strict Maclaurin chain (abstract).** For a positive, strictly log-concave
sequence with `p 0 = 1`, the shifted root sequence `k ↦ p_(k+1)^{1/(k+1)}` is
`StrictAnti`: `p_1^{1/1} > p_2^{1/2} > p_3^{1/3} > ⋯`.  Specialised to `p k = eₖ/C(n,k)`
with all inputs distinct (strict Newton), this is Maclaurin's inequality with strict
inequalities throughout. -/
theorem logConcave_root_antitone_seq_strict (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2) :
    StrictAnti (fun k : ℕ => p (k + 1) ^ ((1 : ℝ) / (k + 1))) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  simpa using
    logConcave_root_antitone_strict p hp0 hpos hlc hstrict (k + 1) (Nat.succ_pos k)

/-- **Strict upper bound: every later root mean is strictly below the first term.**
For a positive, *strictly* log-concave sequence with `p 0 = 1`, the root mean
`p (k+1)^{1/(k+1)}` is strictly smaller than `p 1` for every `k ≥ 1`. The strict
companion of `logConcave_root_le_first`: where the non-strict engine only gives
`≤ p 1`, strict log-concavity makes the inequality strict past the first index.
Immediate from the strict chain `logConcave_root_antitone_seq_strict` evaluated at
`0 < k`. Specialised to `p k = eₖ/C(n,k)` with distinct inputs, this is `Mₖ₊₁ < M₁`:
the arithmetic mean strictly dominates every later Maclaurin mean. -/
theorem logConcave_root_lt_first (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2)
    (k : ℕ) (hk : 0 < k) :
    p (k + 1) ^ ((1 : ℝ) / (k + 1)) < p 1 := by
  have hsa := logConcave_root_antitone_seq_strict p hp0 hpos hlc hstrict
  have h := hsa hk
  simpa using h

/-! ## Ratio form: log-concavity ⟺ the consecutive-ratio sequence is antitone

The engine above phrases log-concavity through the *root means* `p_k^{1/k}`. Its most
elementary reformulation is through the **consecutive ratios** `r_m := p (m+1) / p m`:
for a positive sequence, the log-concavity inequality `p m · p (m+2) ≤ (p (m+1))²` is
*exactly* `r_(m+1) ≤ r_m`, i.e. the ratio sequence is non-increasing. This is the
discrete analogue of "a log-concave function has non-increasing logarithmic
derivative", and it is the primitive from which the root-mean monotonicity is usually
derived (`p_k^{1/k}` is the geometric mean of `r_0, …, r_(k-1)`, and the geometric mean
of a non-increasing sequence is itself non-increasing). Because it is an honest
equivalence — no `p 0 = 1` normalisation needed — it is recorded here as an `Iff`. -/

/-- **Ratio form of log-concavity.** For a positive sequence `p`, log-concavity
`∀ m, p m · p (m+2) ≤ (p (m+1))²` holds **iff** the consecutive ratios
`m ↦ p (m+1) / p m` form an `Antitone` sequence. Each direction clears the positive
denominators (`div_le_div_iff`) and reduces to the same polynomial inequality. -/
theorem logConcave_iff_ratio_antitone (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j) :
    (∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) ↔
      Antitone (fun m : ℕ => p (m + 1) / p m) := by
  constructor
  · intro hlc
    apply antitone_nat_of_succ_le
    intro m
    show p (m + 2) / p (m + 1) ≤ p (m + 1) / p m
    rw [div_le_div_iff₀ (hpos (m + 1)) (hpos m)]
    nlinarith [hlc m]
  · intro hanti m
    have h : p (m + 2) / p (m + 1) ≤ p (m + 1) / p m := hanti (Nat.le_succ m)
    rw [div_le_div_iff₀ (hpos (m + 1)) (hpos m)] at h
    nlinarith [h]

/-- **Strict ratio form.** For a positive, *strictly* log-concave sequence
(`∀ m, p m · p (m+2) < (p (m+1))²`), the consecutive ratios `m ↦ p (m+1) / p m` are
`StrictAnti`. The strict analogue of the forward direction of
`logConcave_iff_ratio_antitone`. -/
theorem logConcave_ratio_strictAnti (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2) :
    StrictAnti (fun m : ℕ => p (m + 1) / p m) := by
  apply strictAnti_nat_of_succ_lt
  intro m
  show p (m + 2) / p (m + 1) < p (m + 1) / p m
  rw [div_lt_div_iff₀ (hpos (m + 1)) (hpos m)]
  nlinarith [hstrict m]

/-- **Strict ratio equivalence.** For a positive sequence `p`, *strict* log-concavity
`∀ m, p m · p (m+2) < (p (m+1))²` holds **iff** the consecutive ratios
`m ↦ p (m+1) / p m` are `StrictAnti`. This upgrades the one-directional
`logConcave_ratio_strictAnti` to a full `Iff`, exactly mirroring the non-strict
`logConcave_iff_ratio_antitone`. The reverse direction reads off a single strict step
`p (m+2)/p (m+1) < p (m+1)/p m` and clears the positive denominators. -/
theorem logConcave_strict_iff_ratio_strictAnti (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j) :
    (∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2) ↔
      StrictAnti (fun m : ℕ => p (m + 1) / p m) := by
  constructor
  · exact logConcave_ratio_strictAnti p hpos
  · intro hsa m
    have h : p (m + 2) / p (m + 1) < p (m + 1) / p m := hsa (by omega : m < m + 1)
    rw [div_lt_div_iff₀ (hpos (m + 1)) (hpos m)] at h
    nlinarith [h]

/-- **Consecutive ratios are bounded by the first ratio.** For a positive log-concave
sequence with `p 0 = 1`, every consecutive ratio is at most the first one,
`p (m+1) / p m ≤ p 1 / p 0 = p 1`. Immediate from the ratio-antitone form
`logConcave_iff_ratio_antitone` evaluated against index `0`. -/
theorem logConcave_ratio_le_first (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (m : ℕ) :
    p (m + 1) / p m ≤ p 1 := by
  have hanti := (logConcave_iff_ratio_antitone p hpos).mp hlc
  simpa [hp0] using hanti (Nat.zero_le m)

/-- **Every root mean is bounded by the first term.** For a positive log-concave
sequence with `p 0 = 1`, the whole root sequence `p (k+1)^{1/(k+1)}` lies below its
initial value `p 1^{1/1} = p 1`:  `p (k+1)^{1/(k+1)} ≤ p 1` for every `k`.

Specialised to `p k = eₖ/C(n,k)`, this is the top of the Maclaurin chain: every
Maclaurin mean `Mₖ` is at most `M₁ = e₁/n`, the arithmetic mean of the inputs — i.e.
`AM ≥ Mₖ` for all `k`. A direct consequence of the global antitone chain
`logConcave_root_antitone_seq` evaluated against index `0`. -/
theorem logConcave_root_le_first (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) :
    p (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ p 1 := by
  have hanti := logConcave_root_antitone_seq p hp0 hpos hlc
  simpa using hanti (Nat.zero_le k)

/-- **Geometric growth bound.** A positive log-concave sequence with `p 0 = 1` grows at most
geometrically at rate `p 1`: `p k ≤ (p 1) ^ k` for every `k`.  This is the sequence form of
`logConcave_root_le_first` (`p (k+1)^{1/(k+1)} ≤ p 1`) cleared of the root — raise both nonnegative
sides to the `(k+1)`-th power.  It is sharp: geometric `p k = r^k` attains equality
(`geometric_root_antitone_eq`).  The dual lower bound `(r_last)^k ≤ p k` comes from
`logConcave_root_ge_last_ratio`. -/
theorem logConcave_le_first_pow (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) :
    p k ≤ (p 1) ^ k := by
  cases k with
  | zero => simp [hp0]
  | succ j =>
    have hroot := logConcave_root_le_first p hp0 hpos hlc j
    have hpj : (0 : ℝ) < p (j + 1) := hpos (j + 1)
    have he : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hbase : (0 : ℝ) ≤ p (j + 1) ^ ((1 : ℝ) / ((j : ℝ) + 1)) :=
      (Real.rpow_pos_of_pos hpj _).le
    have hpow := Real.rpow_le_rpow hbase hroot (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
    rw [← Real.rpow_natCast (p 1) (j + 1)]
    push_cast
    calc p (j + 1)
        = (p (j + 1) ^ ((1 : ℝ) / ((j : ℝ) + 1))) ^ ((j : ℝ) + 1) := by
          rw [← Real.rpow_mul hpj.le, one_div, inv_mul_cancel₀ he, Real.rpow_one]
      _ ≤ (p 1) ^ ((j : ℝ) + 1) := hpow

/-! ## Lower bound: every root mean is at least the last consecutive ratio

`logConcave_root_le_first` bounds each root mean `p (k+1)^{1/(k+1)}` *above* by the
first consecutive ratio `p 1 = r_0`. The matching *lower* bound is that it is at least
the **last** consecutive ratio `r_k = p (k+1) / p k`: the root mean is the geometric
mean of `r_0 ≥ r_1 ≥ ⋯ ≥ r_k`, so it lies between the smallest ratio `r_k` and the
largest `r_0`. Together the two bounds sandwich the whole Maclaurin chain between
consecutive ratios. -/

/-- **Every root mean is at least the last consecutive ratio.** For a positive
log-concave sequence with `p 0 = 1`, `p (k+1) / p k ≤ p (k+1)^{1/(k+1)}` for every `k`.
The dual of `logConcave_root_le_first`. Proof: both sides are nonnegative, so it
suffices to compare their `(k+1)`-th powers; the right side powers back to `p (k+1)`,
and the left side's `(k+1)`-th power is `≤ p (k+1)` exactly by the multiplicative core
`logConcave_pow_antitone` (`p (k+1)^k ≤ p k^{k+1}`). -/
theorem logConcave_root_ge_last_ratio (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) :
    p (k + 1) / p k ≤ p (k + 1) ^ ((1 : ℝ) / (k + 1)) := by
  have ha : 0 < p (k + 1) := hpos (k + 1)
  have hb : 0 < p k := hpos k
  have hcore : p (k + 1) ^ k ≤ p k ^ (k + 1) :=
    logConcave_pow_antitone p hp0 hlc k (fun j _ => hpos j)
  have hR : 0 ≤ p (k + 1) ^ ((1 : ℝ) / (k + 1)) := Real.rpow_nonneg ha.le _
  -- The right side, raised to the `(k+1)`-th power, is `p (k+1)`.
  have hRpow : (p (k + 1) ^ ((1 : ℝ) / (k + 1))) ^ (k + 1) = p (k + 1) := by
    rw [one_div, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_inv_natCast_pow ha.le (Nat.succ_ne_zero k)
  refine le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) hR ?_
  rw [hRpow, div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < p k ^ (k + 1))]
  calc p (k + 1) ^ (k + 1)
        = p (k + 1) ^ k * p (k + 1) := by rw [pow_succ]
    _ ≤ p k ^ (k + 1) * p (k + 1) := mul_le_mul_of_nonneg_right hcore ha.le
    _ = p (k + 1) * p k ^ (k + 1) := by ring

/-- **The root-mean sandwich.** For a positive log-concave sequence with `p 0 = 1`,
every root mean lies between the last and first consecutive ratios:
`p (k+1) / p k ≤ p (k+1)^{1/(k+1)} ≤ p 1` for every `k`. Combines
`logConcave_root_ge_last_ratio` with `logConcave_root_le_first`. Specialised to
`p k = eₖ/C(n,k)` this places each Maclaurin mean `Mₖ₊₁` between the consecutive
ratio `eₖ₊₁ C(n,k) / (eₖ C(n,k+1))` and the arithmetic mean `M₁`. -/
theorem logConcave_root_ratio_sandwich (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) :
    p (k + 1) / p k ≤ p (k + 1) ^ ((1 : ℝ) / (k + 1)) ∧
      p (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ p 1 :=
  ⟨logConcave_root_ge_last_ratio p hp0 hpos hlc k,
    logConcave_root_le_first p hp0 hpos hlc k⟩

/-! ## Strict sandwich: strict log-concavity separates the root mean from both ratios

The non-strict sandwich `logConcave_root_ratio_sandwich` places each root mean between
the last consecutive ratio `r_k = p (k+1) / p k` and the first `r_0 = p 1`. Under
*strict* log-concavity both inclusions become strict past the first index: the strict
upper separation is `logConcave_root_lt_first` (`p (k+1)^{1/(k+1)} < p 1`), and the
matching strict *lower* separation is recorded here. Both require `k ≥ 1`, since at
`k = 0` the root mean, the last ratio and the first ratio all coincide with `p 1`. -/

/-- **Strict lower bound: every later root mean strictly exceeds its last ratio.** For a
positive, *strictly* log-concave sequence with `p 0 = 1`,
`p (k+1) / p k < p (k+1)^{1/(k+1)}` for every `k ≥ 1`. The strict companion of
`logConcave_root_ge_last_ratio`, dual to the strict upper bound
`logConcave_root_lt_first`. Proof mirrors the non-strict lower bound: both sides are
nonnegative, so it suffices to compare their `(k+1)`-th powers; the right side powers
back to `p (k+1)`, and the left side's `(k+1)`-th power is *strictly* below `p (k+1)`
by the strict multiplicative core `logConcave_pow_antitone_strict`
(`p (k+1)^k < p k^{k+1}`, valid for `k ≥ 1`). Specialised to `p k = eₖ/C(n,k)` with
distinct inputs, this strictly separates each Maclaurin mean `Mₖ₊₁` from its
consecutive ratio. -/
theorem logConcave_root_gt_last_ratio (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2)
    (k : ℕ) (hk : 0 < k) :
    p (k + 1) / p k < p (k + 1) ^ ((1 : ℝ) / (k + 1)) := by
  have ha : 0 < p (k + 1) := hpos (k + 1)
  have hb : 0 < p k := hpos k
  have hcore : p (k + 1) ^ k < p k ^ (k + 1) :=
    logConcave_pow_antitone_strict p hp0 hpos hlc hstrict k hk
  -- The right side, raised to the `(k+1)`-th power, is `p (k+1)`.
  have hRpow : (p (k + 1) ^ ((1 : ℝ) / (k + 1))) ^ (k + 1) = p (k + 1) := by
    rw [one_div, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_inv_natCast_pow ha.le (Nat.succ_ne_zero k)
  refine lt_of_pow_lt_pow_left₀ (k + 1) (Real.rpow_nonneg ha.le _) ?_
  rw [hRpow, div_pow, div_lt_iff₀ (by positivity : (0 : ℝ) < p k ^ (k + 1))]
  calc p (k + 1) ^ (k + 1)
        = p (k + 1) ^ k * p (k + 1) := by rw [pow_succ]
    _ < p k ^ (k + 1) * p (k + 1) := mul_lt_mul_of_pos_right hcore ha
    _ = p (k + 1) * p k ^ (k + 1) := by ring

/-- **The strict root-mean sandwich.** For a positive, *strictly* log-concave sequence
with `p 0 = 1`, every root mean past the first index lies *strictly* between the last
and first consecutive ratios:
`p (k+1) / p k < p (k+1)^{1/(k+1)} < p 1` for every `k ≥ 1`. The strict analogue of
`logConcave_root_ratio_sandwich`, combining the strict lower bound
`logConcave_root_gt_last_ratio` with the strict upper bound `logConcave_root_lt_first`.
Specialised to `p k = eₖ/C(n,k)` with distinct inputs, this strictly places each
Maclaurin mean `Mₖ₊₁` between its consecutive ratio and the arithmetic mean `M₁`. -/
theorem logConcave_root_ratio_sandwich_strict (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hstrict : ∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2)
    (k : ℕ) (hk : 0 < k) :
    p (k + 1) / p k < p (k + 1) ^ ((1 : ℝ) / (k + 1)) ∧
      p (k + 1) ^ ((1 : ℝ) / (k + 1)) < p 1 :=
  ⟨logConcave_root_gt_last_ratio p hp0 hpos hlc hstrict k hk,
    logConcave_root_lt_first p hp0 hpos hlc hstrict k hk⟩

/-! ## The additive (logarithmic) form: `log ∘ p` is midpoint-concave

Every statement above is phrased *multiplicatively* — the hypothesis
`p m · p (m+2) ≤ (p (m+1))²` never mentions a logarithm, and the proofs deliberately
avoid them to stay elementary. Yet the name "log-concave" refers to the honest additive
fact that the sequence `a k := Real.log (p k)` is **midpoint-concave**:

  `a m + a (m+2) ≤ 2 · a (m+1)   for all m.`

For a positive sequence the two are literally equivalent — taking `Real.log` turns the
product `p m · p (m+2)` into the sum `a m + a (m+2)` and `(p (m+1))²` into `2 · a (m+1)`,
and this transformation is reversible by exponentiation. Recording the equivalence makes
the terminology honest and lets any midpoint-concavity fact about real sequences feed the
engine (and vice versa). -/

/-- **Multiplicative log-concavity ⟺ additive midpoint-concavity of `log ∘ p`.** For a
positive sequence `p`, the multiplicative hypothesis `p m · p (m+2) ≤ (p (m+1))²` used
throughout this file holds **iff** the log sequence `k ↦ Real.log (p k)` is
midpoint-concave, `Real.log (p m) + Real.log (p (m+2)) ≤ 2 · Real.log (p (m+1))`. The
forward direction applies `Real.log` monotonicity and splits the product/​power with
`Real.log_mul`/`Real.log_pow`; the reverse re-assembles the same identities and
exponentiates. This is the statement that makes the name "log-concave" literal. -/
theorem logConcave_iff_log_seq_concave (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j) :
    (∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) ↔
      (∀ m, Real.log (p m) + Real.log (p (m + 2)) ≤ 2 * Real.log (p (m + 1))) := by
  constructor
  · intro hlc m
    have hmono : Real.log (p m * p (m + 2)) ≤ Real.log ((p (m + 1)) ^ 2) :=
      Real.log_le_log (mul_pos (hpos m) (hpos (m + 2))) (hlc m)
    rw [Real.log_mul (hpos m).ne' (hpos (m + 2)).ne', Real.log_pow] at hmono
    push_cast at hmono
    linarith
  · intro hcc m
    have hlog : Real.log (p m * p (m + 2)) ≤ Real.log ((p (m + 1)) ^ 2) := by
      rw [Real.log_mul (hpos m).ne' (hpos (m + 2)).ne', Real.log_pow]
      push_cast
      linarith [hcc m]
    have hexp := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (mul_pos (hpos m) (hpos (m + 2))),
      Real.exp_log (pow_pos (hpos (m + 1)) 2)] at hexp

/-- **Strict multiplicative log-concavity ⟺ strict additive midpoint-concavity.** The
strict analogue of `logConcave_iff_log_seq_concave`: for a positive sequence `p`,
`p m · p (m+2) < (p (m+1))²` holds **iff** the log sequence is *strictly* midpoint-concave,
`Real.log (p m) + Real.log (p (m+2)) < 2 · Real.log (p (m+1))`. Same proof shape with the
strict monotonicity lemmas `Real.log_lt_log` / `Real.exp_lt_exp`. -/
theorem logConcave_strict_iff_log_seq_concave_strict (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j) :
    (∀ m, p m * p (m + 2) < (p (m + 1)) ^ 2) ↔
      (∀ m, Real.log (p m) + Real.log (p (m + 2)) < 2 * Real.log (p (m + 1))) := by
  constructor
  · intro hlc m
    have hmono : Real.log (p m * p (m + 2)) < Real.log ((p (m + 1)) ^ 2) :=
      Real.log_lt_log (mul_pos (hpos m) (hpos (m + 2))) (hlc m)
    rw [Real.log_mul (hpos m).ne' (hpos (m + 2)).ne', Real.log_pow] at hmono
    push_cast at hmono
    linarith
  · intro hcc m
    have hlog : Real.log (p m * p (m + 2)) < Real.log ((p (m + 1)) ^ 2) := by
      rw [Real.log_mul (hpos m).ne' (hpos (m + 2)).ne', Real.log_pow]
      push_cast
      linarith [hcc m]
    have hexp := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (mul_pos (hpos m) (hpos (m + 2))),
      Real.exp_log (pow_pos (hpos (m + 1)) 2)] at hexp

/-! ## Closure: log-concave positive sequences are closed under pointwise product

Log-concavity is preserved by pointwise multiplication: if `p` and `q` are positive and
log-concave, so is `k ↦ p k · q k`. Additively this is just "a sum of two midpoint-concave
sequences is midpoint-concave", but the multiplicative proof is elementary — it multiplies
the two log-concavity inequalities factorwise via `mul_le_mul`. Combined with the trivial
base case (the constant sequence `1` is log-concave), this exhibits the positive
log-concave sequences as a multiplicative submonoid, and in particular shows the Maclaurin
engine applies to any product `eₖ/C(n,k)` of real-rooted data. -/

/-- **Log-concavity is closed under pointwise product.** If `p` and `q` are positive
log-concave sequences then their pointwise product `k ↦ p k · q k` is log-concave:
`(p m · q m)·(p (m+2) · q (m+2)) ≤ (p (m+1) · q (m+1))²`. Proof: regroup so the two
log-concavity inequalities `p m · p (m+2) ≤ (p (m+1))²` and `q m · q (m+2) ≤ (q (m+1))²`
multiply factorwise (`mul_le_mul`, both sides nonnegative). -/
theorem logConcave_mul (p q : ℕ → ℝ) (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j)
    (hlcp : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2)
    (hlcq : ∀ m, q m * q (m + 2) ≤ (q (m + 1)) ^ 2) :
    ∀ m, (p m * q m) * (p (m + 2) * q (m + 2)) ≤ (p (m + 1) * q (m + 1)) ^ 2 := by
  intro m
  calc (p m * q m) * (p (m + 2) * q (m + 2))
        = (p m * p (m + 2)) * (q m * q (m + 2)) := by ring
    _ ≤ (p (m + 1)) ^ 2 * (q (m + 1)) ^ 2 :=
        mul_le_mul (hlcp m) (hlcq m) (mul_pos (hq m) (hq (m + 2))).le
          (pow_pos (hp (m + 1)) 2).le
    _ = (p (m + 1) * q (m + 1)) ^ 2 := by ring

/-- **The pointwise product of normalised log-concave sequences is normalised.** If
`p 0 = q 0 = 1` then the product sequence also starts at `1`, so `logConcave_mul` together
with this fact keeps the product inside the exact hypothesis class (`p 0 = 1`, positive,
log-concave) that the root-mean engine `logConcave_root_antitone_seq` consumes. -/
theorem logConcave_mul_normalised (p q : ℕ → ℝ) (hp0 : p 0 = 1) (hq0 : q 0 = 1) :
    (fun k => p k * q k) 0 = 1 := by
  simp [hp0, hq0]

/-- **Log-concavity is closed under nonnegative scaling.** If `p` is log-concave then so is
`c · p` for any `c ≥ 0`: scaling multiplies both sides of the defining inequality by the
same nonnegative factor `c²`. Together with `logConcave_smul_normalised` this rescales any
log-concave sequence to the normalised class (`p 0 = 1`) without leaving it. -/
theorem logConcave_smul (p : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    ∀ m, (c * p m) * (c * p (m + 2)) ≤ (c * p (m + 1)) ^ 2 := by
  intro m
  calc (c * p m) * (c * p (m + 2)) = c ^ 2 * (p m * p (m + 2)) := by ring
    _ ≤ c ^ 2 * (p (m + 1)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left (hlc m); positivity
    _ = (c * p (m + 1)) ^ 2 := by ring

/-- **Scaling a normalised sequence by its reciprocal-first entry renormalises it.** If
`p 0 ≠ 0`, the sequence `(1 / p 0) · p` starts at `1`, so `logConcave_smul` keeps a
positive log-concave sequence inside the normalised hypothesis class the root-mean engine
`logConcave_root_antitone_seq` consumes. -/
theorem logConcave_smul_normalised (p : ℕ → ℝ) (h0 : p 0 ≠ 0) :
    (fun k => (1 / p 0) * p k) 0 = 1 := by
  simp [one_div, inv_mul_cancel₀ h0]

/-- **Log-concavity is closed under pointwise natural powers.** If `p` is a nonnegative
log-concave sequence then so is `k ↦ p k ^ t` for every `t : ℕ`: raising the defining
inequality `p m · p (m+2) ≤ (p (m+1))²` to the `t`-th power (monotone on nonnegatives)
gives `(p m ^ t)·(p (m+2) ^ t) ≤ (p (m+1) ^ t)²`. In particular every power of a
log-concave sequence is again log-concave. -/
theorem logConcave_pow_const (p : ℕ → ℝ) (t : ℕ) (hp : ∀ j, 0 ≤ p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    ∀ m, (p m ^ t) * (p (m + 2) ^ t) ≤ (p (m + 1) ^ t) ^ 2 := by
  intro m
  calc (p m ^ t) * (p (m + 2) ^ t)
        = (p m * p (m + 2)) ^ t := by rw [mul_pow]
    _ ≤ ((p (m + 1)) ^ 2) ^ t :=
        pow_le_pow_left₀ (mul_nonneg (hp m) (hp (m + 2))) (hlc m) t
    _ = (p (m + 1) ^ t) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Log-concavity is invariant under geometric tilt.** For `r > 0` the pointwise product
`k ↦ p k · r^k` of a positive log-concave sequence `p` with the geometric sequence `r^k` is
again log-concave. The geometric sequence is log-concave with equality
(`geometric_logConcave_eq`), so this is the `q k = r^k` case of `logConcave_mul`. Tilting by a
geometric factor therefore preserves the entire root-mean antitone structure. -/
theorem logConcave_mul_geometric (p : ℕ → ℝ) (r : ℝ) (hr : 0 < r) (hp : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    ∀ m, (p m * r ^ m) * (p (m + 2) * r ^ (m + 2)) ≤ (p (m + 1) * r ^ (m + 1)) ^ 2 :=
  logConcave_mul p (fun j => r ^ j) hp (fun j => pow_pos hr j) hlc
    (fun m => (geometric_logConcave_eq r m).le)

/-- **Geometric tilt preserves normalisation.** If `p 0 = 1` then the geometric tilt
`k ↦ p k · r^k` also starts at `1` (`r^0 = 1`), so `logConcave_mul_geometric` keeps the
sequence inside the normalised hypothesis class. -/
theorem logConcave_mul_geometric_normalised (p : ℕ → ℝ) (r : ℝ) (hp0 : p 0 = 1) :
    (fun k => p k * r ^ k) 0 = 1 := by
  simp [hp0]

/-! ## Arbitrary-gap log-concavity: the exchange inequality and discrete TP2

The defining hypothesis `p m · p (m+2) ≤ (p (m+1))²` compares indices that are exactly
two apart. It is the tip of a much stronger structural property: log-concavity of a
positive sequence is equivalent to the **total positivity of order 2** (`TP2`) of the
`2 × 2` minors `p a · p b`, i.e. *concentrating* two indices (moving them closer together
while preserving their sum) can only increase the product. The three results below extract
that general "index-majorization" content directly from the ratio-antitone form
`logConcave_iff_ratio_antitone`, each recovering the defining inequality as a special case:

* `logConcave_exchange` — the single-step exchange `p i · p (j+1) ≤ p (i+1) · p j` for `i ≤ j`
  (defining case `j = i+1`);
* `logConcave_logSupermod` — the general master inequality `p a · p (b+c) ≤ p (a+c) · p b`
  for `a ≤ b` and arbitrary shift `c` (discrete log-supermodularity / TP2);
* `logConcave_spread` — arbitrary-gap log-concavity `p m · p (m+2d) ≤ (p (m+d))²`
  (defining case `d = 1`).
-/

/-- **Exchange inequality.** For a positive log-concave sequence and `i ≤ j`, moving the two
indices `i, j+1` one step *closer together* (to `i+1, j`) does not decrease the product:
`p i · p (j+1) ≤ p (i+1) · p j`. This is the fundamental single exchange step of discrete
log-supermodularity; the defining log-concavity `p i · p (i+2) ≤ (p (i+1))²` is the case
`j = i+1`. Read straight off the ratio-antitone form: `p (j+1)/p j ≤ p (i+1)/p i`, cleared
of positive denominators. -/
theorem logConcave_exchange (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) {i j : ℕ} (hij : i ≤ j) :
    p i * p (j + 1) ≤ p (i + 1) * p j := by
  have hanti := (logConcave_iff_ratio_antitone p hpos).mp hlc
  have h : p (j + 1) / p j ≤ p (i + 1) / p i := hanti hij
  rw [div_le_div_iff₀ (hpos j) (hpos i)] at h
  nlinarith [h]

/-- **Discrete log-supermodularity (TP2).** For a positive log-concave sequence, `a ≤ b`,
and any shift `c`, one has `p a · p (b+c) ≤ p (a+c) · p b`: pushing the smaller index up by
`c` (to `a+c`) while pulling the larger index down by `c` (from `b+c` to `b`) — a move that
concentrates the pair while keeping the total `(a) + (b+c) = (a+c) + b` fixed — can only
increase the product. Equivalently, every `2 × 2` minor `p a · p (b+c) - p (a+c) · p b` of
the Hankel-type matrix is `≤ 0`, i.e. the sequence is totally positive of order 2. Proved by
induction on `c`: the successor step multiplies the induction hypothesis by the antitone
consecutive ratio at the base index `a+c ≤ b+c` and cancels the common positive factor
`p (a+c)`. The defining inequality and `logConcave_exchange` are the cases `c = 1`. -/
theorem logConcave_logSupermod (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) {a b : ℕ} (hab : a ≤ b) (c : ℕ) :
    p a * p (b + c) ≤ p (a + c) * p b := by
  have hanti := (logConcave_iff_ratio_antitone p hpos).mp hlc
  induction c with
  | zero => simp
  | succ c ih =>
    have hr : p (b + c + 1) / p (b + c) ≤ p (a + c + 1) / p (a + c) :=
      hanti (by omega : a + c ≤ b + c)
    rw [div_le_div_iff₀ (hpos (b + c)) (hpos (a + c))] at hr
    have key : (p a * p (b + c + 1)) * p (a + c) ≤ (p (a + c + 1) * p b) * p (a + c) := by
      nlinarith [mul_le_mul_of_nonneg_left hr (hpos a).le,
        mul_le_mul_of_nonneg_right ih (hpos (a + c + 1)).le]
    exact le_of_mul_le_mul_right key (hpos (a + c))

/-- **Arbitrary-gap log-concavity.** For a positive log-concave sequence, the log-concavity
inequality holds across *any* even gap `2d`, not just the defining gap `2`:
`p m · p (m + 2d) ≤ (p (m+d))²`. The endpoints `m` and `m+2d` are the extreme pair with
midpoint `m+d`, so this is the `a := m`, `b := m+d`, `c := d` instance of
`logConcave_logSupermod`. Taking `d = 1` recovers the defining `p m · p (m+2) ≤ (p (m+1))²`. -/
theorem logConcave_spread (p : ℕ → ℝ) (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (m d : ℕ) :
    p m * p (m + 2 * d) ≤ (p (m + d)) ^ 2 := by
  have h := logConcave_logSupermod p hpos hlc (Nat.le_add_right m d) d
  have e : m + d + d = m + 2 * d := by ring
  rw [e] at h
  rw [pow_two]
  exact h

end MaclaurinLogConcave
