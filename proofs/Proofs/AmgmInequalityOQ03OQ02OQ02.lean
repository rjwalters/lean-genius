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
  rw [rpow_pow_root_self hr (Nat.succ_pos k), rpow_pow_root_self hr hk]

/-- **The geometric root sequence is constant (hence the abstract chain is flat).** For
`r > 0`, `logConcave_root_antitone_seq`'s sequence `k ↦ (r^(k+1))^{1/(k+1)}` is the constant
function `r`. Combined with `geometric_logConcave_eq` (the hypotheses hold with equality), this
exhibits the equality case of the whole Maclaurin chain `M_1 ≥ M_2 ≥ ⋯`. -/
theorem geometric_root_seq_const {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (r ^ (k + 1)) ^ ((1 : ℝ) / (k + 1)) = r :=
  rpow_pow_root_self hr (Nat.succ_pos k)

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
    rw [div_le_div_iff (hpos (m + 1)) (hpos m)]
    nlinarith [hlc m]
  · intro hanti m
    have h : p (m + 2) / p (m + 1) ≤ p (m + 1) / p m := hanti (Nat.le_succ m)
    rw [div_le_div_iff (hpos (m + 1)) (hpos m)] at h
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
  rw [div_lt_div_iff (hpos (m + 1)) (hpos m)]
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
    rw [div_lt_div_iff (hpos (m + 1)) (hpos m)] at h
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

end MaclaurinLogConcave
