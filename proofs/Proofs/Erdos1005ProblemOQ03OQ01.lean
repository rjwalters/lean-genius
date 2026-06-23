import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-
# Erdős Problem #1005 (OQ-03 / OQ-01): The Farey Next-Term Recurrence

## Parent

Erdős #1005 asks for the structure of the *longest run of consecutive
similarly ordered Farey fractions* of order `n`. Any analysis of runs must be
able to **walk** the Farey sequence: given two consecutive terms it must
produce the next one. The sibling entry `Erdos1005ProblemOQ03` (the Farey
adjacency criterion `b + d > n`) tells us *when* two unimodular neighbours are
adjacent. This file supplies the missing constructive half: the explicit
**successor formula** that generates the whole sequence — and hence every run.

## This file

Let `a/b < c/d` be adjacent in `F_n` (unimodular, `bc - ad = 1`, with
`b + d > n`), and suppose `c/d < 1` (so a successor exists). Put

  `k := ⌊(n + b) / d⌋`,   `e := k·c - a`,   `f := k·d - b`.

We prove that `e/f` is exactly the **next** Farey fraction of order `n` after
`c/d`:

* `succ_unimodular` — `e·d - c·f = 1`: the new pair `c/d, e/f` is again
  unimodular. This is *automatic* algebra: `ed - cf = (kc-a)d - c(kd-b) =
  bc - ad = 1`. The recurrence preserves the unimodular invariant for free.

* `succ_den_le` — `f ≤ n`: the successor stays in `F_n`. Immediate from
  `k·d ≤ n + b` (definition of `⌊·⌋`).

* `succ_den_pos` / `succ_num_pos` — `f ≥ 1` and `e ≥ 1`.

* `succ_adjacent_pair` — `n < d + f`: by the sibling's adjacency criterion,
  `c/d` and `e/f` are adjacent, because `(k+1)·d > n + b`.

* `cur_lt_succ` — `c/d < e/f`: the successor lies to the right.

* `succ_coprime` — `gcd(e, f) = 1`: `e/f` is in lowest terms.

* `is_successor` — the headline: **no** Farey fraction of order `n` lies
  strictly between `c/d` and `e/f`. So `e/f` is *the* immediate successor.

* `den_recurrence` — the denominator recurrence in closed form,
  `f = ⌊(n + b)/d⌋ · d - b`, the engine that drives any run analysis:
  `q_{i+1} = ⌊(n + q_{i-1})/q_i⌋ · q_i - q_{i-1}`.

Every theorem is fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.

(Self-contained: the small `FareyFraction` scaffold and the adjacency lemma
`intermediate_denom_ge` are re-declared here, matching the sibling file, because
the parent's `import Mathlib.Data.Rat.Basic` no longer resolves under Mathlib
`v4.26.0`.)

Reference: https://erdosproblems.com/1005
-/

namespace Erdos1005OQ03OQ01

-- ══════════════════════════════════════════════════════════════════
-- § 1: Farey fractions (mirrors the sibling scaffold)
-- ══════════════════════════════════════════════════════════════════

/-- A Farey fraction of order `n`: a pair `(p, q)` with `0 ≤ p ≤ q`,
    `1 ≤ q ≤ n`, and `gcd(p, q) = 1`. -/
structure FareyFraction (n : ℕ) where
  p : ℕ
  q : ℕ
  hq_pos : 1 ≤ q
  hq_le : q ≤ n
  hp_le : p ≤ q
  hcoprime : Nat.Coprime p q

/-- The rational value of a Farey fraction. -/
def FareyFraction.toRat {n : ℕ} (f : FareyFraction n) : ℚ :=
  f.p / f.q

/-- Two unimodular neighbours satisfy `bc - ad = 1`. -/
def IsConsecutiveFarey {n : ℕ} (f g : FareyFraction n) : Prop :=
  g.p * f.q - f.p * g.q = 1

-- ══════════════════════════════════════════════════════════════════
-- § 2: Order is cross-multiplication; the denominator-sum lemma
-- ══════════════════════════════════════════════════════════════════

/-- Strict order of two Farey fractions is cross-multiplication. -/
theorem toRat_lt_iff {n : ℕ} (f g : FareyFraction n) :
    f.toRat < g.toRat ↔ f.p * g.q < g.p * f.q := by
  unfold FareyFraction.toRat
  have hf : (0 : ℚ) < f.q := Nat.cast_pos.mpr f.hq_pos
  have hg : (0 : ℚ) < g.q := Nat.cast_pos.mpr g.hq_pos
  rw [div_lt_div_iff₀ hf hg]
  constructor <;> intro h <;> exact_mod_cast h

/-- **Denominator-sum lemma** (sibling `intermediate_denom_ge`). If
    `a/b < p/q < c/d` and the outer pair is unimodular (`bc - ad = 1`), then
    `q ≥ b + d`. Re-proved here so the file stands alone. -/
theorem intermediate_denom_ge {n : ℕ} (f g h : FareyFraction n)
    (huni : IsConsecutiveFarey f g)
    (h1 : f.toRat < h.toRat) (h2 : h.toRat < g.toRat) :
    f.q + g.q ≤ h.q := by
  have hcb : g.p * f.q = f.p * g.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  have hfh : f.p * h.q < h.p * f.q := (toRat_lt_iff f h).mp h1
  have hhg : h.p * g.q < g.p * h.q := (toRat_lt_iff h g).mp h2
  have hcbZ : (g.p : ℤ) * f.q = (f.p : ℤ) * g.q + 1 := by exact_mod_cast hcb
  have h1Z : (f.p : ℤ) * h.q + 1 ≤ (h.p : ℤ) * f.q := by exact_mod_cast hfh
  have h2Z : (h.p : ℤ) * g.q + 1 ≤ (g.p : ℤ) * h.q := by exact_mod_cast hhg
  have key : (h.q : ℤ)
      = (g.q : ℤ) * ((h.p : ℤ) * f.q - (f.p : ℤ) * h.q)
        + (f.q : ℤ) * ((g.p : ℤ) * h.q - (h.p : ℤ) * g.q) := by
    linear_combination (-(h.q : ℤ)) * hcbZ
  have t1 : (1 : ℤ) ≤ (h.p : ℤ) * f.q - (f.p : ℤ) * h.q := by linarith
  have t2 : (1 : ℤ) ≤ (g.p : ℤ) * h.q - (h.p : ℤ) * g.q := by linarith
  have bound : (f.q : ℤ) + g.q ≤ h.q := by
    nlinarith [mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℤ) ≤ (g.q : ℤ)),
               mul_le_mul_of_nonneg_left t2 (by linarith : (0:ℤ) ≤ (f.q : ℤ)), key]
  exact_mod_cast bound

/-- **Adjacency (sufficiency)** — a unimodular pair with `b + d > n` is adjacent
    in `F_n`. -/
theorem farey_adjacent_of_denom_sum_gt {n : ℕ} (f g : FareyFraction n)
    (huni : IsConsecutiveFarey f g) (hsum : n < f.q + g.q) :
    ∀ h : FareyFraction n, ¬ (f.toRat < h.toRat ∧ h.toRat < g.toRat) := by
  rintro h ⟨h1, h2⟩
  have hge : f.q + g.q ≤ h.q := intermediate_denom_ge f g h huni h1 h2
  exact absurd (le_trans hge h.hq_le) (by omega)

-- ══════════════════════════════════════════════════════════════════
-- § 3: The successor and its arithmetic certificates
-- ══════════════════════════════════════════════════════════════════

/-- The integer multiplier `k = ⌊(n + b)/d⌋` that defines the successor. -/
def succK {n : ℕ} (pred cur : FareyFraction n) : ℕ :=
  (n + pred.q) / cur.q

/-- The successor numerator `e = k·c - a`. -/
def succNum {n : ℕ} (pred cur : FareyFraction n) : ℕ :=
  succK pred cur * cur.p - pred.p

/-- The successor denominator `f = k·d - b`. -/
def succDen {n : ℕ} (pred cur : FareyFraction n) : ℕ :=
  succK pred cur * cur.q - pred.q

variable {n : ℕ} (pred cur : FareyFraction n)

/-- `k·d ≤ n + b`: upper half of the floor-division bracket. -/
theorem succK_mul_le : succK pred cur * cur.q ≤ n + pred.q := by
  unfold succK
  exact Nat.div_mul_le_self _ _

/-- `n + b < (k+1)·d`: lower half of the floor-division bracket. -/
theorem lt_succK_succ_mul : n + pred.q < (succK pred cur + 1) * cur.q := by
  unfold succK
  have hpos : 0 < cur.q := cur.hq_pos
  have h1 : cur.q * ((n + pred.q) / cur.q) + (n + pred.q) % cur.q = n + pred.q :=
    Nat.div_add_mod (n + pred.q) cur.q
  have h2 : (n + pred.q) % cur.q < cur.q := Nat.mod_lt _ hpos
  calc n + pred.q
      = cur.q * ((n + pred.q) / cur.q) + (n + pred.q) % cur.q := h1.symm
    _ < cur.q * ((n + pred.q) / cur.q) + cur.q := by omega
    _ = ((n + pred.q) / cur.q + 1) * cur.q := by ring

/-- `k·d > b`, so the successor denominator is a genuine `ℕ` subtraction.
    Reason: `k·d > (n + b) - d ≥ b` since `d ≤ n`. -/
theorem den_lt_succK_mul : pred.q < succK pred cur * cur.q := by
  have hlt := lt_succK_succ_mul pred cur
  have hdn : cur.q ≤ n := cur.hq_le
  -- (k+1)·d = k·d + d, and n + b < k·d + d ⇒ k·d > n + b - d ≥ b
  have : n + pred.q < succK pred cur * cur.q + cur.q := by
    have := hlt; simpa [Nat.add_mul, Nat.one_mul] using this
  omega

/-- `k·c > a`, so the successor numerator is a genuine `ℕ` subtraction.
    Reason: `d·(k·c) = c·(k·d) ≥ c·(b+1) = bc + c > bc - 1 = a·d`. -/
theorem num_lt_succK_mul (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) :
    pred.p < succK pred cur * cur.p := by
  -- unimodular: c·b = a·d + 1
  have hcb : cur.p * pred.q = pred.p * cur.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  -- c ≥ 1: from a/b < c/d and a ≥ 0 we get c ≥ 1
  have hc_pos : 0 < cur.p := by
    rcases Nat.eq_zero_or_pos cur.p with h0 | h0
    · exfalso
      have hcross : pred.p * cur.q < cur.p * pred.q := (toRat_lt_iff pred cur).mp hlt
      simp [h0] at hcross
    · exact h0
  have hkd : pred.q < succK pred cur * cur.q := den_lt_succK_mul pred cur
  -- c·b < c·(k·d) = (k·c)·d, and c·b = a·d + 1, so a·d < (k·c)·d ⇒ a < k·c
  have step1 : cur.p * pred.q < cur.p * (succK pred cur * cur.q) :=
    mul_lt_mul_of_pos_left hkd hc_pos
  have hrw : cur.p * (succK pred cur * cur.q) = (succK pred cur * cur.p) * cur.q := by ring
  rw [hrw, hcb] at step1
  have hmul : pred.p * cur.q < succK pred cur * cur.p * cur.q := by omega
  exact lt_of_mul_lt_mul_right hmul (Nat.zero_le _)

-- ══════════════════════════════════════════════════════════════════
-- § 4: The successor relations
-- ══════════════════════════════════════════════════════════════════

/-- **Unimodular preservation.** `e·d - c·f = 1`: the new pair `c/d, e/f` is
    again unimodular. Pure algebra: `ed - cf = bc - ad = 1`. -/
theorem succ_unimodular (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) :
    succNum pred cur * cur.q - cur.p * succDen pred cur = 1 := by
  have hcb : cur.p * pred.q = pred.p * cur.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  have hkd : pred.q < succK pred cur * cur.q := den_lt_succK_mul pred cur
  have hkc : pred.p < succK pred cur * cur.p :=
    num_lt_succK_mul pred cur huni hlt
  -- The clean identity e·d = c·f + 1 (no truncated subtraction).
  have hed : succNum pred cur * cur.q = cur.p * succDen pred cur + 1 := by
    unfold succNum succDen
    zify [le_of_lt hkc, le_of_lt hkd]
    have hcbZ : (cur.p : ℤ) * pred.q = (pred.p : ℤ) * cur.q + 1 := by exact_mod_cast hcb
    linear_combination hcbZ
  omega

/-- The successor denominator is `≤ n`: it stays in `F_n`. -/
theorem succ_den_le : succDen pred cur ≤ n := by
  unfold succDen
  have := succK_mul_le pred cur
  omega

/-- The successor denominator is positive. -/
theorem succ_den_pos : 1 ≤ succDen pred cur := by
  unfold succDen
  have := den_lt_succK_mul pred cur
  omega

/-- `c/d` and `e/f` are an adjacent pair: `n < d + f`.
    Because `(k+1)·d > n + b`, so `d + f = (k+1)d - b > n`. -/
theorem succ_adjacent_pair : n < cur.q + succDen pred cur := by
  unfold succDen
  have h := lt_succK_succ_mul pred cur
  have hk : pred.q < succK pred cur * cur.q := den_lt_succK_mul pred cur
  -- (k+1)·d = k·d + d > n + b ⇒ d + (k·d - b) > n
  have : n + pred.q < succK pred cur * cur.q + cur.q := by
    simpa [Nat.add_mul, Nat.one_mul] using h
  omega

/-- The successor numerator is positive. -/
theorem succ_num_pos (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) :
    1 ≤ succNum pred cur := by
  unfold succNum
  have := num_lt_succK_mul pred cur huni hlt
  omega

/-- **Lowest terms.** `gcd(e, f) = 1`, from the unimodular relation
    `e·d - c·f = 1`. -/
theorem succ_coprime (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) :
    Nat.Coprime (succNum pred cur) (succDen pred cur) := by
  have huni2 := succ_unimodular pred cur huni hlt
  rw [Nat.Coprime]
  set g := Nat.gcd (succNum pred cur) (succDen pred cur) with hg
  have hge : g ∣ succNum pred cur * cur.q :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have hgf : g ∣ cur.p * succDen pred cur :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  -- e·d = c·f + 1
  have hkc : pred.p < succK pred cur * cur.p :=
    num_lt_succK_mul pred cur huni hlt
  have hkd : pred.q < succK pred cur * cur.q := den_lt_succK_mul pred cur
  have hed : succNum pred cur * cur.q = cur.p * succDen pred cur + 1 := by
    have := huni2
    omega
  rw [hed] at hge
  exact Nat.dvd_one.mp ((Nat.dvd_add_right hgf).mp hge)

/-- **The successor stays in `[0,1]`:** `e ≤ f`, provided `c < d` (i.e.
    `c/d < 1`, so a successor below `1` exists). From `e·d = c·f + 1` with
    `c ≤ d - 1` and `f ≥ 1`: `e·d ≤ (d-1)f + 1 ≤ d·f`. -/
theorem succ_num_le_den (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    succNum pred cur ≤ succDen pred cur := by
  have hkc : pred.p < succK pred cur * cur.p :=
    num_lt_succK_mul pred cur huni hlt
  have hkd : pred.q < succK pred cur * cur.q := den_lt_succK_mul pred cur
  have hed : succNum pred cur * cur.q = cur.p * succDen pred cur + 1 := by
    have := succ_unimodular pred cur huni hlt
    omega
  have hfpos : 1 ≤ succDen pred cur := succ_den_pos pred cur
  -- e·d = c·f + 1 ≤ (d-1)·f + 1 ≤ d·f
  have hbound : succNum pred cur * cur.q ≤ succDen pred cur * cur.q := by
    calc succNum pred cur * cur.q
        = cur.p * succDen pred cur + 1 := hed
      _ ≤ (cur.q - 1) * succDen pred cur + 1 := by
            have hle : cur.p ≤ cur.q - 1 := by omega
            have : cur.p * succDen pred cur ≤ (cur.q - 1) * succDen pred cur := by gcongr
            omega
      _ ≤ succDen pred cur * cur.q := by
            have h1 : (cur.q - 1) * succDen pred cur + succDen pred cur
                = succDen pred cur * cur.q := by
              have hq1 : cur.q - 1 + 1 = cur.q := by have := cur.hq_pos; omega
              calc (cur.q - 1) * succDen pred cur + succDen pred cur
                  = (cur.q - 1 + 1) * succDen pred cur := by ring
                _ = cur.q * succDen pred cur := by rw [hq1]
                _ = succDen pred cur * cur.q := by ring
            omega
  have hq_pos : 0 < cur.q := cur.hq_pos
  exact le_of_mul_le_mul_right hbound hq_pos

-- ══════════════════════════════════════════════════════════════════
-- § 5: Packaging the successor as a Farey fraction of order `n`
-- ══════════════════════════════════════════════════════════════════

/-- The successor `e/f`, packaged as a Farey fraction of order `n`. -/
def succFarey (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) : FareyFraction n where
  p := succNum pred cur
  q := succDen pred cur
  hq_pos := succ_den_pos pred cur
  hq_le := succ_den_le pred cur
  hp_le := succ_num_le_den pred cur huni hlt hcd
  hcoprime := succ_coprime pred cur huni hlt

@[simp] theorem succFarey_p (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    (succFarey pred cur huni hlt hcd).p = succNum pred cur := rfl

@[simp] theorem succFarey_q (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    (succFarey pred cur huni hlt hcd).q = succDen pred cur := rfl

/-- **The successor lies to the right:** `c/d < e/f`. From `e·d = c·f + 1`. -/
theorem cur_lt_succ (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    cur.toRat < (succFarey pred cur huni hlt hcd).toRat := by
  rw [toRat_lt_iff]
  simp only [succFarey_p, succFarey_q]
  have hed : succNum pred cur * cur.q = cur.p * succDen pred cur + 1 := by
    have := succ_unimodular pred cur huni hlt
    omega
  omega

/-- `c/d` and `e/f` form a consecutive (unimodular) pair. -/
theorem isConsecutive_cur_succ (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    IsConsecutiveFarey cur (succFarey pred cur huni hlt hcd) := by
  unfold IsConsecutiveFarey
  simp only [succFarey_p, succFarey_q]
  exact succ_unimodular pred cur huni hlt

/-- **Headline: `e/f` is the immediate successor of `c/d` in `F_n`.** No Farey
    fraction of order `n` lies strictly between `c/d` and `e/f`. -/
theorem is_successor (huni : IsConsecutiveFarey pred cur)
    (hlt : pred.toRat < cur.toRat) (hcd : cur.p < cur.q) :
    ∀ h : FareyFraction n,
      ¬ (cur.toRat < h.toRat ∧ h.toRat < (succFarey pred cur huni hlt hcd).toRat) := by
  have hcons := isConsecutive_cur_succ pred cur huni hlt hcd
  have hsum : n < cur.q + (succFarey pred cur huni hlt hcd).q := by
    simp only [succFarey_q]; exact succ_adjacent_pair pred cur
  exact farey_adjacent_of_denom_sum_gt cur (succFarey pred cur huni hlt hcd) hcons hsum

/-- **Denominator recurrence (closed form).** The denominator of the successor
    is `f = ⌊(n + b)/d⌋ · d - b`. Iterating gives the run-generating recurrence
    `q_{i+1} = ⌊(n + q_{i-1})/q_i⌋ · q_i - q_{i-1}`. -/
theorem den_recurrence :
    succDen pred cur = ((n + pred.q) / cur.q) * cur.q - pred.q := rfl

/-- **Numerator recurrence (closed form).** `e = ⌊(n + b)/d⌋ · c - a`. -/
theorem num_recurrence :
    succNum pred cur = ((n + pred.q) / cur.q) * cur.p - pred.p := rfl

end Erdos1005OQ03OQ01
