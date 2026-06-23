/-
Erdős Problem #1002 — OQ-03: How the inner sum behaves for rational α
(dependence on the continued-fraction expansion of α, rational case).

Background.  Erdős #1002 studies the limiting distribution of the inner sum
    S(α, n) = Σ_{k=1}^{n} (1/2 − {αk}),
where {·} is the fractional part.  The qualitative behaviour of S(α, n)
depends sharply on the arithmetic of α — concretely, on its continued-fraction
expansion.  For a quadratic irrational (eventually periodic CF, bounded partial
quotients) S stays bounded; for general irrationals it can be unbounded; and for
**rational** α the expansion terminates and the behaviour is the cleanest of all.

This file resolves the rational case completely, with no axioms.

Main results (for a reduced fraction α = p/q, i.e. gcd(p,q) = 1, q ≥ 1):

  * `innerSum_period_sum` :  S(p/q, q) = 1/2.
        The sum over one full period is the **universal constant 1/2**,
        independent of p and of q.  (The denominator q is the length of the
        continued-fraction period — here a terminating expansion.)

  * `innerSum_linear` :  S(p/q, n·q) = n/2.
        Hence for rational α the inner sum grows **exactly linearly**, with the
        per-step rate 1/(2q) governed solely by the denominator q.

The crux is an elementary fact: as m runs over a full period, the residues
p·m mod q run over a complete residue system (multiplication by a unit permutes
ℤ/qℤ), so Σ {pm/q} = (q−1)/2 and the deviations telescope to 1/2.

Self-contained: imports only Mathlib.
-/

import Mathlib

set_option maxHeartbeats 800000

open Real

namespace Erdos1002OQ03

/-! ## Definitions (mirrored from `Erdos1002Problem.lean`) -/

/-- Deviation from the midpoint: `1/2 − {x}`. -/
noncomputable def deviation (x : ℝ) : ℝ :=
  1 / 2 - Int.fract x

/-- Inner sum: `S(α, n) = Σ_{k=1}^{n} (1/2 − {αk})`. -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deviation (α * (↑k + 1))

/-! ## Part I: A complete residue system

As `k` ranges over `range q`, the shifted residues `(p·(k+1)) mod q` form a
permutation of `range q` when `gcd(p, q) = 1`.  Hence the sum of residues is
unchanged. -/

/-- `k ↦ (p·(k+1)) mod q` is injective on `range q` when `gcd(p,q)=1`. -/
private theorem mulmod_shift_injOn (p q : ℕ) (_hq : q ≥ 1) (hcop : Nat.gcd p q = 1) :
    Set.InjOn (fun k => (p * (k + 1)) % q) (Finset.range q) := by
  intro a ha b hb hab
  simp only at hab
  have hcop' : Nat.gcd q p = 1 := by rwa [Nat.gcd_comm]
  have hmod : p * (a + 1) ≡ p * (b + 1) [MOD q] := hab
  have h1 : a + 1 ≡ b + 1 [MOD q] := Nat.ModEq.cancel_left_of_coprime hcop' hmod
  have h2 : a ≡ b [MOD q] := Nat.ModEq.add_right_cancel' 1 h1
  have halt : a < q := Finset.mem_range.mp ha
  have hblt : b < q := Finset.mem_range.mp hb
  have hmm : a % q = b % q := h2
  rwa [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at hmm

/-- The image of `range q` under `k ↦ (p·(k+1)) mod q` is all of `range q`. -/
private theorem mulmod_shift_image (p q : ℕ) (hq : q ≥ 1) (hcop : Nat.gcd p q = 1) :
    (Finset.range q).image (fun k => (p * (k + 1)) % q) = Finset.range q := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨m, _, rfl⟩ := hy
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  · exact le_of_eq (Finset.card_image_of_injOn (mulmod_shift_injOn p q hq hcop)).symm

/-- **Complete residue system.**  For `gcd(p,q)=1`,
    `Σ_{k<q} (p·(k+1) mod q) = Σ_{m<q} m`. -/
private theorem sum_mulmod_shift (p q : ℕ) (hq : q ≥ 1) (hcop : Nat.gcd p q = 1) :
    ∑ k ∈ Finset.range q, ((p * (k + 1)) % q) = ∑ m ∈ Finset.range q, m := by
  conv_rhs => rw [← mulmod_shift_image p q hq hcop]
  rw [Finset.sum_image (mulmod_shift_injOn p q hq hcop)]

/-! ## Part II: Fractional part of `a / q` -/

/-- `Int.fract (a / q) = (a mod q) / q` for naturals `a`, `q` with `q > 0`. -/
private theorem fract_natDiv (a q : ℕ) (hq : 0 < q) :
    Int.fract ((↑a : ℝ) / ↑q) = (↑(a % q) : ℝ) / ↑q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hd : (↑a : ℝ) = ↑q * ↑(a / q) + ↑(a % q) := by
    exact_mod_cast (Nat.div_add_mod a q).symm
  rw [hd, add_div, mul_div_cancel_left₀ _ hqne, Int.fract_natCast_add]
  refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
  rw [div_lt_one hq0]
  exact_mod_cast Nat.mod_lt a hq

/-! ## Part III: The per-period sum equals 1/2 -/

/-- **Per-period sum.**  For a reduced fraction `p/q` (gcd = 1, q ≥ 1),
    the inner sum over one full period equals the universal constant `1/2`:
        `S(p/q, q) = 1/2`. -/
theorem innerSum_period_sum (p q : ℕ) (hq : q ≥ 1) (hcop : Nat.gcd p q = 1) :
    innerSum (↑p / ↑q) q = 1 / 2 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  -- rewrite each deviation term as `1/2 − residue/q`
  have hterm : ∀ k ∈ Finset.range q,
      deviation (↑p / ↑q * (↑k + 1)) = 1 / 2 - (↑((p * (k + 1)) % q) : ℝ) / ↑q := by
    intro k _
    unfold deviation
    congr 1
    rw [show (↑p / ↑q * (↑k + 1) : ℝ) = (↑(p * (k + 1)) : ℝ) / ↑q from by push_cast; ring,
        fract_natDiv (p * (k + 1)) q hq]
  simp only [innerSum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.sum_div]
  -- goal: ↑q * (1/2) − (Σ residues) / ↑q = 1/2
  have hcrs : (∑ k ∈ Finset.range q, (↑((p * (k + 1)) % q) : ℝ)) = (↑q * (↑q - 1)) / 2 := by
    have hnat : ∑ k ∈ Finset.range q, ((p * (k + 1)) % q) = ∑ m ∈ Finset.range q, m :=
      sum_mulmod_shift p q hq hcop
    have h2 : (∑ m ∈ Finset.range q, m) * 2 = q * (q - 1) := Finset.sum_range_id_mul_two q
    have hc : (((∑ m ∈ Finset.range q, m) * 2 : ℕ) : ℝ) = ((q * (q - 1) : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hh : ((∑ m ∈ Finset.range q, m : ℕ) : ℝ) * 2 = ↑q * (↑q - 1) := by
      calc ((∑ m ∈ Finset.range q, m : ℕ) : ℝ) * 2
          = (((∑ m ∈ Finset.range q, m) * 2 : ℕ) : ℝ) := by push_cast; ring
        _ = ((q * (q - 1) : ℕ) : ℝ) := hc
        _ = ↑q * (↑q - 1) := by rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one]
    calc (∑ k ∈ Finset.range q, (↑((p * (k + 1)) % q) : ℝ))
        = ((∑ k ∈ Finset.range q, ((p * (k + 1)) % q) : ℕ) : ℝ) := by push_cast; rfl
      _ = ((∑ m ∈ Finset.range q, m : ℕ) : ℝ) := by rw [hnat]
      _ = (↑q * (↑q - 1)) / 2 := by linarith [hh]
  rw [hcrs]
  field_simp
  ring

/-! ## Part IV: Linear growth `S(p/q, n·q) = n/2`

We reuse the additive period recurrence (`deviation` is `q`-periodic in the
index), proved here locally, then induct on the number of periods. -/

/-- `deviation` is invariant under natural shifts. -/
private theorem deviation_add_nat (x : ℝ) (n : ℕ) :
    deviation (x + ↑n) = deviation x := by
  unfold deviation
  rw [Int.fract_add_natCast]

/-- The map `k ↦ deviation(p/q · (k+1))` has period `q`. -/
private theorem deviation_rational_periodic (p q : ℕ) (hq : q ≥ 1) (k : ℕ) :
    deviation (↑p / ↑q * (↑(k + q) + 1)) = deviation (↑p / ↑q * (↑k + 1)) := by
  have hqne : (↑q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  rw [show (↑k : ℝ) + ↑q + 1 = (↑k + 1) + ↑q from by ring, mul_add,
      show (↑p : ℝ) / ↑q * ↑q = ↑p from by field_simp]
  exact deviation_add_nat (↑p / ↑q * (↑k + 1)) p

/-- Summing a `q`-periodic function over any `q` consecutive values is constant. -/
private theorem cyclic_sum_periodic (g : ℕ → ℝ) (q : ℕ) (hper : ∀ k, g (k + q) = g k)
    (n : ℕ) : ∑ k ∈ Finset.range q, g (n + k) = ∑ k ∈ Finset.range q, g k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_rw : ∀ k, g (m + 1 + k) = g (m + (k + 1)) := fun k => by congr 1; omega
    simp_rw [h_rw]
    have hr := Finset.sum_range_succ (fun k => g (m + k)) q
    have hr' := Finset.sum_range_succ' (fun k => g (m + k)) q
    have hper_m : g (m + q) = g m := hper m
    have hz : g (m + 0) = g m := by rw [Nat.add_zero]
    linarith

/-- The inner-sum period recurrence: `S(p/q, n+q) = S(p/q, n) + S(p/q, q)`. -/
private theorem innerSum_period_rec (p q : ℕ) (hq : q ≥ 1) (n : ℕ) :
    innerSum (↑p / ↑q) (n + q) = innerSum (↑p / ↑q) n + innerSum (↑p / ↑q) q := by
  simp only [innerSum]
  rw [Finset.sum_range_add]
  congr 1
  exact cyclic_sum_periodic (fun k => deviation (↑p / ↑q * (↑k + 1))) q
    (deviation_rational_periodic p q hq) n

/-- **Linear growth.**  For a reduced fraction `p/q`, the inner sum over `n`
    full periods is exactly `n/2`:
        `S(p/q, n·q) = n/2`. -/
theorem innerSum_linear (p q : ℕ) (hq : q ≥ 1) (hcop : Nat.gcd p q = 1) (n : ℕ) :
    innerSum (↑p / ↑q) (n * q) = ↑n / 2 := by
  induction n with
  | zero => simp [innerSum]
  | succ m ih =>
    have hrec : innerSum (↑p / ↑q) (m * q + q)
        = innerSum (↑p / ↑q) (m * q) + innerSum (↑p / ↑q) q :=
      innerSum_period_rec p q hq (m * q)
    have hstep : (m + 1) * q = m * q + q := by ring
    rw [hstep, hrec, ih, innerSum_period_sum p q hq hcop]
    push_cast; ring

/-! ## Part V: Sanity-check corollaries -/

/-- The growth is genuinely unbounded: e.g. after two periods the sum is `1`. -/
example (p q : ℕ) (hq : q ≥ 1) (hcop : Nat.gcd p q = 1) :
    innerSum (↑p / ↑q) (2 * q) = 1 := by
  rw [innerSum_linear p q hq hcop 2]; norm_num

/-- Concretely, for `α = 1/2` (q = 2): one period sums to `1/2`. -/
example : innerSum (1 / 2 : ℝ) 2 = 1 / 2 := by
  have h := innerSum_period_sum 1 2 (by norm_num) (by decide)
  simpa using h

end Erdos1002OQ03
