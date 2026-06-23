import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-
# Chebyshev bounds OQ-03 / OQ-01: the θ–π form of the Prime Number Theorem

The parent entry (`chebyshev-bounds-oq-03`) proves `ψ(x) ∼ θ(x)` (prime powers are
negligible) and lists as its first open question:

> *Complete the chain: prove `θ(x) ∼ x ⟺ π(x) ∼ x/log x` via partial summation,
> formalizing the transfer between the prime-log sum and the prime-counting function.*

This file closes that gap.  Rather than Abel summation we use the **elementary
two-inequality argument** (Apostol, *Introduction to Analytic Number Theory*, Thm 4.4),
which needs only two bracketing estimates and is far more amenable to formalization:

* `theta_le_primeCounting_mul_log` :  `θ(x) ≤ π(x) · log x`
    (every prime `p ≤ x` contributes `log p ≤ log x`);
* `primeCounting_le` :  `π(x) ≤ x^α + θ(x)/(α · log x)` for `0 < α < 1`
    (split the primes at `x^α`; those above contribute `log p > α · log x`).

Dividing by `x`, writing `f(x) = θ(x)/x` and `g(x) = π(x)·log x / x`, these read

    f(x) ≤ g(x) ≤ x^{α-1} · log x + (1/α) · f(x),

and since `x^{α-1} log x → 0` and `α` may be taken arbitrarily close to `1`, the two
functions have the **same limit**: `θ(x)/x → 1 ⟺ π(x)·log x / x → 1`, i.e.

    θ(x) ∼ x   ⟺   π(x) ∼ x / log x.

Combined with the parent's `ψ ∼ θ`, all three classical forms of PNT are equivalent,
entirely from Chebyshev-level tools — no contour integration.

`π` is Mathlib's `Nat.primeCounting`, evaluated at `⌊x⌋₊`; `θ` is `Chebyshev.theta`.

Sorry-free and axiom-free.
-/

namespace ChebyshevBoundsOQ03OQ01

open Chebyshev Finset Filter Real
open scoped Nat.Prime Topology

/-- Real-valued prime-counting function `π(x) = #{p ≤ x : p prime}`, as a real number. -/
noncomputable def primeCountingReal (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- The index set of `θ x`: the primes in `(0, ⌊x⌋]`. -/
private lemma theta_eq_sum (x : ℝ) :
    θ x = ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta, Finset.sum_filter]

/-- The number of primes in `(0, n]` is exactly `π(n)`. -/
lemma card_filter_prime_Ioc (n : ℕ) :
    ((Ioc 0 n).filter Nat.Prime).card = Nat.primeCounting n := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp⟩; exact ⟨Nat.lt_succ_of_le hpn, hp⟩
  · rintro ⟨hpn, hp⟩; exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp hpn⟩, hp⟩

/-- **Lemma A.**  `θ(x) ≤ π(x) · log x`: each prime `p ≤ x` contributes `log p ≤ log x`. -/
theorem theta_le_primeCounting_mul_log {x : ℝ} (hx : 1 ≤ x) :
    θ x ≤ primeCountingReal x * Real.log x := by
  rw [theta_eq_sum, primeCountingReal, ← card_filter_prime_Ioc]
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p
      ≤ ∑ _p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log x := by
        apply Finset.sum_le_sum
        intro p hp
        rw [mem_filter, mem_Ioc] at hp
        obtain ⟨⟨hp0, hpn⟩, _⟩ := hp
        have hple : (p : ℝ) ≤ x :=
          le_trans (by exact_mod_cast hpn) (Nat.floor_le hx0)
        exact Real.log_le_log (by exact_mod_cast hp0) hple
    _ = (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lemma B.**  For `0 < α < 1`, `π(x) ≤ x^α + θ(x)/(α · log x)`.
Split the primes `≤ x` at `x^α`: those `≤ x^α` number at most `x^α`, and each prime
`p` with `x^α < p ≤ x` satisfies `log p > α · log x`, so the rest number at most
`θ(x)/(α · log x)`. -/
theorem primeCounting_le {x α : ℝ} (hx : 2 ≤ x) (hα0 : 0 < α) (hα1 : α < 1) :
    primeCountingReal x ≤ x ^ α + θ x / (α * Real.log x) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans one_le_two hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le two_pos hx
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxα_pos : (0 : ℝ) < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hαlog_pos : 0 < α * Real.log x := mul_pos hα0 hlogx_pos
  set y : ℝ := x ^ α with hy
  set m : ℕ := ⌊y⌋₊ with hm
  set N : ℕ := ⌊x⌋₊ with hN
  have hyx : y ≤ x := by
    calc y = x ^ α := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hα1)
      _ = x := Real.rpow_one x
  have hmN : m ≤ N := Nat.floor_mono hyx
  -- split the primes in (0, N] at m
  have hsplit : (Ioc 0 N).filter Nat.Prime =
      (Ioc 0 m).filter Nat.Prime ∪ (Ioc m N).filter Nat.Prime := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) hmN]
  have hdisj : Disjoint ((Ioc 0 m).filter Nat.Prime) ((Ioc m N).filter Nat.Prime) := by
    apply Finset.disjoint_left.2
    intro a ha hb
    rw [mem_filter, mem_Ioc] at ha hb
    exact absurd hb.1.1 (not_lt.2 ha.1.2)
  have hcard : Nat.primeCounting N =
      ((Ioc 0 m).filter Nat.Prime).card + ((Ioc m N).filter Nat.Prime).card := by
    rw [← card_filter_prime_Ioc, hsplit, Finset.card_union_of_disjoint hdisj]
  -- count1 = π(m) ≤ y
  have hcount1 : (((Ioc 0 m).filter Nat.Prime).card : ℝ) ≤ y := by
    have h1 : ((Ioc 0 m).filter Nat.Prime).card ≤ m := by
      calc ((Ioc 0 m).filter Nat.Prime).card ≤ (Ioc 0 m).card := Finset.card_filter_le _ _
        _ = m := by rw [Nat.card_Ioc, Nat.sub_zero]
    calc (((Ioc 0 m).filter Nat.Prime).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
      _ ≤ y := Nat.floor_le hxα_pos.le
  -- each prime p with m < p has log p > α log x
  have hkey : ∀ p ∈ (Ioc m N).filter Nat.Prime, α * Real.log x ≤ Real.log p := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have hpm : m < p := hp.1.1
    have hpy : y < (p : ℝ) := by
      have : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
      have hmp : (m : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpm
      linarith
    have hlog : Real.log y < Real.log p := Real.log_lt_log hxα_pos hpy
    rw [hy, Real.log_rpow hx0] at hlog
    exact le_of_lt hlog
  -- count2 * (α log x) ≤ θ x
  have hcount2_mul : (((Ioc m N).filter Nat.Prime).card : ℝ) * (α * Real.log x) ≤ θ x := by
    have hsum1 : (((Ioc m N).filter Nat.Prime).card : ℝ) * (α * Real.log x)
        = ∑ _p ∈ (Ioc m N).filter Nat.Prime, (α * Real.log x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum1]
    calc ∑ _p ∈ (Ioc m N).filter Nat.Prime, (α * Real.log x)
        ≤ ∑ p ∈ (Ioc m N).filter Nat.Prime, Real.log p := Finset.sum_le_sum hkey
      _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [mem_filter, mem_Ioc] at hp ⊢
            exact ⟨⟨lt_of_le_of_lt (Nat.zero_le m) hp.1.1, hp.1.2⟩, hp.2⟩
          · intro p hp _
            rw [mem_filter, mem_Ioc] at hp
            exact Real.log_nonneg (by exact_mod_cast hp.1.1)
      _ = θ x := (theta_eq_sum x).symm
  have hcount2 : (((Ioc m N).filter Nat.Prime).card : ℝ) ≤ θ x / (α * Real.log x) :=
    (le_div_iff₀ hαlog_pos).2 hcount2_mul
  -- assemble
  rw [primeCountingReal, hcard]
  push_cast
  exact add_le_add hcount1 hcount2

/-- **Main theorem (θ–π form of PNT).** `θ(x) ∼ x ⟺ π(x) ∼ x / log x`, in the form
`θ(x)/x → 1 ⟺ π(x)·log x / x → 1`. -/
theorem theta_asymp_iff_primeCounting_asymp :
    Tendsto (fun x => θ x / x) atTop (𝓝 1) ↔
      Tendsto (fun x => primeCountingReal x * Real.log x / x) atTop (𝓝 1) := by
  set f : ℝ → ℝ := fun x => θ x / x with hfdef
  set g : ℝ → ℝ := fun x => primeCountingReal x * Real.log x / x with hgdef
  -- Inequality 1:  f x ≤ g x  (Lemma A, divided by x).
  have hfg : ∀ᶠ x in atTop, f x ≤ g x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
    show θ x / x ≤ primeCountingReal x * Real.log x / x
    gcongr
    exact theta_le_primeCounting_mul_log hx1
  -- The error term  E_α x = log x · x^α / x → 0  for 0 < α < 1.
  have hE : ∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun x => Real.log x * x ^ α / x) atTop (𝓝 0) := by
    intro α hα0 hα1
    have hr : (0 : ℝ) < 1 - α := by linarith
    have hlo := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
    apply hlo.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
    rw [Real.rpow_sub hx0, Real.rpow_one]
    field_simp
  -- Inequality 2:  g x ≤ E_α x + (1/α) f x  for x ≥ 2  (Lemma B, multiplied by log x / x).
  have hgf : ∀ α : ℝ, 0 < α → α < 1 → ∀ᶠ x in atTop,
      g x ≤ Real.log x * x ^ α / x + (1 / α) * f x := by
    intro α hα0 hα1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx2
    have hx0 : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hxne : x ≠ 0 := hx0.ne'
    have hαne : α ≠ 0 := hα0.ne'
    have hlne : Real.log x ≠ 0 := hlogx_pos.ne'
    have hB := primeCounting_le hx2 hα0 hα1
    have hfac : 0 ≤ Real.log x / x := by positivity
    show primeCountingReal x * Real.log x / x ≤ _
    have h1 : primeCountingReal x * Real.log x / x
            ≤ (x ^ α + θ x / (α * Real.log x)) * (Real.log x / x) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hB hfac
    refine le_trans h1 (le_of_eq ?_)
    show _ = Real.log x * x ^ α / x + 1 / α * (θ x / x)
    field_simp
  -- assemble both directions
  constructor
  · -- forward:  θ ∼ x  ⟹  π ∼ x/log x
    intro hf1
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards [(tendsto_order.1 hf1).1 b hb, hfg] with x hbf hfgx
      linarith
    · intro b hb  -- hb : 1 < b
      set α : ℝ := 2 / (1 + b) with hαdef
      have hb0 : 0 < 1 + b := by linarith
      have hα0 : 0 < α := by rw [hαdef]; positivity
      have hα1 : α < 1 := by rw [hαdef, div_lt_one hb0]; linarith
      have hLb : 1 / α < b := by
        rw [hαdef, one_div_div]; linarith
      have hsum : Tendsto (fun x => Real.log x * x ^ α / x + 1 / α * f x)
          atTop (𝓝 (1 / α)) := by
        have h := (hE α hα0 hα1).add (hf1.const_mul (1 / α))
        simpa using h
      filter_upwards [(tendsto_order.1 hsum).2 b hLb, hgf α hα0 hα1] with x hx hgfx
      exact lt_of_le_of_lt hgfx hx
  · -- reverse:  π ∼ x/log x  ⟹  θ ∼ x
    intro hg1
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb  -- hb : b < 1
      set α : ℝ := (max 0 b + 1) / 2 with hαdef
      have hmaxlt : max 0 b < 1 := max_lt zero_lt_one hb
      have hmax0 : 0 ≤ max 0 b := le_max_left _ _
      have hα0 : 0 < α := by rw [hαdef]; positivity
      have hα1 : α < 1 := by rw [hαdef]; linarith
      have hαb : b < α := by
        have hbm : b ≤ max 0 b := le_max_right _ _
        rw [hαdef]; linarith
      have hlow : Tendsto (fun x => α * (g x - Real.log x * x ^ α / x)) atTop (𝓝 α) := by
        have h := ((hg1.sub (hE α hα0 hα1)).const_mul α)
        simpa using h
      filter_upwards [(tendsto_order.1 hlow).1 b hαb, hgf α hα0 hα1] with x hx hgfx
      -- hgfx : g x ≤ E + (1/α) f x ;  derive  α (g x - E) ≤ f x
      have hmul : α * g x ≤ α * (Real.log x * x ^ α / x) + f x := by
        have h2 := mul_le_mul_of_nonneg_left hgfx hα0.le
        have hexp : α * (Real.log x * x ^ α / x + 1 / α * f x)
            = α * (Real.log x * x ^ α / x) + f x := by
          field_simp
        rw [hexp] at h2; exact h2
      nlinarith [hx, hmul]
    · intro b hb  -- hb : 1 < b
      filter_upwards [(tendsto_order.1 hg1).2 b hb, hfg] with x hgb hfgx
      linarith

end ChebyshevBoundsOQ03OQ01
