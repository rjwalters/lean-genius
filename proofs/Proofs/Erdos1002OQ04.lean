/-
  Erdős Problem #1002 — OQ-04: the Liouville (super-approximable) class.

  Background.  Erdős #1002 studies the weighted fractional sum
      f(α, n) = (1/log n) · S(α, n),    S(α, n) = Σ_{k=1}^{n} (1/2 − {αk}),
  and asks whether it has a limiting distribution.  The behaviour of S(α, n)
  is governed by the arithmetic of α:

    * **rational** α — `Erdos1002OQ03` proves S(p/q, n·q) = n/2 *exactly*
      (linear growth, rate 1/(2q));
    * **quadratic irrationals** (more generally badly approximable / bounded
      partial quotients) — S(α, n) = O(log n), so f(α, n) stays bounded;
    * **Liouville numbers** (super-fast rational approximation) — the opposite
      extreme, where S spikes.

  This file resolves the **Liouville side**.  The mechanism is a sharp
  *perturbation lemma*: if α sits just above a reduced fraction p/q, closer than
  1/(Nq)², then for every k ≤ Nq the integer parts agree, ⌊αk⌋ = ⌊(p/q)k⌋, so no
  fractional-part term has yet "wrapped around".  Consequently S(α, Nq) tracks the
  rational value S(p/q, Nq) = N/2 of `Erdos1002OQ03` up to an error < 1:

      0 < α − p/q < 1/(Nq)²   ⟹   N/2 − 1 < S(α, Nq) < N/2.

  Because rationals admit arbitrarily good one-sided irrational approximations
  (`exists_irrational_btwn`), this forces, near *every* rational p/q and for every
  height M, an irrational α with S(α, n) > M — the inner sum is **unbounded over
  the irrationals**, in sharp contrast to the O(log n) boundedness for quadratic
  irrationals.  Iterating the lemma along a sequence p_j/q_j → α with
  α − p_j/q_j < 1/(N_j q_j)² and N_j → ∞ yields a single fixed *Liouville* number
  with S(α, ·) unbounded; that construction (a concrete super-approximable series)
  is the natural capstone and is recorded in the knowledge base.

  Status: 0 sorries, 0 axioms.  Reuses `Erdos1002OQ03.innerSum_linear`.
-/

import Mathlib
import Proofs.Erdos1002OQ03

set_option maxHeartbeats 800000

open Real

namespace Erdos1002OQ04

open Erdos1002OQ03 (innerSum deviation innerSum_linear)

/-! ## Elementary helpers -/

/-- `Int.fract (a / q) = (a mod q) / q` for naturals `a`, `q` with `q > 0`
    (mirrors the private helper of `Erdos1002OQ03`). -/
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

/-- Gauss sum in real form: `Σ_{k<m} (k+1) = m(m+1)/2`. -/
private theorem sum_range_add_one (m : ℕ) :
    ∑ k ∈ Finset.range m, ((k : ℝ) + 1) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

/-! ## The floor-agreement lemma -/

/-- **No wrap-around.**  If `α ≥ p/q` and the perturbation `(α − p/q)·j` is smaller
than the minimal gap `1/q` between `(p/q)·j` and the next integer, then the integer
parts agree: `⌊α·j⌋ = ⌊(p/q)·j⌋`.  This is the geometric heart of the perturbation:
multiplying by `j ≤ Nq` has not yet pushed `α·j` past the integer ceiling of
`(p/q)·j`. -/
private theorem floor_eq_of_close (p q : ℕ) (hq : 1 ≤ q) (α : ℝ) (j : ℕ)
    (hge : (p : ℝ) / q ≤ α)
    (hclose : (α - (p : ℝ) / q) * (j : ℝ) < 1 / (q : ℝ)) :
    ⌊α * (j : ℝ)⌋ = ⌊(p : ℝ) / q * (j : ℝ)⌋ := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set β : ℝ := (p : ℝ) / q with hβ
  have hjpos : (0 : ℝ) ≤ (j : ℝ) := by positivity
  -- `β·j = (p*j)/q`, a nat-over-nat quotient.
  have hβj : β * (j : ℝ) = ((p * j : ℕ) : ℝ) / (q : ℝ) := by
    rw [hβ]; push_cast; ring
  -- fractional part of `β·j` is at most `(q-1)/q`.
  have hfract : Int.fract (β * (j : ℝ)) ≤ ((q : ℝ) - 1) / (q : ℝ) := by
    rw [hβj, fract_natDiv (p * j) q (by omega)]
    rw [div_le_div_iff_of_pos_right hq0]
    have : (p * j) % q ≤ q - 1 := by
      have := Nat.mod_lt (p * j) (show 0 < q by omega); omega
    calc ((((p * j) % q : ℕ)) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = (q : ℝ) - 1 := by
            have : 1 ≤ q := hq
            push_cast [Nat.cast_sub this]; ring
  -- lower: `⌊β·j⌋ ≤ ⌊α·j⌋` by monotonicity (`β·j ≤ α·j`).
  have hmono : ⌊β * (j : ℝ)⌋ ≤ ⌊α * (j : ℝ)⌋ :=
    Int.floor_le_floor (by nlinarith [hge, hjpos])
  -- upper: `α·j < ⌊β·j⌋ + 1`, since `fract(β·j) + (α−β)·j < (q-1)/q + 1/q = 1`.
  have hsplit : β * (j : ℝ) = (⌊β * (j : ℝ)⌋ : ℝ) + Int.fract (β * (j : ℝ)) :=
    (Int.floor_add_fract _).symm
  have key : α * (j : ℝ) < (⌊β * (j : ℝ)⌋ : ℝ) + 1 := by
    have hαβ : α * (j : ℝ) = β * (j : ℝ) + (α - β) * (j : ℝ) := by ring
    have hsum1 : Int.fract (β * (j : ℝ)) + (α - β) * (j : ℝ) < 1 := by
      have hgap : ((q : ℝ) - 1) / q + 1 / q = 1 := by
        rw [← add_div, div_eq_one_iff_eq (ne_of_gt hq0)]; ring
      have hcl : (α - β) * (j : ℝ) < 1 / (q : ℝ) := by rw [hβ]; exact hclose
      linarith [hfract, hcl, hgap]
    linarith [hαβ, hsplit, hsum1]
  have hupper : ⌊α * (j : ℝ)⌋ ≤ ⌊β * (j : ℝ)⌋ := by
    have : ⌊α * (j : ℝ)⌋ < ⌊β * (j : ℝ)⌋ + 1 := by
      apply Int.floor_lt.2
      push_cast
      exact key
    omega
  omega

/-! ## The perturbation theorem -/

/-- **Perturbation lemma (Liouville mechanism).**  Let `p/q` be a reduced fraction
(`gcd(p,q)=1`, `q ≥ 1`) and `N ≥ 1`.  If an irrational/real `α` sits just above
`p/q`, within `1/(Nq)²`, then the inner sum at `n = Nq` is pinned to the rational
value `N/2` of `Erdos1002OQ03.innerSum_linear`, up to error `< 1`:

    0 < α − p/q < 1/(Nq)²   ⟹   N/2 − 1 < S(α, Nq) < N/2.

The proof: under the hypothesis, `floor_eq_of_close` gives `⌊α·k⌋ = ⌊(p/q)·k⌋` for
all `k ≤ Nq`, so termwise `deviation(α·k) = deviation((p/q)·k) − (α−p/q)·k`.
Summing and using `innerSum_linear` and the Gauss sum,
`S(α, Nq) = N/2 − (α−p/q)·Nq(Nq+1)/2`, and the correction lies in `(0, 1)`. -/
theorem innerSum_perturb (p q N : ℕ) (hq : 1 ≤ q) (hcop : Nat.gcd p q = 1) (hN : 1 ≤ N)
    (α : ℝ) (hlo : (p : ℝ) / q < α)
    (hhi : (α - (p : ℝ) / q) * (((N * q : ℕ) : ℝ)) ^ 2 < 1) :
    (N : ℝ) / 2 - 1 < innerSum α (N * q) ∧ innerSum α (N * q) < (N : ℝ) / 2 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set β : ℝ := (p : ℝ) / q with hβ
  set δ : ℝ := α - β with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- `Nq ≥ 1`, real cast `↑(N*q) = N*q`.
  have hNq1 : 1 ≤ N * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNqR : ((N * q : ℕ) : ℝ) = (N : ℝ) * (q : ℝ) := by push_cast; ring
  have hNqpos : (0 : ℝ) < (N : ℝ) * (q : ℝ) := by positivity
  -- the cast hypothesis as a clean real inequality on `δ`.
  have hhi' : δ * ((N : ℝ) * (q : ℝ)) ^ 2 < 1 := by
    rw [hδ, hβ]; rw [hNqR] at hhi; exact hhi
  -- termwise rewrite under floor agreement.
  have hterm : ∀ k ∈ Finset.range (N * q),
      deviation (α * ((k : ℝ) + 1)) = deviation (β * ((k : ℝ) + 1)) - δ * ((k : ℝ) + 1) := by
    intro k hk
    have hklt : k < N * q := Finset.mem_range.mp hk
    -- the perturbation at index `j = k+1` is below the gap `1/q`.
    have hclose : δ * (((k + 1 : ℕ)) : ℝ) < 1 / (q : ℝ) := by
      have hjle : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) * (q : ℝ) := by
        have : (k + 1 : ℕ) ≤ N * q := hklt
        calc ((k + 1 : ℕ) : ℝ) ≤ ((N * q : ℕ) : ℝ) := by exact_mod_cast this
          _ = (N : ℝ) * (q : ℝ) := hNqR
      -- δ·(Nq)·(Nq) < 1  ⟹  δ·(Nq) < 1/(Nq) ≤ 1/q.
      have hstep : δ * ((N : ℝ) * (q : ℝ)) < 1 / ((N : ℝ) * (q : ℝ)) := by
        rw [lt_div_iff₀ hNqpos]; nlinarith [hhi']
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hle : 1 / ((N : ℝ) * (q : ℝ)) ≤ 1 / (q : ℝ) :=
        one_div_le_one_div_of_le hq0 (by nlinarith [hN1R, hq0])
      nlinarith [hjle, hstep, hle, hδpos.le]
    have hfe : ⌊α * (((k + 1 : ℕ)) : ℝ)⌋ = ⌊β * (((k + 1 : ℕ)) : ℝ)⌋ :=
      floor_eq_of_close p q hq α (k + 1) (by rw [← hβ]; exact hlo.le) (by rw [← hβ]; exact hclose)
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hfe
    -- expand deviations through `fract = x - ⌊x⌋`.
    simp only [deviation, Int.fract]
    rw [hfe]; ring
  -- sum the termwise identity.
  have hsum : innerSum α (N * q)
      = innerSum β (N * q) - δ * (∑ k ∈ Finset.range (N * q), ((k : ℝ) + 1)) := by
    simp only [innerSum]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  -- evaluate the two pieces.
  have hlin : innerSum β (N * q) = (N : ℝ) / 2 := by rw [hβ]; exact innerSum_linear p q hq hcop N
  rw [hsum, hlin, sum_range_add_one (N * q), hNqR]
  -- correction `C = δ·Nq(Nq+1)/2 ∈ (0,1)`.
  set m : ℝ := (N : ℝ) * (q : ℝ) with hm
  have hmpos : 0 < m := hNqpos
  have hm1 : 1 ≤ m := by
    rw [hm]; have : ((N * q : ℕ) : ℝ) = (N : ℝ) * q := hNqR
    rw [← this]; exact_mod_cast hNq1
  have hC : 0 < δ * (m * (m + 1) / 2) := by positivity
  have hClt : δ * (m * (m + 1) / 2) < 1 := by
    -- δ·m² < 1, and m(m+1)/2 ≤ m²·(1/2 + 1/(2m)) ≤ m² since m ≥ 1.
    have hδm2 : δ * (m * m) < 1 := by rw [hδ, hβ] at hhi'; nlinarith [hhi']
    nlinarith [hC, hmpos, hm1, hδpos, hδm2]
  constructor <;> [nlinarith [hClt, hC]; nlinarith [hC]]

/-! ## Unboundedness over the irrationals (Liouville side resolved) -/

/-- **Inner sum is unbounded near every rational.**  For every reduced fraction
`p/q` and every height `M`, there is an *irrational* `α > p/q` with `S(α, n) > M`
for some `n`.  Thus `S(α, n)` is unbounded over the irrationals — the defining
contrast with the badly-approximable (quadratic-irrational) class, where
`S(α, n) = O(log n)`.  The spikes accumulate at every rational, which is exactly
the Liouville (super-approximation) phenomenon. -/
theorem innerSum_unbounded_near_rational (p q : ℕ) (hq : 1 ≤ q) (hcop : Nat.gcd p q = 1)
    (M : ℝ) : ∃ α : ℝ, Irrational α ∧ (p : ℝ) / q < α ∧ ∃ n : ℕ, M < innerSum α n := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- choose `N ≥ 1` with `N/2 - 1 > M`.
  obtain ⟨N, hN1, hNM⟩ : ∃ N : ℕ, 1 ≤ N ∧ M < (N : ℝ) / 2 - 1 := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * M + 2)
    refine ⟨max 1 N0, le_max_left _ _, ?_⟩
    have : (N0 : ℝ) ≤ ((max 1 N0 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- pick an irrational in the nonempty interval `(p/q, p/q + 1/(Nq)²)`.
  have hNqpos : (0 : ℝ) < (N : ℝ) * (q : ℝ) := by positivity
  have hwid : (0 : ℝ) < 1 / (((N * q : ℕ) : ℝ)) ^ 2 := by
    have : ((N * q : ℕ) : ℝ) = (N : ℝ) * q := by push_cast; ring
    rw [this]; positivity
  obtain ⟨α, hαirr, hα1, hα2⟩ :=
    exists_irrational_btwn (show (p : ℝ) / q < (p : ℝ) / q + 1 / (((N * q : ℕ) : ℝ)) ^ 2 by linarith)
  refine ⟨α, hαirr, hα1, N * q, ?_⟩
  -- apply the perturbation lemma.
  have hhi : (α - (p : ℝ) / q) * (((N * q : ℕ) : ℝ)) ^ 2 < 1 := by
    have hsq : (0 : ℝ) < (((N * q : ℕ) : ℝ)) ^ 2 := by
      have : ((N * q : ℕ) : ℝ) = (N : ℝ) * q := by push_cast; ring
      rw [this]; positivity
    have hsub : α - (p : ℝ) / q < 1 / (((N * q : ℕ) : ℝ)) ^ 2 := by linarith [hα2]
    rwa [lt_div_iff₀ hsq] at hsub
  obtain ⟨hlow, _⟩ := innerSum_perturb p q N hq hcop hN1 α hα1 hhi
  linarith [hNM, hlow]

/-- **Specialization at `p/q = 0`.**  Concretely: for every `M` there is an
irrational `α ∈ (0, 1)` with `S(α, n) > M` for some `n`.  (Take `p = 0`, `q = 1`.) -/
theorem innerSum_unbounded (M : ℝ) :
    ∃ α : ℝ, Irrational α ∧ 0 < α ∧ ∃ n : ℕ, M < innerSum α n := by
  obtain ⟨α, hirr, hpos, n, hn⟩ := innerSum_unbounded_near_rational 0 1 (le_refl 1) (by decide) M
  exact ⟨α, hirr, by simpa using hpos, n, hn⟩

end Erdos1002OQ04
