/-
  Bridging the Verified First-Moment Bound into the erdos-138 Framework

  `erdos-138` (`Erdos138Problem.lean`) defines the van der Waerden number

      W(k) = sInf { N | every 2-colouring of {1,…,N} has a monochromatic k-AP }

  and axiomatizes *all* of its growth lower bounds (`berlekamp_lower_bound`,
  `kozik_shabanov_lower_bound`).  Separately, `van-der-waerden-first-moment`
  (`VanDerWaerdenFirstMoment.lean`) proves — fully, axiom-free — the elementary
  first-moment (union-bound) bound `vdw_lower_bound`: if `n² < 2^(k-1)` then some
  2-colouring of the ground set `Fin n` has no monochromatic length-`k` AP.

  This file connects the two.  It turns the verified `Fin n` colouring into a
  colouring of `{1,…,N}` and feeds it through erdos-138's own reduction lemmas
  (`contains_mono_ap_imp`, `not_in_guarantee_lt_sInf`) to obtain a **machine-checked
  lower bound on `W k` itself**:

      `firstMoment_W_lower_bound       : N² < 2^(k-1)         → N < W k`
      `firstMoment_W_lower_bound_sharp : N² < 2·(k-1)·2^(k-1) → N < W k`
      `firstMoment_W_pow_lower         : 2^((k-2)/2) < W k`   (power corollary)
      `firstMoment_W_pow_lower_sharp   : 2^((k-1)/2) < W k`   (sharper corollary)

  This is the first *verified* (rather than axiomatized) lower bound on `W` in the
  erdos-138 development.  All four route through the shared engine
  `W_lower_of_no_mono` (which turns any monochromatic-AP-free `Fin N` colouring into
  `N < W k`); the `*_sharp` pair feeds the sharpened AP count
  `2(k-1)·|family| ≤ n²` from `van-der-waerden-first-moment-oq-01`
  (`vdw_lower_bound_sharp`) rather than the loose `n²`, widening the admissible `N`
  by a `√(2(k-1))` factor and lifting the clean power floor from `2^((k-2)/2)` to
  `2^((k-1)/2)`.

  HONEST STRENGTH GAP (important).  Even sharpened, the elementary bound only gives
  `W(k) ≳ √(2(k-1))·2^((k-1)/2) = 2^(k/2+o(k))`, which is asymptotically *negligible*
  against the axiomatized bounds `kozik_shabanov_lower_bound` (`W(k) ≳ c·2^k`) and
  `berlekamp_lower_bound`: the `√k` gain is polynomial and does not touch the
  `2^{k/2}` vs `2^k` exponential gap.  It therefore **does not eliminate** any
  existing erdos-138 axiom — it *supplements* them with a proven bound for the
  elementary regime.  The negligibility is recorded formally as
  `firstMoment_bound_negligible` (the ratio of the two bounds' magnitudes → 0).

  Status: 0 sorries, 0 new axioms.  The `W` lower bounds depend on erdos-138's
  axiom `W_is_nonempty` (which makes `W` well-defined as an `sInf`), inherited
  through `not_in_guarantee_lt_sInf`; `#print axioms` reports
  `[propext, Classical.choice, W_is_nonempty, Quot.sound]`.  No axiom is introduced
  *here*, and the underlying union-bound mathematics
  (`vdw_lower_bound` / `vdw_lower_bound_sharp`) is fully axiom-free.
-/
import Mathlib
import Proofs.VanDerWaerdenFirstMoment
import Proofs.VanDerWaerdenFirstMomentOQ01
import Proofs.Erdos138Problem

namespace Erdos138

open ProbMethod.VanDerWaerden
open ProbMethod.PropertyB (Mono)
open Finset Filter
open scoped Fin.NatCast

/-- Embed `Bool` into `Fin 2` (the colour alphabet used by erdos-138). -/
def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0

theorem boolToFin2_injective : Function.Injective boolToFin2 := by decide

/-- Transport a `Fin N` colouring to a colouring of `{1,…,N} ⊆ ℕ` via the index
shift `v ↦ v - 1` (mapping `{1,…,N}` onto `{0,…,N-1} = Fin N`). -/
def shiftColoring (N : ℕ) [NeZero N] (c : Fin N → Bool) (x : Finset.Icc 1 N) : Fin 2 :=
  boolToFin2 (c ((Nat.cast (x.1 - 1)) : Fin N))

/-- **`W k` is positive for `k ≥ 2`.**  A colouring of the empty ground set
`{1,…,0}` cannot contain a length-`k` AP (which needs a base point `≥ 1`), so
`0 ∉ monoAP_guarantee_set 2 k` and `not_in_guarantee_lt_sInf` gives `0 < W k`. -/
theorem W_pos {k : ℕ} (hk : 2 ≤ k) : 0 < W k := by
  apply not_in_guarantee_lt_sInf
  intro hmem
  -- A coloring of the empty set {1,…,0} can have no length-`k` (k ≥ 2) AP.
  have hcontains : ContainsMonoAPofLength
      (fun _ : Finset.Icc 1 0 => (0 : Fin 2)) k := hmem _
  have hhas :
      HasMonoAP (extend_coloring 0 (fun _ : Finset.Icc 1 0 => (0 : Fin 2))) 0 k :=
    contains_mono_ap_imp 0 k (by omega) _ hcontains
  obtain ⟨a, d, _, ha1, han, _⟩ := hhas
  -- a ≥ 1 but a + (k-1)·d ≤ 0 forces a = 0, contradiction.
  omega

/-- **Bridge core.**  Any `Fin N` colouring (`N > 0`) with *no* monochromatic
length-`k` `vdwAP` certifies `N < W k`.

This is the engine shared by every first-moment lower bound: it is independent of
*why* the colouring has no monochromatic AP (the loose `n²` count, the sharpened
`n²/(2(k-1))` count, …).  We transport `c` to a colouring of `{1,…,N}` via
`shiftColoring`; erdos-138's `contains_mono_ap_imp` says any monochromatic AP for
that colouring would lift to a function-form monochromatic AP of
`extend_coloring N (shiftColoring N c)`, which shifted back by one is a
monochromatic `vdwAP` for `c` — contradicting `hc`.  Hence
`N ∉ monoAP_guarantee_set 2 k`, and `not_in_guarantee_lt_sInf` gives `N < W k`. -/
theorem W_lower_of_no_mono {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    (c : Fin N → Bool)
    (hc : ∀ a d : ℕ, 1 ≤ d → a + (k - 1) * d < N → ¬ Mono (vdwAP N a d k) c) :
    N < W k := by
  -- Evaluation of the extended ℕ-coloring on points of {1,…,N}.
  have eval : ∀ y : ℕ, y ∈ Finset.Icc 1 N →
      extend_coloring N (shiftColoring N c) y
        = boolToFin2 (c ((Nat.cast (y - 1)) : Fin N)) := by
    intro y hy
    simp only [extend_coloring, dif_pos hy, shiftColoring]
  apply not_in_guarantee_lt_sInf
  intro hmem
  have hcontains : ContainsMonoAPofLength (shiftColoring N c) k := hmem _
  have hhas : HasMonoAP (extend_coloring N (shiftColoring N c)) N k :=
    contains_mono_ap_imp N k (by omega) _ hcontains
  obtain ⟨a, d, hd, ha1, han, hmono⟩ := hhas
  -- Build a monochromatic `vdwAP` for `c`, contradicting the first-moment bound.
  have hMono : Mono (vdwAP N (a - 1) d k) c := by
    refine ⟨c ((Nat.cast (a - 1)) : Fin N), ?_⟩
    intro x hx
    simp only [vdwAP, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, hfi⟩ := hx
    -- membership of the relevant ℕ points in {1,…,N}
    have hidd : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    have hmem_i : a + i * d ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]; omega
    have hmem_a : a ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]; omega
    -- the monochromaticity hypothesis at index i (base point a = a + 0·d)
    have hmi := hmono i hi
    rw [eval _ hmem_i, eval _ hmem_a] at hmi
    -- cancel boolToFin2 and align the index shift (a + i·d) - 1 = (a-1) + i·d
    have hcc :
        c ((Nat.cast (a + i * d - 1)) : Fin N) = c ((Nat.cast (a - 1)) : Fin N) :=
      boolToFin2_injective hmi
    have hshift : a + i * d - 1 = a - 1 + i * d := by omega
    rw [hshift] at hcc
    rw [← hfi]
    exact hcc
  exact hc (a - 1) d (by omega) (by omega) hMono

/-- **Verified first-moment lower bound on the van der Waerden number `W`.**

If `N² < 2^(k-1)` (so `N < 2^((k-1)/2)`) and `k ≥ 2`, then `N < W k`.  Feeds the
loose `n²` AP count (`vdw_lower_bound`) through the bridge core
`W_lower_of_no_mono`. -/
theorem firstMoment_W_lower_bound {k N : ℕ} (hk : 2 ≤ k)
    (hNk : N * N < 2 ^ (k - 1)) : N < W k := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; exact W_pos hk
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc⟩ := vdw_lower_bound (n := N) hk hNk
  exact W_lower_of_no_mono hk c hc

/-- **Sharpened verified first-moment lower bound on `W`.**

If `N² < 2·(k-1)·2^(k-1)` and `k ≥ 2`, then `N < W k`.  This is strictly stronger
than `firstMoment_W_lower_bound`: it admits `N` up to `≈ √(2(k-1))·2^((k-1)/2)`, a
`√(2(k-1))` factor wider, by feeding the sharpened AP count `2(k-1)·|family| ≤ n²`
(`vdw_lower_bound_sharp`, entry `van-der-waerden-first-moment-oq-01`) through the
same bridge core.  The witness it delivers is `W(k) ≳ √(2(k-1))·2^((k-1)/2)`.

(It still does not approach the axiomatized `kozik_shabanov_lower_bound`
`W(k) ≳ c·2^k`: a polynomial-in-`k` gain leaves the `2^{k/2}` vs `2^k` exponential
gap — recorded in `firstMoment_bound_negligible` — untouched.) -/
theorem firstMoment_W_lower_bound_sharp {k N : ℕ} (hk : 2 ≤ k)
    (hNk : N ^ 2 < 2 * (k - 1) * 2 ^ (k - 1)) : N < W k := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; exact W_pos hk
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc⟩ := vdw_lower_bound_sharp (n := N) hk hNk
  exact W_lower_of_no_mono hk c hc

/-- **Clean power-of-two corollary.** For `k ≥ 2`, `2^((k-2)/2) < W k`.

Instantiates `firstMoment_W_lower_bound` at `N = 2^((k-2)/2)`: then
`N² = 2^(2⌊(k-2)/2⌋) ≤ 2^(k-2) < 2^(k-1)`. -/
theorem firstMoment_W_pow_lower {k : ℕ} (hk : 2 ≤ k) :
    2 ^ ((k - 2) / 2) < W k := by
  apply firstMoment_W_lower_bound hk
  have hsq : 2 ^ ((k - 2) / 2) * 2 ^ ((k - 2) / 2) = 2 ^ (2 * ((k - 2) / 2)) := by
    rw [← pow_add]; congr 1; ring
  rw [hsq]
  have hle : 2 ^ (2 * ((k - 2) / 2)) ≤ 2 ^ (k - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstep : 2 ^ (k - 2) < 2 ^ (k - 1) := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [hk1, pow_succ]
    have hpos : 0 < 2 ^ (k - 2) := by positivity
    omega
  exact lt_of_le_of_lt hle hstep

/-- **Sharpened power-of-two corollary.** For `k ≥ 2`, `2^((k-1)/2) < W k`.

Instantiates `firstMoment_W_lower_bound_sharp` at `N = 2^((k-1)/2)`: then
`N² = 2^(2⌊(k-1)/2⌋) ≤ 2^(k-1) < 2·(k-1)·2^(k-1)`.  This improves the exponent
floor of `firstMoment_W_pow_lower` from `(k-2)/2` to `(k-1)/2` — a direct dividend
of the sharpened AP count. -/
theorem firstMoment_W_pow_lower_sharp {k : ℕ} (hk : 2 ≤ k) :
    2 ^ ((k - 1) / 2) < W k := by
  apply firstMoment_W_lower_bound_sharp hk
  have hsq : (2 ^ ((k - 1) / 2)) ^ 2 = 2 ^ (2 * ((k - 1) / 2)) := by
    rw [← pow_mul]; congr 1; ring
  rw [hsq]
  have hle : 2 ^ (2 * ((k - 1) / 2)) ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : 2 ^ (k - 1) < 2 * (k - 1) * 2 ^ (k - 1) := by
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    have hk2 : 2 ≤ 2 * (k - 1) := by omega
    have hmul : 2 * 2 ^ (k - 1) ≤ 2 * (k - 1) * 2 ^ (k - 1) :=
      Nat.mul_le_mul_right (2 ^ (k - 1)) hk2
    omega
  exact lt_of_le_of_lt hle hlt

/-- **Honest strength gap (formal).** The first-moment lower bound has magnitude
`≈ 2^((k-1)/2)`; the axiomatized Kozik–Shabanov bound has magnitude `≈ 2^k`.
Comparing squares (to stay in clean integer exponents), `2^(k-1) / (2^k)² = 2^(k-1)/4^k`
tends to `0`.  This certifies that the elementary first-moment bound is
asymptotically negligible against the axiomatized bounds — hence it cannot
eliminate `kozik_shabanov_lower_bound` or `berlekamp_lower_bound`; it only
supplements them. -/
theorem firstMoment_bound_negligible :
    Tendsto (fun k : ℕ => ((2 : ℝ) ^ (k - 1)) / 4 ^ k) atTop (nhds 0) := by
  apply squeeze_zero (fun k => by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1))
  intro k
  have h1 : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  rw [div_le_iff₀ h4]
  have hmul : ((1 : ℝ) / 2) ^ k * 4 ^ k = 2 ^ k := by
    rw [← mul_pow]; norm_num
  rw [hmul]
  exact h1

end Erdos138
