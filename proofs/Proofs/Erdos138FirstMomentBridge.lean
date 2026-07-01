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

      `firstMoment_W_lower_bound : N² < 2^(k-1) → N < W k`            (no new axioms)
      `firstMoment_W_pow_lower   : 2^((k-2)/2) < W k`  (a clean power corollary)

  It also imports the *sharpened* first-moment count (`vdw_lower_bound_sharp`,
  which uses `2·(k-1)·|family| ≤ n²` instead of the loose `|family| ≤ n²`) to
  obtain the textbook bound, widening the admissible range by a `√(2(k-1))` factor:

      `firstMoment_W_lower_bound_sharp : N² < 2·(k-1)·2^(k-1) → N < W k`
      `firstMoment_W_pow_lower_sharp   : 2^((k-1)/2) < W k`  (gains 1 in the
                                          exponent for every odd `k`)

  This is the first *verified* (rather than axiomatized) lower bound on `W` in the
  erdos-138 development.

  HONEST STRENGTH GAP (important).  Even the sharpened bound only gives
  `W(k) ≳ √(2(k-1))·2^((k-1)/2)`, which is asymptotically *negligible* against the
  axiomatized bounds `kozik_shabanov_lower_bound` (`W(k) ≳ c·2^k`) and
  `berlekamp_lower_bound`.  It therefore **does not eliminate** any existing
  erdos-138 axiom — it *supplements* them with a proven bound for the elementary
  regime.  The negligibility is itself recorded formally as
  `firstMoment_bound_negligible` (the ratio of the two bounds' magnitudes → 0).

  Status: 0 sorries, 0 new axioms.  (`W` is still defined via erdos-138's
  axiomatized `W_is_nonempty`, inherited through the bridge lemma
  `not_in_guarantee_lt_sInf`; no axiom is introduced *here*.)
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
shift `v ↦ v - 1` (mapping `{1,…,N}` onto `{0,…,N-1} = Fin N`).

The `[NeZero N]` instance is what the `ℕ → Fin N` coercion
(`open scoped Fin.NatCast`) requires; every caller already establishes it (the
`N = 0` regime is handled separately, before any colouring is transported). -/
def shiftColoring (N : ℕ) [NeZero N] (c : Fin N → Bool) (x : Finset.Icc 1 N) : Fin 2 :=
  boolToFin2 (c ((Nat.cast (x.1 - 1)) : Fin N))

/-- **Verified first-moment lower bound on the van der Waerden number `W`.**

If `N² < 2^(k-1)` (so `N < 2^((k-1)/2)`) and `k ≥ 2`, then `N < W k`.

The proof bridges the two gallery files.  From `vdw_lower_bound` we obtain a
2-colouring `c : Fin N → Bool` of the ground set with no monochromatic length-`k`
AP.  We transport it to a colouring of `{1,…,N}` via `shiftColoring`.  erdos-138's
`contains_mono_ap_imp` says any monochromatic AP for that colouring would lift to a
function-form monochromatic AP of `extend_coloring N (shiftColoring N c)`; we show
that AP, shifted back by one, would be a monochromatic `vdwAP` for `c`,
contradicting the first-moment guarantee.  Hence `N ∉ monoAP_guarantee_set 2 k`,
and `not_in_guarantee_lt_sInf` gives `N < W k`. -/
theorem firstMoment_W_lower_bound {k N : ℕ} (hk : 2 ≤ k)
    (hNk : N * N < 2 ^ (k - 1)) : N < W k := by
  -- N = 0 is immediate: 0 < W k whenever the (nonempty) guarantee set excludes 0.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
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
  -- Main case: N > 0.
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc⟩ := vdw_lower_bound (n := N) hk hNk
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

/-- **Sharpened verified first-moment lower bound on `W`.**

If `N² < 2·(k-1)·2^(k-1)` and `k ≥ 2`, then `N < W k`.

This is the textbook first-moment bound: instead of the loose `n²` count of
length-`k` APs used by `firstMoment_W_lower_bound`, it consumes the sharpened
family count `2·(k-1)·|family| ≤ n²` (`card_vdwFamily_two_mul_le`, packaged as
`vdw_lower_bound_sharp`), which fits `≈ n²/(2(k-1))` APs.  The admissible range
of `N` therefore widens by a factor `√(2(k-1))`, giving the verified witness
`W(k) ≳ √(2(k-1))·2^((k-1)/2)`.

The bridging argument is identical to `firstMoment_W_lower_bound`: the only change
is feeding `vdw_lower_bound_sharp` (rather than `vdw_lower_bound`) at the start —
both produce the same `Fin N` colouring interface, so the transport to `{1,…,N}`
and the `not_in_guarantee_lt_sInf` step are unchanged. -/
theorem firstMoment_W_lower_bound_sharp {k N : ℕ} (hk : 2 ≤ k)
    (hNk : N ^ 2 < 2 * (k - 1) * 2 ^ (k - 1)) : N < W k := by
  -- N = 0 is immediate (independent of the count): 0 < W k.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    apply not_in_guarantee_lt_sInf
    intro hmem
    have hcontains : ContainsMonoAPofLength
        (fun _ : Finset.Icc 1 0 => (0 : Fin 2)) k := hmem _
    have hhas :
        HasMonoAP (extend_coloring 0 (fun _ : Finset.Icc 1 0 => (0 : Fin 2))) 0 k :=
      contains_mono_ap_imp 0 k (by omega) _ hcontains
    obtain ⟨a, d, _, ha1, han, _⟩ := hhas
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc⟩ := vdw_lower_bound_sharp (n := N) hk hNk
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
  have hMono : Mono (vdwAP N (a - 1) d k) c := by
    refine ⟨c ((Nat.cast (a - 1)) : Fin N), ?_⟩
    intro x hx
    simp only [vdwAP, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, hfi⟩ := hx
    have hidd : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    have hmem_i : a + i * d ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]; omega
    have hmem_a : a ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]; omega
    have hmi := hmono i hi
    rw [eval _ hmem_i, eval _ hmem_a] at hmi
    have hcc :
        c ((Nat.cast (a + i * d - 1)) : Fin N) = c ((Nat.cast (a - 1)) : Fin N) :=
      boolToFin2_injective hmi
    have hshift : a + i * d - 1 = a - 1 + i * d := by omega
    rw [hshift] at hcc
    rw [← hfi]
    exact hcc
  exact hc (a - 1) d (by omega) (by omega) hMono

/-- **Sharpened power-of-two corollary.** For `k ≥ 2`, `2^((k-1)/2) < W k`.

Strictly improves the loose corollary `firstMoment_W_pow_lower` (`2^((k-2)/2) < W k`)
— the exponent gains `1` for every odd `k` — and is the integer-exponent shadow of
the `√(2(k-1))·2^((k-1)/2)` witness.  Instantiate
`firstMoment_W_lower_bound_sharp` at `N = 2^((k-1)/2)`: then
`N² = 2^(2⌊(k-1)/2⌋) ≤ 2^(k-1) < 2·(k-1)·2^(k-1)` (the last step uses `k ≥ 2`,
so `2·(k-1) ≥ 2 > 1`). -/
theorem firstMoment_W_pow_lower_sharp {k : ℕ} (hk : 2 ≤ k) :
    2 ^ ((k - 1) / 2) < W k := by
  apply firstMoment_W_lower_bound_sharp hk
  have hsq : (2 ^ ((k - 1) / 2)) ^ 2 = 2 ^ ((k - 1) / 2 * 2) :=
    (pow_mul 2 ((k - 1) / 2) 2).symm
  rw [hsq]
  have hle : 2 ^ ((k - 1) / 2 * 2) ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  have hge : 2 * 2 ^ (k - 1) ≤ 2 * (k - 1) * 2 ^ (k - 1) := by
    gcongr
    omega
  omega

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
