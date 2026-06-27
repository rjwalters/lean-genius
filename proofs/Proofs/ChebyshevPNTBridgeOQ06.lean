/-
# Chebyshev–PNT Bridge OQ-06: From Chebyshev Θ-order Bounds toward the PNT Limit

> BUILD STATUS (2026-06-27): **UNVERIFIED — pending build.** The host Lean/Docker
> build toolchain was unavailable when this file was written (corrupted
> containerd store + a full host disk), so the proofs below could **not** be
> machine-checked this session. Every lemma name used has been cross-checked
> against the pinned Mathlib source, but the file must be compiled via
> `./proofs/scripts/docker-build.sh Proofs.ChebyshevPNTBridgeOQ06` and any
> tactic glitches fixed before it is treated as verified or added to the gallery.

The Prime Number Theorem (PNT) has three classical, *equivalent* analytic
normalizations (Apostol, *Introduction to Analytic Number Theory*, Ch. 4):

* `ψ(x) ~ x`        — von Mangoldt form, `ψ(x) = ∑_{n ≤ x} Λ(n)`;
* `θ(x) ~ x`        — Chebyshev form,    `θ(x) = ∑_{p ≤ x} log p`;
* `π(x) ~ x / log x` — prime-counting form.

The gallery already contains Chebyshev's *Θ-order* bounds — `π(x) = Θ(x/log x)`
(`ChebyshevPNTBridgeOQ05OQ01`) and explicit two-sided density constants. Those
order bounds are decisively *weaker* than PNT: Chebyshev's elementary method
pins the density between two positive constants but can never reach the sharp
limiting constant `1`. Reaching `1` is exactly the content of PNT, which is
**not** in Mathlib (there is no `ψ(x)/x → 1` and no `π(x) ~ x/log x`).

What *is* elementary, and what this file formalizes, is the **first half of the
bridge between the normalizations**: the von Mangoldt form `ψ` and the Chebyshev
form `θ` carry *identical* density asymptotics, because they differ only by the
prime-power correction, which Mathlib bounds by `2√x·log x = o(x)`.

## Results (Part 1, machine-checkable; pending build per the note above)

* **`tendsto_psi_sub_theta_div_zero`** — unconditionally `(ψ(x) − θ(x)) / x → 0`.
* **`tendsto_theta_div_iff_psi_div`** — the **ψ ⇔ θ PNT equivalence**: for every
  limit `L`, `θ(x)/x → L ↔ ψ(x)/x → L`.

The continuation (the `θ ⇔ π` half, which actually reaches `π(x)·log x`) is laid
out as design notes at the bottom rather than asserted, because its Finset /
cardinality bookkeeping could not be machine-checked this session.
-/
import Mathlib

namespace ChebyshevPNTBridgeOQ06

open Real Filter Topology Nat Chebyshev
open scoped Nat.Prime

/-! ═══════════════════════════════════════════════════════════════════════════
PART 1: The ψ ⇔ θ PNT equivalence

`ψ` and `θ` differ only by the prime-power correction `∑_{k ≥ 2} θ(x^{1/k})`,
which Mathlib's `abs_psi_sub_theta_le_sqrt_mul_log` bounds by `2√x·log x`.
Dividing by `x` sends this to `0`, so the two functions share *every* asymptotic
of the shape `f(x)/x → L`.
═══════════════════════════════════════════════════════════════════════════ -/

/-- `log x / √x → 0`: the logarithm grows slower than any positive power. -/
theorem tendsto_log_div_sqrt_zero :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
  rw [Real.sqrt_eq_rpow]

/-- **The ψ–θ gap is `o(x)`.** Unconditionally `(ψ(x) − θ(x)) / x → 0`, from
Mathlib's `|ψ(x) − θ(x)| ≤ 2√x·log x`. -/
theorem tendsto_psi_sub_theta_div_zero :
    Tendsto (fun x : ℝ => (ψ x - θ x) / x) atTop (𝓝 0) := by
  -- `g x = 2 · (√x · log x / x)` dominates `|(ψ x − θ x)/x|` and tends to `0`.
  have hg : Tendsto (fun x : ℝ => 2 * (Real.sqrt x * Real.log x / x)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have h2 : Tendsto (fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
      simpa using hc.mul tendsto_log_div_sqrt_zero
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hsne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
    have hxne : x ≠ 0 := ne_of_gt hx
    have hx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    have e : Real.sqrt x * Real.log x / x = Real.log x / Real.sqrt x := by
      field_simp
      linear_combination Real.log x * hx2
    rw [e]
  apply squeeze_zero_norm' _ hg
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpos, div_le_iff₀ hxpos]
  -- Goal: |ψ x − θ x| ≤ 2 · (√x · log x / x) · x; the RHS equals 2·√x·log x.
  calc |ψ x - θ x|
      ≤ 2 * Real.sqrt x * Real.log x := hbound
    _ = 2 * (Real.sqrt x * Real.log x / x) * x := by
        have hxne : x ≠ 0 := ne_of_gt hxpos
        field_simp

/-- **ψ ⇔ θ PNT equivalence.** For every limit `L`,
`θ(x)/x → L  ↔  ψ(x)/x → L`. In particular the von Mangoldt PNT and the
Chebyshev PNT are interchangeable. -/
theorem tendsto_theta_div_iff_psi_div (L : ℝ) :
    Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 L) ↔
    Tendsto (fun x : ℝ => ψ x / x) atTop (𝓝 L) := by
  constructor
  · intro h
    have hsum := tendsto_psi_sub_theta_div_zero.add h
    rw [zero_add] at hsum
    refine hsum.congr (fun x => ?_)
    ring
  · intro h
    have hsum := h.sub tendsto_psi_sub_theta_div_zero
    rw [sub_zero] at hsum
    refine hsum.congr (fun x => ?_)
    ring

end ChebyshevPNTBridgeOQ06

/-
═══════════════════════════════════════════════════════════════════════════════
CONTINUATION (design notes, not yet formalized): the `θ ⇔ π` half of the bridge
═══════════════════════════════════════════════════════════════════════════════

Reaching the prime-counting form `π(x)·log x` from `θ(x)` is elementary but its
Finset/cardinality bookkeeping was not machine-checked this session. The plan:

1.  LOWER inequality (`θ(n) ≤ π(n)·log n`).
      θ(n) = ∑_{p ≤ n, p prime} log p ≤ ∑_{p ≤ n} log n = π(n)·log n,
    since each of the `π(n)` primes `p ≤ n` has `log p ≤ log n`.
    Lean ingredients (all confirmed present in the pinned Mathlib):
      • `Chebyshev.theta_eq_sum_Icc`, `Nat.floor_natCast`
      • `Finset.sum_le_sum`, `Finset.sum_const`, `nsmul_eq_mul`
      • `Real.log_le_log`, `Real.log_nonneg`, `mul_le_mul_of_nonneg_right`
      • card identity `#{p ∈ Icc 0 n | p.Prime} = π(n)` via
        `Nat.primesBelow_card_eq_primeCounting'` + `Nat.mem_primesBelow`
        (`primeCounting n` is defeq `primeCounting' (n+1)`).
    Consequence: `θ(n)/n ≤ π(n)·log n / n`, so under the von Mangoldt PNT
    (Part 1 transfers `ψ(x)/x → 1` to `θ(x)/x → 1`), `liminf π(n)·log n / n ≥ 1`
    — the sharp Chebyshev *lower* density constant `1`.

2.  UPPER inequality (`π(n)·log n ≤ θ(n)/α + n^α·log n`, any `0 < α < 1`).
      For `n^α < p ≤ n`, `log p > α·log n`, so
        θ(n) ≥ ∑_{n^α < p ≤ n} log p ≥ α·log n·(π(n) − π(n^α)),
      and `π(n^α) ≤ n^α`. Hence `π(n)·log n ≤ θ(n)/α + n^α·log n`.

3.  SHARP limit. If `θ(x)/x → 1` then for each fixed `α < 1`,
      limsup π(n)·log n / n ≤ 1/α,
    and taking `α → 1⁻` gives `limsup ≤ 1`. With step 1's `liminf ≥ 1` this
    yields the full PNT prime-counting form `π(n)·log n / n → 1`.

So PNT-for-π reduces *entirely* to PNT-for-ψ by elementary means (steps 1–3);
the irreducible deep input — a proof that `ψ(x)/x → 1` at all — is exactly what
Chebyshev's order bounds cannot supply and what Mathlib still lacks.
-/
