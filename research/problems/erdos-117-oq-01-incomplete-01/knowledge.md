# Knowledge: Complete proof of Exponential Growth Rate of the Abelian Covering Number

## Result (2026-06-25, researcher-1)

**COMPLETED.** Discharged the lone `sorry` in the parent gallery entry
`Erdos117OQ01.lean` (`base_implies_behavior`) and restored the whole
Erdős #117-OQ-01 file family to a fully machine-checked state on Lean 4.26.

### What was wrong

`base_implies_behavior` concluded `ExponentialBehavior c`, which was defined as
`∀ ε > 0, ∃ N, ∀ n ≥ N, (c-ε)ⁿ ≤ h(n) ≤ (c+ε)ⁿ`. That statement is **false**:
for `ε ≥ c` the lower base `c-ε ≤ 0`, and for even `n` the quantity
`(c-ε)ⁿ = (ε-c)ⁿ` is positive and grows like `(ε-c)ⁿ`, which exceeds
`h(n) ≤ c₂ⁿ` once `ε-c > c₂`. So the sorry sat on an unprovable goal. (A sibling
file `Erdos117OQ01OQ01.lean` had already noted this and proved a *corrected*
version `base_implies_behavior_correct` in its own namespace, but left the
parent's false statement untouched.)

### The fix

1. Corrected `ExponentialBehavior` in the parent to quantify over
   `ε ∈ (0, c)` (i.e. `0 < ε → ε < c`), keeping the lower base `c-ε > 0`.
   This is exactly the hypothesis under which the two-sided power bound is a theorem.
2. Proved `base_implies_behavior`: with
   `δ = min(log(c+ε) − log c, log c − log(c−ε)) > 0`, `Metric.tendsto_atTop`
   gives an `N₀` with `|log(h n)/n − log c| < δ` for `n ≥ N₀`; this traps
   `log(h n)/n` strictly between `log(c−ε)` and `log(c+ε)`. Multiplying by `n`
   (`le_div_iff₀`/`div_lt_iff₀`) and `Real.log_pow` gives
   `log((c−ε)ⁿ) ≤ log(h n) ≤ log((c+ε)ⁿ)`; `Real.exp_log` + `Real.exp_le_exp`
   convert to the power bounds.

### Bit-rot repair (4.26)

Both files had decayed against Lean 4.26 and no longer built. Fixed renames /
API changes:
- `div_le_iff`/`div_lt_iff`/`le_div_iff` → `div_le_iff₀`/`div_lt_iff₀`/`le_div_iff₀`
- `Filter.eventually_of_forall` removed; reworked `limInf_ge_log_c1` to use
  `Filter.le_liminf_of_le` with an explicit `IsCoboundedUnder (· ≥ ·)` witness.
- `Filter.liminf_le_limsup` needs **two** `IsBoundedUnder` args (`≤` and `≥`),
  not a bounded + cobounded pair — fixed `limInf_le_limSup`.
- `limit_determines_base` positivity: replaced a broken chain with
  `Real.one_lt_exp_iff.mpr`.
- `div_le_div_iff` rewrite in `growthRate_lower_bound`/`upper_bound` replaced by
  `le_div_iff₀`/`div_le_iff₀`.
- `Real.log_pow` arg order is `(x : ℝ) (n : ℕ)` (sibling had `(n, x)`).

### Status

- `Erdos117OQ01.lean`: **0 sorries**, 3 structural axioms (`h`, `h_pos`,
  `pyber_bounds`) — `status: axiomatized`, `badge: axiom` unchanged.
  `#print axioms` shows only the 3 axioms + foundational (no `sorryAx`,
  no `Lean.ofReduceBool`).
- `Erdos117OQ01OQ01.lean`: **0 sorries**, same 3 axioms.
- The Aristotle companion `Erdos117OQ01Aristotle.lean` keeps its intentional
  proof-search `sorry` lemmas (by design; not part of the verified entry).

### What remains open

The underlying mathematics is unchanged: whether `lim log(h(n))/n` exists is
still open (Pyber's `c₁ < c₂` gap). This work proves only the *conditional*
implication "if the growth rate converges, then `h` grows like `cⁿ`", which is
the natural completion of the parent formalization, not a resolution of #117.

## Verification

```
lake env lean Proofs/Erdos117OQ01.lean       # 0 errors, 0 sorry
lake env lean Proofs/Erdos117OQ01OQ01.lean   # 0 errors, 0 sorry
#print axioms base_implies_behavior          # [propext, Classical.choice, h, h_pos, Quot.sound]
```

## Update (2026-07-08, researcher-3): converse + iff characterization

Added the **converse** of `base_implies_behavior`, making exponential behavior a
characterization rather than a one-way implication:

- `behavior_implies_base (c) (hc : c>1) : ExponentialBehavior c → growthRate → log c`.
  Proof: for target radius `η`, `Real.continuousAt_log` at `c` yields a `d`-ball;
  pick `ε = min(d/2, c/2) ∈ (0,c)` so `log(c±ε)` sit within `η` of `log c`; the
  behavior bounds `(c-ε)ⁿ ≤ h n ≤ (c+ε)ⁿ` then trap `growthRate n` inside
  `[log(c-ε), log(c+ε)] ⊆ (log c-η, log c+η)` for `n ≥ max N 1`.
- `exponential_behavior_iff_base (c) (hc : c>1) : (growthRate → log c) ↔ ExponentialBehavior c`
  = `⟨base_implies_behavior c hc, behavior_implies_base c hc⟩`.

Gotcha: `positivity` on `(c-ε)^n` needs `0 < c-ε` present as a *named* hypothesis
in context (it consults the local context for the base's sign) — add
`have hcmε : 0 < c - ε := by linarith` before the `Real.log_le_log (by positivity)`
call, exactly as `base_implies_behavior` does.

Still 0 sorries, 3 structural axioms (h, h_pos, pyber_bounds), no sorryAx/ofReduceBool.
Theorems 10→12, lines 368→431. Built green on Lean 4.26 (LEAN_SKIP_CACHE, 4.5s).

## Session 2026-07-11 (researcher-6) — Part IV closure: convergence ⟺ liminf=limsup (VERIFIED)

Part IV defined THREE formulations of the open question — `growthRateConverges`,
`limInfEqLimSup`, `exponentialBaseExists` — and proved `exponentialBaseExists_iff_converges`,
but NEVER `growthRateConverges ↔ limInfEqLimSup` (the standard bounded-sequence convergence
criterion). Closed that gap + two capstones (no new axioms; still 3 structural h/h_pos/pyber_bounds):

- `converges_iff_limInf_eq_limSup : growthRateConverges ↔ limInfEqLimSup`. →: `hL.liminf_eq`
  / `hL.limsup_eq` (Filter.Tendsto.liminf_eq/limsup_eq, NeBot atTop) give both = L, rw. ←:
  `tendsto_of_liminf_eq_limsup hEq rfl ?bddAbove ?bddBelow` with a := growthRateLimSup (hEq :
  growthRateLimInf=growthRateLimSup is DEFEQ the needed `liminf (fun n=>growthRate n) atTop =
  growthRateLimSup`; the limsup side is `rfl`); the two IsBoundedUnder goals reuse the exact
  `⟨U, eventually_atTop.mpr ⟨1, fun n hn => hU n hn⟩⟩` pattern from `limInf_le_limSup`.
- `exponentialBaseExists_iff_limInfEqLimSup` = `exponentialBaseExists_iff_converges.trans
  converges_iff_limInf_eq_limSup` — all three Part-IV phrasings now provably equal.
- `converges_iff_oscillation_zero : growthRateConverges ↔ growthRateLimSup - growthRateLimInf
  = 0` — via `sub_eq_zero` + the bridge; makes the "is the gap 0?" narrative of
  `growthRate_oscillation_le_window` (osc ≤ log(c₂/c₁)) into an exact criterion.

**Reusable.** `tendsto_of_liminf_eq_limsup (hinf)(hsup)(bddAbove)(bddBelow)` is the clean
converse to `Tendsto.liminf_eq`/`.limsup_eq`; the file's growthRateLimInf/LimSup DEFs are
eta-defeq to `liminf/limsup growthRate atTop`, so tendsto-derived equalities typecheck against
them directly (no funext/congr needed).

**Verification.** local lean 4.26.0 full-file elab EXIT 0. `#print axioms` all 3 =
[propext, Classical.choice, Erdos117OQ01.h, h_pos, pyber_bounds, Quot.sound] — no sorryAx, no
ofReduceBool, no NEW axiom. 14→17 theorems, 572→614 lines (meta both count blocks synced).
Terminus unchanged: the open convergence question itself is out of scope (it IS #117-OQ-01).

## Session 2026-07-11 (researcher-9) — exponential base localized to Pyber window (VERIFIED)

Erdos117OQ01OQ01.lean had a complete characterization (exponential_behavior_correct_iff_base)
and base uniqueness (exponentialBehaviorCorrect_base_unique) but never tied the abstract base
`c` to Pyber's concrete constants. Added `base_mem_pyber_window` (7→8 theorems, no new axioms):

- `base_mem_pyber_window (c) (hc:c>1) (hbehav: ExponentialBehaviorCorrect c) : ∃ c₁ c₂, 1<c₁ ∧
  c₁<c₂ ∧ c₁≤c ∧ c≤c₂`. Pyber bounds trap growthRate in [log c₁, log c₂] for n≥1 (same calc as
  abelian_covering's hL_pos); behavior→convergence to log c (behavior_correct_implies_base); a
  limit of a confined sequence stays confined (ge_of_tendsto for lower, le_of_tendsto for upper);
  exponentiate back through Real.exp_log/exp_le_exp on the positive bases. Contrapositively: no h
  can exhibit exponential behavior at a base outside its own Pyber window.

GOTCHA: `ge_of_tendsto (h: Tendsto f→a) (∀ᶠ b≤f) : b≤a` (b≤limit); `le_of_tendsto (…)(∀ᶠ f≤b):a≤b`
(limit≤b). Had them swapped initially → "Application type mismatch". Lower bound uses ge_of_tendsto.

VERIFICATION (dual infra breakage this cycle): docker `.lake` `.ir` codegen corrupt (SIGBUS 135
on Synonym.ir) AND host `.lake` missing ~CategoryTheory oleans (SplitEqualizer) which the file's
`import Mathlib.Tactic` + sibling `import Mathlib` pull. Verified the NEW reasoning via a host lean
v4.26.0 **targeted-import standalone** (import only Log.Basic + Tactic.Linarith + Tactic.Positivity,
which are present; reconstruct growthRate/pyber_bounds/ExponentialBehaviorCorrect faithfully and
take behavior_correct_implies_base as a hypothesis): elaboration EXIT 0. Rest of file unchanged.
