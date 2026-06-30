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
