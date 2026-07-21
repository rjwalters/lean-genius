# Knowledge Base: erdos-98-wip-01

## Session 2026-07-20 (researcher-1) — h(n)→∞ is UNCONDITIONAL (Guth–Katz baseline)

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound):

- `tendsto_const_mul_div_log_atTop` — `c·n/log n → ∞` for `c>0`. Path: `Real.isLittleO_log_id_atTop`
  ∘ `tendsto_natCast_atTop_atTop` ⟹ `log n =o n` ⟹ `log n / n → 0` (`IsLittleO.tendsto_div_nhds_zero`);
  eventually positive (`Real.log_pos`, n≥2) ⟹ `→ 𝓝[>]0` ⟹ reciprocal `→ atTop`
  (`Filter.Tendsto.inv_tendsto_nhdsGT_zero`); `inv_div` + `const_mul_atTop`.
- `guthKatz_imp_tendsto` — `GuthKatzBaseline ⟹ Tendsto h atTop atTop`. The imported (proven)
  Ω(n/log n) lower bound `c·n/log n ≤ h(n)` + the divergence above ⟹ `(h n:ℝ)→∞`
  (`tendsto_atTop_mono'`), then descend to ℕ (`Filter.tendsto_atTop.mpr` + `exact_mod_cast`).

KEY POINT: this sharpens the existing `weak_imp_tendsto`, which derived the SAME divergence
`h(n)→∞` from the OPEN weak conjecture. In fact the divergence is a THEOREM (unconditional,
from Guth–Katz). What genuinely remains open is only the RATE — `h(n)/n→∞` (strong) and
`h(n)≥n` (weak).

### Remaining open
- `h n ≤ n.choose 2` needs a general-position existence witness for all n (constructive, missing).
- Parent Erdős #98 (`h(n)/n→∞`) remains OPEN in mathematics.

## Session 2026-07-21 (researcher-1) — unconditional upper bound h(n) ≤ n.choose 2

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (theoremCount 10→12, host-verified
v4.31 via fresh parent olean + `lake env lean`, exit 0; `#print axioms` =
propext/Classical.choice/Quot.sound on both):

- `h_le_choose_two (n) : h n ≤ n.choose 2` — **resolves the open item** flagged last
  session ("`h n ≤ n.choose 2` needs a general-position existence witness"). The witness
  is *not* needed: split on whether the defining set
  `{numDistinctDistances P | InGeneralPosition P}` is empty. Nonempty ⟹
  `h n ≤ numDistinctDistances P ≤ n.choose 2` (`h_le_of_inGeneralPosition` +
  `numDistinctDistances_le_choose_two`). Empty ⟹ `h n = sInf ∅ = 0 ≤ n.choose 2`
  (`Nat.sInf_empty`). Combined with the unconditional divergence `guthKatz_imp_tendsto`,
  the minimum is now sandwiched: `h n → ∞` yet `h n ≤ n.choose 2` for every n.
- `h_eq_zero_of_le_one (n≤1) : h n = 0` — concrete degenerate values, since
  `n.choose 2 = 0` there (`Nat.choose_eq_zero_of_lt`) caps `h n` at 0.

### Note on honesty
`h_le_choose_two` is vacuous in the (believed-impossible for ℝ²) empty regime; its real
content is the nonempty branch. Proving general-position configs exist for all n
(`Injective ∧ NoThreeCollinear ∧ NoFourConcyclic`) remains the missing constructive piece
and the genuine next target — it would make `h n` a true minimum over a nonempty set.

### Remaining open (UNCHANGED)
Existence of general-position configurations for all n (constructive); parent Erdős #98
(`h(n)/n → ∞`, and even the weak `h(n) ≥ n`) remains OPEN in mathematics.
