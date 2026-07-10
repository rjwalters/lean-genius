# Knowledge Base: erdos-1014-oq-03

Asymptotics of the consecutive off-diagonal Ramsey increment Δ_l(k) = R(k,l+1) − R(k,l).

---

## Session 2026-07-09 (researcher-8) — increment–ratio bridge [VERIFIED]

**Mode**: FRESH (iteration 1, OBSERVE → ACT). **Outcome**: progress
(new file `Erdos1014OQ03.lean`, 3 theorems, **VERIFIED [7743] 0 sorry / 0 axiom**).

### Key mathematical finding (corrects the problem's proposed Approach A)
The problem statement's "Approach A" proposes deriving the increment asymptotic from a power
law `R(k,l) ~ c_k·l^{k-1}/(log l)^{k-2}` by expanding `Δ_l = R(l)·((l+1)/l)^{k-1}(1+o(1)) − R(l)`.
**This is invalid from asymptotic equivalence alone.** A sequence's consecutive difference is
NOT determined by its `~`-equivalence class: `u_l = l²` and `v_l = l² + l·sin l` satisfy `u ~ v`
but `u_{l+1}−u_l = 2l+1` while `v`'s increment oscillates at order `l`. The expansion secretly
assumes the *ratio* asymptotic `R(l+1)/R(l) → ((l+1)/l)^{k-1}`, which does not follow from
`R(l) ~ g(l)`. A rigorous increment statement must hypothesize the ratio (or regular
variation / monotonicity) directly. **So the "tractable target" as written needs a stronger
hypothesis than stated.**

### What I proved (unconditional, self-contained, no Ramsey import)
The correct bridge that IS valid:
- `increment_div_eq_ratio_sub_one` — `(R(l+1) − R(l))/R(l) = R(l+1)/R(l) − 1` (algebraic engine,
  `rw [sub_div, div_self h]`).
- `increment_div_tendsto_zero_iff_ratio_tendsto_one` — for eventually-nonzero `R`, the
  normalized increment `→ 0` **iff** the consecutive ratio `→ 1`. Proof: the two functions are
  eventually equal (via the identity), `tendsto_congr'`, then `Tendsto.add_const/​sub_const`.
- `increment_div_tendsto_zero_of_ratio_tendsto_one` — forward corollary.

**Payoff.** Fed Erdős #1014's proven ratio-convergence `R(k,l+1)/R(k,l) → 1`, the bridge yields
the rigorous, hypothesis-free increment consequence `Δ_l(k) = o(R(k,l))` — the honest bridge
from #1014 to increment behavior, sidestepping the invalid power-law expansion.

### Still open
The full increment asymptotic `Δ_l(k) ~ g_k(l)` (conjecturally `~ c·l/log l` for `k=3`) remains
OPEN — it requires a genuine ratio/regular-variation hypothesis on `R(k,·)`, not obtainable from
the `~` asymptotic alone, and is entangled with the still-open matching of the `Θ(l²/log l)`
constants for `R(3,l)`.

### Files
- `proofs/Proofs/Erdos1014OQ03.lean` (new, 95 lines, 3 theorems, 0 sorry / 0 axiom)
- `src/data/research/problems/erdos-1014-oq-03.json` (leanFiles + knowledge)
