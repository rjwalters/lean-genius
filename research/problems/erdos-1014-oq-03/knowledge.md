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

## Session 2026-07-09 (researcher-3) — log-increment smoothness bridge (UNVERIFIED)

New companion `proofs/Proofs/Erdos1014OQ03LogIncrement.lean` (namespace
`Erdos1014OQ03Log`, imports `Erdos1014OQ03`). Adds the **log-increment**
`Λ_l(k) = log R(k,l+1) − log R(k,l)` as the natural smoothness measure raised in
OQ-03's open questions:

- `log_increment_eventuallyEq_log_ratio`: `log R(l+1) − log R(l) = log(R(l+1)/R(l))`
  eventually (for eventually-positive `R`; `Real.log_div`).
- `logIncrement_tendsto_zero_iff_ratio_tendsto_one`: log-increment → 0 ⟺ ratio → 1
  (continuity of `log` at 1 forward; `exp ∘ log = id` on positives backward).
- `logIncrement_tendsto_zero_iff_increment_div_tendsto_zero`: three-way equivalence
  chaining the parent's normalized-increment bridge — log-increment → 0 ⟺
  normalized increment → 0.
- `logIncrement_tendsto_zero_of_ratio_tendsto_one`: fed #1014's ratio → 1, the
  Ramsey increment is asymptotically log-flat.

0 axioms, 0 sorries, no native_decide. The full asymptotic for Δ_l(k) stays OPEN.

### Verification status: VERIFIED
Clean Docker build `✔ [7744/7744] Built Proofs.Erdos1014OQ03LogIncrement (3.3s)`,
0 axioms / 0 sorries. It took 11 attempts to get a green olean write: a heavy
fleet **SIGBUS-135/139** storm plus intermittent shared-Mathlib-cache corruption
(code-1 `invalid header` on dependency oleans: `NumberTheory/RamificationInertia/
Basic`, `Algebra/Homology/Square.ir`, `Tactic/Basic.olean.server`) blocked the
write on attempts 1–10 — all pure infra at the `import Mathlib` line or the final
write, never math/type errors (every reachable run elaborated the file in ~1–3 s
with zero errors). Attempt 11 landed a fully green write.

## Session 2026-07-19 (researcher-1) — FIRST v4.31 machine verification + warning cleanup

Every prior OQ03 session shipped UNVERIFIED (docker infra down, hand-audit only). This
session gave the family its first real build-check under the v4.31 toolchain: all four files
— `Erdos1014OQ03.lean` (main, 806L, Mathlib-only), `Erdos1014OQ03Concrete`, `...LogIncrement`,
`...Obstruction` — compile **clean** (0 errors, 0 warnings after cleanup), 0 sorries / 0 axioms,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. Verified host-side:
`LEAN_PATH=<main-basepath> lake env lean` for the Mathlib-only main file, and companions against
freshly-built v4.31 dep oleans (Erdos1014Problem + Erdos1014OQ03).

Cleared 3 warnings for a clean re-verify:
- main `Erdos1014OQ03.lean:354`: `tendsto_finset_prod` → `tendsto_finsetProd` (v4.31 deprecation).
- `Obstruction.lean:96`: dropped unused simp arg `Real.norm_natCast`.
- `Obstruction.lean:169`: `rcases … <;> rw [h] <;> norm_num` (seq-focus linter) → explicit bullets
  `· norm_num [h]` (rw closed one branch, so the sequential norm_num had no goals; norm_num [h]
  is robust to the variable goal count).

The full increment asymptotic `Δ_l(k) ~ g_k(l)` remains genuinely OPEN (needs a
regular-variation/Karamata sufficient condition + the R(3,l) constant matching — see
`Obstruction.lean`); not session-sized. Elementary-bridge + closure-property theory is complete.
