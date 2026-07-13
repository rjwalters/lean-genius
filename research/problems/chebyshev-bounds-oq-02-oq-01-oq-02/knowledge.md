# Knowledge: chebyshev-bounds-oq-02-oq-01-oq-02

**Target**: `θ(x) = Θ(x)` — transfer the parent's `ψ(x) = Θ(x)` to the first Chebyshev function.
Formalized as `θ =Θ[atTop] (fun x => x)`.

## Summary

Complete elementary proof drafted (`proofs/Proofs/ChebyshevBoundsOQ02OQ01OQ02.lean`, 10 theorems,
no `sorry`, no `axiom`; depends only on `Mathlib` + the parent `ChebyshevBoundsOQ02OQ01`). The proof
is **not yet machine-verified** — the shared Docker build environment was saturated (5 concurrent
`lean-build` containers, host disk 99% / ~10 GiB free) throughout the session, and Aristotle's MCP
endpoint returned `Resource not found`. All Mathlib lemma names were checked against the pinned
Mathlib source, and every tactic step was hand-audited. **Next session: build when
`docker ps | grep lean-build` is empty, then upgrade status to `verified` and add gallery data.**

## Session 2026-07-01 (Session 1) — FRESH → ACT

**Mode**: FRESH
**Outcome**: progress (complete unverified proof)

### What I Did
- Surveyed the rich `chebyshev-*` gallery ecosystem; confirmed the two load-bearing Mathlib facts
  `Chebyshev.theta_le_psi` and `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` exist, plus the real
  bound `Chebyshev.psi_le_const_mul_self : ψ x ≤ (log 4 + 4)·x`.
- Confirmed the parent `ChebyshevBoundsOQ02OQ01` exports `chebyshevPsi_lower_linear`
  (`(log 2/3)·n ≤ chebyshevPsi n` for `n ≥ 2`), `chebyshevPsi_eq_psi`, and `chebyshevPsi_mono`.
- Designed and wrote the full transfer proof (see Key Findings).
- Verified every non-trivial Mathlib lemma name against the pinned source:
  `Filter.Tendsto.eventually_le_const`, `Filter.Tendsto.const_mul`, `Real.mul_self_sqrt`,
  `Nat.le_floor`, `Nat.lt_floor_add_one`, `div_le_iff₀`, `le_div_iff₀`, `div_mul_eq_mul_div`,
  `Asymptotics.isLittleO_iff` / `isBigO_iff`, `Chebyshev.{psi,theta}_nonneg`,
  `Chebyshev.psi_eq_sum_Icc`, `Nat.floor_natCast`.

### Key Findings (proof structure)
1. **Upper bound** `theta_le_linear` : `θ(x) ≤ (log 4 + 4)·x` for `x ≥ 0` — one line:
   `(theta_le_psi x).trans (psi_le_const_mul_self hx)`.
2. **Floor bridge** `psi_eq_chebyshevPsi_floor` : `ψ(x) = chebyshevPsi ⌊x⌋₊`, since both unfold to
   `∑_{n ∈ Icc 0 ⌊x⌋₊} Λ n` (via `psi_eq_sum_Icc` + `Nat.floor_natCast`).
3. **Real lower bound** `psi_ge_linear` : `(log 2/6)·x ≤ ψ(x)` for `x ≥ 2`. Set `n := ⌊x⌋₊ ≥ 2`;
   parent gives `(log 2/3)·n ≤ chebyshevPsi n = ψ x`; `n ≥ x − 1 ≥ x/2` gives the factor.
4. **`o(x)` correction** `two_sqrt_mul_log_isLittleO` : `2√x·log x = o(x)`, from `log x/√x → 0`
   (`log_div_sqrt_tendsto_zero`, inlined from the verified sibling OQ-03), rearranging
   `2√x·log x / x = 2 log x/√x` via `√x·√x = x`.
5. `two_sqrt_mul_log_le_eventually` : eventually `2√x·log x ≤ (log 2/12)·x`.
6. **Eventual lower bound** `theta_ge_eventually` : eventually `(log 2/12)·x ≤ θ(x)`, from
   `θ = ψ − (ψ − θ) ≥ ψ − |ψ − θ| ≥ (log 2/6)x − 2√x log x ≥ (log 2/12)x`.
7. `theta_isBigO_id` (`θ = O(x)`), `id_isBigO_theta` (`x = O(θ)`, constant `12/log 2`), and the
   capstone `theta_isTheta_id` : **`θ =Θ[atTop] (fun x => x)`**.

### Gotchas Found During Self-Review
- `positivity` **cannot** prove `0 ≤ 2·√x·log x` (sign of `log x` unknown) — replaced with
  `mul_nonneg (mul_nonneg _ hsqrt_pos.le) hlogx` under the `x ≥ 1` hypothesis.
- In `two_sqrt_mul_log_le_eventually`, do **not** strip the LHS `|·|`; use
  `le_abs_self (2√x log x)` so no `log`-sign hypothesis is needed there.
- Ended `two_sqrt_mul_log_isLittleO` with an explicit `calc` (× `√x` then `√x·√x = x`) rather than
  a fragile `nlinarith` over a triple product.

### Files Modified
- `proofs/Proofs/ChebyshevBoundsOQ02OQ01OQ02.lean` (new, complete, unverified)
- `research/problems/chebyshev-bounds-oq-02-oq-01-oq-02/{problem.md, state.md, knowledge.md}`

### Next Steps
- Build `Proofs.ChebyshevBoundsOQ02OQ01OQ02` via `./proofs/scripts/docker-build.sh` when the
  build host is idle; fix any residual tactic issues; run `#print axioms theta_isTheta_id`
  (expect only `propext`, `Classical.choice`, `Quot.sound`).
- On success: mark `status: "verified"`, `axiomCount: 0`, add gallery `meta.json` + annotations.
- Optional follow-up OQ: explicit two-sided `θ` bounds `(log 2/6)m − 2√m log m ≤ θ(m) ≤ (log 4)m`
  (the sibling OQ-02-OQ-01-OQ-01, currently unformalized).
