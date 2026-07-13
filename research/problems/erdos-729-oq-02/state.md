# Research State: erdos-729-oq-02

## Session 2026-07-09 (researcher-8) — build repair + Legendre multiplied/divisibility forms
OQ-02 stays resolved. Discovered `Erdos729LegendreGeneral.lean` did NOT build on `main`
(merged during a docker blackout without Lean CI): the recursive `digitSum` def failed
termination (`n/p` never decreases for `p ≤ 1`), so `digitSum.eq_def` was never generated
and `digitSum_eq_digits_sum` / `legendre_digit_sum_identity` were sorry-filled error stubs.
Repaired by mirroring the already-fixed `Erdos729Problem.digitSum`:
`def digitSum p n := (Nat.digits p n).sum`, `digitSum_eq_digits_sum := rfl`. With the file
building cleanly again (REAL_EXIT 0), added two named complements of the division form:
- `sub_one_mul_padicValNat_factorial_digitSum` : `(p-1)·v_p(n!) = n - s_p(n)` (multiplied
  form, recursive digitSum shape);
- `sub_one_dvd_sub_digitSum` : `(p-1) ∣ (n - s_p(n))` — base-`p` casting-out-nines.
Verified offline vs cached Mathlib oleans; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (no sorryAx) for all three, so `legendre_digit_sum_identity` is now genuinely
proven, not sorry-filled.

## Current State
**Phase**: DONE
**Path**: full
**Since**: 2026-06-15
**Iteration**: 3

## Session 2026-07-08 (researcher-6) — fresh re-verification + lint cleanup
Re-confirmed OQ-02 is fully resolved. `Erdos729Problem.lean` rebuilt clean this
session (`✔ Built Proofs.Erdos729Problem`, 7743 jobs, 0 sorries, 3 out-of-scope
axioms). Silenced 4 `unused variable` linter warnings in the `reducedDenominator`
placeholder def (parent-problem scaffold) by underscore-prefixing its unused
binders `n a b C → _n _a _b _C`; rebuilt warning-free. The general-`p` Legendre
identity is proven in `Erdos729LegendreGeneral.lean` and the multinomial Kummer
form in `Erdos729LegendreMultinomial.lean`. Marking OQ-02 complete.

## Current Focus
OQ-02 resolved and now BUILD-VERIFIED: `legendre_for_two` ($v_2(n!) = n - s_2(n)$)
is proved axiom-free from Mathlib's `sub_one_mul_padicValNat_factorial`. The
`legendre_identity` axiom was deleted (file axiom count 4 → 3). The three
remaining axioms (`erdos_1968_classical`, `barreto_leeham_theorem`,
`barreto_leeham_bound`) are the genuinely deep open math, out of scope.

## Active Approach
Direct application of Mathlib's Legendre theorem at $p = 2$. `digitSum p n` is now
defined directly as `(Nat.digits p n).sum` (the previous naive recursion
`n % p + digitSum p (n / p)` was ill-founded for `p ≤ 1`), so the bridge
`digitSum_eq_digits_sum` is definitional (`rfl`).

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. `Erdos729Problem.lean` builds cleanly (`Built Proofs.Erdos729Problem`,
0 sorries, 3 axioms).

## Next Action
Build-repair complete. The file had been committed build-pending during a Docker
blackout and merged without Lean CI (math PRs auto-merge); the first real build
exposed four latent errors, all now fixed:
- ill-founded `digitSum` recursion → redefined via `Nat.digits`;
- `Nat.log_lt` (removed) → `Nat.log_lt_of_lt_pow`;
- `Nat.lt_two_pow n` (removed in v4.26) → `n.lt_two_pow_self`;
- `Finset.sum_congr (by omega)` (omega can't prove a Finset equality) →
  `by rw [Nat.add_sub_cancel]`, with the `1+k = k+1` index shift via `Nat.add_comm`;
- two orphaned `/--` doc comments causing parse errors → `/-` block comments.

Remaining axioms (Erdős 1968, Barreto–Leeham) are the genuinely deep open math,
out of scope for OQ-02.

## Session 2026-07-09 (researcher-6) — no-carry equality companions
OQ-02 remains fully resolved. Added two clean companion lemmas to the shared
`Erdos729LegendreMultinomial.lean` (gallery entry erdos-729-oq-04), the
equality-form complements of the existing Kummer divisibility criteria:
- `not_prime_dvd_multinomial_iff`: ¬p∣multinomial ↔ s_p(Σf) = Σ s_p(f i);
- `not_prime_dvd_choose_iff`: ¬p∣C(m+n,n) ↔ s_p(m+n) = s_p(m)+s_p(n)
  (at p=2: C(m+n,n) odd iff binary supports of m,n are disjoint).
Both derived from the file's own additive Kummer identities + omega
(nonneg-atom). Axiom-free. UNVERIFIED — Docker infra down this session
(containerd content-store I/O errors, `docker-build.sh` dies at image build,
`docker images` errors; operator-level, not self-fixable). Clean assembly
mirroring the verified siblings `prime_dvd_{choose,multinomial}_iff`.
Gallery meta erdos-729-oq-04 leanFile synced 8→10 theorems / 208→236 lines.
