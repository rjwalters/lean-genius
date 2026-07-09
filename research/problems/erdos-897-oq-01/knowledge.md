# Erdős #897 OQ-01 (Part I) — Knowledge Base

## Session 2026-07-08 (researcher-1) — built the missing Part-I scaffolding

**Discovery:** the research DB (`src/data/research/problems/erdos-897-oq-01.json`)
and registry marked this slug COMPLETED/graduated with a Lean file
`Erdos897OQ01.lean` and gallery entry `erdos-897-oq-01` — but NEITHER existed. Only
the parent's completely-additive reduction had ever landed (into
`Erdos897Problem.lean`, commits #28766/#35294). The specific Part-I deliverables the
DB described (logSqWeight witness, selectivity, strongly-additive reduction) were
never actually built. This session builds them for real.

**Delivered** (`proofs/Proofs/Erdos897OQ01.lean`, 214 L, 9 thm / 1 def, 0 axioms,
0 sorries, no native_decide):
- `logSqWeight n = ∑_{p|n} (log p)²`, proved additive AND strongly additive.
- `exists_additive_unboundedOnPrimePowers` — non-vacuity: the #897 hypothesis is
  satisfiable, so Part I is not vacuously true. (At k=1, (log p)² > M·log p for a
  prime p past exp M via `Nat.exists_infinite_primes`.)
- `not_unboundedOnPrimePowers_logN` / `not_unboundedOnPrimePowers_omega` —
  selectivity: log sits at the boundary (log(p^k)=log(p^k) exactly), ω is bounded
  (ω(p^k)=1); with M=2/log2 the ω inequality would force 1>2.
- `unboundedOnPrimePowers_unbounded` — hypothesis ⇒ plain unboundedness (M=(|B|+1)/log2).
- `stronglyAdditive_unboundedOnPrimePowers_iff` — reduction to f(p)/log p over primes;
  M≥0 drops the k≥1 factor, M<0 invokes the hypothesis at 0 (f(p)>0≥M·log p), reverse
  takes k=1.

**Gotchas:**
- The def `UnboundedOnPrimePowers` renders `Real.log (p^k)` as `Real.log ((↑p)^k)`
  (real power, since `Real.log_pow` applies) — so after `refine ⟨p,1,…⟩` use
  `simp only [pow_one]` (NOT a single `rw [pow_one]`, which only hits the ℕ `p^1`
  inside `f (p^1)` and leaves `Real.log (↑p ^ 1)` unsimplified → nlinarith fails).
- `omega` the parent def coexists with the `omega` tactic fine (term vs tactic position).
- `Real.log_le_log (0<x) (x≤y)`, `Real.log_lt_log`, `Real.log_nonneg`, `Real.log_pos`,
  `Nat.le_self_pow (k≠0) p : p ≤ p^k`, `Nat.le_ceil`, `hp.primeFactors = {p}`,
  `Nat.primeFactors_pow p (k≠0)` all current in v4.26.

**Status:** gallery entry now `verified`/`original`. Part I forward implication stays
OPEN (documented, not asserted).

## Session 2026-07-08b (researcher-1) — converse of (3) is false: Ω separates the notions

Re-served an already-completed slug (file/gallery existed, verified). Added a
**genuinely new** section (5) to `Erdos897OQ01.lean` sharpening theorem (3):

- `bigOmega_prime` : Ω(p)=1 for prime p (factor list [p]).
- `not_unboundedOnPrimePowers_bigOmega` : Ω FAILS the #897 hypothesis — via the
  parent's completely-additive reduction, would need Ω(p)=1 > M·log p ∀M; at
  M=1/log2 forces log p < log2, impossible for prime p≥2.
- `bigOmega_unbounded_on_primePowers` : yet Ω(2^k)=k is plainly unbounded.
- `unbounded_not_implies_unboundedOnPrimePowers` (headline) : ∃ additive f plainly
  unbounded on prime powers but failing the hypothesis ⟹ the converse of theorem
  (3) is FALSE; "unbounded on prime powers" ⊊ "unbounded relative to log".

File now 272 L, 13 thm / 1 def, 0 axioms, 0 sorries, no native_decide. VERIFIED
(exit-135 line-less crash on 1st build = infra, passed on retry).
Reused parent's `bigOmega_completelyAdditive` + `completelyAdditive_..._iff`.

## Session 2026-07-08 (researcher-2) — structure of the satisfier set (Section 6)

Prior sessions covered non-vacuity, selectivity (log/ω/Ω fail), the reduction, and the
failed converse. New direction: the *shape* of the set of functions satisfying
`UnboundedOnPrimePowers`. Added Section (6) (VERIFIED, [7744/7744], 0 axioms; one line-less
exit-135 SIGBUS on 1st build, green on retry):

- `not_unboundedOnPrimePowers_const_mul_logN (c)` — NO constant multiple of `log` satisfies
  the hypothesis (sharpens the c=1 `not_unboundedOnPrimePowers_logN`). Test at M=c: demands
  c·log(p^k) > c·log(p^k). So the hypothesis is genuinely *super-log*, not constant-factor.
- `unboundedOnPrimePowers_pos_smul (hc : 0<c)` — closed under positive scaling (a cone).
  Apply hf at M/c, scale witness by c. Proof gotcha: `rw [gt_iff_lt]` BEFORE `div_lt_iff₀`
  (else rw can't see the `_/c < _` pattern through `GT.gt`); use `show c*f(p^k) > M*Real.log
  ((p:ℝ)^k)` to beta-reduce the lambda-app goal.
- `unboundedOnPrimePowers_add_nonneg` — upward-closed under adding any g ≥ 0 on prime powers.
- `unboundedOnPrimePowers_logSqWeight_add_logN` — robustness corollary (logSqWeight+log still
  satisfies it).

★Cast gotcha (cost 1 build): the def's `Real.log (p^k)` elaborates to `Real.log ((↑p)^k)`
(real npow) NOT `Real.log ↑(p^k)`; `logN (p^k)` gives `Real.log ↑(p^k)`. Bridge with
`Nat.cast_pow` in simp (as `not_unboundedOnPrimePowers_logN` already does), and write goal
`show`s with `(p:ℝ)^k` to match. ★Also: this worktree was RESET mid-session (erdos-897 commit
wiped, HEAD bounced back to prior erdos-165 commit) — re-applied Section 6 from context.

File now 344 L, 17 thm / 1 def, 0 axioms, 0 sorries, no native_decide.
