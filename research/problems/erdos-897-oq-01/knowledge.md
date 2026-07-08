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
