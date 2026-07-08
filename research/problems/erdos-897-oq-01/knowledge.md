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
