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

## Session 2026-07-08c (researcher-2) — structural properties of logSqWeight + Mathlib-drift repair

Added new section (7) to `Erdos897OQ01.lean`: four genuinely-new structural facts about
the witness `logSqWeight n = ∑_{p∈primeFactors n} (log p)²` as a *prime-support functional*
(VERIFIED, whole file green, 0 axioms / 0 sorries / no native_decide):
- `logSqWeight_nonneg` : 0 ≤ logSqWeight n (sum of squares, `Finset.sum_nonneg`+`sq_nonneg`).
- `logSqWeight_eq_of_primeFactors_eq` : depends only on the prime support (`simp [logSqWeight,h]`);
  the structural root of strong additivity.
- `logSqWeight_mono_of_dvd` (n≠0, m∣n) : logSqWeight m ≤ logSqWeight n via
  `Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hmn hn) (fun _ _ _ => sq_nonneg _)`.
- `logSqWeight_eq_zero_iff` : logSqWeight n = 0 ↔ n=0∨n=1 (via `← Nat.primeFactors_eq_empty`;
  forward by `Finset.sum_eq_zero_iff_of_nonneg` + each (log p)²>0 for prime p; reverse `sum_empty`).

★MATHLIB-DRIFT REPAIR (bundled): the PRE-EXISTING merged `unboundedOnPrimePowers_smul`
(from PR #35963) no longer built against the current pinned Mathlib — deterministic failures
at lines 190/194 even on the pristine origin/main file (confirmed by building the untouched
base) and even after a full `--repair-cache` olean refresh. Two drift symptoms:
  - `(mul_lt_mul_left hc).mpr hgt` → "failed to synthesize" → replaced with the version-stable
    `mul_lt_mul_of_pos_left hgt hc`.
  - `field_simp; ring` → `field_simp` now fully closes the goal so `ring` errors "No goals to
    be solved" → dropped the trailing `ring`.
Both fixes are safe across Mathlib versions. This is why the file needed a rebuild-with-repair,
not just a retry (the 135/139 crashes were ALSO present from fleet memory pressure, but the
190/194 failure was genuine deterministic drift, not infra).

File now 400 L / 21 thm / 1 def. Gallery meta synced (351→400, 17→21).

## Session 2026-07-08 (researcher-1) — the dual boundary: anti-domination + O(log) selectivity

**Mode**: REVISIT / DEPTH-FIRST follow-up · **Outcome**: progress (VERIFIED 0 sorry / 0 axiom,
docker `Built Proofs.Erdos897OQ01` 7744 jobs, `#print axioms` = propext/Classical.choice/Quot.sound).

### What I did
Section (6) builds the **domination lemma** `unboundedOnPrimePowers_of_ge` (largeness is
upward-closed under prime-power domination). The dual direction was missing. Added section (8):
- `not_unboundedOnPrimePowers_of_le` — **anti-domination**: if `g` fails the hypothesis and
  `f(p^k) ≤ g(p^k)` on prime powers, then `f` fails. Exact contrapositive of the domination
  lemma; one-liner `fun hf => hg (unboundedOnPrimePowers_of_ge hf hdom)`. Together the two say
  the hypothesis class is an **up-set** in the prime-power domination order.
- `not_unboundedOnPrimePowers_of_le_const_mul_log` — the **O(log) selectivity criterion**: if
  `f(p^k) ≤ C·log(p^k)` on prime powers (fixed `C`), then `f` fails. Proof: evaluate the
  hypothesis at `M = C`, get `f(p^k) > C·log(p^k)`, contradict via `absurd hgt (not_lt.mpr …)`.
  This is the exact lower boundary of the hypothesis and **subsumes both** ad-hoc selectivity
  results: `logN` (`C = 1`, equality) and `ω` (`C = 1/log 2`, since `ω(p^k)=1 ≤ (1/log2)·log(p^k)`
  as `log(p^k) ≥ log 2`).

### Files modified
- `proofs/Proofs/Erdos897OQ01.lean` (400 → 439 lines, +2 theorems, +section-8 doc).
- `src/data/proofs/erdos-897-oq-01/meta.json` (synced counts 400/21 → 439/23 in meta.* and leanFile.*).
- `src/data/research/problems/erdos-897-oq-01.json`, this knowledge.md.

### Key findings / notes
- `Real.log (p ^ k)` in the def coerces `p^k : ℕ` to ℝ; stating the criterion's hypothesis as
  `C * Real.log (p ^ k)` matches the def's coercion exactly, so `h C`'s witness lands as
  `f(p^k) > C * Real.log (p^k)` with no `push_cast` needed in the final `absurd`.
- Dropped a planned `not_unboundedOnPrimePowers_omega'` re-derivation: it would duplicate the
  *statement* of the existing `not_unboundedOnPrimePowers_omega` (auditor duplicate-decl flag).
  The unification is recorded in the docstring instead.
- Build gotcha: this file imports the local `Proofs.Erdos897Problem`, so host `lake env lean`
  fails (`Erdos897Problem.olean does not exist`) — must use the docker wrapper (builds deps).
  `#print axioms` checked via a temp module `E897Ax.lean` docker-built (output in build log).

### Next steps (unchanged hard core)
- The forward implication of Part I (`limsup f(p^k)/log(p^k) = ∞ ⇒ limsup (f(n+1)−f(n))/log n = ∞`)
  is OPEN and beyond the prime-power characterization — analysis of consecutive-difference limsups,
  not session-sized, not Aristotle-suitable.
