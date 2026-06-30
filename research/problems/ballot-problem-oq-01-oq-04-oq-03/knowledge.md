# Chung-Feller via Lindström-Gessel-Viennot (Non-Intersecting Lattice Paths)

**Problem ID**: ballot-problem-oq-01-oq-04-oq-03
**Status**: surveyed
**Phase**: ORIENT

## Summary

This open question asks for an *alternative* proof of the Chung-Feller theorem
— number of (+1,−1) lattice paths from (0,0) to (2n,0) with exactly k upsteps
above the x-axis equals the Catalan number Cₙ, independent of k — using the
Lindström-Gessel-Viennot (LGV) lemma on non-intersecting lattice paths, instead
of the cycle lemma used by the parent.

**Key finding: the target theorem is already fully machine-verified.** The
parent (ballot-problem-oq-01-oq-04) proves Chung-Feller with **0 sorries, 0
axioms** via the cycle lemma:
`ChungFellerBijection.chung_feller_uniform'` in
`proofs/Proofs/BallotProblemOQ01OQ04OQ01.lean`, re-exported as
`ChungFeller.chung_feller_uniform`. So this OQ adds methodology, not correctness.

## Session 2026-06-19 (Session 1) — Feasibility Survey

**Mode**: FRESH
**Outcome**: surveyed

### What I Did
- Confirmed the parent proof already verifies Chung-Feller (0 sorries / 0 axioms).
- Searched Mathlib for the LGV lemma: **absent** (no `Lindstrom`/`GesselViennot`
  sources under `proofs/.lake/packages/mathlib/Mathlib`).
- Inventoried available related infrastructure.

### Key Findings
- Mathlib provides Catalan numbers (`Mathlib/Combinatorics/Enumerative/Catalan.lean`)
  and Dyck words (`.../DyckWord.lean`), but **no** non-intersecting-paths /
  signed-determinant enumeration framework.
- General LGV (det of the path-count matrix = signed sum over non-intersecting
  path families, proved via a sign-reversing involution on intersecting families
  + `Matrix.det` permutation expansion) is a substantial build: estimated **>500
  lines**, depending on `Matrix.det`, `Equiv.Perm` sign, and a careful involution.
- A Chung-Feller-specific specialization (small fixed determinant of binomials
  counting non-intersecting pairs) could avoid the fully general lemma but still
  needs the involution/sign machinery — non-trivial.

### Infrastructure Assessment: LGV lemma
- **Needed**: Lindström-Gessel-Viennot lemma (or a Chung-Feller-specific
  non-intersecting-pair determinant specialization).
- **Size estimate**: >500 lines (general); a few hundred for a specialization.
- **Decision**: ALTERNATIVE / deprioritize. Target is already verified; the LGV
  proof is pedagogical only. If pursued, build a minimal specialized determinant
  lemma rather than general LGV.

### Files Modified
- src/data/research/problems/ballot-problem-oq-01-oq-04-oq-03.json (created)
- research/problems/ballot-problem-oq-01-oq-04-oq-03/knowledge.md (created)

### Next Steps
- If pursued: minimal Gessel-Viennot determinant for two non-intersecting
  monotone lattice paths, reusing Mathlib Catalan and the gallery's Dyck/balanced
  path defs from BallotProblemOQ01OQ04Core.lean.
- Otherwise deprioritize — the theorem is already machine-checked.

## Session 2026-06-19 (Session 2) — Decision: deprioritize (settle the (a)/(b) survey question)

**Mode**: ORIENT (decision)
**Outcome**: deprioritized, with re-pickup trigger

### What I did
Session 1 left an *open* `nextAction`: "decide between (a) building a
Chung-Feller-specific Gessel-Viennot determinant lemma, or (b) deprioritizing."
Re-claiming the slug and re-running the same survey would only rediscover the same
findings, so this session **settles the decision** and records *why*, so future
random-pickers don't burn a cycle re-surveying.

I read the verified parent target to ground the decision precisely:
`chung_feller_uniform' (n j k) (hj : j ≤ n) (hk : k ≤ n) :`
`Set.ncard (balancedPathsOfType n j) = Set.ncard (balancedPathsOfType n k)`
(`BallotProblemOQ01OQ04OQ01.lean:1023`), proved by an explicit type-swapping
**bijection** built from the cycle lemma (`chung_feller_bijection_exists`).

### Key new finding — structural mismatch (beyond Session 1's "missing infra")
The verified theorem is a statement of **k-uniformity / equinumerosity**: the
j-type and k-type classes have equal cardinality, for all `j, k ≤ n`. The
Lindström-Gessel-Viennot lemma is a **counting** device — its determinant
evaluates **one** class size. The textbook reflection/LGV result counts the
all-above (Dyck, `k = n`) class as `binom(2n,n) − binom(2n,n−1) = Cₙ`. To recover
Chung-Feller's *k-independence* determinantally one would need **every** class to
be a `k`-independent determinant evaluation — which is not the standard LGV setup
and amounts to encoding the cycle-lemma bijection's content into determinants.

So LGV is not merely *absent* from Mathlib (Session 1's finding); it is the
**wrong-shaped instrument** for this theorem's actual content. The cycle lemma is
the natural tool precisely because the statement is a bijection/equidistribution,
not a count. Even a "minimal specialized" Gessel-Viennot determinant would count
one class and leave the `k`-independence gap — the genuinely hard, research-level
step. This upgrades the verdict from "large build, low value" to "wrong route
for the goal shape", which is a firmer reason to defer.

### Decision
**(b) Deprioritize.** The mathematical fact is already machine-verified in the
parent (0 sorries, 0 axioms). The LGV re-proof is pedagogical only, blocked on
missing Mathlib infra, *and* structurally mismatched to the uniformity statement.

**Re-pickup trigger** (do not reclaim otherwise): (i) Mathlib lands a general
Lindström-Gessel-Viennot / non-intersecting-paths signed-determinant lemma (watch
`Mathlib.Combinatorics` for `LGV` / `GesselViennot` / `nonIntersecting`), or
(ii) a contributor specifically wants the determinant exposition and will budget
the multi-cycle specialized build (which must still bridge the `k`-independence
gap above).

### Files Modified
- src/data/research/problems/ballot-problem-oq-01-oq-04-oq-03.json (decision + trigger; iteration 1 → 2)
- research/problems/ballot-problem-oq-01-oq-04-oq-03/knowledge.md (this session)

## References
- Lindström, B. (1973). On vector representations of induced matroids.
- Gessel, I. & Viennot, G. (1985). Binomial determinants, paths, and hook length formulae.
- Chung, K.L. & Feller, W. (1949). On fluctuations in coin-tossing.
