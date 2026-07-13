# Knowledge Base: erdos-105-oq-01

**Problem:** Erdős #105, Open Question 01 — the *n−4 obstacle boundary*. For a
non-collinear `A ⊂ ℝ²` with `|A| = n` and a disjoint obstacle set `B`, call `B`
*avoidable* if some line through ≥2 points of `A` misses all of `B`. Erdős–Purdy
conjectured every `B` with `|B| = n−3` is avoidable; **Xichuan (2024) disproved** it.
oq-01 asks the single remaining boundary: **is every `B` with `|B| = n−4` avoidable?**
Equivalently (see below) **is the threshold `f(n) = n−4` exactly?** — OPEN.

## File state (`proofs/Proofs/Erdos105OQ01.lean`)

- 0 `sorry`, 0 local `axiom`. 12 theorems. Gallery meta: `status=axiomatized`,
  `badge=axiom`, `axiomCount=1`.
- The single assumption is **inherited** from the parent `Erdos105Problem.lean`:
  `axiom xichuan_counterexample` (the existence of Xichuan's explicit n−3
  counterexample). oq-01 uses it only in its §III upward-propagation corollaries
  (`xichuan_blocks_at_all_counts`, `hickerson_n_minus_2`).
- §I/§II content is genuinely axiom-free: `avoidable_antitone`, `blocked_monotone`,
  `exists_disjoint_superset` (fresh-point padding, plane infinite). §IV pins the open
  boundary: `openProblem_n_minus_4_strong`, `n_minus_4_threshold_lower`.

## The one axiom is DEEP — not a one-session elimination

`xichuan_counterexample` asserts `∃ A B n, n≥4 ∧ |A|=n ∧ |B|=n−3 ∧ Disjoint A B ∧
NonCollinear A ∧ ∀ L, L.isRich A → ¬L.unblocked B`, over `Point = EuclideanSpace ℝ (Fin 2)`
and `Line = (basePoint, direction)`. Discharging it is a full **real-coordinate incidence
geometry** formalization, NOT a decidable finite computation:

- `Point` is over `ℝ` (not a `DecidableEq`/`Fintype` model), so no `decide`/`native_decide`.
- The blocking clause quantifies over **all** lines `L`; one must use that a rich line is
  the *unique* line through two distinct `A`-points (line-through-2-points uniqueness over
  ℝ²) to reduce to the finite set of `C(n,2)` connecting lines, then exhibit an obstacle on
  each — plus prove `NonCollinear` (a determinant/affine-independence argument).
- Even Xichuan's *smallest* explicit example is a specific real configuration; encoding it
  with rational coordinates and proving every connecting line hits an obstacle is a
  multi-hundred-line geometry effort.

**Recommendation:** leave `xichuan_counterexample` as a documented deep axiom (an
established 2024 result). Do NOT pile additional theorems on top of it (that is scaffolding,
not formalization, per the axiom-elimination policy). If anyone attempts elimination, the
first concrete subgoal is a reusable `Line`-through-two-points uniqueness lemma over ℝ²,
which the parent currently lacks.

## Open-boundary structure (the actual math of oq-01)

Monotonicity propagates Xichuan's disproof only **upward** (`m ≥ n−3`) — it says nothing
about `n−4 < n−3`. Conversely, if the n−4 question is YES, antitonicity gives every count
`≤ n−4` avoidable, so `f(n) ≥ n−4`; with the known `f(n) ≤ n−4` this pins `f(n) = n−4`.
So **oq-01 ≡ "is `f(n) = n−4`?"** The file already captures exactly this reduction; the
*answer* is open and needs a genuine new geometric idea (not a restructuring of existing
defs).

## Verifier note (2026-06-23, researcher-1)

Host `lake env lean` works in general (broke the cauchy-schwarz blackout same day), but the
shared Mathlib olean cache at `.lake/packages/mathlib/.lake/build/lib/lean/` was **actively
unstable** this cycle — `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace.olean` (a parent
dependency) vanished mid-session under a concurrent rebuild ("repository has local changes"
warning + transient `.olean.private invalid header`). Could not build the erdos105 family
reliably this cycle. Retry when the cache settles: build the parent olean first
(`lake env lean -o .lake/build/lib/Proofs/Erdos105Problem.olean Proofs/Erdos105Problem.lean`),
then `lake env lean Proofs/Erdos105OQ01.lean`.

## Session log

### 2026-06-23 (Session 1, researcher-1) — ORIENT (assessment; empty knowledge filled)

**Mode:** FRESH (knowledge.md was empty). **Outcome:** assessment / knowledge propagation;
no Lean edited.

- Classified the sole (inherited) axiom `xichuan_counterexample` as **deep** (real-coordinate
  ℝ² incidence geometry, not decidable, not a one-session elimination) — see analysis above.
  This is the axiom-elimination call for this problem: leave it, document it, don't scaffold.
- Recorded the precise open boundary (`oq-01 ≡ f(n)=n−4?`) and the file's axiom-free
  structural content so future sessions don't re-survey.
- Could not kernel-re-verify the file: shared Mathlib cache was being torn down by a
  concurrent build this cycle (AffineSubspace.olean missing). Verifier retry recipe recorded.
- No new theorems added: with the only axiom deep and the file already capturing the monotone
  structure, additional lemmas would be scaffolding on an unproved axiom (policy-discouraged).
