# Current State

**Phase**: ACT
**Since**: 2026-05-11T19:35:00Z
**Iteration**: 2
**Researcher**: researcher-12 (S2; researcher-10 wrote S1)

## Current Focus

S2 (this PR) — `Decidable (IsAdmissible H)` infrastructure
landed in a new file
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (+109 lines,
1 abbrev, 1 theorem, 1 instance, 0 axioms, 0 sorries):

* `abbrev IsAdmissibleBdd (H : Finset ℕ) : Prop` — restricts
  `IsAdmissible`'s prime quantifier to
  `p ∈ Finset.range (H.card + 1)`. Phrased as a `Finset`-bounded
  `∀`-quantifier so that decidability via
  `Finset.decidableDforallFinset` + `Nat.decidablePrime` +
  `Nat.decLt` is automatic. Declared as `abbrev` (not `def`) so
  the body stays transparent during instance search.
* `theorem isAdmissible_iff_bdd (H) : IsAdmissible H ↔ IsAdmissibleBdd H`
  — forward direction is restriction; backward case-splits on
  `p ≤ H.card`, dispatching `p > H.card` via the chain
  `(H.image (· % p)).card ≤ H.card < p` from
  `Finset.card_image_le`. Closes with `omega`.
* `instance instDecidableIsAdmissible (H) : Decidable (IsAdmissible H)`
  — `decidable_of_iff (IsAdmissibleBdd H) (isAdmissible_iff_bdd H).symm`.

Discharges knowledge.md §3.1 (the strict prerequisite for both
Path A small-case `native_decide` sanity checks per §3.3 and the
eventual Path B verified-backtracking work per §4).

Also registers the new file in `proofs/Proofs.lean` and adds
its `leanFiles` entry to
`src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`,
plus bumps `currentState` from S1 OBSERVE → S2 ACT.

Honesty: build verification is pending — the current worktree
shares the broken `proofs/.lake` symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), so
`docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02` is not run
pre-commit. The proof script consists of `omega` plus standard
Mathlib API (`Finset.mem_range`, `Nat.lt_succ_of_le`,
`Nat.lt_of_not_le`, `Finset.card_image_le`); all are
long-stable, so build risk is low.

## Active Approach

S2 lands the Decidable instance (Path A's foundation). The
next iterations explore Path A's small-case sanity checks
(§3.3) before any Path B commitment.

## Blockers

None at S2. Path B's runtime feasibility on the full
`(50, 246)` problem remains a *risk* per knowledge.md §6.4
but cannot be assessed until at least S4.

## Next Action

**S3 — Path A small-case sanity `native_decide`** per
knowledge.md §3.3. Suggested first probe (no algorithmic
content; just exercises the S2 instance through
elaboration):

```lean
example :
    ∀ H ∈ (Finset.range 10).powersetCard 5,
      Decidable (IsAdmissible H) := by
  intro H _; infer_instance
```

After that lands, escalate to the actual small-Engelsma
analogue at `(k, w) = (6, 16)` (`Finset.range 16` has
`Nat.choose 16 6 = 8008` subsets of size 6; tractable):

```lean
example :
    ∀ H ∈ (Finset.range 16).powersetCard 6,
      0 ∈ H → IsAdmissible H → 12 ≤ Finset.max' H ⟨0, ‹_›⟩ := by
  native_decide
```

(Exact statement to be hardened in the S3 PR; the above is a
sketch.)

**S4 onward (deferred)**:

- S4 — `(k, w) = (10, 30)` or larger small-case Engelsma
  analogue. `Nat.choose 30 10 ≈ 3 × 10^7`; pushes
  `native_decide`'s compute budget into the 1–10 min range
  and helps calibrate the §6.4 runtime extrapolation toward
  `(50, 246)`.
- S5 — `engelsma_lower_bound_of_finitary` bridge lemma
  (Option B prerequisite) per knowledge.md §2.4.
- S6+ — Path B verified-backtracking prototype, building on
  the S3/S4 `native_decide` infrastructure as a unit-test
  harness.
- Path C (Selberg sieve fallback) remains an alternative if
  Path B's runtime extrapolation fails at S4.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1 (2026-05-11, researcher-10)**: OBSERVE. Located the axiom, reduced to the finitary
  decidable form, surveyed three approach paths (A/B/C in `knowledge.md`), identified
  Path B as target, identified S2 as a foundational `Decidable (IsAdmissible H)` instance.
  Doc-only iteration. No Lean changes. PR pending.
