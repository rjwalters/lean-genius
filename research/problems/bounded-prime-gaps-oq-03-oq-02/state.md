# Current State

**Phase**: ACT
**Since**: 2026-05-12T16:55:00Z
**Iteration**: 9
**Researcher**: researcher-5 (S9); researcher-3 (S8); researcher-5 (S6); researcher-11 (S5); researcher-10 (S4); researcher-8 (S3); researcher-12 (S2); researcher-10 (S1)

## Current Focus

S9 (this PR) — **Path-B Option-3 hybrid scaffold** per
`knowledge.md` §4.3. Establishes the `Bool`-valued search API +
correctness contract that future pruned iterations (S10+) plug into.
Extends `BoundedPrimeGapsOQ03OQ02.lean` (617 → 761 lines, +144) with
three top-level declarations and one positive unit test.

### S9 deliverables

```lean
/-- (i) Naive admissibility search. -/
def engelsmaSearch (w k : ℕ) : Bool :=
  decide (∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H)

/-- (ii) Bool/Prop bridge. -/
theorem engelsmaSearch_eq_false_iff (w k : ℕ) :
    engelsmaSearch w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H

/-- (iii) Composition with S8's bridge. -/
theorem engelsma_lower_bound_of_engelsmaSearch_false
    (h : engelsmaSearch 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne

/-- (iv) Positive unit test (35 subsets; witnessed by {0, 2, 6}). -/
theorem engelsmaSearch_7_3_eq_true : engelsmaSearch 7 3 = true := by
  native_decide
```

### Axiom bookkeeping

`axiomCount` stays at `1`. The unit test reuses S4's
`Lean.ofReduceBool`; the three S9 theorems are pure proofs using
only `decide_eq_false_iff_not`, `not_exists`, `not_and`, and S8's
already-merged `engelsma_lower_bound_of_finitary`. No new axioms;
no new sorries.

### Previous focus (S8)

S8 — **`engelsma_lower_bound_of_finitary` bridge lemma**
per `knowledge.md` §2.4. Pure-Lean combinatorics, parallel to S7's
deferred `(10, 30)` `native_decide` (still risky on CI). Extends
`BoundedPrimeGapsOQ03OQ02.lean` (357 → 617 lines, +260) with three
sub-pieces.

```lean
theorem engelsma_lower_bound_of_finitary
    (hfin : ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H →
      ¬ IsAdmissible H) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne
```

### Sub-piece (a) — Translation invariance toolkit

* `sub_mod_eq_mod_add_sub_mod` (private) — the modular identity
  `(a - m) % p = ((a % p) + (p - m % p)) % p` for `m ≤ a`, proven via
  a `Nat.ModEq` chain (add `m % p` to both sides, cancel after both
  reduce to `a` modulo `p`).
* `card_image_image_sub_mod_eq` (private) — per-prime residue
  cardinality preservation: `((H.image (· - m)).image (· % p)).card =
  (H.image (· % p)).card`, via the bijection
  `r ↦ (r + (p - m % p)) % p`.
* `card_image_sub_eq` — translation preserves overall cardinality.
* `image_sub_nonempty` — translation preserves nonemptyness.
* `image_sub_max'_eq` — `(H.image (· - m)).max' = H.max' - m`.
* `image_sub_min'_eq_zero` — `(H.image (· - H.min')).min' = 0`.
* `isAdmissible_image_sub_iff` — the headline:
  `IsAdmissible (H.image (· - m)) ↔ IsAdmissible H` when `m ≤ ∀ a ∈ H`.

### Sub-piece (b) — 50-subset extraction

* `exists_subset_card_50_containing_zero` (private) — for any `H'`
  with `0 ∈ H'` and `H'.card ≥ 50`, produces `H₀ ⊆ H'` with
  `H₀.card = 50` and `0 ∈ H₀`. Construction: 49-subset of
  `H'.erase 0`, re-insert `0`.

### Sub-piece (c) — Wiring

The headline `engelsma_lower_bound_of_finitary` runs the §2.4 proof
sketch: by contradiction, set `m := H.min'`, translate to
`H' := H.image (· - m)`, observe `0 ∈ H'` (witnessed by `m - m`),
`H'.max' = H.max' - m < 246` (the contradictory hypothesis),
`H'.card ≥ 50` (by (a)), `IsAdmissible H'` (by (a)). Apply (b) to get
`H₀ ⊆ H'` with `0 ∈ H₀`, `H₀.card = 50`. By
`BoundedPrimeGaps.admissible_subset`, `IsAdmissible H₀`. Each
element of `H₀` is `≤ H'.max' < 246`, so `H₀ ⊆ Finset.range 246`.
Hence `H₀ ∈ (Finset.range 246).powersetCard 50`. Apply `hfin` to
derive `¬ IsAdmissible H₀` — contradiction.

### Why now (instead of S7)?

`state.md`'s prior `Next Action` was S7 = `(10, 30)` `native_decide`
(deferred via S6). S7 still carries the documented 30-120 s runtime
risk; S8 is **pure-Lean combinatorics** with no `native_decide` cost
and is explicitly marked "tackleable in parallel with S7" in the
prior state.md. Landing S8 unblocks Path B (S9+): once we have a
verified search procedure returning `false` for `(50, 246)`, S8's
bridge lemma immediately discharges the original `engelsma_lower_bound`
axiom — no further wiring is needed.

### Axiom bookkeeping

`axiomCount` stays at `1` (the `Lean.ofReduceBool` axiom introduced
in S4 by `native_decide` is preserved). All S8 proofs are pure
combinatorics — no `native_decide`, no new axioms. `theoremCount`:
11 → 20 (9 new lemmas/theorems; the helpers + headline split as
described above).

### Previous focus (S6)

S6 — **Non-vacuous Engelsma analogues at the boundary
`w = H(k)+1`** for `k = 3, 4, 5, 6`. S4 (6,16) and S5 (8,22) verified
the bound *vacuously* (Engelsma's table has `H(k) > w−1` in both
cases, so no admissible tuple fits); S6 closes that gap by enumerating
the minimal **non-vacuous** cases `(3,7)`, `(4,9)`, `(5,13)`, `(6,17)`
where the bound `H(k) ≤ H.max'` is tight (witnessed by classical
Hardy–Littlewood patterns from `BoundedPrimeGaps.lean`).

```lean
theorem engelsma_analogue_nonvacuous_3_7 :
    ∀ H ∈ (Finset.range 7).powersetCard 3,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 6 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(7,3) = 35

theorem engelsma_analogue_nonvacuous_4_9 :
    ∀ H ∈ (Finset.range 9).powersetCard 4,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 8 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(9,4) = 126

theorem engelsma_analogue_nonvacuous_5_13 :
    ∀ H ∈ (Finset.range 13).powersetCard 5,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 12 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(13,5) = 1,287

theorem engelsma_analogue_nonvacuous_6_17 :
    ∀ H ∈ (Finset.range 17).powersetCard 6,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 16 ≤ H.max' ⟨0, h0⟩ := by
  native_decide   -- C(17,6) = 12,376
```

Cumulative cost ≈ `1.4 × 10⁴` subsets — well below S5's `3.2 × 10⁵`
and four orders of magnitude below the (deferred) `(10, 30)` case.
All four theorems are non-vacuous: each is witnessed by a known
admissible k-tuple from `BoundedPrimeGaps.lean` (`{0,2}`, `{0,2,6}`,
`{0,2,6,8}`) or its standard sibling (`{0,2,6,8,12}`,
`{0,4,6,10,12,16}`). `native_decide` must distinguish admissible
from non-admissible to discharge each, exercising the S2 `Decidable`
instance over real cases.

**Why deviate from state.md's stated S6 next-action (`(10, 30)`)?**
The `(10, 30)` case is still vacuous (Engelsma records
`H(10) ≥ 32 > 29`), so it adds another `3 × 10⁷`-subset stress test
of the decider *without* exercising the diameter bound. The
non-vacuous boundary cases (S6 here) cost ~14k subsets total
(four orders of magnitude cheaper) **and** genuinely test the
bound, supplying the qualitative §6.4 feasibility-checkpoint
evidence that the run-up to `(10, 30)` really wants: do tight
bounds via `native_decide` actually go through, not just vacuous
ones? The originally planned `(10, 30)` step is renumbered to S7
below.

**Axiom bookkeeping**: All four `native_decide` calls reuse the
`Lean.ofReduceBool` axiom introduced in S4; `leanFile.axiomCount`
stays at `1`.

**theoremCount**: 7 → 11 (adds the four `engelsma_analogue_nonvacuous_*`).
**lineCount**: 245 → 357.

## Next Action

**S10 — Replace the naive `engelsmaSearch` with a pruned variant.**
With S9's surface API now fixed
(`engelsma_lower_bound_of_engelsmaSearch_false` lands with this PR),
the remaining Path-B work proceeds at the implementation layer
without touching downstream consumers.

```lean
-- S10 deliverable: pruned variant per knowledge.md §4.2
def engelsmaSearchPruned (w k : ℕ) : Bool := ...

-- S11: correctness (~200-300 lines)
theorem engelsmaSearchPruned_eq_engelsmaSearch (w k : ℕ) :
    engelsmaSearchPruned w k = engelsmaSearch w k := ...

-- S12: native_decide discharge of the axiom
theorem engelsmaSearchPruned_50_246 :
    engelsmaSearchPruned 246 50 = false := by native_decide
```

S10 ≈ 100-200 lines (pruner def); S11 ≈ 200-300 lines (correctness
via structural induction); S12 = single `native_decide`.

A simpler S11 variant proves `engelsmaSearchPruned_eq_false_iff`
directly with the same RHS as the S9 naive baseline — the wiring
through `engelsma_lower_bound_of_engelsmaSearch_false` stays
unchanged.

**Alternative deferred S7** — `(10, 30)` `native_decide` analogue.
Lower priority than S10–S12 Path-B work.

### Previous focus (S5)

S5 — Intermediate-scale Engelsma analogue via `native_decide`
at `(k, w) = (8, 22)`, a **cautious scaling checkpoint** between
S4's $\binom{16}{6} = 8008$ search and the originally planned S6
case $\binom{30}{10} \approx 3 \times 10^7$:

```
theorem engelsma_analogue_8_22 :
    ∀ H ∈ (Finset.range 22).powersetCard 8,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 18 ≤ H.max' ⟨0, h0⟩ := by
  native_decide
```

Search space `Nat.choose 22 8 = 319,770` ≈ `3.2 × 10⁵` — roughly
**40× the S4 case** but still four orders of magnitude below
the deferred S6 case. The implication is vacuously satisfied at
every enumerated subset since Engelsma's table records `H(8) = 26`
> 21, so no admissible 8-tuple fits in `Finset.range 22`. The
threshold `18 ≤ H.max'` mirrors S4's convention of a conservative
under-estimate of the (unattained) diameter bound.

**Why deviate from state.md's stated S5 next-action (`(10, 30)`)?**
The (10, 30) case has documented runtime risk: 30–120 s estimated
under `native_decide`, possibly exceeding default CI timeouts. The
local worktree shares the broken `proofs/.lake` symlink, so we
cannot pre-verify build. Per `knowledge.md` §6.4 — the feasibility
checkpoint principle — we want **empirical scaling evidence** at
an intermediate scale (40× S4) before committing to the 3,750× S4
case. If S5 builds in a few seconds, the (10, 30) extrapolation
becomes principled (~33× slow-down → tens of seconds). If S5 itself
runs slowly, that informs whether we proceed to (10, 30) or move
directly to the §6.4 Path-C-prime fallback. The originally planned
`(10, 30)` case is **renumbered to S6** below.

**Axiom bookkeeping**: `native_decide` reuses the `Lean.ofReduceBool`
axiom introduced in S4; `leanFile.axiomCount` stays at `1` (each
additional `native_decide` requires the axiom once per file, not
once per use).

**theoremCount**: 6 → 7 (the new `engelsma_analogue_8_22`).
**lineCount**: 192 → 245.

### Previous focus (S3)

S3 — Kernel-`decide` regression checks for the S2 `Decidable`
instance: four theorems demonstrating correct reduction on small tuples.

* `admissible_twin_via_S2`         — `IsAdmissible {0, 2}` via S2 instance.
* `admissible_triple_via_S2`       — `IsAdmissible {0, 2, 6}` via S2 instance.
* `admissible_quadruple_via_S2`    — `IsAdmissible {0, 2, 6, 8}` via S2 instance.
* `not_admissible_zero_one_via_S2` — `¬ IsAdmissible {0, 1}` via S2 instance
  (negative case; `(·%2)` image card = 2 ≥ 2).

All four use kernel `decide` (not `native_decide`), keeping `axiomCount = 0`.
These are the simplest Path-A (verified-backtracking) sanity checks per
`knowledge.md` §3.3 — exercising the new instance on tuples already proven
admissible in `BoundedPrimeGaps.lean` (via hand-written calculation) plus one
negative case to confirm the decider rejects non-admissible inputs.

`native_decide`-based Engelsma-analogue checks (`(k, w) = (6, 16)` and
beyond) are explicitly deferred to S4, where the introduction of the
`Lean.ofReduceBool` axiom needs to be accounted for in meta.json.

### Previous focus (S2)

S2 — `Decidable (IsAdmissible H)` infrastructure
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

## Subsequent Iterations (deferred)

- S10 — Pruned variant `engelsmaSearchPruned (w k : ℕ) : Bool` per
  knowledge.md §4.2. Branch-and-bound over admissible k-tuples in
  `Finset.range w`; short-circuit on first failed residue cover.
  ~100-200 lines for the def alone. Should use Array/List runtime
  representation per §4.5.
- S11 — Correctness `engelsmaSearchPruned_eq_engelsmaSearch` (or
  `_eq_false_iff` directly). Structural induction, pre-validated
  against S6's non-vacuous witnesses + S9's naive baseline.
  ~200-300 lines.
- S12 — `engelsmaSearchPruned 246 50 = false` via `native_decide`.
  Final discharge via `engelsma_lower_bound_of_engelsmaSearch_false`.
- Alternative deferred S7 — (10, 30) `native_decide` analogue.
- Path C (Selberg sieve) remains a fallback per knowledge.md §5.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1 (2026-05-11, researcher-10)**: OBSERVE. Located the axiom, reduced to the finitary
  decidable form, surveyed three approach paths (A/B/C in `knowledge.md`), identified
  Path B as target, identified S2 as a foundational `Decidable (IsAdmissible H)` instance.
  Doc-only iteration. No Lean changes. PR #17774 merged.
- **S2 (2026-05-11, researcher-12)**: ACT. New file
  `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (109 lines): `IsAdmissibleBdd`,
  `isAdmissible_iff_bdd`, `instDecidableIsAdmissible`. 0 axioms, 0 sorries.
  Build pending. PR #17790 merged.
- **S3 (2026-05-12, researcher-8)**: ACT. Extended S2 file (109 → 149 lines, +40):
  4 kernel-`decide` regression theorems exercising the S2 instance on
  `{0, 2}`, `{0, 2, 6}`, `{0, 2, 6, 8}` (positive) and `{0, 1}` (negative).
  Kernel decide preserves `axiomCount = 0`; `native_decide`-based larger
  Engelsma analogues deferred to S4. PR #17812 merged.
- **S4 (2026-05-12, researcher-10)**: ACT. Extended S3 file (149 → 192 lines, +43):
  `engelsma_analogue_6_16` via `native_decide` over the 8008 subsets of
  `(Finset.range 16).powersetCard 6`. First `native_decide` in this file;
  introduces the `Lean.ofReduceBool` axiom (`leanFile.axiomCount` 0 → 1).
  Vacuous antecedent (no admissible 6-tuple fits in range 16; Engelsma
  records narrowest diameter 16). PR #17847 merged.
- **S5 (2026-05-12, researcher-11)**: ACT. Extended S4 file (192 → 245 lines, +53):
  `engelsma_analogue_8_22` via `native_decide` over the 319,770 subsets of
  `(Finset.range 22).powersetCard 8`. Intermediate scaling checkpoint
  (~40× S4 search), reuses the `Lean.ofReduceBool` axiom from S4
  (`axiomCount` stays at 1). Vacuous antecedent (Engelsma records H(8)=26
  > 21, so no admissible 8-tuple fits in range 22). The originally planned
  (10, 30) case is deferred to S6, pending evidence on S5's `native_decide`
  runtime to extrapolate the (10, 30) feasibility. Build pending; the
  Docker symlink trap prevents local verification.
- **S6 (2026-05-12, researcher-5)**: ACT. Extended S5 file (245 → 357 lines, +112):
  four **non-vacuous** Engelsma analogues `engelsma_analogue_nonvacuous_(k, H(k)+1)`
  for `k = 3, 4, 5, 6` via `native_decide`. Search spaces 35 / 126 / 1,287 / 12,376
  (cumulative ~1.4 × 10⁴). Reuses the `Lean.ofReduceBool` axiom from S4
  (`axiomCount` stays at 1). Theorem count 7 → 11. Each bound is tight,
  witnessed by classical Hardy–Littlewood admissible tuples (the parent
  file's `admissible_twin`, `admissible_triple_0_2_6`,
  `admissible_quadruple_0_2_6_8`, plus `{0,2,6,8,12}` and `{0,4,6,10,12,16}`).
  Closes the gap left by S4/S5 (both vacuous) — actually exercises the
  diameter bound rather than relying on emptiness of admissible witnesses.
  Originally planned S6 = (10, 30) renumbered to S7 (still vacuous, higher
  runtime risk, lower mathematical value than the boundary non-vacuous
  cases here). Build pending; the Docker symlink trap prevents local
  verification. PR #18027 merged.
- **S8 (2026-05-12, researcher-3)**: ACT. Extended S6 file (357 → 617 lines, +260):
  the `engelsma_lower_bound_of_finitary` bridge lemma per knowledge.md §2.4.
  Pure-Lean combinatorics — no `native_decide`, no new axioms (`axiomCount`
  stays at 1). Three sub-pieces: (a) translation invariance toolkit
  (`isAdmissible_image_sub_iff` + the per-prime modular bijection lemma
  `card_image_image_sub_mod_eq` + 4 helpers `card_image_sub_eq` /
  `image_sub_nonempty` / `image_sub_max'_eq` / `image_sub_min'_eq_zero`,
  with the foundational modular identity `sub_mod_eq_mod_add_sub_mod` proven
  via a `Nat.ModEq` chain); (b) 50-subset extraction
  `exists_subset_card_50_containing_zero`; (c) wiring in the headline
  `engelsma_lower_bound_of_finitary` theorem. theoremCount 11 → 20 (9 new
  lemmas/theorems). Reduces the unbounded `engelsma_lower_bound` axiom in
  `BoundedPrimeGapsOQ03.lean` (line 134) to its finitary form
  `∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H` —
  Path-B (S9+) verified-backtracking work then needs only to discharge
  the latter to close the axiom. Build pending; the Docker symlink trap
  blocks local verification (memory: feedback_researcher_lake_symlink_broken).
  Skipped S7 (vacuous (10, 30) `native_decide`) per state.md's note that
  S8 is "tackleable in parallel with S7" with higher mathematical value.
- **S9 (2026-05-12, researcher-5)**: ACT. Extended S8 file (617 → 761 lines, +144):
  Path-B Option-3 hybrid scaffold per knowledge.md §4.3. Three new
  declarations: `def engelsmaSearch (w k : ℕ) : Bool` (naive
  `decide`-backed enumeration); `theorem engelsmaSearch_eq_false_iff`
  (Bool/Prop bridge equating `engelsmaSearch w k = false` with the
  finitary form); `theorem engelsma_lower_bound_of_engelsmaSearch_false`
  (composes the bridge with S8's `engelsma_lower_bound_of_finitary`
  to reduce the axiom statement to a single Bool equation
  `engelsmaSearch 246 50 = false`). Plus a positive unit test
  `engelsmaSearch_7_3_eq_true` via `native_decide` (35 subsets;
  witnessed by `{0, 2, 6}`). theoremCount 20 → 23; defCount 1 → 2;
  axiomCount stays at 1 (Lean.ofReduceBool reused). 0 sorries.
  The naive `engelsmaSearch` is intractable at (50, 246); shipped
  here as the surface API that future pruned variants (S10+)
  replace in-place. Build pending.
