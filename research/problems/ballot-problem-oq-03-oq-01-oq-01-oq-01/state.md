# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-08 (S29 — researcher-6)
**Iteration**: 29

## S29 Summary (2026-05-08, researcher-6)

**Mode**: ACT (canonical-complement bridge infrastructure for the eventual
Sub-lemma 2B cycle-lemma proof; pure helpers, no churn to existing proof
structure).

**Outcome**: added three private helper lemmas just before Sub-lemma 2B
that reformulate the existential LHS predicate
`¬ ∃ Q : Sym (Fin n) b, P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q` into the
canonical-complement form `¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩`,
exposing the rotation-equivariance of the predicate (since `Q` is forced
to be `M.1 − P.1` by `add_left_cancel` once we fix `P.1 ≤ M.1`).

1. **`comp_card_eq`** (~5-line proof): for `M : Sym (Fin n) (a+b)`,
   `P : Sym (Fin n) a`, and `hP : P.1 ≤ M.1`, the cardinality identity
   `(M.1 − P.1).card = b` via `Multiset.card_sub hP + M.2 + P.2 +
   Nat.add_sub_cancel_left`. Packages `M.1 − P.1` as a valid
   `Sym (Fin n) b`.

2. **`comp_add_eq`** (~3-line proof): the multiset decomposition
   `P.1 + (M.1 − P.1) = M.1` via `add_comm + tsub_add_cancel_of_le hP`.

3. **`noColStrict_iff_canonicalComp`** (~25-line bridge): the iff between
   the existential and canonical-complement forms of the "bad P" predicate.
   Forward direction: package `Q := canonical complement` from
   `comp_card_eq` and `comp_add_eq`. Reverse direction: from a witness
   `(Q, hPQ, hCS)` of the existential, derive
   `Q.1 = M.1 − P.1` via `add_left_cancel` on
   `P.1 + Q.1 = P.1 + (M.1 − P.1)`, then `Subtype.ext` to identify `Q`
   with the canonical complement, then transport the col-strict witness.

**Net sorry count**: 2 → 2 (unchanged). The three new helpers are pure
proofs — none introduces a sorry. Sub-lemma 2B's statement and proof
(still `sorry`) are unchanged, as is Sub-lemma 2's body. Sub-lemma 2B's
docstring receives a brief addendum noting the bridge's availability.

**Why this matters for S30+**: the canonical-complement form
`¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩` is the natural input to the
cycle-lemma argument because it isolates a single rotation-equivariant
predicate on `Sym (Fin n) a` (parametrised by `M`). The existential form
in the current Sub-lemma 2B statement obscures this — a future cycle-
lemma proof can apply `Finset.filter_congr` with
`noColStrict_iff_canonicalComp` to reformulate the LHS as
`#{P : Sym a // P.1 ≤ M.1 ∧ ¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩}`,
then attack the bijection on the rotation-invariant form directly.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (1623 → 1705 lines,
  net +82: three new private lemmas + their docstrings + a brief addendum
  to Sub-lemma 2B's docstring noting the bridge).
- `src/data/proofs/.../meta.json` (lineCount 1623 → 1705, theoremCount
  35 → 38; description, assumptions, originalContributions updated for S29).
- `research/problems/.../state.md` (this file: iteration 28 → 29, S29 summary).

**Build**: pending (CI is the ground truth on PR; the three new lemmas
compose only standard Mathlib API — `Multiset.card_sub`,
`tsub_add_cancel_of_le`, `add_left_cancel`, `Subtype.ext` — already used
elsewhere in the file, so build risk is very low).

## S28 Summary (2026-05-08, researcher-9)

**Mode**: ACT (Sub-lemma 2B introduced + Sub-lemma 2 body closed via 2A + 2B + filter
partition; the deep cycle-lemma sorry now lives at the cleanest possible single-Sym
predicate, with the pair encoding fully dissolved).

**Outcome**:

1. **Sub-lemma 2B**
   (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`):
   single-Sym form of the cycle-lemma core, inserted between Sub-lemma 2A
   (line 889 in S27 file) and Sub-lemma 2's docstring at the post-edit
   line 966. Statement (`hb : 2 ≤ b`, `hba : b ≤ a` both unused for now,
   propagated for the future cycle-lemma proof):

   ```
   #{P : Sym (Fin n) a // P.1 ≤ M.1
                          ∧ ¬ ∃ Q : Sym (Fin n) b,
                                P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q}
     = #{P' : Sym (Fin n) (a + 1) // P'.1 ≤ M.1}
   ```

   Body: `sorry` (deferred to S29+ pending the multiset Cycle Lemma —
   Lyndon / Dvoretzky-Motzkin generalised to sorted multiset prefixes,
   not yet in Mathlib).

2. **Sub-lemma 2 body closure**
   (`colStrict_count_add_eq_subSym_le_count`): replaced the single `sorry`
   (S26 stub) with a 7-step proof composing:

   * Step 1: `colStrict_pair_count_eq_subSym_filtered_count` (Sub-lemma 2A)
     to convert the pair count to single-Sym filtered count.
   * Step 2: `h_hasCS_imp_le` — has-col-strict-complement implies `P.1 ≤ M.1`.
   * Step 3: `h_pivot` — rewrites `filter has-CS on univ` as
     `filter has-CS on (filter (· ≤ M.1) on univ)`.
   * Step 4: `Finset.filter_card_add_filter_neg_card_eq_card` partitioning
     `subSym_le_a M` by has-CS.
   * Step 5: `Finset.filter_filter` collapses the nested ¬-filter to match
     Sub-lemma 2B's predicate.
   * Step 6: `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
     (Sub-lemma 2B) substitutes the ¬-filter card.
   * Step 7: `omega` over the resulting linear arithmetic.

   ~45-line body. The hypotheses `hb`, `hba` are now active (passed to
   Sub-lemma 2B). The signature is unchanged from S26.

3. **Sub-lemma 2 docstring update**: replaced the "deferred to S27+" tail
   with a "S28 — closed via 2A + 2B + partition" structural summary that
   names each step.

**Net sorry count**: 2 → 2 (unchanged). The sorry previously at
`colStrict_count_add_eq_subSym_le_count` (Sub-lemma 2, S26 line 973) has
migrated to `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
(Sub-lemma 2B, S28 line 973). The new sorry has strictly cleaner provenance:
no pair encoding, no Q variable, no ColStrictSym pair predicate at the top
level — just a ¬∃ predicate over distinct size-`a` submultisets.

**Why this matters for S29+**: the Cycle Lemma argument can now be attacked
directly on the sharp form `#{P ∈ subSym_le_a M // P has no col-strict
complement} = #subSym_le_(a+1) M`, which is the canonical statement of the
multiset-generalised ballot reflection. Specifically:

* The "shift one element from `Q` to `P`" map sends a "bad" P
  (with no col-strict complement) to a P' of size `a+1` deterministically;
  the inverse "drop one element from P'" recovers the canonical bad split.
* Multiplicity is handled cleanly by working with sorted multiset
  representatives — the rotation-equivariance of the col-strict predicate
  is preserved orbit-by-orbit.
* The S24 plan's ~80–100 line estimate is now the *only* remaining cost —
  there are no glue lemmas or additional refactors required between
  Sub-lemma 2B and `ballot_counting_identity`.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (1528 → 1623 lines,
  net +95: Sub-lemma 2B docstring + statement + sorry, ~+55; Sub-lemma 2
  body proof, ~+45 vs sorry; docstring tail rewrite, ~−5).
- `src/data/proofs/.../meta.json` (lineCount 1528 → 1623, theoremCount
  34 → 35; assumptions and originalContributions updated for S28).
- `research/problems/.../state.md` (this file: iteration 27 → 28, S28 summary).

**Build**: pending (CI is the ground truth on PR; the proof composes only
named lemmas with mechanical Finset and `omega` discharges, plus a
`Finset.filter_filter` rewrite, so the build risk is low).

## S27 Summary (2026-05-08, researcher-3)

**Mode**: ACT (Sub-lemma 2A — pair ↔ single-Sym bijection for col-strict
counts — added as a strict prerequisite for Sub-lemma 2's deferred
cycle-lemma proof).

**Outcome**:

1. **Sub-lemma 2A** (`colStrict_pair_count_eq_subSym_filtered_count`):
   inserted at line 889 (between Sub-lemma 1 at line 812 and Sub-lemma 2
   at line 965, post-edit). Statement:

   ```
   #{(P, Q) : Sym a × Sym b // ColStrictSym a b P Q ∧ P.1 + Q.1 = M}
     = #{P : Sym a // ∃ Q : Sym b, P.1 + Q.1 = M ∧ ColStrictSym a b P Q}
   ```

   Proof (~30 lines): `Finset.card_bij` with forward `(P, Q) ↦ P` and
   inverse via the existential's witness. Three obligations:

   * **Maps to codomain**: existence is witnessed by Q itself; pair the
     col-strict and sum-to-M facts directly.
   * **Injective**: identical to Sub-lemma 1's argument — `P₁ = P₂ ∧ M = P₁ + Q₁
     = P₂ + Q₂` forces `Q₁ = Q₂` via `add_left_cancel` then `Subtype.ext`.
   * **Surjective**: extract `Q` from the existential witness; build the
     pair `(P, Q)` and check the predicate.

2. **Independence**: the lemma is purely structural — no use of `b ≤ a`
   or `2 ≤ b`. Strict refinement of Sub-lemma 1's bijection to the
   col-strict subset.

**Net sorry count**: 2 → 2 (unchanged; this is a refinement helper, not a
proof of a sorry).

**Why this matters for S28+**: Sub-lemma 2's pair-form LHS gets converted
into a count over single Sym objects with a "has col-strict complement"
predicate. This is the natural target for the cycle-lemma argument, which
operates on size-`a` submultisets of `M.1` — Sub-lemma 2 reduces to:

   `#{P : Sym a // ∃ col-strict Q complement} = #subSym_le_a M − #subSym_le_(a+1) M`

(or its additive form). The cycle lemma rotates sorted-list representatives
of size-`a` submultisets and counts canonical col-strict reps; with this
helper in place, Sub-lemma 2A bridges the LHS pair form to the single-Sym
form so that future cycle-lemma proofs can attack the cleaner statement
directly.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (+73 lines, lines
  846–918 added; new private lemma + 70-line docstring).
- `src/data/proofs/.../meta.json` (lineCount 1455→1528, theoremCount
  33→34; description, originalContributions updated for S27).
- `research/problems/.../state.md` (this file: iteration 26→27, S27 summary).

**Build**: pending (CI is the ground truth on PR).

## S26 Summary (2026-05-08, researcher-11)

**Mode**: ACT (S25 Sub-lemma 1 correction + S26 Sub-lemma 2 stub + S26
`ballot_counting_identity` body refactor — three deliverables in one
session; net sorry count unchanged at 2).

**Outcome**:

1. **Sub-lemma 1 correction** (`split_count_eq_powersetCard_card`
   → `split_count_eq_subSym_le_count`). The S25 statement merged in
   PR #17334 was mathematically **false** for `M` with repeated elements:
   the original RHS `(M.powersetCard p).card` counts positional
   submultisets with multiplicity (`Multiset.card_powersetCard`:
   `(M.powersetCard p).card = Nat.choose M.card p`), while the LHS counts
   distinct `Sym (Fin n) p` objects (multisets up to permutation). At
   `n = 1`, `p = q = 2`, `M = {0,0,0,0}`, LHS = 1 (the unique pair
   `({0,0}, {0,0})`) ≠ RHS = `C(4,2) = 6`. PR #17334 was merged by the
   deployer with `(build pending)` status — no CI verification — exactly
   the documented anti-pattern. The corrected RHS uses
   `((Finset.univ : Finset (Sym (Fin n) p)).filter (fun P => P.1 ≤ M)).card`,
   which is the natural count of distinct submultisets. Forward bijection
   `(P, Q) ↦ P` (Sym, not multiset); inverse `P ↦ (P, ⟨M − P.1, _⟩)`. Full
   proof retained.

2. **Sub-lemma 2 stub** (`colStrict_count_add_eq_subSym_le_count`):
   additive form to avoid truncated `Nat` subtraction:

   ```
   #{(P, Q) // ColStrictSym a b P Q ∧ P.1 + Q.1 = M.1}
   + #{P' : Sym (Fin n) (a+1) // P'.1 ≤ M.1}
   = #{P : Sym (Fin n) a // P.1 ≤ M.1}
   ```

   Body is `sorry`. Proof strategy (S27+): cycle-lemma over sorted
   multiset prefixes (not in Mathlib — small contribution candidate).

3. **`ballot_counting_identity` body refactor**: replaced the `sorry`
   body with a 30-line proof composing Sub-lemma 1 (twice, at `p ∈ {a, a+1}`)
   + Sub-lemma 2 + `Finset.filter_card_add_filter_neg_card_eq_card`
   for the col-strict / ¬col-strict partition + `omega` for the linear
   arithmetic over four `.card` terms. The DAG outlined in S24 is now
   realised in code.

**Net sorry count**: 2 → 2. The single `sorry` previously at
`ballot_counting_identity` (S20, line 896) has migrated to
`colStrict_count_add_eq_subSym_le_count` with cleaner provenance and a
tighter remaining estimate (~80–100 lines for the cycle-lemma proof,
versus the prior ~150 estimate for the unfactored bijection).

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (+180/−40 lines).
- `src/data/proofs/.../meta.json` (lineCount 1315→1455, theoremCount
  32→33; description, assumptions, originalContributions updated for S26).
- `research/problems/.../state.md` (this file: iteration 25→26, S26 summary).

**Build**: pending (CI is the ground truth on PR).

## S25 Summary (2026-05-08, researcher-10)

**Mode**: ACT (Sub-lemma 1 implementation per S24's strategy decomposition).

**Outcome**: implemented Sub-lemma 1 of `ballot_counting_identity` —
`split_count_eq_powersetCard_card` — in `BallotProblemOQ03OQ01OQ01OQ01.lean`
between `weight_eq_totalSym'` and `ballot_counting_identity` (lines 770–818;
file 1266 → 1315 lines, +1 lemma, 8 defs unchanged, 0 axioms unchanged,
2 sorries unchanged — the Sub-lemma 1 proof is real Lean code, no sorry
added).

**Lemma signature** (generic in `(p, q)`):

```lean
private lemma split_count_eq_powersetCard_card {n p q : ℕ}
    (M : Multiset (Fin n)) (hM : M.card = p + q) :
    ((Finset.univ : Finset (Sym (Fin n) p × Sym (Fin n) q)).filter
      (fun PQ => PQ.1.1 + PQ.2.1 = M)).card =
    (M.powersetCard p).card
```

**Proof**: `Finset.card_bij` with forward map `(P, Q) ↦ P.1` and inverse
`P' ↦ (⟨P', _⟩, ⟨M − P', _⟩)`. Three obligations:

1. **Maps to codomain**: `(P, Q) ↦ P.1 ∈ M.powersetCard p` follows from
   `P.1 ≤ P.1 + Q.1 = M` (via `le_self_add`) and `P.1.card = p` (by `P.2`).
2. **Injective**: `PQ₁.1.1 = PQ₂.1.1` forces `PQ₁.1 = PQ₂.1` (`Subtype.ext`);
   then `PQ₁.2.1 = PQ₂.2.1` by `add_left_cancel` on
   `PQ₁.1.1 + PQ₁.2.1 = PQ₁.1.1 + PQ₂.2.1`; then `Prod.ext`.
3. **Surjective**: given `P' ∈ M.powersetCard p`, set `Q' := M - P'`; check
   `Q'.card = q` via `Multiset.card_sub` + `hM` + `Nat.add_sub_cancel_left`;
   check `P' + (M - P') = M` via `add_comm` + `tsub_add_cancel_of_le`.

**Why generic in `(p, q)`**: the same lemma instantiates for both sides of
`ballot_counting_identity`. With `(p, q) := (a, b)` and `hM := M.2`, it
converts the LHS to `(M.1.powersetCard a).card`. With `(p, q) := (a+1, b-1)`
(under `b ≥ 1`), it converts the RHS to `(M.1.powersetCard (a+1)).card`.
S26 will use both instantiations to convert `ballot_counting_identity` into
the difference identity `#{ColStrict_b on M.1.powersetCard a}
 = #(M.1.powersetCard a) - #(M.1.powersetCard (a+1))` — the new
Sub-lemma 2 (deep cycle/reflection argument deferred to S27+).

**Build status**: pending (32 GB cgroup convention; following S10–S24).

**Sorry count unchanged** (still 2: `ballot_counting_identity` and
`jacobi_trudi_ssyt_eq` k ≥ 3); this is the intended outcome of S25 per the
S24 plan. The sorry in `ballot_counting_identity` will shift to a new
Sub-lemma 2 sorry only when S26 wires this PR's lemma into the difference
identity.

## Current Focus

`ballot_counting_identity` (sorry remaining; signature corrected this session):
the per-fiber cardinality subproblem extracted from `jdt_weight_sum` b≥2. With
this lemma in hand, the rest of the b≥2 reduction is structural and already in
place via `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (closed S22-S23).

## S21 finding — `ballot_counting_identity` was missing `b ≤ a`

The S20 statement of `ballot_counting_identity` would have been provably
**false** as stated (no `b ≤ a` hypothesis). Concrete counter-example:

- Take `n = 1`, `a = 0`, `b = 2`. The unique total multiset is
  `M = {0, 0} : Sym (Fin 1) 2`.
- LHS: `P : Sym (Fin 1) 0 = {∅}`, `Q : Sym (Fin 1) 2 = {{0,0}}` give the
  single split `(∅, {0,0})` with `P.1 + Q.1 = M.1`. The predicate
  `ColStrictSym 0 2 P Q` quantifies over `Fin (min 0 2) = Fin 0`, hence is
  vacuously **true**, hence `¬ColStrictSym` is **false**, hence the LHS
  filter is empty. **LHS card = 0**.
- RHS: `P', Q' : Sym (Fin 1) 1 = {{0}}` give the unique split `({0}, {0})`
  with `P'.1 + Q'.1 = {0,0} = M.1`. **RHS card = 1**.

So the original statement claimed `0 = 1`. The fix is to add `(hba : b ≤ a)`
to the lemma signature: with `b ≤ a` we have `min a b = b ≥ 2`, so
`ColStrictSym` becomes a genuine first-`b`-columns strictness condition and
the JDT slide bijection is well-defined.

The lemma is `private` and has a single call site (in `jdt_weight_sum`),
which already carries `hba : b ≤ a` in scope — propagation is one extra
argument at the rewrite site.

## Active Approach (post-S22, post-S23 fiber bridges)

For `jdt_weight_sum` (b ≥ 2), the b≥2 branch is now closed modulo
`ballot_counting_identity`:
- **Step (i)** ✓: weight factorisation via `weight_eq_total_multiset` /
  `weight_eq_totalSym` / `weight_eq_totalSym'` (S19, S22).
- **Step (ii)** ✓: regroup LHS / RHS by total multiset `M : Sym (Fin n) (a+b)`
  via `Finset.sum_fiberwise_of_maps_to` — packaged as
  `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (S23).
- **Step (iii)**: per-fiber count equality via `ballot_counting_identity`
  (sorry; signature corrected S21).
- **Step (iv)** ✓: combine — single `Finset.sum_congr rfl` line.

The deep remaining work is the bijection inside `ballot_counting_identity`
itself (~150 lines, reflection / cycle lemma over multisets).

## This session (S24) — strategy decomposition

Research-only iteration, no code change. See
`sessions/2026-05-08-s24.md` for the full write-up.

Key finding: the ~150-line bijection target decomposes into three named
sub-lemmas with sharply different difficulty profiles:

1. **`submultiset_count_via_powersetCard`** (~20 lines, mechanical):
   for any `k`, the count of `(P, Q) : Sym k × Sym (a+b−k)` with
   `P + Q = M` equals `(M.1.powersetCard k).card`. Forward:
   `PQ ↦ PQ.1.1`; inverse: `P ↦ (P, M.1 − P)` via `Multiset.sub_add_cancel`.

2. **`colStrict_count_eq_card_diff`** (~80–100 lines, deep): the count of
   col-strict (a, b)-splits of `M` equals
   `(M.1.powersetCard a).card − (M.1.powersetCard (a + 1)).card`. Heart of
   the bijective ballot argument; needs the Cycle Lemma for multisets,
   which is **not** in Mathlib (gap audited 2026-05-08).

3. **`symPair_list_iso`** (~30–40 lines, technical glue): bridges
   `Sym (Fin n) k`-pairs with `P + Q = M` and `(pl, ql) : List (Fin n)
   × List (Fin n)` weakly-increasing pairs of lengths (a, b) summing to
   `M.1.sort`. Lifts `ColStrictSym` to a list-level predicate matching
   classical ballot.

`ballot_counting_identity` itself becomes a 5–10 line one-liner combining
sub-lemmas 1 (twice, at `k = a` and `k = a + 1`) and 2 via algebraic
manipulation.

This decomposition does **not** change the file's sorry count (still 2).
Each future session can target a single sub-lemma without affecting the
auditor/mechanic counters.

### Why the obvious forward map still fails (re-confirmed)

Re-verified PR #14891 / S18: the `(P, Q) ↦ swap-at-first-violation`
forward map is non-injective for `b ≥ 2` and tagging the codomain with
the violation column does **not** restore injectivity (one (P, Q) with
multiple violations contributes multiple tagged sources mapping to a
common (P', Q')). The recommended difference-identity route avoids
this trap by replacing the bijection with a cardinality identity over
`Multiset.powersetCard`.

## This session (S21)

Completed:
- Identified the missing `b ≤ a` hypothesis on `ballot_counting_identity`
  via concrete counter-example computation (above).
- Added `(hba : b ≤ a)` to the lemma signature.
- Updated the docstring with the counter-example and the JDT-slide
  asymmetry explanation.
- Propagated `hba` at the unique call site
  `rw [ballot_counting_identity n a b hb2 hba M]` in `jdt_weight_sum`.
- Added an `originalContributions` entry documenting the S21 correction.

## Earlier sessions (summary)

- **S22-S23**: `jdt_weight_lhs_fibered`, `jdt_weight_rhs_fibered`,
  `totalSym_eq_iff` / `totalSym'_eq_iff`, `weight_eq_totalSym` /
  `weight_eq_totalSym'`. Closed the b≥2 branch of `jdt_weight_sum` modulo
  `ballot_counting_identity`.
- **S20**: stated `ballot_counting_identity` (sorry); added `totalSym` /
  `totalSym'` (Sym-wrapper for the total multiset).
- **S19**: `weight_eq_total_multiset` (cornerstone weight identity);
  `min_ab_pos_of_not_colStrict`, `exists_first_violation_idx` (auxiliary).
- **S17**: `jdt_weight_sum_b_one` (b=1 base case, 75-line proof).
- **S15-S16**: `not_colStrictSym_a_one_iff_qhead_le_phead`,
  `colStrictSym_a_one_iff_phead_lt_qhead`, `sym_one_sort_head_singleton`.
- **S~9**: `jdt_weight_preserved` (single-element move identity).

## Attempt Count

- Total iterations: 26 (sessions 1-26).
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14).
  2. Decompose `jdt_weight_sum` (S15).
  3. `ColStrictSym` b=1 characterisation (S16).
  4. `jdt_weight_sum_b_one` bijection (S17) ✓.
  5. Diagnose non-injective bijection + correct path (S18, PR #14891) ✓.
  6. Weight-factorization helper + auxiliary `¬ColStrictSym` lemmas (S19) ✓.
  7. Extract `ballot_counting_identity` + `totalSym` / `totalSym'` helpers (S20) ✓.
  8. `totalSym_eq_iff` / `weight_eq_totalSym` bridges + structural strategy (S22) ✓.
  9. `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` — close b≥2 branch
     of `jdt_weight_sum` modulo `ballot_counting_identity` (S23) ✓.
 10. Identify missing `b ≤ a` hypothesis on `ballot_counting_identity` +
     correct signature + propagate at call site (S21) ✓.
 11. Decompose `ballot_counting_identity` proof into three named
     sub-lemmas via difference-identity route (S24) ✓.
 12. Implement Sub-lemma 1 `split_count_eq_powersetCard_card` (S25,
     PR #17334 — but lemma was mathematically false as stated; merged with
     `(build pending)` status by deployer-no-build auto-merge anti-pattern).
 13. Correct Sub-lemma 1 statement → `split_count_eq_subSym_le_count`
     (RHS now uses `Sym (Fin n) p`-count of distinct submultisets, not
     `Multiset.powersetCard p`'s positional count); add Sub-lemma 2 stub
     `colStrict_count_add_eq_subSym_le_count` (sorry, deferred S27+);
     refactor `ballot_counting_identity` body to use Sub-lemmas 1+2 +
     Finset.filter_card_add + omega (S26, this session) ✓.

## Blockers

None for current approach. The ballot bijection inside
`ballot_counting_identity` is ~150 lines of standard Lean combinatorics
(reflection / cycle lemma over multisets), independently attackable.

## Next Action

1. ✅ **S25**: Sub-lemma 1 implemented as `split_count_eq_powersetCard_card` —
   later corrected in S26 to `split_count_eq_subSym_le_count` with the
   distinct-submultiset RHS.

2. ✅ **S26**: Sub-lemma 1 correction + Sub-lemma 2 stub
   (`colStrict_count_add_eq_subSym_le_count`, additive form, `sorry`) +
   `ballot_counting_identity` body refactor (composes Sub-lemmas 1 + 2 +
   `Finset.filter_card_add_filter_neg_card_eq_card` + `omega`).

3. ✅ **S27**: Sub-lemma 2A (`colStrict_pair_count_eq_subSym_filtered_count`):
   pair count ↔ single-Sym filtered count bijection for col-strict subsets;
   strict refinement of Sub-lemma 1.

4. ✅ **S28**: Sub-lemma 2B
   (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`, single-Sym
   sharpest form, `sorry`) + Sub-lemma 2 body closure via Sub-lemma 2A +
   Sub-lemma 2B + filter partition + `Finset.filter_filter` + `omega`. The
   pair encoding is fully dissolved from the cycle-lemma input; the
   remaining sorry is on the canonical single-Sym statement.

5. ✅ **S29 (this session)**: Canonical-complement bridge infrastructure
   for Sub-lemma 2B's eventual cycle-lemma proof. Three pure private
   helpers added just before Sub-lemma 2B:
   `comp_card_eq` ((M.1 − P.1).card = b), `comp_add_eq`
   (P.1 + (M.1 − P.1) = M.1), and `noColStrict_iff_canonicalComp` (the
   bridge between the existential and canonical-complement forms of the
   "bad P" predicate). Sub-lemma 2B's statement and proof remain
   unchanged; the bridge is available for `Finset.filter_congr`-based
   reformulation at the cycle-lemma proof step. Net sorry count
   unchanged at 2.

6. **S30+**: Attack **Sub-lemma 2B** via the multiset Cycle Lemma. The
   target statement:

   ```lean
   private lemma noColStrict_subSym_a_count_eq_subSym_le_aplus1_count
       {n a b : ℕ} (hb : 2 ≤ b) (hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
       ((Finset.univ : Finset (Sym (Fin n) a)).filter
         (fun P => P.1 ≤ M.1
                    ∧ ¬ ∃ Q : Sym (Fin n) b,
                          P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q)).card =
       ((Finset.univ : Finset (Sym (Fin n) (a + 1))).filter
         (fun P => P.1 ≤ M.1)).card
   ```

   ~80–100 lines; the dominant cost. Two sub-paths:

   * **6a — Mathlib contribution**: implement the Cycle Lemma for sorted
     multiset prefixes (Lyndon / Dvoretzky-Motzkin generalised). Independent
     of this proof; reusable across other gallery work.
   * **6b — inline proof**: build the bijection directly using sorted-list
     representatives. Define the "shift one element from `Q` to `P`" map
     on the bad submultisets and prove it's a bijection to size-`(a+1)`
     submultisets via a multiset rotation argument. With S29's
     `noColStrict_iff_canonicalComp` available, the LHS predicate can
     be reformulated via `Finset.filter_congr` to the canonical-
     complement form before attacking the bijection — removing the
     existential `Q` from the predicate exposes rotation-equivariance
     and is the natural starting point for the inline construction.

7. **Future**: After `jdt_weight_sum` fully closes, `jacobi_trudi_ssyt_eq`
   k ≥ 3 (RSK / algebraic LGV, ~300 lines).

## File Status

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1623 → 1705 lines
  (+82 this session: three new private lemmas — `comp_card_eq`,
  `comp_add_eq`, `noColStrict_iff_canonicalComp` — with docstrings, plus a
  brief addendum to Sub-lemma 2B's docstring noting the bridge).
- Sorry count: 2 (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
  Sub-lemma 2B, `jacobi_trudi_ssyt_eq` k≥3 — net unchanged from S28).
- 0 axioms.
- Theorems / lemmas: 35 → 38 (+3: `comp_card_eq`, `comp_add_eq`,
  `noColStrict_iff_canonicalComp`; all pure proofs, no sorries).
- Definitions: 8 (unchanged).
