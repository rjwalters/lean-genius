# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-08 (S25 — researcher-10)
**Iteration**: 25

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

- Total iterations: 25 (sessions 1-25).
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
 12. Implement Sub-lemma 1 `split_count_eq_powersetCard_card` —
     `Finset.card_bij` between multiset-split pairs and submultisets
     (S25, this session) ✓.

## Blockers

None for current approach. The ballot bijection inside
`ballot_counting_identity` is ~150 lines of standard Lean combinatorics
(reflection / cycle lemma over multisets), independently attackable.

## Next Action

1. ✅ **S25 (this session)**: Sub-lemma 1 implemented as
   `split_count_eq_powersetCard_card` — generic in `(p, q)` so it serves
   both LHS (`p = a, q = b`) and RHS (`p = a + 1, q = b - 1`) of
   `ballot_counting_identity`. ~49 lines including docstring.

2. **S26**: State **Sub-lemma 2** (`colStrict_count_eq_card_diff`) with
   `sorry`. The signature is the difference identity:

   ```lean
   private lemma colStrict_count_eq_card_diff {n a b : ℕ}
       (hb : 2 ≤ b) (hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
       ((M.1.powersetCard a).filter
         (fun P => /- ColStrict_b on (P.toSym, (M.1 - P).toSym) -/)).card =
       (M.1.powersetCard a).card - (M.1.powersetCard (a + 1)).card
   ```

   Then replace the body of `ballot_counting_identity` with a one-liner
   combining Sub-lemma 1 (twice — for `p = a, b` and `p = a + 1, b - 1`)
   with Sub-lemma 2 to convert both sides to `M.powersetCard`-cardinality
   arithmetic. Net sorry count: unchanged (one `sorry` replaces another,
   with cleaner provenance).

3. **S27+**: Attack **Sub-lemma 2** proof via the Cycle Lemma route.
   ~80–100 lines; the dominant cost. Requires either a small Mathlib
   contribution (Cycle Lemma for sorted multiset prefixes) or an
   inline proof.

4. **Future**: After `jdt_weight_sum` fully closes, `jacobi_trudi_ssyt_eq`
   k ≥ 3 (RSK / algebraic LGV, ~300 lines).

## File Status

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1266 → 1315 lines
  (+49 this session: Sub-lemma 1 + docstring).
- Sorry count: 2 (`ballot_counting_identity`, `jacobi_trudi_ssyt_eq` k≥3,
  both unchanged).
- 0 axioms.
- Theorems / lemmas: +1 (`split_count_eq_powersetCard_card`).
- Definitions: 8 (unchanged).
