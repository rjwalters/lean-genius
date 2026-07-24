# Current State

**OQ-03a PROVED, OQ-03b recursion layer PROVED** (2026-07-24,
researcher-1, S9): `RamseyHypergraph.lean` is **0-sorry / 0-axiom**
(1007 LOC, 26 theorems). S8 closed `ramsey_existence` (OQ-03a); S9
added the `sInf` glue lemmas and the **recursive Erdős–Rado
inequality** `R_{k+1}(s,t) ≤ R_k(R_{k+1}(s-1,t), R_{k+1}(s,t-1)) + 1`
(`ramseyNumber_succ_le`). Remaining sub-goals: S10 unwinds the
recursion into the tower bound (OQ-03b, quantitative form) and OQ-03c
(Erdős–Hajnal stepping-up lower bound).

**Phase**: ACT (S9 closes the recursion layer of OQ-03b; S10 targets
the tower unwind)
**Since**: 2026-07-24 (S9, researcher-1)
**Iteration**: 9
**Researcher**: researcher-1 (S9, S8 ACT-F, S7 ACT-E, S5-prep, S4-prep); researcher-9 (S6 ACT-D, S4 ACT-C, S2); researcher-11 (S3); researcher-8 (S1)

## Current Focus

Session 9 (S9, researcher-1, 2026-07-24): the quantitative glue layer
of OQ-03b. Five new sorry-free declarations (lines 835 → 1007, +172),
all in a new "S9" section at the end of the file:

* `ramseyNumber_le_of_isRamsey {n k s t} (h : IsRamsey n k s t) :
  ramseyNumber k s t ≤ n` — upper `sInf` glue, `Nat.sInf_le`. No side
  conditions.
* `isRamsey_ramseyNumber (k s t) (hk : 1 ≤ k) (hs : k ≤ s)
  (ht : k ≤ t) : IsRamsey (ramseyNumber k s t) k s t` — membership
  glue: `Nat.sInf_mem` on the defining set, nonempty by
  `ramsey_existence_of_one_le`.
* `min_le_ramseyNumber (k s t) (hk hs ht) : min s t ≤
  ramseyNumber k s t` — vertex-count lower bound: run the `sInf`
  witness on the constant-`true` coloring; the extracted clique's
  `card` (`= s` or `= t`) is at most the vertex count
  (`Finset.card_le_card (subset_univ _)` + `card_univ` + `card_fin`).
  This is what certifies inner `ramseyNumber` values as legal (≥ `k`)
  target sizes at lower uniformity — replacing the S8 `max`-bump.
* `IsRamsey.step {k s t n₁ n₂ m} (hs : 1 ≤ s) (ht : 1 ≤ t)
  (hn₁ : IsRamsey n₁ (k+1) (s-1) t) (hn₂ : IsRamsey n₂ (k+1) s (t-1))
  (hm : IsRamsey m k n₁ n₂) : IsRamsey (m+1) (k+1) s t` — the S8
  genuine-case recursion body extracted with explicit witnesses (link
  coloring at `v = Fin.last m`, certificate run in `univ.erase v` via
  `IsRamsey.within`, splice via `link_lifts` + `insert_vertex`). The
  S8 induction itself is left untouched (additive diff).
* `ramseyNumber_succ_le (k s t) (hk : 1 ≤ k) (hs : k + 2 ≤ s)
  (ht : k + 2 ≤ t) : ramseyNumber (k+1) s t ≤
  ramseyNumber k (ramseyNumber (k+1) (s-1) t)
  (ramseyNumber (k+1) s (t-1)) + 1` — **the recursive Erdős–Rado
  inequality** (OQ-03b, recursion layer): instantiate `IsRamsey.step`
  at the three `sInf` witnesses; `min_le_ramseyNumber` certifies
  `k ≤ n₁, n₂` (since `min (s-1) t ≥ k+1` in the hypothesis range);
  conclude by `ramseyNumber_le_of_isRamsey`.

Build: host-verified in-worktree (`lake env lean`, toolchain v4.31.0),
exit 0, no errors; only pre-existing deprecation/lint warnings from
S3–S8 code. `leanFile` counts: lineCount 835 → 1007, theoremCount
21 → 26 (+5), defCount 5, sorryCount 0, axiomCount 0.

## Prior Session Focus (S8 ACT-F)

Session 8 (S8 ACT-F, researcher-1, 2026-07-24): run the Ramsey 1930
recursion body, close the file's last sorry. Two new declarations
(lines 684 → 835, +151):

* `IsRamsey.within {ν k s t} (hR : IsRamsey ν k s t) {m}
  (χ : kColoring m) (A : Finset (Fin m)) (hA : A.card = ν)` — the
  **transfer lemma**: run a Ramsey certificate inside any size-matched
  vertex subset `A`, producing a monochromatic `s`- or `t`-clique
  **contained in `A`**. Pulls `χ` back along
  `(A.orderEmbOfFin hA).toEmbedding`, extracts the clique on the
  `Fin ν` side, pushes forward; monochromaticity transports along
  `Finset.subset_map_iff` (the `mono_n` pattern, relativized). This one
  lemma serves both restriction steps of the classical proof.
* `ramsey_existence_of_one_le : ∀ k s t, 1 ≤ k → k ≤ s → k ≤ t →
  ∃ n, IsRamsey n k s t` — the two-layer induction. Outer: structural
  induction on `k`; base `k = 1` is `isRamsey_one_iff` with
  `n = s + t - 1`. Inner: **bounded** induction on `s + t ≤ N` (plain
  `Nat.rec` — deliberately avoids `Nat.strongRecOn` naming/API drift);
  boundaries `s = k` / `t = k` via `is_ramsey_self_right/left`. Genuine
  step (`s, t > k + 1`): inner IH gives `n₁` for `(s-1, t)` and `n₂`
  for `(s, t-1)`, bumped to `max nᵢ k` via `mono_n` to satisfy the
  outer IH's target-size side conditions; outer IH gives `m` with
  `IsRamsey m k (max n₁ k) (max n₂ k)`; witness is `m + 1`. For any
  `χ`: run the `k`-uniform certificate on `kColoring.link χ v`
  (`v = Fin.last m`) within `univ.erase v` (`IsRamsey.within`); in the
  link-mono-`c` clique `S`, run `hn₁`/`hn₂` within `S`; either the
  opposite-color full-size clique appears outright, or a `c`-colored
  clique one short of target is spliced with `v` via `link_lifts` +
  `insert_vertex` (`powersetCard_mono` bridges
  `insert v S' ⊆ insert v S`).
* `ramsey_existence` now delegates to `ramsey_existence_of_one_le`.

Build: host-verified via sibling-worktree Mathlib oleans
(`lake env lean`, toolchain v4.31.0), exit 0. `leanFile` counts:
lineCount 684 → 835, theoremCount 19 → 21 (+`within`,
+`ramsey_existence_of_one_le`), defCount 5, sorryCount 1 → 0,
axiomCount 0.

## Prior Session Focus (S7 ACT-E)

Session 7 (S7 ACT-E, researcher-1, 2026-06-04): land the splice lemma
`IsMonochromatic.insert_vertex` — the single missing ingredient
between the S6 link infrastructure (`kColoring.link`,
`IsMonochromatic.link_lifts`) and the Ramsey 1930 inductive step. One
sorry-free declaration lands in `RamseyHypergraph.lean`, lines 654 →
688 (+34):

* `IsMonochromatic.insert_vertex {n k} {χ : kColoring n} {c}
  {v : Fin n} {S' : Finset (Fin n)} (hvS' : v ∉ S')
  (hS' : IsMonochromatic χ k S' c)
  (hLink : ∀ T ∈ (insert v S').powersetCard k, v ∈ T → χ T = c) :
  IsMonochromatic χ k (insert v S') c` —
  the splice composing a non-vertex-side `k`-mono sub-clique `S'`
  with the vertex-side link-derived coverage `hLink` (produced by
  `link_lifts`) to yield the `k`-mono clique `insert v S'` of size
  `|S'| + 1`. Proof is a direct `by_cases hvT : v ∈ T` on each
  `k`-subset `T ⊆ insert v S'`: when `v ∈ T`, `hLink` discharges;
  when `v ∉ T`, `T ⊆ S'` and `hS'` discharges.

`leanFile` counts (`RamseyHypergraph.lean`): lineCount 654 → 688
(+34), theoremCount 18 → 19 (+1 for `insert_vertex`), defCount 5
(unchanged), sorryCount 1 (unchanged), axiomCount 0 (unchanged).

The lone surviving sorry in `ramsey_existence` (the `s > k ∧ t > k`
genuine inductive case) is unchanged. With `insert_vertex` landed, the
**non-recursive** ingredients of the Ramsey 1930 proof are complete;
S8 ACT-F can run the `Nat.strongRecOn` induction body and close the
file's last sorry.

## Prior Session Outputs (S6 ACT-D, researcher-9)

Session 6 (S6 ACT-D, researcher-9, 2026-05-12): introduce the link
(neighborhood) coloring infrastructure that drives the Ramsey 1930
recursion. Two sorry-free declarations land in `RamseyHypergraph.lean`,
lines 584 → 654 (+70):

* `kColoring.link (χ : kColoring n) (v : Fin n) : kColoring n` —
  the link coloring at `v`, sending `T` to `χ (insert v T)`. Encoded
  type-uniformly on the full `Fin n` so the uniformity stays implicit
  (it is supplied by `IsRamsey`'s `k` parameter). Defining `simp`
  rule: `kColoring.link_apply`.
* `IsMonochromatic.link_lifts (χ : kColoring n) (v : Fin n) (c : Bool)
  (S : Finset (Fin n)) (hvS : v ∉ S)
  (hSm : IsMonochromatic (kColoring.link χ v) (k - 1) S c) :
  ∀ T ∈ (insert v S).powersetCard k, v ∈ T → χ T = c` —
  the vertex-side `(k-1) → k` monochromaticity transfer. Decomposes
  every such `T` as `insert v T'` with `T' = T.erase v ⊆ S` and
  `|T'| = k - 1`, then evaluates `hSm` on `T'` via
  `Finset.insert_erase` + `Finset.card_erase_of_mem` +
  `kColoring.link_apply`. Works at every `k ≥ 0` (the `k = 0` case is
  vacuous: `v ∈ T` with `|T| = 0` is impossible).

`leanFile` counts (this file): lineCount 584 → 654 (+70), theoremCount
17 → 18 (+1 for `link_lifts`; `link_apply` is `@[simp] lemma`),
defCount 4 → 5 (+1 for `kColoring.link`), sorryCount 1 (unchanged),
axiomCount 0 (unchanged).

Together these are the splice infrastructure for S7 ACT-E: combine
with `anti_s` / `anti_t` / `mono_n` (S4-S5) to build
`IsMonochromatic.insert_vertex` (a `k`-mono sub-clique on the
non-vertex side, plus link-monochromaticity of the full neighborhood,
imply `insert v S'` is `k`-mono of size `|S'| + 1`), then run the
double induction on `(k, s + t)` against `is_ramsey_self_*` as base.

## Prior Session Outputs (S5-prep, researcher-1)

Session 5 (S5-prep, researcher-1, 2026-05-12): widen the
`ramsey_existence` inductive-step toolkit with three monotonicity facts
independent of the deferred sorry. Reconstructs the orphan branch
`research/erdos-szekeres-oq-03-s5-mono-helpers-1778575256` (authored
2026-05-12 01:46 UTC, PR never created) on top of the post-S4-ACT-C state.

Output of this session (build pending; the local worktree shares the broken
`proofs/.lake` symlink per memory `feedback_researcher_lake_symlink_broken.md`):

* `proofs/Proofs/RamseyHypergraph.lean` — 500 → 584 lines, +84.
  New sorry-free lemmas, placed between `is_ramsey_self_left` and
  `ramsey_existence` so that all monotonicity helpers precede the S5 target:
  - `IsMonochromatic.mono {n k} {χ : kColoring n} {c} {S S'} :
    S' ⊆ S → IsMonochromatic χ k S c → IsMonochromatic χ k S' c`
    — subset closure: every `k`-subset of `S'` is a `k`-subset of `S` via
    `Finset.mem_powersetCard` + `Finset.subset.trans`.
  - `IsRamsey.mono_n {n m k s t} (h : n ≤ m) : IsRamsey n k s t →
    IsRamsey m k s t` — monotonicity in `n` via the canonical embedding
    `Fin n ↪ Fin m` built as `⟨Fin.castLE h, Fin.castLE_injective h⟩`.
    Restrict any coloring of `[m]^{(k)}` to `χ' := fun S ↦ χ (S.map f)`
    on `[n]^{(k)}`; obtain a clique `S ⊆ Fin n` by hypothesis; lift to
    `S.map f` and use `Finset.subset_map_iff` to recognise each
    `k`-subset of `S.map f` as `T₀.map f` for some `T₀ ⊆ S` of card `k`,
    where monochromaticity of `T₀` under `χ'` is already known.
  - `ramseyNumber_swap (k s t : ℕ) : ramseyNumber k s t = ramseyNumber k t s`
    — direct corollary of `IsRamsey.swap`: the two `sInf`-defining sets
    agree pointwise.
* New import: `Mathlib.Data.Finset.Map` (for `Finset.subset_map_iff`).
* `leanFile` counts (this file): lineCount 500 → 584 (+84), theoremCount
  14 → 17 (+3), defCount 4 (unchanged), sorryCount 1 (unchanged),
  axiomCount 0 (unchanged).

## Prior Session Outputs (S4 ACT-C, researcher-9)

Session 4 (S4 ACT-C, researcher-9, 2026-05-12): factored `ramsey_existence`
through the two boundary cases (`s = k` and `t = k`) and the
anti-monotonicity of `IsRamsey` in both target sizes. The remaining sorry
is now restricted to the genuine inductive content `s > k ∧ t > k`.

Output of this session (build pending; the local worktree shares the broken
`proofs/.lake` symlink per memory `feedback_researcher_lake_symlink_broken.md`):

* `proofs/Proofs/RamseyHypergraph.lean` — 373 → 500 lines, +127.
  New sorry-free lemmas:
  - `IsRamsey.anti_s {n k s s' t} : s' ≤ s → IsRamsey n k s t → IsRamsey n k s' t`
    — anti-monotonicity in the `false`-target. Extract an `s'`-sub-clique of
    the `s`-clique via `Finset.exists_subset_card_eq`; monochromaticity
    descends to subsets through `Finset.subset.trans` on `mem_powersetCard`.
  - `IsRamsey.anti_t` — symmetric in `t`.
  - `is_ramsey_self_right (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    IsRamsey t k k t` — the `s = k` boundary case at `n = t`. Case-split on
    `∃ S, |S| = k ∧ χ S = false`:
      - **Case A.** Some `k`-subset `S` is colored `false` ⇒ `S` itself is the
        mono-`false` `k`-clique. Sole `k`-sub-subset `T ⊆ S` satisfies
        `|T| = k = |S|`, so `T = S` by `Finset.eq_of_subset_of_card_le`.
      - **Case B.** No `k`-subset is `false` ⇒ every `k`-subset is `true`,
        and `Finset.univ` (card `t` by `Fintype.card_fin`) is the mono-`true`
        `t`-clique.
  - `is_ramsey_self_left (k s : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) :
    IsRamsey s k s k` — `t = k` boundary, via `IsRamsey.swap.mpr` of
    `is_ramsey_self_right k s hk hks`.
* `ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t)`:
  refactored to discharge both boundaries:
  - `s = k`: take `n = t`, apply `is_ramsey_self_right`.
  - `t = k`: take `n = s`, apply `is_ramsey_self_left`.
  - `s > k ∧ t > k`: the genuine inductive case; deferred to S5.
* `leanFile` counts (this file): lineCount 373 → 500 (+127), theoremCount
  10 → 14 (+4), defCount 4 (unchanged), sorryCount 1 (unchanged),
  axiomCount 0 (unchanged).

## Prior Session Outputs (S3, researcher-11)

* `proofs/Proofs/RamseyHypergraph.lean`: `isRamsey_one_iff` and
  `ramseyNumber_one s t = s + t - 1`. PR #17960 merged (build verified).

S3 introduced `isRamsey_one_iff (n s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
IsRamsey n 1 s t ↔ s + t - 1 ≤ n` (forward via `Finset.filter_card_add_filter_neg_card_eq_card`
pigeonhole + `Finset.exists_subset_card_eq`; backward via the
`min (s-1) n`-prefix bad coloring with two `Fin.val_injective` card bounds)
and derived `ramseyNumber_one` by `Nat.sInf` on the upward-closed set
`{n | s + t - 1 ≤ n}`.

## Prior Session Outputs (S2, researcher-9)

* `proofs/Proofs/RamseyHypergraph.lean` (147 lines): API surface
  (`kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`) +
  `isMonochromatic_of_card_lt`, `isMonochromatic_empty_zero`,
  `is_ramsey_zero_false`, `is_ramsey_zero_true`; `ramsey_existence` and
  `ramseyNumber_one` stated as sorries. PR #17909 merged.

## Prior Session Outputs (S1, researcher-8)

* `problem.md` — formal restatement of OQ-03 as three sub-goals.
* `knowledge.md` — literature survey + Mathlib API audit.

## Active Approach

Three-step Lean formalization plan (S2 → S4):

1. **S2 (ACT-A).** Define `RamseyK.IsRamsey n k s t` and
   `RamseyK.ramseyNumber k s t`. Prove the `k = 1` sanity check
   `ramseyNumber 1 s t = s + t - 1` via pigeonhole (~30 lines of Lean,
   no new Mathlib dependencies). State `ramsey_existence` as a sorry.
2. **S3 (ACT-B).** Discharge `ramsey_existence` via the two-layer
   neighborhood induction. Base case `k = 2` reuses
   `SimpleGraph.ramseyNumber`'s existence proof (or re-proves it inline
   using pigeonhole). Inductive step uses the "fix a vertex, induct on
   `(k-1)`-coloring of neighborhood" construction.
3. **S4 (ACT-C).** State `erdos_rado_upper` as `ramseyNumber k s s ≤
   tower (k-1) (c_k * s)`. Likely needs an explicit `c_k` (e.g.
   `c_k = 4 * (k-1)!`); the tower function can be defined via
   `Nat.iterate (2 ^ ·) (k-1) (c_k * s)` so no new tower API.
   Proof: follow the Erdős–Rado recursive bound
   `R_k(s,t) ≤ R_{k-1}(R_k(s-1,t), R_k(s,t-1)) + 1`, unwound.

S5+ would tackle the stepping-up lower bound (OQ-03c), but only after S4
lands. The lower bound is harder and may need its own sub-OQ.

## Blockers

None for S2 (definitions are straightforward Mathlib boilerplate).

For S3/S4: `Hypergraph` is not yet in Mathlib, so we work directly with
`Finset (Fin n)` filtered by `card = k` (`Finset.powersetCard`). This is
adequate but verbose.

## Next Action

**S10 — Tower unwind of the Erdős–Rado recursion (OQ-03b,
quantitative form).**

S9 landed the glue (`ramseyNumber_le_of_isRamsey`,
`isRamsey_ramseyNumber`, `min_le_ramseyNumber`) and the recursion
inequality `ramseyNumber_succ_le`. What remains for OQ-03b:

1. **Diagonal-friendly wrappers**: `ramseyNumber (k+1) s s ≤ ...`
   specializations, and a graph-level anchor `ramseyNumber 2 s t ≤
   Nat.choose (s + t - 2) (s - 1)` (or just cite `ramseyNumber_one` as
   the base — the unwind can start at `k = 1`).
2. **S10 main**: define `tower : ℕ → ℕ → ℕ` (e.g.
   `Nat.iterate (2 ^ ·)`) and prove by induction on `k` that iterating
   `ramseyNumber_succ_le` down to the pigeonhole base
   `ramseyNumber_one` gives `ramseyNumber k s s ≤ tower (k - 1) (c_k * s)`
   for an explicit `c_k`. The delicate part is bounding the *double*
   recursion (both `s` and `t` shrink) by a single-variable tower —
   the classical trick bounds `R_{k+1}(s,t) ≤ R_k(R_{k+1}(s-1,t) +
   R_{k+1}(s,t-1), ·)`-style sums by monotonicity
   (`IsRamsey.anti_s/anti_t` give `ramseyNumber` monotonicity in the
   targets via the glue lemmas — worth stating as its own S10-prep
   lemma `ramseyNumber_mono`).
3. **S11+**: OQ-03c (Erdős–Hajnal stepping-up lower bound) per the
   S-up-4 PREP notes below.

## Attempt Counts

- Total attempts: 9
- Current approach attempts: 9
- Approaches tried: 9 (literature survey + Lean API design; S2 scaffold;
  S3 `ramseyNumber_one` via pigeonhole iff helper; S4 ACT-C boundary
  factoring + anti-monotonicity; S5-prep monotonicity helpers; S6 ACT-D
  link/neighborhood coloring infrastructure; S7 ACT-E splice lemma
  `insert_vertex`; S8 ACT-F transfer lemma `IsRamsey.within` + two-layer
  induction `ramsey_existence_of_one_le` — OQ-03a closed; S9 `sInf` glue
  + `IsRamsey.step` + `ramseyNumber_succ_le` — OQ-03b recursion layer
  closed)

## Outcome of S1

ORIENT complete. Three sub-goals (existence, Erdős–Rado upper, Erdős–Hajnal
lower) cleanly stated; Mathlib gaps identified; S2 ACT-A is unblocked.

## Outcome of S2

S2 SCAFFOLD landed (build pending). `RamseyHypergraph.lean` adds 4
definitions and 4 sorry-free supporting lemmas alongside 2 sorries
(`ramsey_existence`, `ramseyNumber_one`). The `IsMonochromatic`-of-too-small
helper and the `s=0` / `t=0` degenerate Ramsey base cases form the
foundation for S3's pigeonhole and inductive arguments. PR #17909 merged.

## Outcome of S3

S3 closed `ramseyNumber_one s t = s + t - 1` (the `k = 1` pigeonhole
sanity check), reducing the file's `sorryCount` 2 → 1. The proof
introduces a new helper `isRamsey_one_iff : IsRamsey n 1 s t ↔
s + t - 1 ≤ n` that factors the result cleanly. Forward direction uses
`Finset.filter_card_add_filter_neg_card_eq_card` plus
`Finset.exists_subset_card_eq` for the pigeonhole; reverse (contrapositive)
constructs the bad coloring with `min (s-1) n` `false`-singletons and
bounds the clique cards via `Finset.range`/`Finset.Ico` images of the
globally-injective `Fin.val`. `ramseyNumber 1 s t = s + t - 1` then
follows from the iff via `Nat.sInf` on the upward-closed set. PR #17960
merged.

## Outcome of S4-prep

S4-prep landed three sorry-free lemmas extending the API surface for the
S4 inductive proof: `IsRamsey.swap` (color symmetry via `χ ↦ !χ`, halving
the case analysis of any recursive bound) and `ramseyNumber_zero_false`/
`ramseyNumber_zero_true` (degenerate-side `ramseyNumber` collapses to 0
when one target size is 0). PR #17977 merged.

## Outcome of S4 ACT-C

S4 ACT-C delivered a structural factoring of `ramsey_existence`. Four new
sorry-free lemmas land: `IsRamsey.anti_s` and `IsRamsey.anti_t`
(anti-monotonicity in the target sizes via `Finset.exists_subset_card_eq`
sub-clique extraction), `is_ramsey_self_right` (the `s = k` boundary at
`n = t` via a direct Bool case-split on `∃ S, |S| = k ∧ χ S = false` —
either the false `k`-subset is the mono-`false` `k`-clique via
`Finset.eq_of_subset_of_card_le`, or `Finset.univ` is the mono-`true`
`t`-clique), and `is_ramsey_self_left` (the `t = k` boundary, via
`IsRamsey.swap.mpr`). `ramsey_existence` is then refactored to discharge
both boundaries via these helpers, with the lone surviving sorry confined
to the genuine inductive case `s > k ∧ t > k` (the S5 target). Build
pending (worktree shares the broken `proofs/.lake` symlink); proof
patterns mirror the S3 idioms (`cases hχ : χ T with`, `Finset.mem_powersetCard`
membership unfold) so build risk is low.

## Outcome of S5-prep

Three sorry-free monotonicity helpers land (build pending; worktree shares
the broken `proofs/.lake` symlink): `IsMonochromatic.mono` (subset
closure), `IsRamsey.mono_n` (monotonicity in `n` via the canonical
`Fin n ↪ Fin m` embedding `⟨Fin.castLE h, Fin.castLE_injective h⟩`, with
`χ' := fun S ↦ χ (S.map f)` as the restricted coloring and
`Finset.subset_map_iff` to recognise lifted clique-subsets), and
`ramseyNumber_swap` (corollary of `IsRamsey.swap` via congruence on the
`sInf`-defining set). File grows 500 → 584 lines (+84); theorem count
14 → 17 (+3); sorries / axioms unchanged at 1 / 0. New import:
`Mathlib.Data.Finset.Map`. Reconstructs the orphan branch
`research/erdos-szekeres-oq-03-s5-mono-helpers-1778575256` (authored
2026-05-12 01:46 UTC by a prior `researcher-1` session, PR never
created) on top of the post-S4-ACT-C state. PR #18122 merged.

## Outcome of S6 ACT-D

Two sorry-free declarations land (build pending; the local worktree
shares the same broken `proofs/.lake` symlink): `kColoring.link`
(the link/neighborhood coloring at a vertex `v`, `χ.link v T = χ (insert v T)`,
with a defining `@[simp] lemma kColoring.link_apply`) and
`IsMonochromatic.link_lifts` (the vertex-side `(k - 1) → k`
monochromaticity transfer: if `S ⊆ Fin n \ {v}` is `(k-1)`-mono for
`χ.link v` at colour `c`, then every `k`-subset `T ⊆ insert v S`
containing `v` has `χ T = c`, via the canonical decomposition
`T = insert v (T.erase v)` and `Finset.card_erase_of_mem`). File grows
584 → 654 lines (+70); theorem count 17 → 18 (+1); defCount 4 → 5
(+1 for `kColoring.link`); sorries / axioms unchanged at 1 / 0. No
new imports.

## Outcome of S7 ACT-E

One sorry-free declaration lands (build pending; the local worktree
shares the same broken `proofs/.lake` symlink):
`IsMonochromatic.insert_vertex` — the splice composing a non-vertex-side
`k`-mono sub-clique `S'` (hypothesis `hS'`) with the vertex-side
link-derived coverage `hLink` (produced by `link_lifts`) to yield the
`k`-mono clique `insert v S'` of size `|S'| + 1`. Proof is a direct
`by_cases hvT : v ∈ T` on each `k`-subset `T ⊆ insert v S'`: when
`v ∈ T`, `hLink` discharges; when `v ∉ T`, every `x ∈ T` lies in
`insert v S'` but is not `v`, so `T ⊆ S'` and `hS'` discharges. File
grows 654 → 688 lines (+34); theorem count 18 → 19 (+1); defCount 5
(unchanged); sorries / axioms unchanged at 1 / 0. No new imports.
With this lemma landed, the non-recursive ingredients of the Ramsey
1930 proof are complete; S8 ACT-F can run the `Nat.strongRecOn`
induction body on `(k, s + t)` and close the file's last sorry.
