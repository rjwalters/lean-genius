# Current State

**Phase**: ACT (S3c PREP backlog complete — all 5 step-design memos for Part VIII's proof sketch merged; 4 ACT candidates pending: Step 2 / Step 3 / Step 4 / Step 5. Step 1 is the only ACT closed in the chain so far.)
**Since**: 2026-05-11T22:00:00Z
**Last Updated**: 2026-05-13 (S3c-prep-{5,6,7,8,9} backlog sync by researcher-1; doc-only — no Lean edits, no `problem.md` / `knowledge.md` edits)
**Iteration**: 13

## S3c-PREP Backlog Sync (2026-05-13, researcher-1)

**Mode**: STATE-SYNC (doc-only). Between 2026-05-13T00:09Z (PR #18395, S3c-prep-5) and 2026-05-13T09:17Z (PR #18720, S3c-prep-9), five design-memo PREPs for Steps 2–5 of Part VIII's S3c proof sketch merged into `main` without back-propagating into `state.md`'s header or its session-log block. The `sessions/` sub-directory has all five files; the header still nominated "S3c continuation" with a Step-2-only focus from S3c-prep-4 (2026-05-12, researcher-12). This entry brings the header back in sync, packages the PREP chain's findings as a single forward-look table, and pins the recommended ACT ordering for the Step-{2,3,4,5} ACT authors.

### Step status spectrum

| Step | Description | PREP status | ACT status | ACT LOC budget |
|------|-------------|-------------|------------|----------------|
| 1 | Row 0 forced to all zeros (lattice prefix length 1) | — (closed) | **ACT closed** — Parts XII (#18126) + XIII (#18207, #18241); `skewSSYTFin_row0_forced_zero` at file lines 717–808 | — |
| 2 | Row 1 content determined (`c₀ = lam.parts 0 − r₀` zeros, `c₁ = lam.parts 1` ones) | **PREP merged** — #18395 (design memo) + #18579 (`Partition.weight_two_eq` + `Fintype.sum_sigma` v4.26.0 audit) | pending | ~80–110 LOC, 0 sorries |
| 3 | Row 1 step-function uniqueness (`j ↦ if j.val < c₀ then 0 else 1`) | **PREP merged** — #18636 + v4.26.0 backport skeleton (Mathlib HEAD's `Fin.lt_card_filter_univ_iff_apply_of_imp` absent at v4.26.0; ~30-LOC backport supplied) | pending | ~110 LOC, 0 sorries |
| 4 | Column-strict on overlap (Guard C) + row-2 lattice (Guard D) match `lrCoeff2`'s if-cascade | **PREP merged** — #18676 with two-table Mathlib-core audit (`List.count_append:283`, `List.count_replicate_self:334`, `Fin.lt_iff_val_lt_val:161`, …) | pending | ~80–110 LOC, 0 sorries (1 intentional auxiliary `sorry` flagged) |
| 5 | Bijection closure: `Fintype.card_eq_of_equiv` to singleton (all guards) / empty (any fail) | **PREP merged** — #18720 with `Fintype.card_unique` / `Fintype.card_eq_zero_iff` / `Unique.mk'` audit at pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | pending | ~160 LOC, 0 sorries (5a canonical 70 + 5b uniqueness 25 + 5c case-split 40 + adapters 25) |

### PREP entries (one line per merged PR)

* **S3c-prep-5 PREP — Step 2 row-1 content design memo** (#18395, 2026-05-13T00:09Z, researcher-6, doc-only +367 LOC). Pins target signatures `skewSSYTFin_row1_zero_count` + `skewSSYTFin_row1_one_count` (decoupling lattice-word reasoning into `hrow0`-as-hypothesis); flags `Nat`-subtraction trap on `lam.parts 0 − r₀` (needs `h_lam0_ge` prior corollary); flags `Partition.weight_two_eq` adapter as the only non-mechanical risk; vacuous `r₀ = 0` handled inline by Step 1's call site.
* **S3c-prep-6 PREP — `Partition.weight_two_eq` + Mathlib `sum_sigma` citation audit** (#18579, 2026-05-13T04:48Z, researcher-3, doc-only +445 LOC). Discharges the 5-min `Partition.weight_two_eq` probe nominated by S3c-prep-5 §3.4 / §9. Findings: `Partition.weight_two_eq` is not a named lemma in any of the 6 Hilbert-15 cluster files, but the load-bearing simp pattern `[Partition.weight, Fin.sum_univ_two]` is already in-scope at file line 283 (`toPartition2_size`); recommends Option B (4-line `@[simp]` adapter). Bearer table verified at Mathlib v4.26.0: `Fintype.sum_sigma` at `Data/Fintype/BigOperators.lean:148`, `Finset.sum_sigma` at `Algebra/BigOperators/Group/Finset/Sigma.lean:38`, `Fin.sum_univ_two` at `Algebra/BigOperators/Fin.lean:111`. `Fintype.card_filter_sigma` absent at v4.26.0 — manual chain is canonical.
* **S3c-prep-7 PREP — row-1 step-function uniqueness + Mathlib v4.26.0 backport audit** (#18636, 2026-05-13T07:17Z, researcher-5, doc-only +801 LOC). Key finding: the natural one-shot Mathlib bearer `Fin.lt_card_filter_univ_iff_apply_of_imp` (HEAD `Data/Fintype/Fin.lean:70`) and helper `Fin.card_filter_val_lt` (HEAD line 47) are absent at v4.26.0 — both lie in the 30-line post-v4.26.0 delta. Supplies ~30-LOC backport skeleton using only v4.26.0 primitives (`Fin.card_Iic`, `Finset.card_le_card`, `Finset.mem_filter`, `Finset.mem_Iic`, `Finset.mem_Iio`), replacing `grind` with explicit tactic chains. Step 3 target signatures: row-1 monotonicity adapter (parallels Part XII's `skewSSYTFin_row0_mono`), row-1 zero-downward-closure, step-function characterization main theorem, plus 2-line composite `skewSSYTFin_row1_unique_of_zero_count_eq` for cross-tableau uniqueness.
* **S3c-prep-8 PREP — Step 4 column-strict + row-2 lattice guard match** (#18676, 2026-05-13T08:07Z, researcher-12, doc-only +810 LOC). Guard C analysis: `SkewSSYTFin` column-strict at `(i₁, i₂) = (0, 1)` with `j₁ = μ.parts 1 + j₂.val − μ.parts 0`, composed with Step 1's row-0-all-zeros, forces `T ⟨1, j₂⟩ = 1` on the overlap region; combined with Step 3's row-1 step function this gives `c₀ ≤ μ.parts 0 − μ.parts 1`. Guard D analysis: `T.reverseRowWord = replicate r₀ 0 ++ replicate c₁ 1 ++ replicate c₀ 0` under Steps 1 + 3; lattice at prefix `r₀ + c₁` collapses to `c₁ ≤ r₀`, matching `r₁ < lam.b → 0`. Target signatures `skewSSYTFin_row1_one_of_overlap` (~22 LOC) + `skewSSYTFin_lattice_bound_row1` (~28 LOC) + helper `reverseRowWord_two_canonical` (~30 LOC, one internal `sorry` on the `(finRange r₁).reverse.map ↦ replicate` chain flagged via §6.7 mitigation: factor as separate `List.reverse_map_finRange_step_function` helper).
* **S3c-prep-9 PREP — Step 5 bijection closure design memo** (#18720, 2026-05-13T09:17Z, researcher-1, doc-only +~850 LOC). Step 5 ACT decomposition: 5a `canonicalFun ν μ c₀` construction with row-weak + column-strict + content + lattice-word fields (~70 LOC); 5b `Subsingleton` instance for the filtered subtype packaging Steps 1 + 2 + 3's forward directions (~25 LOC); 5c case-split closure via `allGuardsHold` predicate + `Fintype.card_unique` / `Fintype.card_eq_zero_iff` (~40 LOC). All bearers verified at pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — no new bearer needs to be added. The overlap-empty case in Guard C is vacuous on both sides. Recommended `lrCoeff2_eq_one_iff_allGuardsHold` adapter (~25 LOC) gives a cleaner Step-5c diff than a 6-way `by_cases` walk through `lrCoeff2`'s if-cascade.

### ACT candidates — recommended ordering and budget

The five PREP memos collectively pin every Mathlib API + tactic decision for Step 2 → Step 5 ACT. Recommended dependency-respecting ordering (matching S3c-prep-9 §1):

1. **Step 2 ACT** (~80–110 LOC, low risk). Row-1 zero-count + one-count theorems using #18395 §4 skeletons + #18579's `Partition.weight_two_eq` adapter (Option B, ~4 lines). Discharges the content-equation arithmetic; unblocks Steps 3–5.
2. **Step 3 ACT** (~110 LOC, low/medium risk). Row-1 step-function uniqueness; the only non-trivial input is the ~30-LOC `Fin.lt_card_filter_univ_iff_apply_of_imp` v4.26.0 backport from #18636 §3.
3. **Step 4 ACT** (~80–110 LOC, medium risk). Guards C + D, leaning on Steps 1 + 3 outputs. The `reverseRowWord_two_canonical` helper carries the one auxiliary `sorry` flagged by #18676 §6.7 — factor as `List.reverse_map_finRange_step_function` to localize.
4. **Step 5 ACT** (~160 LOC, low risk after Steps 2–4 land). `canonicalFun` + `Subsingleton` + `Fintype.card_unique` / `card_eq_zero_iff`. All bearers in-scope at v4.26.0. Closes the file's single remaining `sorry` at line 413 (`lrCoeffN_def_two_eq_lrCoeff2_of_support`).

After Step 5 ACT, `lrCoeffN_def_two_eq_lrCoeff2` is unconditionally proved, enabling:

* **S3d** — lift the 7 verified Gr(2,4) `lrCoeff2 … = 1` (resp. `= 0`) results from `Hilbert15OQ02.lean` to `lrCoeffN_def`-form via `native_decide` after `rw [lrCoeffN_def_two_eq_lrCoeff2]`.
* **S4** — replace `axiom lrCoeffN` at `Hilbert15OQ02OQ03.lean:128` with `def lrCoeffN {n} := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`, reducing the parent file's axiom count 3 → 2 (only `admissible` and `klyachko_theorem` would remain).

### Honesty / scope guarantees

* **No Lean edits.** `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` is unchanged at 808 LOC / 1 sorry / 0 axioms.
* **No `problem.md` / `knowledge.md` edits.** This PR rewrites only `state.md` (this section + header line update) plus `currentState.{focus,nextAction,iteration}` + `knowledge.progressSummary` + `lastUpdate` in `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`.
* **No race with PR #17966.** That PR has been open since 2026-05-12T07:37Z with `mergeable=CONFLICTING` on protected `.lean` / `state.md` / JSON files; my edits to `state.md` and JSON are append-style (new header entry + new section) and do not touch the same regions #17966 modifies.
* **All PR titles, numbers, timestamps, line counts, authors verified** via `gh pr view <N> -R rjwalters/lean-genius` immediately before commit. The five PREP `sessions/` files (`2026-05-12-s3c-prep-5-row1-content.md`, `2026-05-13-s3c-prep-{6,7,8,9}-*.md`) are present on `origin/main` at the merge commits cited above.
* **STATE-SYNC counts as 1 of 2 per session** (cap per `[Researcher — STATE-SYNC variant for active threads with PREP backlog]` memory).

## S3c-Prep-4 Summary (2026-05-12, researcher-12)

**Mode**: ACT — supply the **single-cell input** required by S3c-prep-3
(`skewSSYTFin_row0_eq_zero_of_top_zero`) by instantiating the lattice-word
predicate at prefix length `1` of `T.reverseRowWord`. With this Part XIII
in place, Step 1 of Part VIII's S3c proof sketch — "row 0 is forced to all
zeros" — is fully discharged under the positivity hypothesis `0 < r₀`,
exposed as the corollary `skewSSYTFin_row0_forced_zero`.

### Deliverable

Append Part XIII (S3c-Prep-4) to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`
(+131 lines, 677 → 808; 1 sorry unchanged; +1 private helper, +2 public
theorems, +1 composed corollary; 0 axioms):

* `reverse_finRange_take_one_of_pos` (private helper) — For `r > 0` and
  any `f : Fin r → α`, the `take 1` prefix of
  `(List.finRange r).reverse.map f` equals the singleton
  `[f ⟨r - 1, Nat.sub_lt h Nat.one_pos⟩]`. Proved by
  case-decomposition `r = k + 1` (via
  `Nat.exists_eq_succ_of_ne_zero` with the `rfl` pattern) followed by
  `List.finRange_succ` unfolding into `(finRange k).map Fin.castSucc ++
  [Fin.last k]`; reversing puts `Fin.last k` at the head, then
  `take 1` reduces to `[f (Fin.last k)]`. The `(k+1) - 1 = k`
  identification with `Fin.last k`'s `.val = k` closes by `rfl` via
  proof-irrelevance on `Fin`'s `isLt` field.

* `reverseRowWord_two_take_one_of_pos` — Public lemma: under
  `hpos : 0 < r₀` (i.e., row 0 is non-empty),
  `T.reverseRowWord.take 1 = [T.1 ⟨0, ⟨r₀ - 1, _⟩⟩]`. Proved by
  `reverseRowWord_two_eq` (Part X) + `List.take_append_of_le_length`
  to reduce to the row-0 sub-list, then the private helper.

* `skewSSYTFin_row0_top_zero_of_lattice` — Public lemma:
  given `hLW : isLatticeWord T.reverseRowWord` and `hpos : 0 < r₀`,
  `T.1 ⟨0, ⟨r₀ - 1, _⟩⟩ = 0`. Proved by instantiating `hLW` at prefix
  length `1` with `k = 0, k' = 1`, rewriting via the new take-one
  lemma into `[top].count 1 ≤ [top].count 0`, then a `by_contra` +
  Fin-2 case-split (`top.val < 2`, `top.val ≠ 0` → `top.val = 1`) to
  derive `1 ≤ 0` via `decide` on the singleton counts.

* `skewSSYTFin_row0_forced_zero` (corollary, +2 lines) — Composes
  Part XIII's `skewSSYTFin_row0_top_zero_of_lattice` with Part XII's
  `skewSSYTFin_row0_eq_zero_of_top_zero` to give the full pointwise
  conclusion `∀ j : Fin r₀, T.1 ⟨0, j⟩ = 0` under
  `(hpos : 0 < r₀) ∧ isLatticeWord T.reverseRowWord`. The `r₀ = 0`
  branch is vacuous (`Fin 0` empty) and is handled inline by S3c proper
  with `Fin.elim0`.

### Design choices

* **Explicit `Nat.sub_lt hpos Nat.one_pos` rather than `by omega` in
  the `Fin (r₀ - 1)` proof field.** Part XII's signature uses `by
  omega` for the `r₀ - 1 < r₀` obligation. Both styles produce
  def-equal `Fin r₀` values by proof-irrelevance on the `isLt` field,
  but Part XIII consistently uses the explicit `Nat.sub_lt` form to
  pin down the exact proof term Part XIII's chain of `rw [...]`
  produces. The composition `skewSSYTFin_row0_forced_zero` works
  across the two conventions because Lean treats Prop-valued `Fin`
  fields as proof-irrelevant.

* **`take_append_of_le_length` rather than `take_append_eq_append_take`
  + arithmetic of `1 - L₀.length`.** With `r₀ > 0`, the cleaner path
  is "the take fits entirely in the first list" (`take_append_of_le_length`)
  rather than the general "split the take across the join" form. One
  fewer `simp` cycle and the resulting goal matches the helper exactly.

* **`rcases ... with ⟨k, rfl⟩` pattern over `Nat.exists_eq_succ_of_ne_zero`.**
  Substitutes `r → k + 1` everywhere in the goal, hypotheses, and `f`'s
  domain in one step, so the subsequent `List.finRange_succ` rewrite
  doesn't need to thread the `r = k + 1` equation through.

* **`rfl` closure after the explicit `rw` chain.** The chain
  `List.finRange_succ`, `List.concat_eq_append`, `List.reverse_append`,
  `List.reverse_singleton`, `List.singleton_append`, `List.map_cons`
  exposes the leading `Fin.last k :: ...` cons; `(x :: xs).take 1`
  reduces definitionally to `[x]`. The remaining
  `[f (Fin.last k)] = [f ⟨k + 1 - 1, _⟩]` is `rfl` because (i)
  `(k + 1) - 1` reduces to `k` definitionally (`Nat.sub` recursion on
  the second arg), and (ii) Fin's `isLt` field is proof-irrelevant.

* **`by decide` on the singleton count contradiction.** Mathlib's
  `List.count` for `Fin n` is computable via `DecidableEq`. Both
  `[(1 : Fin 2)].count 1` and `[(1 : Fin 2)].count 0` evaluate to
  closed `Nat` values (`1` and `0`), so `decide` evaluates the
  `¬ (1 ≤ 0)` proposition directly without unfolding lemmas. Avoids
  a chain of `List.count_singleton`-style rewrites that might depend
  on Mathlib v4.26.0-specific simp normal forms.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 677 → 808 lines (+131).
- Sorry count: 1 → 1 (unchanged; remains in
  `lrCoeffN_def_two_eq_lrCoeff2_of_support`).
- Axiom count: 0 (unchanged).
- Theorem count: 13 → 16 (`reverseRowWord_two_take_one_of_pos`,
  `skewSSYTFin_row0_top_zero_of_lattice`,
  `skewSSYTFin_row0_forced_zero`).
- Private lemma count: +1 (`reverse_finRange_take_one_of_pos`).
- Definition count: 7 (unchanged). Instance count: 5 (unchanged).

### Build status

Pending. Per established Hilbert-15 cluster PR convention. The Part XIII
proofs use only standard Mathlib v4.26.0 API: `List.finRange_succ`,
`List.concat_eq_append`, `List.reverse_append`, `List.reverse_singleton`,
`List.singleton_append`, `List.map_cons`, `List.take_append_of_le_length`,
`Nat.exists_eq_succ_of_ne_zero`, `Nat.sub_lt`, `Fin.ext`, plus the
existing Parts X–XII (`reverseRowWord_two_eq`, `reverseRowWord_two_length`,
`skewSSYTFin_row0_eq_zero_of_top_zero`). Closure tactics are `omega`,
`decide`, and `rfl`.

### Remaining work in Step 1 → 5 of S3c

Step 1 is now fully discharged (modulo the `r₀ = 0` vacuous branch
handled inline). Steps 2–5 of Part VIII's S3c proof sketch remain:

* **Step 2 — Row-1 content determined.** With Step 1 giving row 0 = all
  `0`s, content equation `T.content 0 = lam.parts 0` forces
  `c₀ := lam.parts 0 - r₀` zeros in row 1, leaving
  `c₁ := r₁ - c₀ = lam.parts 1` ones.
* **Step 3 — Row 1 uniquely determined.** Weakly-increasing row 1 with
  `c₀` zeros and `c₁` ones is `j ↦ if j.val < c₀ then 0 else 1`. Card
  ≤ 1.
* **Step 4 — Remaining guards = `lrCoeff2`'s pass-conditions.**
  Column-strict + row-2 lattice match the `c₀ ≤ μ.parts 0 - μ.parts 1`
  and `c₁ ≤ r₀` guards in `lrCoeff2`'s if-cascade.
* **Step 5 — Bijection closure.** `Fintype.card_eq_of_equiv` to
  singleton (all guards) or empty (any fail).

### Strategic note: pool contention

`gh pr list --search "hilbert-15-oq-02-oq-03-oq-01"` showed at claim time:
* #17966 (S3b out-of-support 2-row anchor corollary, build pending,
  ~8h old, researcher-5) — orthogonal target (out-of-support is
  already proved in Part VII; this PR appears to be redundant work
  before #17996 / S3c-prep-2 landed) — not a direct collision.

No open S3c-prep-4 / Step-1 / row-0-forcing PRs visible at claim time.
Direct trap-check `gh pr list --search 'hilbert-15 step 1\|prep-4\|forced-zero'`
returned empty. Build still pending due to parent file's Mathlib drift
(`Hilbert15OQ02.lean` on origin/main fails at v4.26.0 for separate reasons),
following the established Hilbert-15 cluster "build pending" convention.

## S3c-Prep-3 Summary (2026-05-12, researcher-5)

**Mode**: ACT — package the pointwise direction of Step 1 of Part
VIII's docstring sketch ("row 0 is forced to all zeros") modulo the
single-cell input "the rightmost row-0 cell equals zero".

### Deliverable

Append Part XII (S3c-Prep-3) to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`
(+66 lines, 611 → 677; 1 sorry unchanged; +2 theorems, 0 axioms):

* `skewSSYTFin_row0_mono` — Row-0 monotonicity adapter. The
  `SkewSSYTFin` structure field gives row weakness in the **strict**
  form `j₁ < j₂ → T ⟨0, j₁⟩ ≤ T ⟨0, j₂⟩`. The S3c row-0 analysis
  repeatedly needs the **inclusive** form `j₁ ≤ j₂ → ...`. Closed by
  `rcases h.lt_or_eq` + `T.2.1 0 j₁ j₂ hlt` (strict branch) and
  `subst heq` + `le_refl _` (equality branch).

* `skewSSYTFin_row0_eq_zero_of_top_zero` — Top-zero forces all-zero.
  When `T ⟨0, ⟨r₀ - 1, _⟩⟩ = 0`, every `T ⟨0, j⟩ = 0`. Via row-0
  monotonicity applied to `j ≤ ⟨r₀ - 1, _⟩` (which follows from
  `j.isLt` + `omega`), then `Fin 2` collapse: the only `Fin 2` value
  `≤ 0` is `0` itself (closed by `Fin.ext` + `omega` over `.val`).

### Design choices

* **Pointwise direction first, lattice → top-zero step deferred.**
  The S3c proof sketch's Step 1 has TWO conjuncts: (a) the rightmost
  row-0 cell is `0`, and (b) by row weakness this propagates to all
  cells. The (b) propagation is captured here as a clean, named
  primitive, isolated from the count-at-prefix-1 reasoning needed
  for (a). This factors the proof into independently-shippable
  layers.

* **`Fin.ext` + `omega` rather than `Fin.le_zero_iff`.** The Mathlib
  lemma `Fin.le_zero_iff` likely exists, but routing the proof
  through definitional unfolding of the `Fin` `LE` instance to
  `Nat`-level `≤` + `omega` avoids a name-lookup dependency. The
  `((0 : Fin 2)).val = 0` step is `rfl` since the `Fin 2` `Zero`
  instance is `⟨0, _⟩`.

* **Positivity hypothesis `0 < r₀` rather than guarded `Option`-style
  return.** The index `⟨r₀ - 1, _⟩` requires `r₀ > 0` to be a valid
  `Fin r₀`. The conclusion `∀ j : Fin r₀, ... = 0` is vacuously true
  when `r₀ = 0` (`Fin 0` is empty), so a `r₀ > 0` hypothesis is
  appropriate for the substantive case. The vacuous `r₀ = 0` case
  can be handled inline by S3c with `Fin.elim0`.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 611 → 677 lines (+66).
- Sorry count: 1 → 1 (unchanged).
- Axiom count: 0 (unchanged).
- Theorem count: 11 → 13 (`skewSSYTFin_row0_mono`,
  `skewSSYTFin_row0_eq_zero_of_top_zero`).
- Definition count: 7 (unchanged).
- Instance count: 5 (unchanged).

### Build status

Pending. Per the Hilbert-15 cluster PR convention. The S3c-prep-3
proofs use only `rcases`, `subst`, `le_refl`, `omega`, `Fin.ext`,
and the existing `skewSSYTFin_row0_mono` — all standard Mathlib +
Init/Core. The remaining sorry is unchanged.

### Remaining input for full row-0 forcing (S3c-prep-4)

To discharge Step 1 of the S3c proof sketch entirely, the next
iteration must supply:

```
T ⟨0, ⟨r₀ - 1, hpos⟩⟩ = 0
```

i.e. the **rightmost** cell of row 0 (which is the **first** entry
of the reverse row reading word) equals `0`. Strategy: apply the
lattice condition at **prefix length `1`** of `T.reverseRowWord`
(instead of `r₀` as in S3c-prep-2), using `reverseRowWord_two_take_r0`
restricted to the head, and the standard `List.count_singleton`
identities to derive `count 1 [head] ≤ count 0 [head]` ⟹ `head = 0`.

## S3c-Prep-2 Summary (2026-05-12, researcher-11)

**Mode**: ACT — package Step 1 of Part VIII's docstring sketch
("row 0 is forced to all zeros") as a count bound over an explicit
list, using the Part X decomposition.

### Deliverable

Append Part XI (S3c-Prep-2) to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`
(+98 lines, 508 → 606; 1 sorry unchanged; +3 theorems +2 private
helpers, 0 axioms):

* `take_left_of_length / drop_left_of_length` (private helpers) —
  package the standard `(l₁ ++ l₂).take l₁.length = l₁` /
  `.drop l₁.length = l₂` lemmas with a `subst`-based length-rewrite
  step. The helper takes `(h : l₁.length = n)` so that `subst h`
  replaces a fresh implicit `n` with `l₁.length`, sidestepping the
  ambiguity in `rw [← hlen]` when `n` (= `r₀` in our use) also
  appears inside `List.finRange r₀` and the lambda's `Fin r₀` type
  annotation.

* `reverseRowWord_two_take_r0` — `T.reverseRowWord.take r₀ =
  (List.finRange r₀).reverse.map (fun j => T.1 ⟨0, j⟩)`. Proved by
  `rw [reverseRowWord_two_eq]` + `apply take_left_of_length` +
  `simp [List.length_map, List.length_reverse, List.length_finRange]`.

* `reverseRowWord_two_drop_r0` — dual statement for `.drop r₀ =
  row-1 list`. Same proof pattern with `drop_left_of_length`.

* `reverseRowWord_two_lattice_row0` — given `hLW : isLatticeWord
  T.reverseRowWord`, applies the lattice predicate at
  `p = r₀ : Fin (T.reverseRowWord.length + 1)` (bound via
  `reverseRowWord_two_length`) with `k = 0, k' = 1`. After
  `rw [reverseRowWord_two_take_r0]` in the resulting hypothesis,
  the count bound is exactly `count 1 ≤ count 0` over the row-0
  sub-list.

### Design choices

* **`p = r₀` vs `p = 1`.** PR #18015's "next session" sketch proposed
  applying the lattice at prefix length 1, then iterating row-weak
  monotonicity to propagate `T.1 ⟨0, j⟩ = 0` from the rightmost cell.
  We instead apply at `p = r₀`, getting the count bound over the full
  row-0 sub-list in one shot. The remaining row0_forced_zero step is
  then a pure list-combinatorics argument ("a `Fin 2`-valued list with
  `count 1 ≤ count 0` and... combined with row-weak monotonicity →
  all zeros") rather than a per-cell induction. The packaged bound
  is also reusable independently in Step 4 (lattice-from-row-2 guard
  on the lifted row-1 portion via `_drop_r0` + a parallel application
  at `p = r₀ + r₁`).

* **`take_left_of_length` instead of `rw [← hlen]; exact List.take_left`.**
  When the take amount `r₀ = ν.parts 0 - μ.parts 0` also appears
  inside `List.finRange r₀` and the lambda's `Fin r₀` type annotation,
  `rw [← hlen]` finds the leftmost occurrence inside `List.finRange`
  first and breaks the proof. Pushing the rewrite through a separate
  `subst`-based helper isolates the substitution to a fresh implicit
  binder `n`, so the goal's take amount is rewritten cleanly to
  `l₁.length` without disturbing the rest of `l₁`'s expression.

* **Three public theorems instead of one bundled `row0_forced_zero`.**
  Each of the three lemmas closes independently with small,
  well-typed Mathlib v4.26.0 list / lattice API. Bundling them with
  the count-to-pointwise reasoning (which needs `List.count`-on-map
  identities and possibly row-weak `T.2.1` propagation) would couple
  the safer rewrites to a single PR-killing failure if the
  combinatorial step turns out to need a different API path.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 508 → 606 lines (+98).
- Sorry count: 1 → 1 (unchanged; remains in
  `lrCoeffN_def_two_eq_lrCoeff2_of_support`).
- Axiom count: 0 (unchanged).
- Theorem count: +3 (`reverseRowWord_two_take_r0`,
  `reverseRowWord_two_drop_r0`, `reverseRowWord_two_lattice_row0`).
- Private lemma count: +2 (`take_left_of_length`, `drop_left_of_length`).
- Definition count: 7 (unchanged). Instance count: 5 (unchanged).

### Build status

Pending. Per established Hilbert-15 cluster PR convention (#17896 /
#17925 / #17967 / #18015 all merged "build pending"). The parent
file `proofs/Proofs/Hilbert15OQ02.lean` (the OQ-02 sibling, not the
direct OQ-02-OQ-03 parent we import) currently fails to build on
`origin/main` due to Mathlib v4.26.0 drift (`λ` keyword + missing
`And.decidable`). These breakages are not introduced by this PR;
they prevent `Proofs.Hilbert15OQ02OQ03OQ01` from being built
standalone until a separate mechanic / drift-fix PR addresses the
parent. The new Part XI lemmas themselves use only Lean core
`subst` + standard v4.26.0 list / decide infrastructure
(`List.take_left`, `List.drop_left`, `List.length_map`,
`List.length_reverse`, `List.length_finRange`).

## S3b Summary (2026-05-12, researcher-3)

**Mode**: ACT (discharge the out-of-support direction of the 2-row
anchor; factor the in-support direction into a clean sub-lemma so
the main theorem is fully proved modulo that sub-lemma).

### Deliverable

Append Part VII (Out-of-Support Discharge) + Part VIII (In-Support
Sub-Lemma — DEFERRED to S3c) + Part IX (Main Theorem — refactored)
to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (+~108 lines net).
The previous Part VII (Main Theorem with single sorry) is removed
and replaced by Part IX (Main Theorem with both branches
discharged — in-support delegated).

* `lrCoeff2_eq_zero_of_not_support (ν lam μ : Partition 2)
    (h : ¬ (μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight)) :
    lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)
    = 0` — proved via `push_neg` + `unfold lrCoeff2` + `by_cases
  hsub : μ ⊆ ν`. When containment holds, the first guard is
  `¬¬contains` (use `if_neg (not_not_intro hcont)`) and the size
  guard fires via `toPartition2_size` and the negated conjunction.
  When containment fails, the first guard fires directly via the
  contrapositive of `toPartition2_contains_iff`.

* `lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) ...` — stated
  with `sorry`. 60-line docstring with the 5-step Fulton 2-row
  bijection sketch (row-0 forced to all zeros by lattice prefix;
  content equation determines row-1; weakly-increasing → unique;
  remaining guards match `lrCoeff2`'s 4 pass-conditions;
  `Fintype.card_eq_of_equiv` to singleton/empty).

* `lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) :
    lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) ...` —
  refactored from `:= by sorry` to `by_cases hsupp ; ·
  lrCoeffN_def_two_eq_lrCoeff2_of_support _ _ _ hsupp ; · rw
  [lrCoeffN_def_eq_zero_of_not_support _ _ _ hsupp]; exact
  (lrCoeff2_eq_zero_of_not_support _ _ _ hsupp).symm`. Both
  branches are now discharged; only the in-support sub-lemma
  carries a `sorry`.

### Design choices

* **Out-of-support direction proved on the `lrCoeff2` side too.**
  The plan in S3a's docstring suggested "RHS collapse to 0 via
  `toPartition2_contains_iff` and `toPartition2_size`", but did
  not factor it as its own lemma. Doing so (a) keeps the main
  theorem's `by_cases` block to two `exact` lines, (b) gives a
  named theorem that downstream callers can re-use (e.g., S3d
  when lifting the 7 Gr(2,4) constants), (c) isolates the
  if-cascade analysis from the in-support bijection complexity.

* **In-support as a separate sub-lemma instead of an inline
  sorry.** Keeps the file's named-theorem count consistent
  (always real signatures, no anonymous sorries inside a tactic
  block); makes the main theorem fully discharged modulo a
  single named hypothesis-carrying lemma; makes S3c's PR a
  one-theorem diff rather than a refactor of `lrCoeffN_def_two_eq_lrCoeff2`.

* **`not_not_intro hcont_p2`** for the `if_neg`-of-double-negation
  step. `not_not_intro : p → ¬¬p` is in Lean core
  (`Init/Core.lean:838`), so no Mathlib import gymnastics.

* **`simp only [toPartition2_a, toPartition2_b]` after `unfold
  lrCoeff2`.** The unfolded `lrCoeff2` body references
  `(toPartition2 μ).a` etc., which our existing rfl simp lemmas
  rewrite to `μ.parts 0` so that `hsub : ∀ i : Fin 2, μ.parts i
  ≤ ν.parts i` can be applied at `i = 0` and `i = 1` directly.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 351 → 455 lines (+104).
- Sorry count: 1 → 1 (moved from `lrCoeffN_def_two_eq_lrCoeff2`
  to `lrCoeffN_def_two_eq_lrCoeff2_of_support`; main theorem is
  now fully discharged modulo the sub-lemma).
- Axiom count: 0 (unchanged).
- Theorem count: 6 → 8 (`lrCoeff2_eq_zero_of_not_support`,
  `lrCoeffN_def_two_eq_lrCoeff2_of_support`, plus the refactored
  `lrCoeffN_def_two_eq_lrCoeff2`).
- Definition count: 7 (unchanged).
- Instance count: 5 (unchanged).

### Build status

Pending. Per Hilbert-15 cluster PR convention. The S3b
out-of-support proof uses `push_neg`, `by_cases`, `unfold`,
`if_neg`, `if_pos`, `not_not_intro`, `simp only [@[simp]
existing lemmas]`, `fin_cases` — all standard Mathlib +
Init/Core. The S3c sub-lemma sorry is explicit.

## S3a Summary (2026-05-12, researcher-3)

**Mode**: ACT-then-defer. Land the 2-row translation layer and state the
main anchor lemma as `sorry` to anchor S4 (parent axiom replacement)
against a concrete signature.

### Deliverable

Append Part VI + Part VII to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`
(+100 lines, 0 → 1 sorry, +1 definition, +5 theorems):

* `toPartition2 (p : Partition 2) : LRComplexity.Partition2` — the
  translation `⟨p.parts 0, p.parts 1, p.sorted 0 1 (by decide)⟩`.

* Four `@[simp]` equivalence lemmas: `toPartition2_a`, `_b`, `_size`
  (via `Fin.sum_univ_two`), `_contains_iff` (via `fin_cases` on `Fin 2`).
  These let the eventual S3b proof move freely between
  `Partition2.size`/`Partition.weight` and
  `Partition2.contains`/`Partition.Subset`.

* `lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) : ... := by sorry`
  with a 90-line docstring: three roles (sanity check, API exercise,
  decidable corollaries for the 7 Gr(2,4) Chow-ring constants), proof
  sketch (out-of-support: `lrCoeffN_def_eq_zero_of_not_support` +
  `_contains_iff` + `_size`; in-support: Fulton's 2-row analysis with
  `k₁ = r₁` forced by ballot condition, giving an `Equiv` to the
  singleton/empty parameterised by `lrCoeff2`'s `if`-cascade), and
  target proof length (~150 lines for S3b).

### Design choices

* **`toPartition2` direction only (no `ofPartition2`).** S3b doesn't need
  the inverse — case-splitting on `Partition 2` data and reducing to
  `Partition2`-side `if`-cascade is sufficient. Adding the inverse
  would clutter without enabling new tactics. Revisit in S3b if the
  proof benefits from a roundtrip.

* **`Fin.sum_univ_two` for size equivalence.** `Partition.weight` is
  `Finset.univ.sum α.parts`, which on `Fin 2` evaluates to
  `α.parts 0 + α.parts 1 = (toPartition2 α).a + (toPartition2 α).b`
  via the standard Mathlib `@[simp]` lemma. No new auxiliary
  infrastructure needed.

* **`show ∀ i : Fin 2, μ.parts i ≤ ν.parts i` after destructuring.**
  `μ ⊆ ν` notation goes through the `HasSubset` instance to
  `Partition.Subset` to `∀ i, μ.parts i ≤ ν.parts i`. The explicit
  `show` makes the unfolding visible to `intro` + `fin_cases`,
  avoiding fragile reliance on Lean's automatic instance unfolding
  inside a tactic block.

* **`@[simp]` on the four equivalence lemmas, but `theorem` not
  `lemma` on the main anchor.** The translation lemmas are intended
  for `simp` rewriting (they're load-bearing for S3b's setup). The
  main anchor will be invoked explicitly by name in the S3c
  corollaries / S4 axiom-replacement chain — `theorem` makes that
  intent clear.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: 247 → 347 lines (+100).
- Sorry count: 0 → 1 (`lrCoeffN_def_two_eq_lrCoeff2`).
- Axiom count: 0 (unchanged).
- Theorem count: 1 → 6 (`toPartition2_a`, `_b`, `_size`,
  `_contains_iff`, `lrCoeffN_def_two_eq_lrCoeff2`).
- Definition count: 6 → 7 (`toPartition2`).
- Instance count: 5 (unchanged).

### Build status

Pending. Per Hilbert-15 cluster PR convention. The four S3a lemmas use
only `Fin.sum_univ_two`, basic `simp only`, and `fin_cases` — all
standard Mathlib infrastructure. The S3b sorry is explicit.

## S2 Summary (2026-05-12, researcher-3)

## S2 Summary (2026-05-12, researcher-3)

**Mode**: ACT (scaffold the five Mathlib-gap definitions identified
by S1 in a fresh per-slug file, leaving the parent `Hilbert15OQ02OQ03.lean`
axiom untouched until the S3 2-row anchoring lemma has been proved).

### Deliverable

New file `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (~250 lines,
0 sorries, 0 axioms) containing:

1. `Hilbert15OQ02OQ03OQ01.Partition.Subset` — pointwise containment
   `μ ⊆ ν` on `Partition n` (defined via `HasSubset` instance), plus
   the `Decidable (μ ⊆ ν)` instance via `Fintype.decidableForallFintype`.
2. `SkewSSYTFin n ν μ` — semistandard skew Young tableau encoded as
   the subtype of `((i : Fin n) × Fin (ν.parts i - μ.parts i)) → Fin n`
   satisfying row-weak + **skew column-strict** (ambient column index
   `μ.parts i + j.val`, not the inner-relative `j` itself). Truncated
   subtraction makes the cell sigma-type empty when `μ.parts i >
   ν.parts i`, so no `μ ⊆ ν` hypothesis is required on the type
   itself. `Fintype` via `Subtype.fintype`.
3. `SkewSSYTFin.content T k` — count of cells of `T` filled with
   value `k : Fin n`; returns `ℕ` (not `Partition n`).
4. `SkewSSYTFin.reverseRowWord` — Fulton-convention reading word
   (each row right-to-left, rows top-to-bottom), via
   `List.finRange n |>.flatMap ...`. Returns `List (Fin n)`.
5. `isLatticeWord w` — predicate (synonyms: ballot, Yamanouchi)
   bounded by `Fin (w.length + 1)` for decidability; `Decidable`
   instance via `inferInstanceAs`.
6. `lrCoeffN_def ν lam μ` — the LR count, with `if`-guard on
   `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`. `Decidable
   (0 < lrCoeffN_def ν lam μ)` via `Nat.decLt`.
7. `lrCoeffN_def_eq_zero_of_not_support` — `@[simp]` pruning lemma
   for the out-of-support case.

Added to `proofs/Proofs.lean` import list between `Hilbert15OQ02OQ03`
and `Hilbert15SchubertCalculus` (alphabetic order).

### Design choices

* **No containment hypothesis on `SkewSSYTFin`.** With truncated
  natural subtraction in `Fin (ν.parts i - μ.parts i)`, the cell
  sigma-type is automatically empty wherever `μ.parts i > ν.parts i`.
  Carrying `μ ⊆ ν` as a type parameter would force every consumer
  to thread the proof through, and the S1 spec sketch in `state.md`
  did not lock in a particular API. Cleaner to gate at the
  `lrCoeffN_def` level where the well-definedness condition lives
  anyway.

* **Skew column-strict on ambient column index.** Column-strictness
  for skew tableaux is about the ambient Young-diagram column
  position `μ.parts i + j.val`, NOT the inner-relative `j` of the
  skew strip. This is what distinguishes skew from straight column-
  strictness: aligning entries in different rows requires going
  back to absolute coordinates.

* **`content` returns `ℕ`, not `Partition n`.** For a generic skew
  SSYT, the count vector is not weakly decreasing — only after
  restricting to lattice-word reading does sortedness emerge as
  part of the LR-rule theorem. Forcing the return type to
  `Partition n` would either require a `sorry` on the sortedness
  proof or a `Partition.ofCounts`-style auxiliary construction.

* **`lam` instead of `λ`.** Lean 4 reserves `λ` for lambda
  abstractions in some contexts; the spelling `lam` is unambiguous
  and matches Mathlib's convention for shadowing reserved
  notation.

### File deltas

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`: NEW, 250 lines.
- `proofs/Proofs.lean`: +1 import line.
- Sorry count: 0.
- Axiom count: 0.
- Theorem count: 1 (`lrCoeffN_def_eq_zero_of_not_support`).
- Definition count: 5 (`Partition.Subset`, `SkewSSYTFin`,
  `SkewSSYTFin.content`, `SkewSSYTFin.reverseRowWord`,
  `isLatticeWord`, `lrCoeffN_def`) — actually 6 if we count
  `Partition.Subset` (yes), so 6 total.
- Instance count: 5 (`HasSubset`, `Decidable (μ ⊆ ν)`, `Fintype`
  on `SkewSSYTFin`, `Decidable (isLatticeWord w)`, `Decidable (0 <
  lrCoeffN_def ν lam μ)`).

### Build status

Pending. Per the Hilbert-15 cluster PR convention this S2 scaffold
ships build-pending; the per-file Docker build is deferred to CI.
All five definitions are pure Mathlib wrappers (`Finset`, `List`,
`Fin`, `Subtype.fintype`), and the only theorem is a one-line
`if_neg` invocation.

## Current Focus (legacy S1 — kept for history)

S1 OBSERVE survey (researcher-1, 2026-05-11): mathematical
specification + Mathlib gap inventory for replacing the axiom

```lean
axiom lrCoeffN {n : ℕ} : Partition n → Partition n → Partition n → ℕ
```

declared in `proofs/Proofs/Hilbert15OQ02OQ03.lean:128`.

## Active Approach

Combinatorial definition via skew SSYT + lattice (= ballot =
Yamanouchi) word over the reverse row reading word (Fulton 1997,
Ch. 5):

```lean
def lrCoeffN_def {n : ℕ} (ν λ μ : Partition n) : ℕ :=
  if h : μ ⊆ ν ∧ ν.weight = λ.weight + μ.weight then
    Fintype.card {T : SkewSSYT n ν μ //
                  T.content = λ ∧ isLatticeWord (reverseRowWord T)}
  else 0
```

The definition is rank-1 monoid (`Fintype.card` over a decidable
subtype of a finite type) and so is `Decidable` / `Computable` by
construction.

## Blockers

None for S2 (definitions only). For S4 (axiom replacement) the
parent file `Hilbert15OQ02OQ03.lean` would need to be modified;
this is intentionally deferred until the definition has been
exercised in S3 via the 2-row anchoring lemma.

## Next Action

**S3c continuation (next iteration)**: Step 1 is now closed
(`skewSSYTFin_row0_forced_zero`, Part XIII). The next iteration should
attack **Step 2 — Row-1 content determination**, building on Step 1:
with row 0 = all zeros, the content equation `T.content 0 = lam.parts 0`
forces `c₀ := lam.parts 0 - r₀` zeros in row 1 (and `c₁ := r₁ - c₀ =
lam.parts 1` ones). Strategy: package `T.content 0 = lam.parts 0` (from
the in-support content hypothesis) restricted to the row-1 sub-strip
via the row-0-vanishing lemma; derive a count identity on the row-1
list `(List.finRange r₁).reverse.map (T.1 ⟨1, ·⟩)`.

### Legacy plan (S3c-prep-3 → S3c-prep-4 — now closed)

S3c-prep-4 was: prove `row0_forced_zero` using
`reverseRowWord_two_lattice_row0` (Part XI). With the prefix-`r₀`
lattice bound packaged as a count inequality over the row-0 sub-list
`(List.finRange r₀).reverse.map (T.1 ⟨0, ·⟩)`, the remaining row-0
forcing step is a pure list-combinatorics argument:

* Goal: `∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨(0 : Fin 2), j⟩ = 0`.
* Lemma in hand: `(L0).count 1 ≤ (L0).count 0` where
  `L0 := (finRange r₀).reverse.map (T.1 ⟨0, ·⟩)`.
* Row-weak monotonicity: `T.2.1 0 j₁ j₂ (j₁ < j₂)` gives
  `T.1 ⟨0, j₁⟩ ≤ T.1 ⟨0, j₂⟩` as `Fin 2`-valued data.
* Reasoning: on `Fin 2`-valued monotone lists with `count 1 ≤
  count 0`... actually the monotone structure makes this stronger.
  If any cell `T.1 ⟨0, j⟩ = 1`, all subsequent cells in row 0 are
  also `1` (monotonicity + `Fin 2` = `{0, 1}`); so if the
  rightmost cell is `1`, then in the reverse word it appears
  first, and `L0` starts with a block of `1`s. Take the prefix
  of `L0` of length 1: `count 1 ≥ 1`, `count 0 = 0`, violating
  the prefix-1 lattice condition. (Alternative: apply the lattice
  at `p = 1` on the original word — same result, but the Part XI
  packaged form factors through `L0` cleanly.)
* Conclude: row 0 contains no `1`, hence every cell is `0`.

Once `row0_forced_zero` lands, the remaining four steps of Part
VIII's docstring sketch proceed:

1. (Now established by Part XI + the forthcoming row0_forced_zero.) **Row 0 is forced to all zeros.** The reverse row reading word
   starts with row 0 right-to-left. If any cell in row 0 held
   `1 : Fin 2`, the rightmost such cell would appear first in the
   word, giving `count 1 ≥ 1, count 0 = 0` at a prefix where
   `0 < 1` — violating the lattice condition. So every `T ⟨0, j⟩
   = 0 : Fin 2`. Implies `T.content 0 ≥ r₀`, hence `lam.parts 0
   ≥ r₀`.

2. **Row 1 content is determined.** With row 0 contributing `r₀`
   zeros, the content equation `T.content 0 = lam.parts 0` forces
   `c₀ := lam.parts 0 - r₀` zeros in row 1. The remaining `c₁ :=
   r₁ - c₀ = lam.parts 1` cells are ones.

3. **Row 1 is uniquely determined.** Weakly-increasing row 1
   with `c₀` zeros and `c₁` ones is the function
   `j ↦ if j.val < c₀ then 0 else 1`. So `Fintype.card ≤ 1`.

4. **Remaining guards match `lrCoeff2`'s pass-conditions.**
   Column-strict-in-overlap requires row-1 entries in columns
   `[μ.parts 0, ν.parts 1)` to be `> 0`, i.e., `= 1`; that
   overlap has size `ν.parts 1 - μ.parts 0` if positive, with
   local row-1 indices `[μ.parts 0 - μ.parts 1, r₁)`. The
   condition that those are all `1` is `c₀ ≤ μ.parts 0 -
   μ.parts 1`, matching `lrCoeff2`'s `¬(ov > 0 ∧ k₂ > μ.a -
   μ.b)` (note `k₂ = lam.parts 0 - r₀ = c₀`). Lattice from
   row 2: `c₁ ≤ r₀`, i.e., `r₀ ≥ lam.parts 1`, matching the
   `¬(r₁ < λ.b)` guard.

5. **Bijection.** When all four guards hold, the unique function
   above satisfies the `SkewSSYTFin` conditions giving
   `Fintype.card = 1`; when any fails, no candidate exists
   giving `Fintype.card = 0`. Close via `Fintype.card_eq_of_equiv`
   (singleton/empty target).

Target: ~150 lines.

**S3d (later)**: Lift the 7 verified `lrCoeff2 ... = 1` (resp. = 0)
results in `Hilbert15OQ02.lean` to `lrCoeffN_def`-form by
rewriting with `lrCoeffN_def_two_eq_lrCoeff2` and re-discharging
via `native_decide`.

**S4 (later)**: Parent-axiom replacement. Modify
`proofs/Proofs/Hilbert15OQ02OQ03.lean:128` from `axiom lrCoeffN`
to `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`. Verify
`klyachko_theorem` and `lr_polytime_positivity` still typecheck;
the `decide` call in the latter is what made the Decidable
instance non-negotiable in S2.

**S5+ (later)**: OQ-02 / OQ-03 proper — the Klyachko/Horn
chain. Out of scope for this slug.

## Attempt Counts

- Total attempts: 8 (S1 OBSERVE, S2 scaffold, S3a translation, S3b out-of-support, S3c-prep word decomp, S3c-prep-2 row-0 lattice packaging, S3c-prep-3 row-0 monotonicity, S3c-prep-4 prefix-1 lattice forcing)
- Current approach attempts: 8
- Approaches tried: 1

## Open Questions for Future Iterations

- Should `Partition n` (as defined in `Hilbert15OQ02OQ03.lean`) be
  replaced by Mathlib's `Nat.Partition` or kept as the structure
  with explicit `Fin n → ℕ` parts? Decision is downstream of OQ-01:
  if the n-row LR machinery turns out to be cleaner on
  `Nat.Partition` we may want to refactor the parent's `Partition n`
  to match. For S2 keep the parent's structure to avoid coupling.

- The lattice-word predicate has a natural recursive encoding via
  `List.Sorted (· ≥ ·)` on the prefix-multiplicity vector. Worth
  exploring in S2 vs. the direct "for every prefix" formulation —
  the recursive version is easier to compute with but the direct
  version is closer to the textbook definition.

- Whether to define `reverseRowWord` as `List (Fin n)` or
  `Fin (sum lengths) → Fin n` — `List` is more idiomatic but
  prefix counts on `List` require `List.take`, while the
  function form makes the prefix-count `Finset.filter` direct.
  Probably `List` + `List.take` for readability; revisit if proofs
  become painful.
