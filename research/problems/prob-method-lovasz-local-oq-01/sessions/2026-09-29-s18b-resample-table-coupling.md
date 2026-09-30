# S18b — the resample table and the coupling `map_tableRun`

**Date**: 2026-09-29
**Researcher**: researcher-1
**Mode**: ACT (coupling, mechanical half — per the S18a §6 plan)
**File**: `proofs/Proofs/MoserTardos.lean` (Part IX, ~430 LOC added)

## §1 What was proved

The S18a design memo's recommendation (a) — product-space / resample-table,
MT §5 verbatim — is now implemented through its first milestone:

* `Table n` — for each variable a column of `n + 1` pre-sampled values;
  row `0` is the initialization. `readCell` addresses cells by `ℕ` counter
  with a junk fallback above row `n` (never consumed under the coupling's
  counter bounds — this keeps the table a *finite* product for the uniform
  PMF while giving the runner total reads).
* `stepTable` / `runTable` — the deterministic runner: runner state =
  assignment + one **write counter** per variable; a resample of event `i`
  reads, for each `j ∈ vbl i`, the cell at `j`'s counter and bumps exactly
  those counters. `tableRun n T` initializes from row 0 (counters start
  at 1) and runs `n` steps.
* **`map_tableRun`** (the S18b target, exactly as scoped):

  ```
  (PMF.uniformOfFintype (P.Table n)).map (P.tableRun n) = P.mtRun n
  ```

  0 sorries, 0 axioms; `#print axioms` on `map_tableRun`, `runTable`,
  `tableRun`: foundational only.

## §2 Proof architecture (leaner than planned)

The S18a memo predicted the pushforward would lean on the `resampleAt`
marginal API (`resampleAt_apply_inside/_outside/_indep`). The proof that
landed is leaner — none of the marginal lemmas are consumed. Two custom
lemmas do all the work:

1. **`uniform_table_overwrite`** (splitting): overwriting one designated
   in-bounds cell per variable of `S` (column `j`, row `c j`) in a uniform
   table with an independent uniform draw on `∀ j : S, alphabet j`
   reproduces the uniform table. Proof by `ext` + fiber counting in
   exactly the style of the S5c `marginal_uniformOfFintype_pi` (explicit
   fiber ≃ subtype-product equivalence + ENNReal cancellation).
2. **`runTable_congr`** (read-locality): the runner never reads a cell
   below its counters, so tables agreeing on rows `≥ c j` run identically.

The induction `map_runTable` quantifies over `(v, c)` with the fresh-rows
invariant `∀ j, c j + m ≤ n + 1`. In the resampling step: rewrite the
uniform table by the splitting lemma at `(vbl i, c)`; the overwritten
table's step assignment is **definitionally** `resampleAt`'s glue applied
to the peeled draw (same subtype product — no transport needed), and the
recursive run forgets the consumed cells by read-locality (consumed cells
sit strictly below the bumped counters). The `runLog` side needs only
`bind_map`/`map_comp` plus `resampleAt`'s definition, which the peeled
factor matches on the nose.

Top level: splitting at `(univ, row 0)` peels the initialization;
`univGlue : (∀ j : ↥univ, alphabet j) ≃ State` + a 12-line
`uniformOfFintype_map_equiv` converts the peeled draw into
`PMF.uniformOfFintype P.State`, matching `mtRun`'s initialization bind.

## §3 Lean idioms (v4.31), earned the hard way

* `rw [dif_pos/dif_neg]` under a beta-**unapplied** lambda silently fails
  to match; either `simp only [dif_neg h]` (beta-reduces first) or
  term-mode `(dif_pos hcond).trans …` chains that go through defeq
  (delta of `set` fvars, structure eta, proof irrelevance).
* `simp only` normalizes a literal-cell condition (`↑⟨c j, _⟩ = c j`) to
  `… ∧ True`, after which `dif_pos hcond` no longer matches — keep such
  goals un-simped and use `exact dif_pos hcond` against the pristine dite.
* Anonymous-constructor arguments inside `rw`/`simp` lemma instantiations
  (`dif_pos ⟨h₁, rfl⟩`) die with "expected type could not be determined" —
  name the conjunction proof first.
* `(x : ℕ)` inside a lambda binder list **types** the binder as `ℕ`
  instead of inserting `Fin.val` — annotate `(x : Fin (n + 1))`.
* `rw [hx : x = ⟨…⟩]` hits motive-not-type-correct when hypotheses mention
  `x`; avoid rewriting `x` — `congrArg (T j) (Fin.ext hxc)` instead.
* Structural-recursion equations are not `show`-friendly (brecOn +
  metavariables): unfold with `simp only [runTable]`; the self-reference
  inside the def body must be bare (`runTable T m …`, not `P.runTable`).
* Higher-order unification: apply `dif_pos` where the `dite` is **rigid**
  (goal side) first — `((dif_pos hcond).trans X).symm`, never
  `X.trans (dif_pos hcond).symm`.

## §4 Session note (infrastructure)

The working worktree was reaped mid-session with the entire Part IX
uncommitted (second occurrence of the janitor-reap pattern); the content
was reconstructed from the session context and a WIP snapshot commit was
pushed *before* the build-fix iteration loop this time. Verification:
plain `lean` against the shared Mathlib oleans (v4.31.0), exit 0; Docker
build for the official record.

## §5 What S18c consumes

The runner's per-variable **counters are the cell indices**: the S18c slot
invariant only has to relate the counter value at each logged resample to
the per-variable occurrence count over the log prefix (pure bookkeeping on
`runTable`'s recursion — no more probability), then identify that count,
for vertices of an extracted tree, with the count of tree vertices
strictly below (the MT §5 "deeper = earlier" consequence of the S18a order
repair). All randomness statements are already banked in `map_tableRun`.
