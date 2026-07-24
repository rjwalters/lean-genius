# S17 ACT — witness_valid: deepest-attachment extraction is proper (researcher-3, 2026-07-24)

**Mode**: ACT (substantive Lean delivery).
**Slug**: prob-method-lovasz-local-oq-01
**File**: `proofs/Proofs/MoserTardos.lean` 580 → 724 LOC (+144); 0 new sorries,
0 new axioms (file stays 0/0).
**Verification**: host `lean` v4.31.0 full-file elaboration against the pinned
Mathlib olean set (researcher-1 sibling worktree `.lake`, same pin as the S16
Docker build): 0 errors, 0 warnings. `#print axioms` for `witness_valid` and
`isProper_attach` = `[propext, Classical.choice, Quot.sound]`.

## 1. What landed

The S16 roadmap item `witness_valid` (execution-log extraction produces proper
witness trees) in relational form, appended to Part VI inside
`namespace MTProblem.WitnessTree`:

| Decl | Role |
|---|---|
| `HasMatchAt j τ d` | some depth-`d` vertex has `j ∈ Γ⁺(label)` |
| `inductive Attach j τ d τ'` | leaf `j` attached under a matching vertex at depth `d` |
| `AttachDeepest j τ τ'` | `∃ d`, `Attach` at `d` + `∀ d', HasMatchAt j τ d' → d' ≤ d` |
| `Attach.hasMatchAt` | attachment site is a match |
| `Attach.labelOf_eq` | attachment below the root preserves the root label |
| `isProper_attach` | **core**: proper + depth-maximal attach → proper |
| `inductive ExtractsFrom j log τ` | root + per-entry attach-or-skip over a log segment |
| `witness_valid` | **headline**: `ExtractsFrom j l τ → isProper τ` |

## 2. Design decision — relation, not program

MT §4's "attach at a deepest vertex whose label shares variables" is
formalized as a *relation* rather than a recursive function:

- The S18+ probability bound consumes only the two facts the relation records
  (site matches; nothing matches strictly deeper), never the ability to
  *compute* the tree.
- A computational extraction would immediately hit the `collisionAdj`
  noncomputability wall the S16 session already flagged when it deferred
  `DecidablePred isProper` — a relation sidesteps it entirely.
- `ExtractsFrom`'s `skip` constructor requires `∀ d, ¬HasMatchAt k τ d`, so an
  entry may be skipped ONLY when no vertex matches — the relation is faithful
  to MT §4 (no spurious nondeterministic skips).

## 3. The propriety proof (`isProper_attach`)

Induction over the `Attach` derivation, carrying `isProper τ` and the
maximality hypothesis as implications:

- **`here` case (attach at the root, `d = 0`)**: the interesting step is
  sibling distinctness. If an existing child `u` of the root had label `j`,
  then `HasMatchAt j u 0` holds via `self_mem_inclNbhd` (`j ∈ Γ⁺(j)`), so
  `HasMatchAt j τ 1` — and maximality gives `1 ≤ 0`, absurd. This is exactly
  the Moser–Tardos distinct-siblings observation.
- **`child` case**: the list-splitting constructor
  `node i (pre ++ t :: post) → node i (pre ++ t' :: post)` localizes the
  change. Maximality relativizes to the subtree by
  `d' + 1 ≤ d + 1 → d' ≤ d` applied to `⟨t, mem, ·⟩`. Nodup of the new label
  list is a pure rewrite once `labelOf t' = labelOf t` (`Attach.labelOf_eq`).

`witness_valid` is then a three-case induction over `ExtractsFrom` using
`isProper_leaf` and `isProper_attach`.

## 4. Lean gotchas hit (and fixes)

1. `isProper` is a match-def, not an inductive: `rcases hp` fails with
   "not an inductive datatype" — `simp only [isProper] at hp ⊢` first.
2. `subst (this : l = j)` eliminated `j` (the theorem variable) instead of
   `l`, producing "unknown identifier j" downstream — use
   `rw` with the equation in the goal instead.
3. The `∃ t ∈ ch, HasMatchAt j t d` structural-recursion form elaborated
   first try, confirming the S13/S16 finding for the `∀`-form transfers to
   the `∃`-form.

## 5. Honesty block

- `witness_valid` is propriety only. It does NOT yet connect trees to the
  random execution: there is no execution-log *instrumentation* of `run`
  (the log here is an arbitrary `List (Fin P.numEvents)` segment), and no
  probability statement. Those are S18+ (`witness_prob_bd`: coupling the
  resample chain to a fixed proper tree).
- Verification is host elaboration against the same pin as S16's Docker
  build, not a fresh Docker run; the file is standalone-importing-Mathlib,
  so full elaboration is a complete check of this file's proofs.

## 6. Next (S18)

`witness_prob_bd`: fix a proper tree τ rooted at `i`; show the probability
that τ is the extracted tree of a length-`t` execution prefix is at most
`∏_v uniformDrawProb (labelOf v)`. Requires instrumenting `run` with the
resampled-event log (PMF on `State × List (Fin numEvents)` or a trajectory
measure) and the resample-table coupling argument (MT §4, Lemma 3.1). Then
OQ-01-C `gw_sum_bound`.
