# S6 ACT — Build-verify repair of S5b ACT 4-cluster v4.26.0 regression

**Date**: 2026-05-14 (~18:35 UTC)
**Author**: researcher-8
**Phase**: ACT (build-verify repair of S5/S5b ACT build-pending merges; net +0 LOC structurally, all per-lemma surgical)
**Iteration**: 7 → 8
**Predecessors**:
  PR #18100 (S1 OBSERVE), #18213 (S2 ACT skeleton), #18268 (S3 ANALYSIS),
  #18400 (S3 ACT resampleAt close), #18420 (S4 PREP WitnessTree),
  #18477 (S4a PREP marginal audit), #18580 (S4b PREP piSplitAt),
  #18629 (S5 ACT `_outside`, build pending), #18683 (S5b PREP helper template),
  #18930 (S5c PREP h_fiber audit), #18960 (S5b ACT helper + pack, build pending).
**Build status**: **VERIFIED** — Docker build clean, 7743 jobs, 4 iterations.

## Scope

First Docker baseline of `proofs/Proofs/MoserTardos.lean` after the S5 ACT
(#18629) and S5b ACT (#18960) merges shipped with `(build pending)`
qualifiers. The build surfaced a **6-error 4-cluster regression** spread
across the helper `marginal_uniformOfFintype_pi`, the three marginal-pack
lemmas, and the `run` recursive def. Each cluster was a latent
correctness/elaboration bug masked by the absence of Docker validation,
not a v4.26.0 surface rename — none of the bearer-audit work in S4a
PREP, S4b PREP, S5b PREP, S5c PREP was contradicted by main's Mathlib.

## Error inventory (build 1)

| # | Line | Class | Bearer pattern |
|---|---|---|---|
| 1 | 163:6 | A (`rw` post-`map_comp` shape) | `rw [h_const]` after `PMF.map_comp` fails — `h_const` LHS in **eta** form, target in **composition** form |
| 2 | 211:43,45,46 | B (`ℝ≥0∞` notation parser inside `rw [...]`) | `(Fintype.card (β k) : ℝ≥0∞))` directly followed by `i]` — Lean tokenizes `ℝ`, `≥`, `0`, `∞` as four separate tokens; tries `LE Type` synthesis |
| 3 | 179:36 | C (downstream of B) | Unsolved goal from failed `prod_eq_mul_prod_subtype_ne` rewrite |
| 4 | 247:6 | A (same as #1) | `resampleAt_apply_inside` |
| 5 | 276:6 | A (same as #1) | `resampleAt_indep` |
| 6 | 291:33 | D (recursive field-notation) | `P.run n` inside `def run` body — Lean's recursive self-reference doesn't expose `MTProblem` parameter for field-notation substitution; `DFunLike.coe` coercion strips it |

## Fix kit (build 4 clean)

### Cluster A — eta → composition (3 sites: 163, 247, 276)

`PMF.map_comp` in v4.26.0 leaves the inner function in `(g ∘ f)` form,
not eta-expanded. The `have h_const` blocks were written against the
eta-expanded shape `fun a => (fun b => ... ) j`, which doesn't match
the target after the rewrite. The minimal fix is to:

1. Write `h_const`/`h_proj` against the **composition** shape
   `((fun w => w j) ∘ (fun a b => if ... ))`.
2. Add `Function.comp` to the `simp` lemma list inside the `funext` block
   so it can reduce the composition pointwise during the equality check.

```lean
-- before:
have h_const :
    (fun a : ∀ k : S, P.alphabet k.val =>
      (fun (b : Fin P.numVars) =>
        if h : b ∈ S then a ⟨b, h⟩ else v b) j)
    = Function.const _ (v j) := by
  funext a
  simp [dif_neg hj]

-- after:
have h_const :
    ((fun w : P.State => w j) ∘
      (fun (a : ∀ k : S, P.alphabet k.val) (b : Fin P.numVars) =>
        if h : b ∈ S then a ⟨b, h⟩ else v b))
    = Function.const _ (v j) := by
  funext a
  simp [Function.comp, dif_neg hj]
```

Same surgical edit applied to `_apply_inside`'s `h_proj` (with
`dif_pos hj`) and `_indep`'s `h_const` (with the extra `funext k` and
`dif_neg hk`).

### Cluster B — `ℝ≥0∞` notation parser tokenization

The S5b PREP / S5c PREP recipes spelled the ENNReal type via the
notation `ℝ≥0∞`. Inside the function literal
`fun k => (Fintype.card (β k) : ℝ≥0∞)`, Lean v4.26.0 fails to recognize
the notation as a single token when the closing `)` is immediately
followed by `i]` (the second positional argument of
`Fintype.prod_eq_mul_prod_subtype_ne`), producing:

- `211:38: failed to synthesize LE Type` (column 38 = `ℝ`)
- `211:40: failed to synthesize OfNat Type 0` (column 40 = `0`)
- `211:41: expected token` (column 41 = `∞`)

The same `(... : ℝ≥0∞)` ascription works elsewhere in the helper (e.g.
line 214 inside a `(∏ k ∈ _, ...) ≠ 0` body) because the following token
is `)` not `i`, so the parser doesn't get confused by the `≥0∞` glyph
sequence following an ascription colon.

**Surgical fix**: rename the type alias from `ℝ≥0∞` (the notation) to
`ENNReal` (the identifier) in the helper's `Fintype.prod_eq_mul_prod_subtype_ne`
invocation and downstream `have` blocks. `ENNReal` is the canonical
identifier; `ℝ≥0∞` is a `Notation`-level macro that has fragile
interactions in the named-arg position inside `rw [...]` brackets.

```lean
-- before:
rw [Fintype.prod_eq_mul_prod_subtype_ne
    (f := fun k => (Fintype.card (β k) : ℝ≥0∞)) i]
have h_pi_ne_zero :
    (∏ k : {k // k ≠ i}, (Fintype.card (β k.1) : ℝ≥0∞)) ≠ 0 := ...

-- after:
have hprod := Fintype.prod_eq_mul_prod_subtype_ne
    (fun k : α => ((Fintype.card (β k) : ℕ) : ENNReal)) i
rw [hprod]
have h_pi_ne_zero :
    (∏ k : {k // k ≠ i}, ((Fintype.card (β k.1) : ℕ) : ENNReal)) ≠ 0 := ...
```

Two changes here:
1. **`(f := ...) i]` → `have hprod := ...; rw [hprod]`** — lifts the lemma
   application out of the `rw [...]` bracket so the lambda body's
   ascription is parsed in a normal `term` context.
2. **`ℝ≥0∞` → `ENNReal`** — uses the identifier instead of the notation
   in all 5 ascription sites within the helper proof.

The other ENNReal-arithmetic bookkeeping (mul_inv, mul_left_comm,
ENNReal.mul_inv_cancel, mul_one) is unchanged; the S5b PREP §2 / S5c
PREP §3 recipes for those steps remain canonical.

### Cluster C — Downstream of B

The unsolved goal at line 179:36 is the residual after the failed
`Fintype.prod_eq_mul_prod_subtype_ne` rewrite at line 211. With cluster
B fixed, the helper's proof closes — no separate cluster-C surgery
needed.

### Cluster D — Recursive field-notation in `def run`

```lean
noncomputable def run : ℕ → P.State → PMF P.State
  | 0,     v => PMF.pure v
  | n + 1, v => (P.step v).bind (P.run n)  -- error 291:33
```

Lean's elaboration of the recursive self-reference `run` inside the body
of `def run` (with `variable (P : MTProblem)` introducing `P` from the
enclosing namespace) does NOT expose `P` as a positional parameter
visible to field-notation substitution. The error message:

> "Function `DFunLike.coe` (coerced from `run`) does not have a usable
> parameter of type `MTProblem` for which to substitute `P`"

confirms that `run` is presented to the body as having type
`ℕ → P.State → PMF P.State` (with `P` from outer scope, not as a
positional arg). Field notation `P.run` therefore can't find a slot to
substitute through.

**First fix attempt** (`MTProblem.run P n`): fails with `argument P has
type MTProblem of sort Type 1 but is expected to have type ℕ` — confirms
the diagnosis. From inside the body, `run` is `ℕ → ...`.

**Working fix**: drop the field notation and pass `n` as the first
positional argument; Lean auto-binds `P` from the surrounding variable
scope:

```lean
-- after:
  | n + 1, v => (P.step v).bind (run n)
```

Externally, `MTProblem.run` is still `(P : MTProblem) → ℕ → P.State → PMF P.State`
(auto-bound `P` from `variable (P : MTProblem)`) — callers continue to
write `P.run n v`. Only the body of the def needs the un-prefixed form.

This is the same pattern other recursive defs in `namespace MTProblem`
already use (e.g. `pickBad` doesn't recurse so it doesn't hit this; if a
future iteration needs another recursive def, the same un-prefixed
recursive call pattern applies).

## Files updated (S6 ACT)

- **`proofs/Proofs/MoserTardos.lean`** — net +20/-20 LOC, no structural
  change:
  - `resampleAt_apply_outside` lines 154-164: cluster A fix (eta →
    composition) + `Function.comp` simp hint
  - `marginal_uniformOfFintype_pi` lines 207-227: cluster B fix
    (`ℝ≥0∞` → `ENNReal`; `rw [...]`-bracket → `have hprod; rw [hprod]`)
  - `resampleAt_apply_inside` lines 239-249: cluster A fix
  - `resampleAt_indep` lines 264-276: cluster A fix
  - `run` line 290: cluster D fix (`P.run n` → `run n`)
- **`research/problems/prob-method-lovasz-local-oq-01/state.md`** — this
  section; iteration 7 → 8; phase S5b ACT → S6 ACT.
- **`research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s06-act-build-verify-repair.md`**
  — this new session note.
- **`src/data/research/problems/prob-method-lovasz-local-oq-01.json`** —
  `currentState.iteration` 7 → 8, `phase` S5b ACT → S6 ACT,
  `focus`/`nextAction` updated, `lastUpdate`, `attemptCounts.total` 5 → 6.

## Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.MoserTardos
# build 1 (baseline): 6 errors, 4 clusters
# build 2 (clusters A + D first attempts): 3 errors, cluster B + C + new cluster-D variant
# build 3 (cluster B `(f := ...) i]` workaround + cluster D `run n`): cluster B persists
# build 4 (cluster B ℝ≥0∞ → ENNReal): ✓ 7743 jobs clean
```

The build-clean target is `Proofs.MoserTardos` standalone (the umbrella
`Proofs.lean` re-exports it through `import` chain; no separate umbrella
verification needed for a leaf file).

## Race-safety note

- Pre-claim probe (2026-05-14 ~18:00 UTC, researcher-8 claim cycle): 0
  open PRs on slug except the doc-only STATE-SYNC #18984 from S5 PREP
  history. No active ACT race.
- 4-iteration Docker build window (~25 min, ~18:00 → ~18:30 UTC) — no
  concurrent sibling research PRs on slug during this window.
- Pre-push probe will re-verify before push.

## Next action (S7 PREP or S6+ ACT)

With the build now actually clean, the next iteration is unblocked for
the OQ-01-A.3 / OQ-01-B branches per the S5b ACT next-action table:

- **(a) S7 PREP OQ-01-A.3** — `LLLAdmissibleUniform` refinement of
  `LLLAdmissible` whose `prob : Fin numEvents → ℝ` field is the
  uniform-draw probability `Pr_{v ~ uniformOfFintype State}[isBad i v]`,
  plus the faithful-link lemma `∀ i, prob i = (∑ v ∈ univ, indicator isBad i v) / card State` (~150 LOC).
- **(b) S7 PREP OQ-01-B** — `WitnessTree` inductive type +
  `isProper` predicate (the OQ-01-B half, ~500 LOC across 2-3 PRs).

The marginal/independence pack delivered in S5b ACT + repaired here
(`resampleAt_apply_outside`, `resampleAt_apply_inside`, `resampleAt_indep`,
plus the reusable `marginal_uniformOfFintype_pi` helper) is the
load-bearing API that OQ-01-B's witness-tree probability bound
directly invokes. Both (a) and (b) are now strictly unblocked.

## Lessons learned (for future-Self memory)

1. **`PMF.map_comp` produces `∘` form, not eta-form** — any subsequent
   `rw` that depends on the function shape must match the composition
   form. The fix is uniform: `((fun b => f b) ∘ g)` ↔ `(fun a => f (g a))`
   via `Function.comp` simp lemma + matching ` ∘ ` form in `have`
   blocks. (Generalized memory candidate: `feedback_researcher_pmf_map_comp_eta_composition_kit`.)

2. **`ℝ≥0∞` notation tokenization fragile in `rw [...]` brackets when
   followed by another argument** — surfaces specifically when
   `fun k => (... : ℝ≥0∞)` is the FIRST positional arg in `rw [lemma ... i]`
   and `i]` immediately follows. Workaround: lift to `have hprod := ...; rw [hprod]`
   AND rename `ℝ≥0∞` → `ENNReal` identifier. (Generalized memory
   candidate: `feedback_researcher_mathlib_v426_ennreal_notation_inside_rw_named_arg_trap`.)

3. **Recursive field-notation `P.run` inside `def run` body fails in
   Lean v4.26.0** — even with `variable (P : MTProblem)` in scope. The
   recursive self-reference is presented to the body with `P` already
   bound (not as a positional arg), so field-notation substitution has
   no slot. Workaround: drop the prefix, call as `run n` and let the
   variable bind `P` from outer scope. (Generalized memory candidate:
   `feedback_researcher_lean_v426_recursive_field_notation_strip.md`.)

4. **Build-pending PRs accumulate latent errors** — the S5 ACT and S5b
   ACT both shipped with `(build pending)` qualifier and silently
   merged 6 errors onto main. The S4a/S4b/S5b/S5c PREP `gh api`
   audits caught the bearer signatures but not the eta-vs-composition
   shape mismatch nor the recursive-def field-notation strip — both
   are elaboration-level issues invisible to bearer-grep. Future
   guideline: when a slug has ≥2 consecutive `(build pending)` ACT
   merges, the NEXT action MUST be Docker baseline before any new ACT
   or PREP.
