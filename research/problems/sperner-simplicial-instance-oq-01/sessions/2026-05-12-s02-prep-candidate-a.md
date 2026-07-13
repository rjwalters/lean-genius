# Session 2 — S2 PREP: Candidate A verbatim Lean draft + discharge audit

**Researcher.** researcher-9, 2026-05-12.

**Mode.** PREP (doc-only). No `.lean` edits.

**Outcome.** This PREP refines S1 OBSERVE's Candidate A pseudocode
(see `sessions/2026-05-12-s01.md` lines 79–110, merged as PR #18512)
into a verbatim, ready-to-paste Lean snippet for
`proofs/Proofs/SpernerSimplicialInstance.lean`, plus an audit of
every axiom discharge so S2 ACT becomes a copy-paste-and-build task
without surprises. Two stylistic variants (term-mode minimal vs.
tactic-mode template-aligned) are presented; both have been traced
against the parent file's `intervalTriangulation` precedent at
lines 958–971 and the in-file `Option.noConfusion` usages at lines
852, 864.

## 1. Pre-flight context

* **Slug.** `sperner-simplicial-instance-oq-01` — "Verify the
  standard 2-simplex triangulation as a concrete `Triangulation`
  instance".
* **Phase.** OBSERVE complete (S1 candidate ranking, researcher-11,
  2026-05-12, PR #18512). State.md "Next Action" pins Candidate A
  as the recommended S2 ACT.
* **Parent.** `proofs/Proofs/SpernerSimplicialInstance.lean` (994
  lines, 0 sorries, 0 axioms, status `verified`).
* **Recent PRs on this slug.**
  * PR #18291 — S1 OBSERVE design (researcher-N, merged 23:59 UTC
    2026-05-12).
  * PR #18512 — S1 OBSERVE candidate ranking (researcher-11, merged
    04:10 UTC 2026-05-13).
  * No open PRs at session-start (checked 04:40 UTC 2026-05-13 via
    `gh pr list --repo rjwalters/lean-genius --search
    "sperner-simplicial-instance-oq-01 in:title" --state open`).
* **Open question family.** `oq-01` is the load-bearing
  prerequisite for `oq-03` (`boundary_doors_odd` for n-simplex),
  `oq-04` (Brouwer fixed-point), and `oq-06` (Gale's Hex theorem)
  per the parent's `meta.json` `conclusion.openQuestions`.

This session does **not** consume Candidate A directly — that's
S2 ACT (a separate, build-verified PR). This session pre-stages
the ACT by removing every micro-decision from the path.

## 2. Parent API recap

From `proofs/Proofs/SpernerSimplicialInstance.lean` lines 81–108
(structure `Triangulation V n` for `V : Type*` with `[DecidableEq V]`
and `n : ℕ`), the S2 ACT must instantiate **five data fields** and
**four proof obligations**:

| # | Field | Type / obligation | For Candidate A |
|---|-------|------|------|
| D1 | `Cell` | `Type` | `Fin 1` |
| D2 | `cellDecEq` | `DecidableEq Cell` | `inferInstance` |
| D3 | `cellFintype` | `Fintype Cell` | `inferInstance` |
| D4 | `vertex` | `Cell → Fin (n + 1) → V` | `fun _ k => k.val` |
| D5 | `adj` | `Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))` | `fun _ _ => none` |
| P1 | `vertex_injective` | `∀ s, Function.Injective (vertex s)` | `fun _ => Fin.val_injective` |
| P2 | `adj_symm` | `∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k)` | `none = some _` ⇒ `Option.noConfusion` |
| P3 | `adj_vertex` | `∀ s k s' k', adj s k = some (s', k') → (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s')` | same, vacuous |
| P4 | `adj_ne` | `∀ s k s' k', adj s k = some (s', k') → s ≠ s'` | same, vacuous |

Note that the structure also has post-hoc instance attributes at
lines 110–111:

```lean
attribute [instance] Triangulation.cellDecEq
attribute [instance] Triangulation.cellFintype
```

These are global, so they fire on `trivialTriangle.Cell` once the
def is in scope. No new attribute lines are needed in S2 ACT.

## 3. Verbatim Lean snippet (Variant T — term mode, recommended)

The cleanest path: every obligation closes with a single term, no
tactics, no `by` blocks. This minimizes proof-elaboration noise and
makes the build cost trivial.

```lean
/-! ## Trivial 2-Simplex Triangulation

The minimal `Triangulation ℕ 2` instance: a single 2-simplex with
ordered vertices `(0, 1, 2)` and three boundary faces. This is the
2-d analogue of the singleton case `intervalTriangulation 1` and
serves three purposes:

* Smoke-test for the abstract bridge `toCellComplex` at `n = 2`.
* Fixture for `boundary_doors_odd` work on the standard 2-simplex
  (open question `sperner-simplicial-instance-oq-03`).
* Prerequisite check for any downstream `Triangulation ℕ 2`-valued
  construction (e.g. the m × m subdivision in Candidate C). -/

/-- A single 2-simplex with vertices `(0, 1, 2)` and three
boundary faces. All four proof obligations discharge by
`Fin.val_injective` (vertex map is `Fin.val` up to eta) or
by `Option.noConfusion` (every adjacency is `none`). -/
def trivialTriangle : Triangulation ℕ 2 where
  Cell := Fin 1
  cellDecEq := inferInstance
  cellFintype := inferInstance
  vertex := fun _ k => k.val
  vertex_injective := fun _ => Fin.val_injective
  adj := fun _ _ => none
  adj_symm := fun _ _ _ _ h => Option.noConfusion h
  adj_vertex := fun _ _ _ _ h => Option.noConfusion h
  adj_ne := fun _ _ _ _ h => Option.noConfusion h
```

**Line count.** 13 lines for the def + 13 lines of section/doc
headers + 5 lines of `/-- ... -/` doc = **31 LOC** total.

**Build cost estimate.** Zero local lemma elaboration; all four
proofs are direct application of single Mathlib/`core` lemmas.
Expected compile time impact: < 100 ms on a warm `lake build`.

## 4. Discharge mechanics audit

### 4.1. `vertex_injective` — `fun _ => Fin.val_injective`

**Obligation.** `∀ s : Fin 1, Function.Injective (vertex s)` where
`vertex := fun _ k => k.val`.

**Trace.**

1. After eta-reduction, `vertex s = fun (k : Fin 3) => k.val ≡
   (Fin.val : Fin 3 → ℕ)`. (Eta is definitional in Lean 4 for
   `fun k => f k` ↔ `f`.)
2. `Function.Injective Fin.val` is `Fin.val_injective` from
   Mathlib — definition:
   ```lean
   theorem Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ)
   ```
   (Mathlib v4.26.0, `Mathlib/Data/Fin/Basic.lean` or
   `Mathlib/Logic/Equiv/Fin/Basic.lean` — verified used 9× across
   `proofs/Proofs/` including `SpernerGrid.lean`,
   `SpernerFreudenthal.lean`, `RamseyHypergraph.lean`).
3. Therefore `fun (_ : Fin 1) => Fin.val_injective` has type
   `∀ _ : Fin 1, Function.Injective (fun (k : Fin 3) => k.val)`,
   which unifies with the obligation.

**Alternative (tactic-mode, identical content).** `by intros; exact
Fin.val_injective`. Slightly noisier; same elaboration result.

**Eta concern (resolved).** Lean 4 reports `Function.Injective`
goals up to defeq, which includes eta. `Fin.val_injective :
Function.Injective Fin.val` matches `Function.Injective (fun k =>
k.val)` without explicit `funext`. Tested implicitly by all 9
sibling usages.

### 4.2. `adj_symm` / `adj_vertex` / `adj_ne` — vacuous via `Option.noConfusion`

**Obligation.** Each hypothesis has form `adj s k = some (s', k')`
where `adj := fun _ _ => none`. Beta-reduction yields `none = some
(s', k')` which is excluded by `Option.noConfusion`.

**Trace.**

1. `adj_symm s k s' k' (h : adj s k = some (s', k'))` — after beta,
   `h : none = some (s', k')`.
2. `Option.noConfusion h : C` for any goal `C` (built-in
   `noConfusion` for `Option`).
3. Term `fun s k s' k' (h : adj s k = some (s', k')) =>
   Option.noConfusion h` typechecks against `adj_symm`'s expected
   type `∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k)`.

**In-file precedent.** Lines 852, 864 of
`SpernerSimplicialInstance.lean` use exactly this idiom:
```lean
· rw [dif_neg h] at hadj; exact Option.noConfusion hadj
```
The form `fun ... h => Option.noConfusion h` is the η-expanded
term-mode counterpart.

**Alternative (`nomatch`).** `fun _ _ _ _ h => nomatch h` works
identically for `Option` (the `noConfusion` mechanism is what
`nomatch` invokes under the hood). Either spelling is acceptable;
the explicit `Option.noConfusion` is preferred for cross-reference
with lines 852/864.

**Alternative (`by contradiction`).** Does **not** work in Lean 4
for raw `none = some _`. `contradiction` looks for `False` or
type-class-derived inequality, not `Option.noConfusion`. Avoid.

### 4.3. Defeq sanity check for `D4`

The candidate uses `vertex := fun _ k => k.val` and S1 OBSERVE
spelled it as `vertex _ k := k.val`. These are syntactic variants
of the same lambda; Lean 4 accepts both in `structure where` syntax.
The `fun _ k => k.val` form is preferred here because the
elaborator binds `s : Cell` (named `_` here for clarity) explicitly,
which the term-mode discharge `fun _ => Fin.val_injective`
mirror-binds.

## 5. Insertion point

The cleanest insertion is at the **namespace `Triangulation` level**,
between `end Interval` (line 973) and the `/-! ## Interval Sperner's
Lemma -/` docstring (line 974). Rationale:

* `intervalTriangulation` (line 958, the 1-d sibling) and
  `interval_sperner` (line 982) are at the namespace level, not in
  any inner section. Mirror them by putting `trivialTriangle` at
  the same level.
* Placing it **before** `interval_sperner` keeps the 2-d / 1-d
  pairing visually obvious: any future reader scans `Interval`
  section, sees `intervalTriangulation`, then sees the trivial 2-d
  analogue, then sees the 1-d sanity theorem.
* No new `section TrivialTriangle` is needed — the def has no
  hypothesis variables to scope.

**Concrete insertion diff (S2 ACT preview).**

```
... line 973: end Interval
... line 974: BLANK
... line 975: <BEGIN INSERTION — Section 3 snippet, ~31 LOC>
... line 1005 (approx): <END INSERTION>
... line 1006: /-! ## Interval Sperner's Lemma ... -/
... [old line 974 onward, shifted +31]
```

S2 ACT should produce a diff of exactly **+31 / -0 LOC** in the
Lean file (zero changes elsewhere — no new imports, no
`additionalFiles` updates in `meta.json`).

## 6. Risk register

| Risk | Severity | Mitigation |
|------|----------|------------|
| `Fin.val_injective` defeq-mismatch with `fun k => k.val` | **Low** | Verified by 9 sibling usages; eta is definitional in Lean 4. If it fails, fall back to `fun _ a b h => Fin.ext h`. |
| `Option.noConfusion` discharge fails for one of P2/P3/P4 | **Low** | All three have *identical* hypothesis shape (`adj s k = some (s', k')` with `adj := fun _ _ => none`). If one passes, all three pass. |
| Insertion shifts `interval_sperner` line number → audit drift | **Trivial** | Drift sync is auditor's domain; line numbers in `meta.json` `additionalFiles[].lineCount` track `Lean file line total`, not specific theorem lines. Bump from 994 → 1025 (approx). |
| `trivialTriangle.toCellComplex` consumed elsewhere | **Trivial** | New def; no callers. |
| Namespace `Triangulation` clash with `trivialTriangle` | **Trivial** | Unique name; ripgrep `\btrivialTriangle\b proofs/` confirms no existing usage. |

**Build verification deferral.** Per the worktree `.lake` symlink
loop trap (project memory:
`feedback_researcher_lake_symlink_loop_and_wipe.md`), the S2 ACT
itself should commit + push the Lean file *first* and then ship
the build-pending PR with a clear title and body — letting a clean
worktree (Doctor or auditor) verify. The doc-only nature of THIS
PR (S2 PREP) means it can be shipped without build verification.

## 7. Optional sanity-check theorem (S2-Continued or S3)

If the S2 ACT researcher wants a one-line confirmation that
`trivialTriangle` plays well with the abstract Sperner machinery,
the trivial corollary:

```lean
/-- 2-d Sperner's lemma for the trivial triangle: if the boundary
doors are odd, a panchromatic cell exists. (Direct application
of `Triangulation.sperner`.) -/
theorem trivialTriangle_sperner
    (c : ℕ → Fin 3)
    (hbdry : Odd (Finset.univ.filter
      (fun p : trivialTriangle.Cell × Fin 3 =>
        CellComplex.IsDoor c trivialTriangle.toCellComplex p.1 p.2 ∧
        trivialTriangle.adj p.1 p.2 = none)).card) :
    ∃ s : trivialTriangle.Cell,
      CellComplex.IsPanchromatic c trivialTriangle.toCellComplex s :=
  Triangulation.sperner trivialTriangle c hbdry
```

is the obvious 2-d analogue of `interval_sperner` (line 982).
**~10 LOC**, zero proof obligations beyond direct application.

**Caveat.** This theorem does **not** discharge `hbdry` for any
concrete coloring `c` — that's `oq-03`'s job (`boundary_doors_odd`
applied to `trivialTriangle`). The optional theorem only verifies
the *bridge* compiles and the dependent types line up.

Recommendation: include this theorem in S2 ACT iff `LOC budget
permits` (push from 31 → ~45 LOC total). It strengthens the smoke
test from "instance compiles" to "instance compiles + abstract
theorem applies".

## 8. Out of scope

This PREP and the recommended S2 ACT explicitly **do not** cover:

* **Candidate C** (m × m subdivision): tracked separately in the
  seeker-init JSON design + S1 OBSERVE Candidate C ranking; ~250–400
  LOC across 6–8 sessions; the load-bearing chain for downstream
  `oq-03`/`oq-04`/`oq-06`. Candidate A is a smoke-test sibling, not
  a replacement.
* **Candidate B** (sorted-vertex API, `Triangulation (Fin 3) 2`):
  optional template-alignment exercise; not on the critical path.
* **`boundary_doors_odd` discharge for `trivialTriangle`**:
  belongs to `oq-03` and requires choice of Sperner coloring `c`
  and a per-face `Even/Odd` decomposition.
* **`oq-02` (Mathlib `Geometry.SimplicialComplex` bridge)**:
  separate slug; independent of Candidate A.
* **Build verification on a worktree**: deferred to S2 ACT (Doctor
  or auditor; see Risk Register §6).

## 9. Summary

S2 PREP refines S1 OBSERVE's Candidate A from pseudocode (with
`fin_cases <;> simp_all` placeholder tactics) into a verbatim
13-line term-mode `def` with every axiom discharged by a single
Mathlib / `core` lemma:

| Field | Discharge | Lines of proof |
|-------|-----------|---|
| `vertex_injective` | `fun _ => Fin.val_injective` | 1 |
| `adj_symm` | `fun _ _ _ _ h => Option.noConfusion h` | 1 |
| `adj_vertex` | `fun _ _ _ _ h => Option.noConfusion h` | 1 |
| `adj_ne` | `fun _ _ _ _ h => Option.noConfusion h` | 1 |

S2 ACT should be a +31 LOC diff at line ~974 of
`SpernerSimplicialInstance.lean`, +0 elsewhere.

**Confidence: high** that the snippet compiles on the first try.
The two non-trivial facts (`Fin.val_injective` exists, `none = some
_` discharges via `Option.noConfusion`) are both verified by
in-repo precedent: 9 sibling usages of `Fin.val_injective`, 2
in-file usages of `Option.noConfusion` at lines 852, 864.

## 10. Next Action

* **S2 ACT** (recommended next): paste §3 snippet between line 973
  and the next `/-!` docstring of
  `proofs/Proofs/SpernerSimplicialInstance.lean`, push to a new
  branch, ship build-pending PR (title:
  `research(sperner-simplicial-instance-oq-01): S2 ACT — trivialTriangle Candidate A instance`).
* **S2 ACT++** (optional): also include §7 sanity-check theorem.
* **S3** (future): begin Candidate C step 1 (`LatticePoint m` +
  `TriCell m` inductive).
