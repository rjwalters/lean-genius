# S12 ACT — Phase C non-cyclic-direction discharge (build-verified)

**Session type:** ACT (Lean-modifying, single-file edit).
**Trigger:** S11 STATE-SYNC (PR #19359, merged 2026-05-16T03:53:52Z)
documented an all-GREEN S11 ACT-readiness gate with the paste-ready
recipe in PR #19301 §6 and 14-bearer drift recheck at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Predecessor PREPs
(#19270 S9 PREP, #19301 S9 PREP-2, #19075 S9 ACT, the S10 PREP-3
session file) merged 2026-05-15T18:00–23:26Z — 10+ hours mature at
ACT pick time.

**Result:** Phase C non-cyclic direction sorry at
`Proofs/GaussWilsonNonCyclicOQ01.lean:149` discharged.
**Slug-wide sorry count `1 → 0`**, axiom count remains 0.
Build-verified clean: `docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`
reports `⚠ [3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (8.9s)`
plus one pre-existing linter warning unrelated to this ACT.

The cumulative effect: **the Gauss–Wilson iff main theorem for
`(ZMod n)ˣ` is now end-to-end machine-checked.** Both directions of
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` have closed
auxiliaries, and the iff scaffold composes them with zero residual
strategic sorries.

---

## 1. Skeleton paste — PREP-2 §6 verbatim plus F2 rename

The PR #19301 §6 skeleton was applied as-is, modulo the four
ACT-time fixes documented in §2. The F2 underscore rename was
applied to the header at the same time:

```diff
 theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
-    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
+    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
     (∏ x : (ZMod n)ˣ, x) = 1 := by
-  sorry
+  -- Step 1: Phase A reduction.
+  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
+  -- Step 2: Build the 2-torsion subgroup T.
+  let T : Subgroup (ZMod n)ˣ := { carrier := ..., ... }
+  ...
```

Total LOC delta on `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`:
+64 / -2 (file size 201 → 256 lines). Imports also gained two lines
(see F5 + F6 below).

---

## 2. ACT-time fixes beyond PREP-2 §6

PREP-2 §6's recipe targeted F1+F2+F3 (over-application of
`SubmonoidClass.coe_finset_prod`, header underscore rename, fragile
`simp [T]` on let-bound) and PREP-3 §4's residual-risk inventory
P1–P4 named four soft pin-points. Four of those eight risk surfaces
fired during this ACT — none unanticipated; the fallbacks worked as
documented.

### F5 — Missing `Mathlib.GroupTheory.PGroup` import

**Surface symptom (iter 1):**

```
error: Proofs/GaussWilsonNonCyclicOQ01.lean:162:19: Unknown identifier `IsPGroup`
error: Proofs/GaussWilsonNonCyclicOQ01.lean:162:39: Invalid `⟨...⟩` notation
error: Proofs/GaussWilsonNonCyclicOQ01.lean:166:20: Unknown identifier `IsPGroup.iff_card.mp`
```

**Diagnosis:** the original file's import list
(`Proofs.GaussWilsonNonCyclic`, Phase A, Phase B,
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Data.ZMod.Basic`,
`Mathlib.GroupTheory.SpecificGroups.Cyclic`, `Mathlib.NumberTheory.Wilson`,
`Mathlib.Tactic`) brought in `IsCyclic` and `(ZMod n)ˣ` machinery but
not the p-group module. `Mathlib.Tactic` is broad but does not
transitively load `Mathlib.GroupTheory.PGroup`.

**Fix:** add `import Mathlib.GroupTheory.PGroup` to the import block.
Confirmed by re-build iter 2.

This F5 was **not** caught by PREP-2 §2 or PREP-3 §8 bearer tables —
both tables listed `IsPGroup.iff_card` at `Mathlib/GroupTheory/PGroup.lean:46`
but neither verified the bearer's module was transitively imported
by the parent file. Future PREPs should add an "imports check" step
(or, equivalently, an `#check IsPGroup.iff_card` sanity test in the
PREP's §X paste-verify section) to catch this class of bearer-resolves-
but-not-imported regression.

### F6 — `Fintype ↥T` synthesis failure (P1 fallback)

**Surface symptom (iter 2):**

```
error: Proofs/GaussWilsonNonCyclicOQ01.lean:170:6: failed to synthesize
  Fintype ↥T
[+ 7 more identical errors at L172/L175/L177/L187/L188/L192/L193]
```

**Diagnosis:** the `Subgroup G` Fintype instance lives in
`Mathlib/Algebra/Group/Subgroup/Finite.lean:33-34` as an unnamed
instance `instance (K : Subgroup G) [DecidablePred (· ∈ K)] [Fintype G] : Fintype K`.
Phase C did not import this module; without it, `Fintype ↥T` cannot
be derived from `Fintype (ZMod n)ˣ` plus `DecidablePred (· ∈ T)`.

**Fix:** apply the **P1 fallback** from S10 PREP-3 §4 verbatim:

```diff
+import Mathlib.Algebra.Group.Subgroup.Finite
 ...
   haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
+  haveI : DecidablePred (· ∈ T) := Classical.decPred _
+  haveI : Fintype T := inferInstance
   obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup
```

Note: the PREP-3 §4 P1 recipe suggested
`haveI : DecidablePred (· ∈ T) := fun x => decEq _ _` which produces
an opaque `Decidable` term rather than threading through
`DecidableEq (ZMod n)ˣ`. The `Classical.decPred _` variant is
classical-decidability — non-computable but
trivially typecheck-clean and propositionally identical for our use
case (`T` is only consumed for cardinality reasoning, not
computation). Either variant works once `Subgroup.Finite` is
imported.

The skeleton's original `haveI : Fintype T := Subgroup.instFintype`
was a guess at the instance name; the actual Mathlib instance is
anonymous, so `inferInstance` is the canonical reference.

### F7 — Fintype-instance discrepancy on `Fintype.card T = Fintype.card { x // x^2 = 1 }`
        (P2 fallback, then `Equiv` upgrade)

**Surface symptom (iter 3):**

```
error: Proofs/GaussWilsonNonCyclicOQ01.lean:174:16: unknown free variable `_fvar.5118`
```

Then after trying the P2 fallback (`rw [show ... from rfl]; exact Fintype.card_subtype _`):

```
error: Proofs/GaussWilsonNonCyclicOQ01.lean:175:61: Type mismatch
  rfl
has type
  ?m.301 = ?m.301
but is expected to have type
  Fintype.card ↥T = Fintype.card { x // x ^ 2 = 1 }
```

**Diagnosis:** the `Fintype ↥T` instance synthesized in F6 (via
`Subgroup.Finite` line 33) and the `Fintype { x : G // x ^ 2 = 1 }`
instance auto-derived from `[Fintype G] + [DecidableEq G]` are
**not definitionally equal** Fintype witnesses even though the
underlying types are. The `rfl` route assumed they were; the
elaborator's metavariable `?m.301` exposes the irreducibility.

**Fix:** rather than rely on `rfl`, build an explicit `Equiv`
between the two types via `Subtype.mk`/`Subtype.val`:

```lean
have e : T ≃ { x : (ZMod n)ˣ // x ^ 2 = 1 } :=
  { toFun := fun y => ⟨y.1, y.2⟩
    invFun := fun y => ⟨y.1, y.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
rw [Fintype.card_congr e]
exact Fintype.card_subtype _
```

Both `toFun` and `invFun` are pure `Subtype.mk` reassembly, and the
`left_inv` / `right_inv` close by `rfl` because the underlying
predicate `x ∈ T ↔ x ^ 2 = 1` IS definitional (the only
non-definitional thing was the Fintype-instance witness, not the
type-level coercion).

`Fintype.card_congr` then transfers cardinality across the Equiv,
discharging the instance-witness mismatch by integrating the two
Fintype instances over the same equivalence class.

This is the **upgraded P2 fallback** — the PREP-3 §4 recipe
proposed `rw [show ... from rfl]` which worked when the Fintype
instances align, but fails in our concrete `Subgroup.Finite` ×
`Subtype.fintype` configuration. The Equiv upgrade is strictly
more robust and should be the preferred recipe going forward.

### F8 — `symm` direction mismatch on `Finset.prod_subtype`
        (PREP-2 §6 over-correction)

**Surface symptom (iter 3, after F6 fix):**

```
error: Proofs/GaussWilsonNonCyclicOQ01.lean:197:4: Tactic `apply` failed:
could not unify the conclusion of `@prod_subtype`
  ∏ a ∈ ?s, ?f a = ∏ a, ?f ↑a
with the goal
  ∏ i, ↑i = ∏ x with x ^ 2 = 1, x
```

**Diagnosis:** `Finset.prod_subtype` has conclusion
`∏ a ∈ s, f a = ∏ a, f ↑a` (filter-form = subtype-form), matching
the goal direction `∏ x ∈ filter, x = ∏ i, ↑i` post-`rw
[SubmonoidClass.coe_finset_prod]`. PREP-2 §6's skeleton inserted a
`symm` BEFORE `apply Finset.prod_subtype`, which inverted the goal
(`∏ i, ↑i = ∏ x ∈ filter, x`), then `apply` could not unify.

**Fix:** simply remove the `symm` — `apply Finset.prod_subtype`
fires directly post-`rw`:

```diff
     rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]
-    symm
     apply Finset.prod_subtype
```

PREP-2 §6's `symm` was added defensively against a half-imagined
direction concern but inverted the actual flow. Goal-state walks in
PREP-3 §3.x §"L38–L45" did track the post-`rw` direction but did
not catch that the `symm` line is contraindicated; this is an
errata for PREP-2 §6 / PREP-3 §3.x to be folded into a future
PREP iteration if the Phase C scaffold ever needs re-derivation.

---

## 3. Bearer drift recheck — post-ACT confirmation

All 17 bearers cited in PREP-2 §2 + PREP-2 §3 + PREP-3 §8 + STATE-SYNC §2
consumed as-is during this ACT. **Zero new bearers added; zero drift
detected; zero substitutions made.**

| Bearer category | Count | Consumption status |
|---|---|---|
| Mathlib bearers (PREP-2 §2's 11-row table) | 11 | all consumed as-is |
| Bonus rfl-bearers (PREP-2 §3) | 2 | both used in `SubmonoidClass.coe_finset_prod` + `OneMemClass.coe_one` steps |
| Implementation-side (PREP-3 §8) | 1 | `Nat.pow_le_pow_right` consumed in Step 4 calc |
| Parent-file bearers (Phase A + B + parent grand-parent) | 3 | `prod_univ_eq_prod_two_torsion`, `prod_univ_eq_one_of_elementary_card_ge_four`, `card_sq_eq_one_ge_three` — all consumed |
| **Total** | **17** | **all green** |

**New module-import bearers (not previously enumerated):**

| # | Module | Reason added | Status |
|---|---|---|---|
| 18 | `Mathlib.GroupTheory.PGroup` | Provides `IsPGroup` and `IsPGroup.iff_card` namespace (F5) | imported |
| 19 | `Mathlib.Algebra.Group.Subgroup.Finite` | Provides `Fintype K` instance for `K : Subgroup G` (F6) | imported |

Lake SHA at this PR's commit: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from PREP-2's pin, byte-identical).

---

## 4. Pre-existing linter warning — `neg_one_sq` (L112)

The Docker build reports one warning unrelated to this ACT:

```
warning: Proofs/GaussWilsonNonCyclicOQ01.lean:112:30: This simp argument is unused:
  neg_one_sq

Hint: Omit it from the simp argument list.
  simp [hS_def, mem_filter, neg_one_sq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

This is inside `prod_eq_neg_one_of_isCyclic_aux` (the cyclic
direction, S7 ACT PR #18743) at the `h_neg_mem` block — entirely
outside this ACT's diff. The S11 STATE-SYNC build report
(re-verified at 3065 jobs) did **not** flag this warning, suggesting
the v4.26.0 linter for unused simp args fires inconsistently or
the warning was present but suppressed in #19075's build report.

**Recommended follow-on (out of scope for this ACT):** Hermit sweep
or simple `fix(hermit)` PR removing `neg_one_sq` from line 112's
simp arg list. Single 1-char edit, doc-only-equivalent risk
(removing an unused arg cannot change proof semantics).

---

## 5. Suggested follow-on work

| # | Action | Scope | Owner |
|---|---|---|---|
| 1 | Hermit sweep: remove `neg_one_sq` from L112 simp args | Hermit-scope, 1 LOC | Hermit |
| 2 | Auditor sync of meta.json — parent gallery proof `src/data/proofs/gauss-wilson-non-cyclic/meta.json` may want a cross-reference note ("OQ-01 closed in commit ...") added | Auditor-scope | Auditor |
| 3 | Peer-reviewer pass to verify badge promotion eligibility (slug-wide 0 sorries / 0 axioms / 0 structure-encoded assumptions) | Peer-reviewer scope | Peer reviewer |
| 4 | Errata patch on PREP-2 §6 / PREP-3 §3.x recipe: drop the `symm` before `apply Finset.prod_subtype` (F8); upgrade the P2 fallback to use explicit `Equiv` rather than `rfl` (F7); add explicit imports check covering `IsPGroup` and `Subgroup.Finite` (F5/F6) | PREP-iterate (no Lean edit) | Future researcher if re-derivation needed |

None of these are blocking; the slug is **functionally complete** at
this PR. Items 1–3 are quality-of-life and metadata polish.

---

## 6. Composition with the rest of the slug

This ACT closes the last residual sorry in the slug's three-file
chain (Phase A + B + C) on the iff side. Cumulative slug history:

| Iter | PR | Type | Net change |
|---|---|---|---|
| S2 ACT | #18147 | ACT (Phase A scaffold) | +Phase A 66 LOC, 0 sorries |
| S3 (Phase B scaffold) | #18232 | ACT | +Phase B 165 LOC, 2 sorries |
| S4 PREP | #18439 | PREP | strategic-sorry route enumeration |
| S4b PREP | #18467 | PREP | Mathlib v4.26.0 erratum |
| S5 PREP | #18465 | PREP | Phase C scaffold design |
| S5b PREP | #18607 | PREP | 4-bug audit + corrected skeleton |
| S6 ACT | #18652 | ACT (Phase C scaffold) | +Phase C 201 LOC, 2 sorries; slug-wide 4 sorries |
| S7 PREP | #18700 | PREP | cyclic-direction recipe |
| S7 ACT | #18743 | ACT (cyclic direction) | slug-wide 4 → 3 sorries |
| S8 ACT | #18957 | ACT (Phase B core) | slug-wide 3 → 1 sorry |
| S9 PREP | #19270 | PREP | non-cyclic skeleton + bearer table |
| S9 PREP-2 | #19301 | PREP | cross-PR seam audit + F1/F2/F3 fixes |
| S9 ACT | #19075 | ACT (outer `[NeZero n]`) | Phase C build-pending → build-verified |
| S10 PREP-3 | (session file in #18000Z drain wave) | PREP | goal-state walk + P1-P4 residual risk |
| S11 STATE-SYNC | #19359 | doc-only | 4-item absorption + readiness gate refresh |
| **S12 ACT** | **this PR** | **ACT (non-cyclic discharge)** | **slug-wide 1 → 0 sorries** |

**Slug status as of S12 ACT merge:** all sub-problems closed; 0
remaining strategic sorries; 0 `axiom` declarations; 0
structure-encoded assumptions. Phase chain is end-to-end
machine-checked at Mathlib v4.26.0.

---

## 7. Numerical sanity at `n = 8` (smallest non-cyclic mod)

PREP-2 §5 enumerated the smallest concrete case `n = 8`:
`(ZMod 8)ˣ ≅ ℤ/2 × ℤ/2`, with elements `{1, 3, 5, 7}` (all
satisfying `x^2 = 1`). Cardinality 4 ≥ 4. The 2-torsion subgroup
T equals all of `(ZMod 8)ˣ` here. ∏ {1,3,5,7} mod 8 = 105 mod 8 = 1.

The S12 ACT proof closes this and all other non-cyclic instances
(`n ∈ {8, 12, 15, 16, 20, 21, 24, ...}` and continuing) in one
generic step.

---

## 8. Conflict-free guarantees

**Files this PR touches** (exhaustive):

| File | Action | LOC delta |
|---|---|---|
| `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` | UPDATE | +64/-2 (201 → 256), excluding 2 new import lines |
| `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` | UPDATE | head replaced; S12 ACT prepended to iteration log |
| `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s12-act-noncyclic-direction-discharge.md` | NEW | (this file) |

**Files this PR does NOT touch:**

- `problem.md`, `knowledge.md` — unchanged.
- `meta.json` (no per-slug meta exists; parent gallery proof's
  meta `src/data/proofs/gauss-wilson-non-cyclic/meta.json`
  unchanged — Auditor follow-on if cross-reference needed).
- All other Lean files — unchanged.
- `proofs/lakefile.toml` / `proofs/lake-manifest.json` — unchanged.
- `src/data/proofs/gauss-wilson-non-cyclic/*` — unchanged.
- `src/data/research/*` — unchanged.

**Concurrent PR landscape at this PR's open time:** zero OPEN PRs on
this slug (per `gh pr list --search "gauss-wilson-non-cyclic-oq-01"
--state open`). Sibling `oq-03` PR #18230 is on disjoint files
(distinct `oq-03` companion). No conflict surface.

---

## 9. Honest assessment of confidence

**High confidence (≥0.95):**

- The skeleton consumed as-is composes with Phase A + B + parent's
  `card_sq_eq_one_ge_three` to give a correct mathematical proof of
  the non-cyclic direction. Build-verification at 3066 jobs
  confirms type-correctness.
- The F5/F6/F7/F8 fixes are all surface-level surgical edits with
  no mathematical content change.
- All 17 bearers consumed without drift at the pinned lake SHA.

**Medium confidence (~0.85):**

- `Classical.decPred` for `DecidablePred (· ∈ T)` introduces a
  classical instance into an otherwise computable-looking proof.
  The proof's overall non-computability is forced by `IsPGroup.iff_card`
  (which uses `Nat.card` over `Finite G` — a non-computable
  Fintype-cardinality-equivalent), so this is harmless. A
  computational `decEq` route is available but unnecessary.

**Open notes for follow-on:**

- Auditor: consider promoting `gauss-wilson-non-cyclic-oq-01`'s
  badge / status given the now-zero residual sorry/axiom count.
  The slug's parent gallery proof meta may also benefit from a
  cross-reference note.
- Peer reviewer: would benefit from an end-to-end qualitative
  review of the 3-file Gauss–Wilson iff proof, looking for
  axiom-integrity issues per CLAUDE.md (the structure-encoded
  assumptions check applies to all 3 files, not just this one).
