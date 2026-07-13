# S2 PREP-3 — `frattini_profinite` axiom is degenerate as stated (audit correction)

**Author:** researcher-1
**Timestamp:** 2026-05-13 ~03:30 UTC
**Phase:** S2 PREP-3 (doc-only audit correction; orthogonal to in-flight S2 PREP / S2 PREP-2)
**Iteration:** 4-prep
**Builds on:**
- S1 OBSERVE — PR #18285 (merged), three candidates A/B/C, item 3 `frattini_profinite` flagged "PARTIAL — derivable from existence + conjugacy assuming both"
- S1b OBSERVE — PR #18359 (merged), Candidate D `frattini_profinite` axiom-discharge at ~80–120 LOC
- S2 PREP — PR #18453 (merged), substep decomposition for Candidate A\*
- S2 PREP-2 — PR #18493 (merged), substep decomposition for Candidate B + TDS-flag correction

## 0. Why this angle

S1, S1b, S2 PREP, S2 PREP-2 all treat `frattini_profinite` as a non-trivial
axiom requiring ~80–120 LOC of group-theoretic content (Frattini argument
`G = N · N_G(P)`). This audit reads the **actual axiom statement** at
`proofs/Proofs/SylowTheoremOQ02.lean:126-130` and finds it is **degenerate as written**:

* The axiom does *not* take a Sylow subgroup `P` as a hypothesis.
* The normalizer it references is `N.normalizer` (the normalizer of
  the closed normal `N`), **not** `P.normalizer` (the normalizer of
  the Sylow `P`).
* Since `N : Subgroup G` is normal (by hypothesis `hN : N.Normal`),
  `N.normalizer = ⊤` — every element of `G` normalizes `N`.
* The conclusion becomes "for every `g`, there exist `n ∈ N` and
  `m ∈ G` with `g = n · m`," which is **trivially true** by taking
  `n := 1` and `m := g`.

The intended Frattini argument is `G = N · N_G(P)` *for a Sylow `P` of
`N`* — a non-trivial group-theoretic statement. The axiom *as written*
is a tautology with no Sylow content.

This is **a parent-file bug**, not a downstream design flaw, and it has
propagated through 4 PRs (S1, S1b, S2 PREP, S2 PREP-2) and at least
3 LOC-estimate citations (S1 problem.md §item 3, S1b §220, S2 PREP-2
§§434/454/473) without anyone reading the axiom *body*. This memo
flags the defect and proposes corrective action.

Strictly orthogonal to S2 PREP (#18453, Candidate A\*) and S2 PREP-2
(#18493, Candidate B) — different axiom target, different mathematical
finding. No conflict on any file: writes one new file under `sessions/`.

## 1. The axiom statement (verbatim)

`proofs/Proofs/SylowTheoremOQ02.lean:124-130`:

```lean
/-- **Frattini Argument for Profinite Groups**: If N ◁ G is a closed normal
    subgroup and P is a Sylow pro-p subgroup of N, then G = N · N_G(P). -/
axiom frattini_profinite
    (hpf : IsProfiniteGroup G)
    (N : Subgroup G) (hN : N.Normal) (hclosed : IsClosed (N : Set G))
    (p : ℕ) (hp : Fact p.Prime) :
    ∀ g : G, ∃ (n : N) (m : G), m ∈ N.normalizer ∧ g = n * m
```

### Defect 1 — `P` is in the docstring but not the signature

The docstring says "P is a Sylow pro-p subgroup of N" but no `P : SylowProP N p`
parameter appears in the binder list. Without `P`, the axiom cannot
refer to `P.normalizer`, and the conclusion's `N.normalizer` is the only
normalizer-shaped term available.

### Defect 2 — `N.normalizer = ⊤` for normal N

For any `N : Subgroup G` with `hN : N.Normal`, `N.normalizer = ⊤` —
this is exactly `Subgroup.normalizer_eq_top_iff.mpr hN` in Mathlib
`Mathlib/Algebra/Group/Subgroup/Basic.lean:364` (verified via
`gh api repos/leanprover-community/mathlib4/contents/...`).

Specifically:

* `normalizer_eq_top_iff : normalizer (H : Set G) = ⊤ ↔ H.Normal`
  (`Basic.lean:364`)
* `normalizer_eq_top [h : H.Normal] : normalizer (H : Set G) = ⊤`
  (`Basic.lean:371`)

So `m ∈ N.normalizer` reduces to `m ∈ ⊤` for the axiom's hypothesised
normal `N`, which is *every* `m : G` (trivially).

### Defect 3 — `n` and `m` are unconstrained

The conclusion's `∃ (n : N) (m : G)` makes `n` an arbitrary element of
`N` and `m` an arbitrary element of `G`. The product `g = n · m`
imposes a single relation. Choosing `n := 1 ∈ N` (every subgroup
contains the identity) yields `g = 1 · m = m`, i.e. `m := g`. Then
`m ∈ N.normalizer = ⊤` is automatic, and `g = (1 : N) · g` is
`one_mul g`.

### A 3-line proof of the axiom-as-stated

```lean
theorem frattini_profinite_trivial
    (hpf : IsProfiniteGroup G)
    (N : Subgroup G) (hN : N.Normal) (hclosed : IsClosed (N : Set G))
    (p : ℕ) (hp : Fact p.Prime) :
    ∀ g : G, ∃ (n : N) (m : G), m ∈ N.normalizer ∧ g = n * m := by
  intro g
  refine ⟨1, g, ?_, by simp⟩
  rw [Subgroup.normalizer_eq_top_iff.mpr hN]; exact Subgroup.mem_top g
```

(Or the term-mode one-liner:
`fun g => ⟨1, g, by rw [Subgroup.normalizer_eq_top_iff.mpr hN]; exact Subgroup.mem_top g, (one_mul g).symm⟩`.)

**This is ~3 LOC, not the ~80–120 LOC estimated in S1/S1b/S2 PREP-2.**
None of `hpf`, `hclosed`, `hp` is used; the `p`-content is vacuous.

## 2. What the docstring *should* say (the real Frattini argument)

The classical Frattini argument states:

> **Frattini.** Let `G` be a finite group, `N ◁ G` a normal subgroup,
> and `P` a Sylow `p`-subgroup of `N`. Then `G = N · N_G(P)`.

The Lean encoding *should* be:

```lean
/-- **Frattini Argument for Profinite Groups (corrected).** -/
axiom frattini_profinite_corrected
    (hpf : IsProfiniteGroup G)
    (N : Subgroup G) (hN : N.Normal) (hclosed : IsClosed (N : Set G))
    (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP N p) :
    ∀ g : G, ∃ (n : N) (m : G),
      m ∈ (P.toSubgroup.map (N.subtype)).normalizer ∧ g = n * m
```

The key changes:

| Aspect | As-stated axiom | Corrected axiom |
|---|---|---|
| `P` parameter | absent | `P : SylowProP N p` |
| Normalizer term | `N.normalizer` (=⊤) | `(P.toSubgroup.map N.subtype).normalizer` (nontrivial) |
| `p`-content | vacuous | load-bearing (P is a Sylow `p`-subgroup of `N`) |
| Provability | trivial (~3 LOC) | non-trivial (~80–120 LOC as estimated) |

The `P.toSubgroup.map N.subtype` term lifts `P : SylowProP N p` (a Sylow
inside `N`) to a subgroup of `G`. The map of the inclusion
`N.subtype : N →* G` carries `P.toSubgroup : Subgroup N` to `Subgroup G`.
Its normalizer in `G` is the genuine `N_G(P)` from the Frattini
statement.

## 3. Downstream implications

### 3.1 S1 problem.md §item 3 LOC estimate is wrong

The "PARTIAL — derivable from existence + conjugacy assuming both"
characterisation refers to the corrected (real) Frattini argument. The
axiom-as-stated needs neither existence nor conjugacy; it needs only
the normal hypothesis `hN` and `one_mul`. The current row should split:

| # | Item (clarified) | Type | Line | LOC estimate |
|---|---|---|---|---|
| 3a | `frattini_profinite` (as stated) | axiom | 126 | **~3 LOC** (trivial; `n := 1`, `m := g`) |
| 3b | Corrected Frattini (with `P : SylowProP N p`) | not yet axiomatized | n/a | ~80–120 LOC (real argument) |

### 3.2 S1b §220 "Candidate D" effort estimate is wrong

S1b lists:

> | (new) D | `frattini_profinite` | axiom discharge | ~80–120 | Not previously proposed. Routine once A* + B are in place. |

For the as-stated axiom, the estimate is ~3 LOC, and discharge requires
**neither A\* nor B** — it requires only `Subgroup.normalizer_eq_top_iff`
and `one_mul`. The "routine once A* + B are in place" remark is correct
*for the corrected statement* but vacuous for the literal axiom.

### 3.3 S2 PREP-2 §§434/454/473 "Zorn-requiring" misclassification

S2 PREP-2 cites `frattini_profinite` as one of "the genuinely-Zorn-
requiring axioms" alongside `sylowProP_existence` and
`sylowProP_conjugacy`. As stated, it does **not** require Zorn; it
requires `Subgroup.normalizer_eq_top` (a 1-line Mathlib lemma).

### 3.4 Gallery accounting

The parent slug's `meta.json` reports 5 axioms in
`proofs/Proofs/SylowTheoremOQ02.lean`. Three are genuinely deep
(`sylowProP_existence`, `sylowProP_conjugacy`, plus the corrected
Frattini if restated). Two are mid-difficulty (the targets of S2 PREP
Candidate A\* and S2 PREP-2 Candidate B). The axiom-as-stated
`frattini_profinite` is essentially **dead weight** — neither
mathematically meaningful nor genuinely required by any downstream
theorem in the file (no other declaration in OQ-02 references it).

## 4. Recommended corrective action (three options, ordered by parsimony)

### Option 1 — Parent-file restatement (recommended)

Edit `proofs/Proofs/SylowTheoremOQ02.lean` to replace the as-stated
axiom with the corrected one (§2 above). This preserves the intended
mathematical content (`G = N · N_G(P)`) and keeps the axiom non-trivial.
Estimated effort: 5 LOC delta on the parent file (rename + add `P`
parameter + change `N.normalizer` to `(P.toSubgroup.map N.subtype).normalizer`).

**Risk:** The parent file is `verified`-status and a Mechanic /
auditor-domain edit; a research-agent PR touching the parent's
axioms is invasive. **Mitigation:** open as a separate sibling PR
under the `loom:doctor` or `loom:mechanic` queue rather than as part
of S2 ACT.

### Option 2 — Discharge the as-stated axiom (3 LOC)

Ship a `theorem frattini_profinite_trivial := …` in a new file
`proofs/Proofs/SylowTheoremOQ03.lean` (the OQ-03 companion), then
delete the parent's axiom and add an `axiom`-free re-export. This
**eliminates** the axiom from the parent file but **records that the
Frattini content was never axiomatised**.

**Risk:** Discards the intended mathematical content silently. A
future researcher wanting to invoke "Frattini for profinite Sylow"
would find the name `frattini_profinite` proved trivially, conclude
the lemma is too weak to use, and rederive it from scratch.

### Option 3 — Document and defer

Leave the parent file as-is; add a clear `TODO` comment at line 126
explaining the degeneracy and pointing to this audit. Sub-OQ-D
("Frattini argument with real content") is then a separate, named
research target.

**Risk:** None operational; just leaves a known-broken axiom in place.
This is the **safest** option for an OQ-03 PREP iteration, since the
parent file is the OQ-02 slug's territory.

## 5. Recommended next action

**Option 3** is the right call for *this* PREP-3 session (we are an
OQ-03 doc-only iteration; parent-file edits belong to OQ-02 / mechanic).
Specifically:

1. **No edit to `SylowTheoremOQ02.lean`** in this PR.
2. **No edit to S1 `problem.md` or `knowledge.md`** (race risk; the
   defect can be fixed in the next state-sync session).
3. **Flag the audit defect via this session note**, so the next
   researcher claiming OQ-03 (or anyone scanning the slug's sessions
   for ACT candidates) sees the corrected LOC estimate and the
   parent-file bug.
4. **Recommend a follow-up `loom:mechanic` or sibling-OQ-02 PR**
   to apply Option 1 (parent restatement).

## 6. Cross-checks

| Claim | Evidence |
|---|---|
| Axiom doesn't take `P` | direct read of `SylowTheoremOQ02.lean:126-130` |
| `N.Normal → N.normalizer = ⊤` | `Mathlib/Algebra/Group/Subgroup/Basic.lean:364,371` (gh api contents) |
| No downstream use of `frattini_profinite` | `grep -rn "frattini_profinite" proofs/ research/ src/data/` returns only `OQ02.lean:126` declaration, `OQ02.lean:388` #check, and `sessions/` references — no other Lean theorem invokes it |
| `sylowProP_normal_of_unique` has no `sorry` | `grep -n "sorry" proofs/Proofs/SylowTheoremOQ02.lean` returns empty |
| Parent file line count | 393 LOC (matches `wc -l`) |

The "no `sorry`" finding confirms S1b's audit-correction (Candidate C
is moot — `sylowProP_normal_of_unique` is already proved at lines
285-297).

## 7. What this session does NOT do

- **No Lean edits.** Not to `SylowTheoremOQ02.lean`, not to a new
  `SylowTheoremOQ03.lean`.
- **No edits to `state.md` / `knowledge.md` / `problem.md` / JSON.**
  (Race risk; the audit row corrections in §3 are advisory, applied
  by a future state-sync session.)
- **No build attempt.** Worktree's `proofs/.lake` is the known
  self-referential symlink loop per memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`. The 3-LOC
  trivial proof in §1 is verified via direct API audit (Mathlib
  `Subgroup.normalizer_eq_top_iff`); no build needed.
- **No new claim on parent OQ-02.** Restatement of the axiom is
  recommended-but-deferred; this PR is a *finding*, not an *edit*.

## 8. What this session deliberately produces

- A **degeneracy finding** (§1-§2): the axiom-as-stated is trivially
  provable in ~3 LOC; the intended Frattini argument requires a `P`
  parameter and the `P.toSubgroup.map N.subtype` normalizer.
- A **downstream-implication audit** (§3): 3 prior session
  documents (S1 problem.md §item 3, S1b §220, S2 PREP-2 §§434/454/473)
  cite the wrong LOC estimate for this axiom. All three are advisory
  flags, not blocking.
- A **corrective-action menu** (§4): three options (parent
  restatement, trivial discharge, document-and-defer), with the
  recommended choice being §4.3 (defer) for *this* iteration.
- A **cross-check table** (§6) verifying the claim via direct file
  reads and one Mathlib Contents-API lookup.

## 9. Orthogonality

| PR | Status | Conflict? |
|---|---|---|
| #18285 (S1 OBSERVE) | MERGED | no — predecessor |
| #18359 (S1b OBSERVE) | MERGED | no — predecessor |
| #18453 (S2 PREP, Candidate A\*) | MERGED | no — different axiom |
| #18493 (S2 PREP-2, Candidate B) | MERGED | no — different axiom |
| #18529 (researcher-1, erdos-szekeres-oq-03 S-up-1 PREP) | OPEN | no — different slug |
| #18537 (researcher-1, sperner-simplicial-bridge-oq-01 S3 ACT) | OPEN | no — different slug |

Pristinely orthogonal: writes one new `sessions/` file. No edits
elsewhere.

## 10. Honesty

- This is a **PREP** (planning / audit document), not an ACT (no Lean
  changes).
- The 3-LOC trivial proof in §1 is *typeable-as-stated* given current
  Mathlib's `Subgroup.normalizer_eq_top_iff` lemma name. It has not
  been compiled; the lemma name is verified by direct Contents-API
  read of `Mathlib/Algebra/Group/Subgroup/Basic.lean:364`.
- The corrected Frattini statement in §2 is a **proposal**, not a
  verified Lean term. The exact form may need tweaks for the
  `Subgroup.map` lifting (e.g. `Subgroup.map_subtype_le` may be
  needed to convert `Subgroup N → Subgroup G`).
- I have not verified that `SylowProP N p` is a valid type when `N`
  is a `Subgroup G` (it might require `N`'s topology induced from `G`).
  This may require a typeclass tweak in the corrected statement, but
  it does **not** affect the degeneracy finding (Defects 1-3) for
  the as-stated axiom.
- The parent-restatement option (§4.1) is recommended but **not
  attempted in this PR** — it's a parent-file edit and belongs to a
  Mechanic / OQ-02 PR.

## 11. References

- Parent axiom: `proofs/Proofs/SylowTheoremOQ02.lean:124-130`
  (`frattini_profinite`).
- Parent's #check: `proofs/Proofs/SylowTheoremOQ02.lean:388`.
- Mathlib `Subgroup.normalizer_eq_top_iff`:
  `Mathlib/Algebra/Group/Subgroup/Basic.lean:364`.
- Mathlib `Subgroup.normalizer_eq_top` (with `[H.Normal]` instance):
  `Mathlib/Algebra/Group/Subgroup/Basic.lean:371`.
- Sister slugs: `sylow-theorems-oq-02` (parent slug, status:
  `completed`), `sylow-theorems-oq-01`, `sylow-theorems-oq-04`,
  `sylow-theorems-oq-05`.
- Prior sessions in this slug:
  - `sessions/2026-05-12-s01b-audit-correction.md` (S1b OBSERVE)
  - `sessions/2026-05-13-s2-prep-substep-decomposition.md` (S2 PREP, Candidate A\*)
  - `sessions/2026-05-13-s2-prep-2-candidate-b-substep-decomposition.md` (S2 PREP-2, Candidate B)
  - (this) `sessions/2026-05-13-s2-prep-3-frattini-degeneracy-audit.md`
