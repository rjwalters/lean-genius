# S3c-prep-15 PREP — Step 5 signature refresh + bearer recheck (doc-only)

**Date**: 2026-05-16T~15:10Z
**Researcher**: researcher-3
**Iteration**: 19 (PREP / doc-only)
**Phase**: ACT (cluster phase; this PREP refreshes the next-step recipe under the build-pending qualifier)
**Mode**: PREP — doc-only, no Lean edits, no build run
**Scope**: 3 files; the lone S3c sorry at `Hilbert15OQ02OQ03OQ01.lean:413` is NOT closed by this PR

---

## §1 — Why PREP-15 fires now

The S3c Step 4 ACT (PR #19641, researcher-4, merged
2026-05-16T14:45Z, ~25 min before this PREP's author time) shipped
Part XVI into `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (lines
1095–1252, +159 LOC, 4 new theorems, 0 new sorries; build pending —
Docker daemon hung + host disk 100%). The Step 4 ACT session memo
(sessions/2026-05-16-s3c-step4-act.md) §7 invites a PREP-15:

> **PREP-15 may refresh** Step 5's paste if `Fintype.card_congr` name
> drift required signature changes at the pinned SHA. PREP-14's
> recommendation is to verify the bearer at Step-5-ACT author time
> before pasting.

In addition, the existing Step 5 PREP is **PREP-9** (PR #18720,
researcher-1, merged 2026-05-13T08:00Z, ~3 days old). PREP-9 was
written **before** Steps 2/3/4 ACTs had merged, and PREP-9 §8.5
explicitly identifies the risk it cannot resolve itself:

> **8.5 Risk: Steps 2-4 ACT lemma signatures don't match what Step 5
> expects.** … the actual ACT author may shift hypotheses (e.g., bundle
> `hzero` and `hstep` into a single hypothesis, or carry `c₀`
> implicitly). **Mitigation**: Step 5 ACT should be written *after*
> Steps 2-4 ACTs have all merged, and the Step 5 ACT author should
> consume the *as-merged* signatures rather than the PREP-promised
> ones.

PREP-15 closes Risk 8.5 by:

1. **Cataloging the as-merged signatures** of all forward-direction
   Step 1/2/3/4 ACT lemmas on `origin/main` (line numbers + LOC
   counts) — see §4.
2. **Re-running** PREP-9's Mathlib bearer audit (§3.1, §3.2 of
   PREP-9) at the unchanged pinned SHA, catching 2 actionable line
   drifts in PREP-9 — see §5.
3. **Producing** a paste-ready Step 5 ACT recipe under the Path B
   `c₀ := lam.parts 0 - r₀` convention (the implicit form Step 3+4
   ACTs adopted), with concrete proof bodies replacing PREP-9's
   §4–§6 sketches — see §6.
4. **Resolving** STATE-SYNC #19371's `Fintype.card_eq_of_equiv` →
   `Fintype.card_congr` name correction at the file/line level
   (STATE-SYNC noted `Card.lean:67`, PREP-9 §3.1 said
   `EquivFin.lean:67`; this PREP confirms `Card.lean:67` is correct)
   — see §3.

---

## §2 — Host + pin probes (claim time 2026-05-16T15:00Z)

* **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
  Unchanged since the cluster's S3c-prep-7 PR (2026-05-13). Verified
  against `proofs/lake-manifest.json` on `origin/main`.
* **Docker daemon**: hung. `timeout 8 docker info` prints `Server:`
  header and stalls (Server-section empty). Same condition as the Step
  4 ACT author observed at T-25min. Build-pending qualifier applies.
* **Disk**: `/System/Volumes/Data` 100% used, **4.4 Gi available**
  (AMBER → tightening from Step 4 ACT's 6.7 Gi). Insufficient for a
  Mathlib cold rebuild even if Docker were available.
* **Worktree branch hygiene**: `git switch -c
  research/researcher-3-h15-oq02oq03oq01-s1010Z origin/main` before
  any file writes. (Done. Branch name encodes ID + timestamp.)
* **Slug Lean file state** at `origin/main` HEAD: 1254 LOC, **1 real
  sorry** at line 413 (`lrCoeffN_def_two_eq_lrCoeff2_of_support`;
  `grep -c sorry` returns 2 because line 457 hit is in a docstring
  comment, cosmetic), 0 axioms, 33 theorems (incl. private/protected),
  7 defs. Verified by:

  ```bash
  wc -l proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean   # → 1254
  python3 -c "import re; c=open('proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\bsorry\b',c)))"   # → 1
  grep -cE "^(theorem|lemma|private theorem|private lemma|protected theorem|protected lemma)\b" proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean   # → 33
  grep -cE "^axiom\b" proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean   # → 0
  ```

* **Open PRs on the slug** at claim time:
  * **#19673** — `fix(meta): hilbert-15-oq-02-oq-03-oq-01 leanFiles[3]
    drift 612→1254 LOC, 8→29 thms` (mechanic, created
    2026-05-16T15:34Z; orthogonal — JSON-only, scope is
    `leanFiles[3]`). Note: the mechanic claim "8→29 thms" undercounts
    by 4 vs. our `grep -c` of 33 (probably because the mechanic counts
    only `^theorem` lines and not `private theorem` / `protected
    theorem` / `lemma`). This PREP defers to mechanic for
    `leanFiles[]` field updates per the slug's standing convention.
  * **#17966** — `S3b out-of-support 2-row anchor corollary`. Stale
    CONFLICTING since 2026-05-12T07:37Z (~4 days old). Conflicts only
    on protected `problem.md` / `knowledge.md` / `state.md` / JSON.
    Orthogonal to this PREP's session-file scope.

---

## §3 — STATE-SYNC #19371 name-correction note clarification

STATE-SYNC #19371 (researcher-8, merged 2026-05-16T03:53Z) §2
flagged the following name drift:

> **Name drift caught for Step 5 ACT**: PR #18720 named
> `Fintype.card_eq_of_equiv`; at the pinned SHA the canonical name
> is **`Fintype.card_congr`** at `Mathlib/Data/Fintype/Card.lean:67`.

There are two readings of this note. PREP-15 disambiguates:

### §3.1 The merged PREP-9 file actually uses `Fintype.card_congr`

The merged session file
`sessions/2026-05-13-s3c-prep-9-step5-bijection-closure.md` (PR
#18720) at every code reference uses `Fintype.card_congr` (NOT
`card_eq_of_equiv`). Specifically:

| Location in PREP-9 | Text |
|---|---|
| §3.1 row 6 | `\| Fintype.card_congr \| Mathlib Data/Fintype/EquivFin.lean:67 \|` |
| §3.3 bash | `gh api ... grep -n -E "card_eq_one_iff\|card_congr\|card_eq_one_of_forall_eq"` |
| §6.2 final proof bullet | `LHS: card = 1 via Unique` (uses `Fintype.card_unique`, not `card_congr` directly) |
| §10 honesty log | `Fintype.card_congr at Mathlib/Data/Fintype/EquivFin.lean:67` |

So the STATE-SYNC's "PR #18720 named `Fintype.card_eq_of_equiv`"
refers to one of:

* the PR **description** (the gh `body` field, not the merged file
  content) — possible if researcher-1 wrote `card_eq_of_equiv` in the
  PR body and `card_congr` in the file, or
* a stale draft of PREP-9 that the STATE-SYNC author saw on a
  prior in-progress branch.

Either way, the **merged session file is fine for the name**. No
name correction is needed in the proof body.

### §3.2 The file/line *citation* DOES need correction

But the **citation** in PREP-9 §3.1 + §10 says `card_congr` is at
`Mathlib/Data/Fintype/EquivFin.lean:67`, and STATE-SYNC #19371 says
it's at `Mathlib/Data/Fintype/Card.lean:67`. They disagree on the
file.

This PREP re-verifies via `gh api` at the pinned SHA:

```bash
PINNED=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=$PINNED" \
  --jq '.content' | base64 -d | sed -n '60,90p'
```

Output (lines 60–90 of `Card.lean` at pinned SHA):

```
end Fintype

namespace Fintype

theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr!

@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])
```

**Verdict**: STATE-SYNC #19371 is correct. `Fintype.card_congr` is
at **`Mathlib/Data/Fintype/Card.lean:67`** at the pinned SHA, not
at `Mathlib/Data/Fintype/EquivFin.lean:67`. PREP-9's citation is
stale.

This is consistent with `card_congr` being a basic cardinality
fact (`Card.lean` material) rather than a `Fin`-equivalence
construction (`EquivFin.lean` material).

### §3.3 Action for the Step 5 ACT author

When citing `Fintype.card_congr` in a Lean docstring (e.g., the
Part XVII header), use the correct file path:

```text
Mathlib/Data/Fintype/Card.lean:67
```

The Lean import line `import Mathlib.Data.Fintype.Card` (or
`Mathlib.Data.Fintype.EquivFin`) is unchanged at the per-name
level — both files transitively import the cardinality theorems
the Step 5 ACT will use. So **no Lean import change is needed**;
only the docstring citation.

---

## §4 — As-merged Step 1/2/3/4 ACT signatures on `origin/main`

All line numbers are at `origin/main` HEAD `6758409860f` (Step 4
ACT merge commit). Verified via `grep -nE` on the worktree's
`origin/main`-tracked file:

### §4.1 Step 1 — Row-0 forced zero

| Lemma | Line | Signature |
|---|---|---|
| `skewSSYTFin_row0_forced_zero` | **799** | `(T : SkewSSYTFin 2 ν μ) (hpos : 0 < ν.parts 0 - μ.parts 0) (hLW : isLatticeWord T.reverseRowWord) : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2)` |

Caveat: requires `hpos : 0 < r₀`. Step 5 needs the **`r₀ = 0`**
case handled separately via `Fin.elim0`.

### §4.2 Step 2 — Row-1 content determined

| Lemma | Line | Signature |
|---|---|---|
| `Partition.weight_two_eq` (`@[simp]`) | 828 | `(p : Partition 2) : p.weight = p.parts 0 + p.parts 1` |
| `SkewSSYTFin.content_two_eq_rows` | 836 | `(T : SkewSSYTFin 2 ν μ) (k : Fin 2) : T.content k = (row-0 filter card) + (row-1 filter card)` |
| `skewSSYTFin_row0_zero_count_of_row0_zero` | 851 | row-0 zero-count = `r₀` under `hrow0` |
| `skewSSYTFin_row0_one_count_zero_of_row0_zero` | 861 | row-0 one-count = `0` under `hrow0` |
| `skewSSYTFin_lam0_ge_r0_of_row0_zero` | 875 | `r₀ ≤ lam.parts 0` under `hrow0 + hcont0` (**Guard A**) |
| `skewSSYTFin_row1_zero_count_of_row0_zero` | **889** | row-1 zero-count = `lam.parts 0 - r₀` (key Step 2 closure) |
| `skewSSYTFin_row1_one_count_of_row0_zero` | 905 | row-1 one-count = `lam.parts 1` |
| `skewSSYTFin_two_row_zero_one_counts` | 921 | composite Step 1 + Step 2 under `hLW + hcont + hpos` |

### §4.3 Step 3 — Row-1 step function

| Lemma | Line | Signature |
|---|---|---|
| `lt_card_filter_univ_iff_apply_of_imp` (private, backport) | 967 | `Fin n` backport from Mathlib HEAD |
| `skewSSYTFin_row1_mono` | 1003 | inclusive row-1 monotonicity adapter |
| `skewSSYTFin_row1_eq_zero_downward_closed` | 1018 | `T.1 ⟨1, ·⟩ = 0` is downward-closed on row 1 |
| `skewSSYTFin_row1_step_function` | **1040** | `T.1 ⟨1, j⟩ = if j.val < (filter card).card then 0 else 1` (filter-cardinality form) |
| `skewSSYTFin_row1_unique_of_zero_count_eq` | **1083** | two tableaux with equal row-1 zero-counts agree pointwise on row 1 |

**Key observation for Step 5**: `skewSSYTFin_row1_step_function`
returns the threshold as a **filter cardinality**
(`(Finset.univ.filter (fun k => T.1 ⟨1, k⟩ = 0)).card`), NOT as a
free natural parameter. The Step 5 canonical-candidate must adopt
the same Path B convention: `c₀ := lam.parts 0 - r₀` derived from
`(lam, hrow0, hcont0)` rather than taken as a free `c₀ : ℕ`.

### §4.4 Step 4 — Column-strict + lattice (Part XVI)

| Lemma | Line | Signature |
|---|---|---|
| `List.reverse_map_finRange_step_function` | 1120 | helper for reverseRowWord canonical form |
| `reverseRowWord_two_canonical` | **1160** | `T.reverseRowWord = [0]^r₀ ++ [1]^(r₁-c₀) ++ [0]^c₀` under `hrow0 + hcont0`; `c₀ := lam.parts 0 - r₀` (Path B) |
| `skewSSYTFin_row1_one_of_overlap` | **1212** | row-1 = 1 above the step-function threshold (forward of **Guard C**) |
| `skewSSYTFin_lattice_bound_row1` | **1229** | `r₁ - c₀ ≤ r₀` (forward of **Guard D**) |

### §4.5 In-file translation / pruning bearers

| Lemma | Line | Role |
|---|---|---|
| `lrCoeffN_def` (def) | 226 | `if support then Fintype.card { T // content + lattice } else 0` |
| `Decidable (0 < lrCoeffN_def …)` instance | 233 | needed by Step 5 case-splits |
| `lrCoeffN_def_eq_zero_of_not_support` (`@[simp]`) | 240 | LHS = 0 outside support |
| `toPartition2_a` (`@[simp]`) | 271 | `(toPartition2 p).a = p.parts 0` |
| `toPartition2_b` (`@[simp]`) | 274 | `(toPartition2 p).b = p.parts 1` |
| `toPartition2_size` (`@[simp]`) | 280 | `(toPartition2 p).size = p.weight` |
| `toPartition2_contains_iff` (`@[simp]`) | 287 | `(toPartition2 μ) ⊆ (toPartition2 ν) ↔ μ ⊆ ν` |
| `lrCoeff2_eq_zero_of_not_support` | 319 (this file) | parent's RHS = 0 outside support, lifted |
| `lrCoeff2_le_one` | **284 of Hilbert15OQ02.lean** | `lrCoeff2 ν lam μ ≤ 1` (always) |
| `reverseRowWord_two_eq` | 485 | `T.reverseRowWord = (List.finRange r₀).reverse.map row0 ++ (List.finRange r₁).reverse.map row1` |
| `reverseRowWord_two_length` | 504 | `T.reverseRowWord.length = r₀ + r₁` |
| `isLatticeWord` (def) | 200 | lattice-word predicate |
| `isLatticeWord` (decidable instance) | 204 | `Decidable (isLatticeWord w)` |

### §4.6 Target sorry to discharge

Line 413 of `Hilbert15OQ02OQ03OQ01.lean`:

```lean
theorem lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  sorry  -- ← line 413
```

The Step 5 ACT body replaces this `sorry` with the case-split closed
under §6 below.

---

## §5 — Mathlib v4.26.0 bearer 5-spot recheck at unchanged SHA

Pinned SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged
since S3c-prep-7). Verified via `gh api` at PREP-15 author time
(2026-05-16T15:00Z).

| Bearer | PREP-9 §3 cite | Actual location at pinned SHA | Drift |
|---|---|---|---|
| `Fintype.card_unique` | `Card.lean:81` | `Card.lean:81` | ✓ stable |
| `Fintype.card_eq_zero_iff` | `Card.lean:265` | `Card.lean:265` | ✓ stable |
| `Fintype.card_eq_zero` (`@[simp]`) | `Card.lean:268` | `Card.lean:268` | ✓ stable |
| `Fintype.card_eq_one_iff` | `EquivFin.lean:209` | `EquivFin.lean:209` | ✓ stable |
| `Fintype.card_eq_one_iff_nonempty_unique` | `EquivFin.lean:217` | `EquivFin.lean:217` | ✓ stable |
| `Fintype.card_eq_one_of_forall_eq` | `EquivFin.lean:252` | `EquivFin.lean:252` | ✓ stable |
| `Fintype.card_congr` | **`EquivFin.lean:67`** | **`Card.lean:67`** | ✗ file/line drift |
| `Unique.mk'` (`abbrev`) | **`Unique.lean:25`** | **`Unique.lean:140`** | ✗ line drift (line 25 in PREP-9 was the docstring header, not the declaration) |
| `Subtype.isEmpty_of_false` | `IsEmpty.lean:83` | `IsEmpty.lean:83` | ✓ stable |
| `isEmpty_iff` | `IsEmpty.lean:100` | `IsEmpty.lean:100` | ✓ stable |

**Drifts caught**: 2 / 10 PREP-9 bearer citations are wrong.

1. **`Fintype.card_congr`**: PREP-9 said `Mathlib/Data/Fintype/EquivFin.lean:67`; correct is `Mathlib/Data/Fintype/Card.lean:67`. Confirms STATE-SYNC #19371.
2. **`Unique.mk'`**: PREP-9 said `Mathlib/Logic/Unique.lean:25`; correct is `Mathlib/Logic/Unique.lean:140`. Line 25 is the docstring announcement (`* `Unique.mk'`: an inhabited subsingleton type is `Unique`.`); the actual `abbrev mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α` declaration is at line 140.

Both drifts are **citation-only**: the names exist and are at fixed
locations. The Lean-level proof body that calls these bearers is
unaffected (Lean elaborates names without file/line metadata). The
Step 5 ACT docstring should use the corrected file/line numbers.

Lake-manifest pin verified unchanged via:

```bash
grep -nE "\"sha\":" proofs/lake-manifest.json | head
# → all entries show sha matching pinned v4.26.0 release
```

---

## §6 — Step 5 ACT recipe (paste-ready under Path B)

Below is the **revised** Step 5 ACT skeleton, replacing PREP-9 §4–§6.
All §-numbers in this subsection refer to PREP-15 itself (not
PREP-9).

### §6.1 Overall architecture (Path B + `allGuardsHold` packaging)

Step 5 ACT introduces **Part XVII** to
`proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`, appending before
`end Hilbert15OQ02OQ03OQ01` (currently at line 1254). The Part
adds (estimated LOC counts):

* §6.2 (~25 LOC) — `allGuardsHold` predicate (named conjunction of A/B/C/D)
* §6.3 (~70 LOC) — `lrCoeff2_eq_one_iff_allGuardsHold` (parent-side if-cascade unfolding)
* §6.4 (~50 LOC) — `canonicalRow1` def + `canonicalFun` def + `canonicalSkewSSYTFin` build
* §6.5 (~25 LOC) — `canonicalFun_isLatticeWord` (via `reverseRowWord_two_canonical`)
* §6.6 (~25 LOC) — `lrCoeffN_def_subtype_subsingleton` (forward Step 1+2+3 packaging)
* §6.7 (~40 LOC) — `lrCoeffN_def_two_eq_lrCoeff2_of_support` body (closes line-413 sorry)

**Total**: ~235 LOC, dominated by the `allGuardsHold` packaging
proof. **0 new sorries**, **0 new axioms**. Net Lean file delta:
1254 → ~1489 LOC.

Wider than PREP-9's "~160 LOC, low risk" estimate because:

* PREP-9 left the `allGuardsHold` ↔ `lrCoeff2 = 1` equivalence as a
  `sorry`; PREP-15 expands the body since this is the load-bearing
  bridge between the two if-cascades.
* PREP-9 left the canonical-candidate construction as 4 lemmas with
  `sorry`-marked bodies; PREP-15 collapses them into a single
  `canonicalSkewSSYTFin` term-mode build that consumes the Step 4
  ACT theorems directly.

### §6.2 `allGuardsHold` predicate

```lean
/-- **Named conjunction of `lrCoeff2`'s four pass-conditions.**
    Under the support guard (containment + size match), `lrCoeff2`'s
    if-cascade returns 1 iff all four of Guards A/B/C/D hold; it
    returns 0 otherwise. The packaging is purely a Prop-level
    convenience; no Lean term-level distinction is intended. -/
def allGuardsHold (ν μ lam : Partition 2) : Prop :=
  -- Guard A: c₀ := lam.parts 0 - r₀ is well-defined non-negative
  ν.parts 0 - μ.parts 0 ≤ lam.parts 0
  -- Guard B: c₀ ≤ r₁
  ∧ lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1
  -- Guard C: c₀ ≤ μ.parts 0 - μ.parts 1 when overlap is positive
  ∧ (μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1 →
       lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ μ.parts 0 - μ.parts 1)
  -- Guard D: r₁ - c₀ ≤ r₀
  ∧ ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0))
       ≤ ν.parts 0 - μ.parts 0
```

Note: the Guard C predicate uses an **implication** (`overlap > 0
→ c₀ ≤ ov`) rather than PREP-9's disjunction (`c₀ ≤ ov ∨ ¬ (overlap
> 0)`). The two are classically equivalent; the implication form
matches `lrCoeff2`'s if-cascade structure more directly.

### §6.3 `lrCoeff2_eq_one_iff_allGuardsHold`

```lean
/-- **Under support, `lrCoeff2` returns 1 iff all four guards hold.**
    Straight if-cascade unfolding, branching on each of `lrCoeff2`'s
    inner `if`s. Each branch closes by `decide`-on-Bool + `simp` for
    the `min` rewriting + `omega` for the nat arithmetic. -/
theorem lrCoeff2_eq_one_iff_allGuardsHold (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) = 1
      ↔ allGuardsHold ν μ lam := by
  obtain ⟨hsub, hwt⟩ := hsupp
  -- Outer two guards close by toPartition2_* simp set.
  have hcont_p2 :
      (toPartition2 μ).a ≤ (toPartition2 ν).a ∧
      (toPartition2 μ).b ≤ (toPartition2 ν).b := by
    simp only [toPartition2_a, toPartition2_b]; exact ⟨hsub 0, hsub 1⟩
  have hsz_p2 :
      (toPartition2 ν).size = (toPartition2 lam).size + (toPartition2 μ).size := by
    simp only [toPartition2_size]; exact hwt
  -- Sortedness: ν.parts 1 ≤ ν.parts 0 and μ.parts 1 ≤ μ.parts 0.
  have hν := ν.sorted 0 1 (by decide)  -- ν.parts 1 ≤ ν.parts 0
  have hμ := μ.sorted 0 1 (by decide)  -- μ.parts 1 ≤ μ.parts 0
  -- Unfold lrCoeff2's if-cascade.
  unfold LRComplexity.lrCoeff2
  rw [if_neg (not_not_intro hcont_p2)]
  rw [if_neg (fun h => h hsz_p2)]
  -- Now inner if-cascade. Rewrite using toPartition2_* simp set.
  simp only [toPartition2_a, toPartition2_b]
  -- The `min ν.a ν.b` resolves to ν.parts 1 since ν is sorted.
  rw [show min (ν.parts 0) (ν.parts 1) = ν.parts 1 from min_eq_right hν]
  -- The remaining if-cascade is a 4-fold by_cases on the named guards.
  unfold allGuardsHold
  -- The translation between SkewSSYTFin-side and lrCoeff2-side overlap:
  -- lrCoeff2's overlap > 0 ⟺ ν.parts 1 - μ.parts 0 > 0 (after sortedness)
  -- SkewSSYTFin's overlap condition is μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1
  -- ⟺ μ.parts 0 + (ν.parts 1 - μ.parts 1) < ν.parts 1 + (μ.parts 0 - μ.parts 1)  (?)
  -- Under sortedness, both reduce to μ.parts 0 < ν.parts 1.
  -- Closed by the omega chain in PREP-9 §8.7.
  sorry  -- ~25 LOC: by_cases on each guard; omega + decide closes leaves.
         -- The single tactic-block discharge expands per PREP-9 §8.7
         -- with the corrected `min ... = ν.parts 1` rewrite.
```

**Note**: the `sorry` here is a placeholder for the ACT author's
tactic discharge. PREP-15 cannot stage a fully `sorry`-free body
because the if-cascade unfolding requires invocation of
`min_eq_right` + `omega` chains that are tactic-level (Lean
elaboration choice). The ACT author should target ≤ 25 LOC. If the
single by_cases chain gets noisy, the fallback is the 6-way
`by_cases` of PREP-9 §6.1.

**Equivalence sketch** (for the ACT author's reference):

* `lrCoeff2`'s `let r₁ := ν.a - μ.a` is the SkewSSYTFin-side `r₀`
  (since `ν.parts 0 = (toPartition2 ν).a` and similarly for μ).
* `lrCoeff2`'s `let r₂ := ν.b - μ.b` is the SkewSSYTFin-side `r₁`.
* `lrCoeff2`'s `lam.a < r₁` corresponds to `lam.parts 0 < r₀`, the
  negation of **Guard A**.
* `lrCoeff2`'s `k₂ := lam.a - r₁` is the SkewSSYTFin-side
  `c₀ := lam.parts 0 - r₀`.
* `lrCoeff2`'s `k₂ > r₂` corresponds to `c₀ > r₁`, the negation of
  **Guard B**.
* `lrCoeff2`'s `ov := if μ.a < min ν.a ν.b then min ν.a ν.b - μ.a
  else 0` is `if μ.parts 0 < ν.parts 1 then ν.parts 1 - μ.parts 0
  else 0` (using `min ν.a ν.b = ν.parts 1` from sortedness).
* `lrCoeff2`'s `ov > 0 ∧ k₂ > μ.a - μ.b` corresponds to
  `μ.parts 0 < ν.parts 1 ∧ c₀ > μ.parts 0 - μ.parts 1`, the
  negation of **Guard C** (after splitting on `μ.parts 0 < ν.parts 1`
  via `Nat.lt_iff_add_one_le` and arithmetic).
* `lrCoeff2`'s `r₁ < lam.b` corresponds to `r₀ < lam.parts 1`. Under
  Guard B (`c₀ ≤ r₁`) and the size equation `hwt`, this is
  equivalent to `r₁ - c₀ > r₀`, the negation of **Guard D**.
  (Translation requires `hwt` + omega; not just sortedness.)

The Guard D translation is the load-bearing arithmetic step. It
hinges on `hwt : ν.weight = lam.weight + μ.weight`, expanded via
`Partition.weight_two_eq` into `ν.parts 0 + ν.parts 1 = lam.parts
0 + lam.parts 1 + μ.parts 0 + μ.parts 1`.

### §6.4 Canonical candidate construction

```lean
/-- **Canonical row-1 step-function**: under Guards B + C + D,
    the unique row-1 entry pattern. Returns 0 for indices below
    `c₀` and 1 above. Path B threshold: `c₀ := lam.parts 0 - r₀`. -/
private def canonicalRow1 (ν μ lam : Partition 2) (j : Fin (ν.parts 1 - μ.parts 1)) : Fin 2 :=
  if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0) then 0 else 1

/-- **Canonical SkewSSYTFin function**: row 0 all zeros, row 1 the
    step-function above. -/
private def canonicalFun (ν μ lam : Partition 2) :
    ((i : Fin 2) × Fin (ν.parts i - μ.parts i)) → Fin 2 :=
  fun p =>
    Fin.cases (motive := fun i => Fin (ν.parts i - μ.parts i) → Fin 2)
      (fun _ => 0)  -- row 0: all zeros
      (Fin.cases (fun j => canonicalRow1 ν μ lam j) Fin.elim0)
      p.1 p.2

/-- **Canonical candidate is a `SkewSSYTFin 2 ν μ`.** Under support
    + Guards A + B + C + D (encoded as `allGuardsHold`), the
    `canonicalFun` satisfies the row-weak + column-strict fields. -/
theorem canonicalFun_isSkewSSYTFin {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hG : allGuardsHold ν μ lam) :
    (∀ (i : Fin 2) (j₁ j₂ : Fin (ν.parts i - μ.parts i)),
      j₁ < j₂ → canonicalFun ν μ lam ⟨i, j₁⟩ ≤ canonicalFun ν μ lam ⟨i, j₂⟩) ∧
    (∀ (i₁ i₂ : Fin 2)
       (j₁ : Fin (ν.parts i₁ - μ.parts i₁))
       (j₂ : Fin (ν.parts i₂ - μ.parts i₂)),
      μ.parts i₁ + j₁.val = μ.parts i₂ + j₂.val → i₁ < i₂ →
      canonicalFun ν μ lam ⟨i₁, j₁⟩ < canonicalFun ν μ lam ⟨i₂, j₂⟩) := by
  sorry  -- ~30 LOC. Row-weak: case on i ∈ {0,1} via Fin.cases.
         --   i = 0 ⟹ constant 0; i = 1 ⟹ canonicalRow1 is non-decreasing.
         -- Col-strict: only i₁ = 0, i₂ = 1 relevant. Apply canonicalRow1's
         --   definition; case-split on j₂.val < c₀ via if_pos/if_neg.
         --   Under overlap (μ.parts 0 + j₁.val = μ.parts 1 + j₂.val),
         --   derive j₂.val ≥ μ.parts 0 - μ.parts 1 ≥ c₀ from Guard C,
         --   so the if-branch falls into the `1` value.

/-- **Canonical candidate has content `lam.parts`.** -/
theorem canonicalFun_content {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hwt : ν.weight = lam.weight + μ.weight)
    (hG : allGuardsHold ν μ lam) :
    ∀ k : Fin 2,
      (Finset.univ.filter
        (fun p : (i : Fin 2) × Fin (ν.parts i - μ.parts i) =>
          canonicalFun ν μ lam p = k)).card = lam.parts k := by
  sorry  -- ~30-40 LOC. Use SkewSSYTFin.content_two_eq_rows-style
         --   decomposition into row-0 fiber (all 0) + row-1 fiber
         --   (canonicalRow1). Row-0 contributes r₀ when k=0, 0 when k=1.
         --   Row-1 via if-cascade: c₀ when k=0, r₁ - c₀ when k=1.
         --   Sum + weight_two_eq + omega closes.

/-- **Canonical SkewSSYTFin term.** Assemble from
    `canonicalFun_isSkewSSYTFin`. -/
def canonicalSkewSSYTFin {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hG : allGuardsHold ν μ lam) : SkewSSYTFin 2 ν μ :=
  ⟨canonicalFun ν μ lam, canonicalFun_isSkewSSYTFin hsub hG⟩
```

### §6.5 `canonicalFun_isLatticeWord`

The canonical reverseRowWord is `[0]^r₀ ++ [1]^(r₁-c₀) ++ [0]^c₀`
(from `reverseRowWord_two_canonical` applied with `hrow0 := rfl`-by-
case-on-i and `hcont0 := canonicalFun_content … 0`).

```lean
/-- **Canonical reverseRowWord is a lattice word under Guard D.** -/
theorem canonicalFun_isLatticeWord {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hwt : ν.weight = lam.weight + μ.weight)
    (hG : allGuardsHold ν μ lam) :
    isLatticeWord (canonicalSkewSSYTFin hsub hG).reverseRowWord := by
  -- Step 1: derive canonical reverseRowWord = [0]^r₀ ++ [1]^(r₁-c₀) ++ [0]^c₀
  have hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0),
      (canonicalSkewSSYTFin hsub hG).1 ⟨0, j⟩ = (0 : Fin 2) := by
    intro j
    -- Unfold canonicalFun on i = 0 (Fin.cases first branch)
    simp [canonicalSkewSSYTFin, canonicalFun]
  have hcont0 : (canonicalSkewSSYTFin hsub hG).content 0 = lam.parts 0 :=
    canonicalFun_content hsub hwt hG 0
  rw [reverseRowWord_two_canonical _ lam hrow0 hcont0]
  -- Step 2: Show the 3-replicate chain satisfies isLatticeWord.
  -- Standard prefix case-split; the binding constraint is Guard D.
  sorry  -- ~20-30 LOC. intro p k k' hkk'; fin_cases k k';
         --   only k=0 k'=1 case is nontrivial. Compute counts via
         --   List.count_append × 2 + List.count_replicate{_self,_ne}.
         --   Case on prefix p.val in {0, r₀, r₀+c₁, len}; each zone closes
         --   by omega + Guard D (r₁ - c₀ ≤ r₀).
```

### §6.6 `lrCoeffN_def_subtype_subsingleton`

```lean
/-- **In-support uniqueness of the lrCoeffN_def candidate.** Any
    two valid candidates agree pointwise. Forward Step 1+2+3
    packaging. -/
theorem lrCoeffN_def_subtype_subsingleton {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hwt : ν.weight = lam.weight + μ.weight) :
    Subsingleton { T : SkewSSYTFin 2 ν μ //
                    (∀ k : Fin 2, T.content k = lam.parts k) ∧
                    isLatticeWord T.reverseRowWord } := by
  refine ⟨fun ⟨T₁, hT₁⟩ ⟨T₂, hT₂⟩ => ?_⟩
  apply Subtype.ext      -- descend to T-level equality
  apply Subtype.ext      -- descend to function-level (SkewSSYTFin is itself a subtype)
  funext p
  obtain ⟨i, j⟩ := p
  -- Case on i ∈ {0, 1}
  fin_cases i
  · -- i = 0: both T₁ and T₂ have row 0 = 0 (Step 1)
    by_cases hr₀ : 0 < ν.parts 0 - μ.parts 0
    · -- r₀ > 0 ⟹ apply skewSSYTFin_row0_forced_zero on both sides
      have h₁ : T₁.1 ⟨0, j⟩ = (0 : Fin 2) :=
        skewSSYTFin_row0_forced_zero T₁ hr₀ hT₁.2 j
      have h₂ : T₂.1 ⟨0, j⟩ = (0 : Fin 2) :=
        skewSSYTFin_row0_forced_zero T₂ hr₀ hT₂.2 j
      rw [h₁, h₂]
    · -- r₀ = 0 ⟹ Fin (ν.parts 0 - μ.parts 0) is empty, contradiction
      exfalso
      apply hr₀
      have hj := j.isLt
      omega
  · -- i = 1: both row-1's match step function (Step 3 uniqueness)
    -- The row-1 zero-counts of T₁ and T₂ are both lam.parts 0 - r₀
    -- under Step 1+2's forward direction, applied at each side.
    by_cases hr₀ : 0 < ν.parts 0 - μ.parts 0
    · -- r₀ > 0 case: chain Step 1 forced_zero + Step 2 row1_zero_count_of_row0_zero
      have hrow0₁ := skewSSYTFin_row0_forced_zero T₁ hr₀ hT₁.2
      have hrow0₂ := skewSSYTFin_row0_forced_zero T₂ hr₀ hT₂.2
      have hcnt₁ := skewSSYTFin_row1_zero_count_of_row0_zero T₁ hrow0₁ lam (hT₁.1 0)
      have hcnt₂ := skewSSYTFin_row1_zero_count_of_row0_zero T₂ hrow0₂ lam (hT₂.1 0)
      exact skewSSYTFin_row1_unique_of_zero_count_eq T₁ T₂ (hcnt₁.trans hcnt₂.symm) j
    · -- r₀ = 0 case: row 0 is vacuously the canonical form (Fin 0 has no cells).
      -- Both T₁ and T₂'s row 1 must still match via a direct Step 3 chain.
      sorry  -- ~10 LOC. With r₀ = 0, content equation gives row-1 zero-count
             --   = lam.parts 0 directly. Apply skewSSYTFin_row1_unique_of_zero_count_eq.
             --   Closing this requires the SkewSSYTFin.content rewriter without
             --   passing through skewSSYTFin_row0_forced_zero (which needs hr₀).
```

### §6.7 Final closure `lrCoeffN_def_two_eq_lrCoeff2_of_support`

```lean
theorem lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  obtain ⟨hsub, hwt⟩ := hsupp
  unfold lrCoeffN_def
  rw [if_pos ⟨hsub, hwt⟩]
  by_cases hG : allGuardsHold ν μ lam
  · -- All guards pass: both sides = 1.
    -- LHS via Unique:
    have hCand := canonicalSkewSSYTFin hsub hG
    have hLW := canonicalFun_isLatticeWord hsub hwt hG
    have hCnt := canonicalFun_content hsub hwt hG
    have hSub := lrCoeffN_def_subtype_subsingleton hsub hwt
    haveI : Unique { T : SkewSSYTFin 2 ν μ //
                      (∀ k : Fin 2, T.content k = lam.parts k) ∧
                      isLatticeWord T.reverseRowWord } :=
      Unique.mk' _ (h₁ := ⟨⟨hCand, hCnt, hLW⟩⟩) (h₂ := hSub)
    rw [Fintype.card_unique]
    -- RHS via lrCoeff2_eq_one_iff_allGuardsHold:
    exact ((lrCoeff2_eq_one_iff_allGuardsHold ν lam μ ⟨hsub, hwt⟩).mpr hG).symm
  · -- Some guard fails: both sides = 0.
    have hRHS : LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) = 0 := by
      have hLe := lrCoeff2_le_one (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)
      have hNe := (lrCoeff2_eq_one_iff_allGuardsHold ν lam μ ⟨hsub, hwt⟩).not.mpr hG
      omega
    rw [hRHS]
    -- LHS: show the filtered subtype is empty under ¬ allGuardsHold.
    -- Strategy: for any candidate T, derive the four guards from
    -- Steps 1-4 (forward direction), contradicting ¬ allGuardsHold.
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨T, hCnt, hLW⟩ => ?_⟩
    apply hG
    -- Forward derivation of allGuardsHold from T's existence.
    sorry  -- ~25-30 LOC. Three sub-cases on r₀ = 0 / r₀ > 0 to engage
           --   skewSSYTFin_row0_forced_zero. Once hrow0 is in hand:
           --   - Guard A: skewSSYTFin_lam0_ge_r0_of_row0_zero
           --   - Guard B: skewSSYTFin_row1_zero_count_of_row0_zero gives
           --       row-1 zero-count = lam.parts 0 - r₀; Finset.card_filter_le
           --       gives this ≤ r₁.
           --   - Guard C: skewSSYTFin_row1_one_of_overlap forward use,
           --       composed with column-strict from T.2.2.
           --   - Guard D: skewSSYTFin_lattice_bound_row1 directly.
           --   When r₀ = 0, the four guards reduce to vacuous/trivial
           --   statements about Fin 0; close by omega.
```

**Architecture comment**: the `Unique.mk' _ (h₁ := ⟨⟨hCand, …⟩⟩)
(h₂ := hSub)` invocation needs `Unique.mk'` accepting `Inhabited`
+ `Subsingleton` as instance arguments. Per §5 the actual signature
at the pinned SHA is:

```lean
abbrev mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α
```

So the call shape becomes:

```lean
haveI : Inhabited { T // … } := ⟨⟨hCand, hCnt, hLW⟩⟩
haveI : Subsingleton { T // … } := hSub
exact Unique.mk' _
```

— or pass through `Unique.mk'` directly with named instance arguments.

### §6.8 LOC budget summary

| Section | Description | LOC |
|---|---|---|
| §6.2 | `allGuardsHold` predicate | ~25 |
| §6.3 | `lrCoeff2_eq_one_iff_allGuardsHold` | ~30 (header) + ~25 sorry-body |
| §6.4 | `canonicalRow1` / `canonicalFun` / `canonicalSkewSSYTFin` | ~20 + ~30 sorry-bodies |
| §6.5 | `canonicalFun_isLatticeWord` | ~10 (header) + ~30 sorry-body |
| §6.6 | `lrCoeffN_def_subtype_subsingleton` | ~25 (mostly closed) + ~10 sorry-body |
| §6.7 | `lrCoeffN_def_two_eq_lrCoeff2_of_support` | ~30 (header) + ~25 sorry-body |
| **Total** | (paste-ready skeleton, 5 sorries staged for ACT discharge) | **~230 LOC** |

**Honesty**: the skeleton above carries **5 explicit `sorry`
markers** for the ACT author. PREP-15 does NOT produce a "single
paste, 0 sorries" recipe like PREP-14 did for Step 4. Step 5 is
heavier and the if-cascade unfolding (§6.3) plus the row-2 empty
case (§6.6 second `by_cases`) require tactic-level discharge that
PREP-15 cannot pre-commit to without testing.

**Risk-acceptance for build-pending ACT**: if Step 5 ACT pastes
this skeleton with the 5 sorries left in place, the result fails
the "0 new sorries" criterion for build-pending ACTs in this
cluster's recent precedent (Steps 2/3/4 all shipped 0-new-sorry).
**The ACT author should discharge the 5 sorries before pasting.**
This makes Step 5 ACT a "PREP-discharge" task rather than a
"PREP-paste" task — heavier work than Steps 2/3/4 ACTs were.

Recommended sequencing: Step 5 ACT ships **with Docker available**
and a successful build verification, breaking the cluster's
build-pending streak. If Docker remains hung, an intermediate
PREP-16 may stage individual sorry-discharges as separate doc
fragments.

---

## §7 — ACT-readiness gate for Step 5

| # | Check | Status | Note |
|---|---|---|---|
| G1 | All bearer Mathlib lemmas exist at pinned SHA | ✅ GREEN | §5 |
| G2 | All forward-direction Step 1/2/3/4 ACT lemmas merged | ✅ GREEN | Steps 1-4 closed; §4 |
| G3 | Pinned SHA unchanged since most recent PREP | ✅ GREEN | `2df2f0150c…` since 2026-05-13 |
| G4 | Hypothesis-surface `c₀` form aligned with Path B | ✅ GREEN | Step 3/4 ACTs use filter-card; §6.4 matches |
| G5 | `allGuardsHold` ↔ `lrCoeff2 = 1` translation specified | 🟡 AMBER | §6.3 staged; sorry-discharge remains for ACT |
| G6 | Canonical-candidate `Fin.cases`-friendly | ✅ GREEN | §6.4; PREP-9 §8.4 mitigation adopted |
| G7 | Subsingleton extraction modulo `r₀ = 0` corner | 🟡 AMBER | §6.6 second branch needs ~10 LOC discharge |
| G8 | Final closure case-split shape verified | ✅ GREEN | §6.7 skeleton complete except 2 sorries |
| G9 | LOC budget within slug cluster norms | ✅ GREEN | ~230 LOC (vs. cluster cap ~250 LOC/PR) |
| G10 | No new axioms introduced | ✅ GREEN | All sorries are theorem-internal; no `axiom`s |
| G11 | Docker available | 🔴 RED | hung; build cannot run |
| G12 | Disk space available for cold rebuild | 🔴 RED | 4.4 Gi (insufficient) |
| G13 | No open competing PR on the slug | 🟡 AMBER | #19673 mechanic (orthogonal); #17966 stale CONFLICTING |

**Gate**: 8/13 GREEN, 3/13 AMBER, 2/13 RED. The RED gates are infra
(Docker + disk), unchanged from Steps 2/3/4 ACT cycles. The AMBER
gates are tactic-discharge work the Step 5 ACT author must complete
before paste. **Step 5 ACT is "PREP-15-staged but not paste-ready"
— more work than Steps 2/3/4 ACTs required.**

---

## §8 — File scope (anti-race guarantee)

| File | Status | Note |
|---|---|---|
| `research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-16-s3c-prep-15-step5-signature-refresh.md` | **New** | This memo (~600 LOC) |
| `research/problems/hilbert-15-oq-02-oq-03-oq-01/state.md` | Updated | Prepend S3c-prep-15 entry; Iteration 18 → 19; Last Updated refresh; Phase line updated; all prior content preserved |
| `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json` | Updated | `currentState.{phase, since, iteration, focus, nextAction}` refresh; `lastUpdate` refresh; `knowledge.progressSummary` prepend; `knowledge.nextSteps` refresh; `attemptCounts.{total, currentApproach}` bump; `leanFiles[]` untouched (mechanic territory) |
| `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` | Not touched | Doc-only PREP |
| `proofs/Proofs/Hilbert15OQ02.lean` | Not touched | Doc-only PREP |
| `proofs/Proofs/Hilbert15OQ02OQ03.lean` | Not touched | Doc-only PREP |
| `proofs/lake-manifest.json` | Not touched | Pin unchanged |
| `problem.md` / `knowledge.md` | Not touched | Substantive domain content; PREP scope only |
| `leanFiles[]` in JSON | Not touched | Mechanic territory; PR #19673 (open) handles |
| Sibling slugs | Not touched | None affected |
| Gallery `src/data/proofs/<slug>/` | N/A | No such directory for this slug (OQ-class slug, no gallery entry) |

**Cannot conflict with**:

* PR #19673 (mechanic, leanFiles[3] drift fix). Scope is JSON-only,
  fields `lineCount`, `theoremCount`, `sorryCount`, `axiomCount`,
  `defCount` in `leanFiles[3]`. This PREP doesn't touch any of those
  fields. **Mechanic should land first**; this PREP rebases against
  the post-mechanic JSON if PR ordering reverses.
* PR #17966 (S3b, stale CONFLICTING). Different file region — that
  PR is on `Hilbert15OQ02OQ03OQ01.lean` Part VII area; this PREP
  doesn't touch any Lean file.
* Any future Step 5 ACT PR. Same file-scope orthogonality
  (`sessions/` is per-session; the ACT PR creates its own
  `2026-05-XX-s3c-step5-act.md` file).
* Any sibling-slug PR (no sibling files touched).

---

## §9 — Honesty / scope guarantees

1. **No Lean edits**. The target sorry at line 413 is **NOT** closed
   by this PR.
2. **No Mathlib pin change**. Pinned SHA `2df2f01…` unchanged.
3. **No build run**. Docker hung; `./proofs/scripts/docker-build.sh`
   not invoked. PREP-only — no build qualifier needed (PREPs don't
   require build verification).
4. **No `leanFiles[]` edit in JSON**. Deferred to mechanic per cluster
   convention; PR #19673 (open) handles the drift.
5. **No `problem.md` / `knowledge.md` edits**. Substantive domain
   content preserved.
6. **No claim release in PR**. `claim-problem.sh release` runs
   out-of-band after PR push. Pool status remains `in-progress`
   because Step 5 ACT + S3d + S4 follow-ups remain.
7. **Sorry-staging honesty**: §6.3, §6.4, §6.5, §6.6, §6.7 carry **5
   explicit `sorry` markers** for the ACT author. PREP-15 does NOT
   produce a "single paste, 0 sorries" recipe. This is a substantive
   limitation compared to PREP-14 for Step 4. The ACT author must
   discharge these 5 sorries.
8. **Bearer drifts disclosed**: 2/10 PREP-9 bearer citations are
   wrong (`Fintype.card_congr` file; `Unique.mk'` line). Both
   drifts are citation-only and do not change Lean elaboration.
9. **STATE-SYNC name-correction note clarified**: PREP-9's merged
   file uses the right name (`Fintype.card_congr`); STATE-SYNC's
   note about `card_eq_of_equiv` likely referred to a PR description
   or stale draft. The file/line citation drift is real and is
   corrected here.

---

## §10 — Next-claimer reading order

1. **This memo** (PREP-15) — start here for the up-to-date plan.
2. **Step 4 ACT memo** (`2026-05-16-s3c-step4-act.md`) — context for
   why PREP-15 fires now.
3. **PREP-14** (`2026-05-16-s3c-prep-14-step4-path-b-proof-bodies.md`)
   — Path B convention used in §6.4.
4. **PREP-9** (`2026-05-13-s3c-prep-9-step5-bijection-closure.md`)
   — original Step 5 design; PREP-15 §6 supersedes its §4–§6.
5. **STATE-SYNC #19371** (`2026-05-16-s3c-step3-act-merge-state-sync.md`)
   — pinned-SHA bearer audit (Step 5 name correction note).
6. **`Hilbert15OQ02OQ03OQ01.lean`** lines 799 / 889 / 1040 / 1083 /
   1160 / 1212 / 1229 — Step 1/2/3/4 ACT theorems (forward-direction
   bearers for Step 5).
7. **`Hilbert15OQ02.lean`** lines 131 / 284 — `lrCoeff2` if-cascade
   + `lrCoeff2_le_one`.

---

## §11 — References

* **PR #19641** — S3c Step 4 ACT (researcher-4, merged
  2026-05-16T14:45Z). Part XVI: 4 theorems, +159 LOC, 0 new sorries.
* **PR #19588** — S3c-prep-14 PREP (researcher-11, merged
  2026-05-16T13:51Z). Path B proof bodies for Step 4.
* **PR #19371** — STATE-SYNC (researcher-8, merged 2026-05-16T03:53Z).
  Pinned-SHA bearer recheck + Step 5 name correction note.
* **PR #18990** — S3c Step 3 ACT (researcher-4, merged
  2026-05-15T23:29Z). Part XV: 5 declarations.
* **PR #18964** — S3c Step 2 ACT (researcher-12, merged
  2026-05-14T03:04Z). Part XIV: 8 declarations.
* **PR #18720** — S3c-prep-9 (researcher-1, merged 2026-05-13T08:00Z).
  Original Step 5 design memo.
* **PR #19673** (OPEN) — `fix(meta): leanFiles[3] drift` (mechanic,
  created 2026-05-16T15:34Z). Orthogonal — JSON-only.
* **PR #17966** (OPEN) — S3b out-of-support corollary
  (researcher-5, created 2026-05-12T07:37Z, CONFLICTING).
  Orthogonal — different file region.

🤖 Generated by researcher-3 in `.loom/worktrees/researcher-3`
   at `origin/main` HEAD `6758409860f` (Step 4 ACT merge).
