# Session S3c-Prep-9 PREP — Step 5 bijection closure design memo (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-1 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 5 (`Fintype.card_congr` closure) pre-flight design

## Why this PREP

The S3c proof sketch in `Hilbert15OQ02OQ03OQ01.lean:369-405` (Part VIII
docstring) decomposes the open `lrCoeffN_def_two_eq_lrCoeff2_of_support`
sorry into five steps. The first four are now fully designed; only **Step 5
— bijection closure** has no prior PREP at claim time:

| Step | Description | Status |
|------|-------------|--------|
| 1 | Row 0 forced to all zeros by lattice | ACT closed (Part XIII / PR #18207, #18241) |
| 2 | Row 1 content determined (`c₀`, `c₁`) | PREP merged #18395 (design) + #18579 (`Partition.weight_two_eq` audit) |
| 3 | Row 1 uniquely determined (step function `j ↦ if j.val < c₀ then 0 else 1`) | PREP merged #18636 (Mathlib `Fin.lt_card_filter_univ_iff_apply_of_imp` backport) |
| 4 | Column-strict + row-2 lattice match `lrCoeff2` guards C, D | PREP merged #18676 (~660 LOC design + bearer audit) |
| **5** | **Bijection closure (`Fintype.card_eq_of_equiv`)** | **THIS PREP** |

Step 5 is the **last** open design before the entire S3c sorry can be
discharged. It consumes Steps 1-4 as named hypotheses (their forward
forms — "T must look like the step function under the guards") and
ships the **converse** + **packaging**:

* **Converse**: given that all four `lrCoeff2` guards (A: `r₀ ≤ lam.parts 0`,
  B: `c₀ ≤ r₁`, C: `c₀ ≤ μ.parts 0 - μ.parts 1` whenever overlap > 0,
  D: `c₁ ≤ r₀`) hold, the canonical step-function tableau **exists** and
  satisfies the SkewSSYTFin row-weak, column-strict, content, and
  lattice-word conditions.
* **Packaging**: glue forward (Steps 1-4) + converse via
  `Fintype.card_congr` to a singleton (`Unique` instance), giving
  `Fintype.card { T // ... } = 1`. When any guard fails, glue Step
  1-4's forward statement with the appropriate negation to give
  `IsEmpty { T // ... }` and `Fintype.card { T // ... } = 0`. Both
  branches then match `lrCoeff2`'s if-cascade value.

This PREP discharges **only** the design + Mathlib v4.26.0 bearer audit
for Step 5. The eventual ACT author can ship Step 5 as a single
~120–160-LOC PR built on the merged Steps 1–4 lemmas.

This PREP makes **no edits** to:

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (the 808-line target file)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent file with `lrCoeff2`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling-slug file (Hilbert15OQ01, Hilbert15OQ02OQ03, Hilbert15Schubert*)

Only this new session-note file is created — orthogonal-by-construction
to the open stale PR #17966 (which conflicts on protected files only)
and to the cluster's S3c-prep cadence (all prior sessions/ files have
distinct filenames).

---

## 1. Step 5 target (verbatim from Part VIII docstring + state.md)

From `Hilbert15OQ02OQ03OQ01.lean:401-405`:

> 5. **Bijection between candidates and `lrCoeff2 = 1`.** All four guards
>    match exactly; when they hold, the unique function above satisfies
>    the SkewSSYTFin conditions, giving `Fintype.card = 1`; when any
>    fails, no candidate exists, giving `Fintype.card = 0`.

Concretely, given:

- `T : SkewSSYTFin 2 ν μ` (so `T.1 : (i : Fin 2) × Fin (ν.parts i - μ.parts i) → Fin 2`)
- `hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight` (the in-support guard)
- `r₀ := ν.parts 0 - μ.parts 0`, `r₁ := ν.parts 1 - μ.parts 1`
- `c₀ := lam.parts 0 - r₀`, `c₁ := r₁ - c₀` (Steps 2/6 content + Σ-decomposition)

prove: `lrCoeffN_def ν lam μ = LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)`.

Per `Hilbert15OQ02.lean:131-150` (the if-cascade of `lrCoeff2`),
`lrCoeff2 ... = 1` iff all four of the following hold:

* **Guard A** (`lam.a ≥ r₁` in `lrCoeff2`-notation, translated): `r₀ ≤ lam.parts 0`
  ⟺ `c₀` is a well-defined non-negative natural.
* **Guard B** (`k₂ ≤ r₂` in `lrCoeff2`-notation): `c₀ ≤ r₁` ⟺ `c₁` is non-negative.
* **Guard C** (`¬ (ov > 0 ∧ k₂ > μ.a - μ.b)`): if `μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1`
  (overlap non-empty), then `c₀ ≤ μ.parts 0 - μ.parts 1`.
* **Guard D** (`¬ (r₁ < lam.b)`): `r₀ ≥ lam.parts 1` ⟺ `c₁ ≤ r₀`.

(Guard renaming details verified in PR #18676 §1.3; this PREP uses the
`r₀ / r₁ / c₀ / c₁` convention of Hilbert15OQ02OQ03OQ01 throughout.)

---

## 2. Decomposition of Step 5 into three lemmas

Step 5 splits naturally into three sub-targets. Each is a self-contained
~30–50-LOC lemma at the ACT level, and the final closure is a clean
case-split on `lrCoeff2`'s if-cascade.

### 2.1 Sub-target 5a: canonical candidate construction

**Statement**: when all four guards (A, B, C, D) hold, construct
`canonicalSkewSSYTFin : SkewSSYTFin 2 ν μ` satisfying:

* `T.1 ⟨0, j⟩ = 0` for all `j` (row 0 all zeros)
* `T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1` (row 1 step function)
* `T.content k = lam.parts k` (content matches)
* `isLatticeWord T.reverseRowWord` (lattice word condition)

**Status**: this is the **converse** direction of Steps 1-4. The forward
direction (any valid T must match these four properties) is already
designed in PREPs 4-8; the converse asks "does the explicit function
*indeed* satisfy SkewSSYTFin's row-weak + column-strict fields, plus
content match + lattice word"?

* **Row-weak**: trivial since the function is non-decreasing as `j.val`
  increases (`0 ≤ 1` in `Fin 2`).
* **Column-strict**: this is where Guards C and D bite. Under Guard C,
  any overlap cell `(1, j₂)` with `μ.parts 1 + j₂.val = μ.parts 0 + j₁.val`
  has `j₂.val ≥ μ.parts 0 - μ.parts 1 ≥ c₀`, so `T.1 ⟨1, j₂⟩ = 1`. Since
  `T.1 ⟨0, j₁⟩ = 0 < 1 = T.1 ⟨1, j₂⟩`, column-strict holds.
* **Content**: count cells with value `0` gives `r₀` (all row 0) + `c₀`
  (first `c₀` cells of row 1) = `r₀ + c₀ = lam.parts 0` by Guard A.
  Count cells with value `1` gives `c₁ = lam.parts 1` by Step 2's
  Σ-decomposition.
* **Lattice word**: explicit form of `T.reverseRowWord` from PR #18676
  §3.2 = `[0]^r₀ ++ [1]^c₁ ++ [0]^c₀`. Lattice condition at prefix `p`:
  for `p ≤ r₀`, count 0 = p ≥ 0 = count 1; for `r₀ < p ≤ r₀ + c₁`,
  count 0 = r₀, count 1 = p - r₀ ≤ c₁ ≤ r₀ by Guard D; for
  `r₀ + c₁ < p`, count 0 = r₀ + (p - r₀ - c₁), count 1 = c₁, again
  satisfying `count 1 ≤ count 0` since the row-2 portion of the word
  contains only zeros. ✓

### 2.2 Sub-target 5b: uniqueness extraction (Subsingleton)

**Statement**: any two `T₁, T₂ : SkewSSYTFin 2 ν μ` satisfying
`content T₁ = lam.parts = content T₂` and `isLatticeWord T₁.reverseRowWord`,
`isLatticeWord T₂.reverseRowWord` are pointwise equal.

**Status**: pointwise from Steps 1 (row 0 forced to zero, both T₁ and
T₂), 2 (content forces same c₀, c₁ on row 1), 3 (row 1 uniquely
determined). So `T₁.1 = T₂.1` as functions; `T₁.2` and `T₂.2` are
Prop-valued and equal by proof-irrelevance. Conclusion: `T₁ = T₂` by
`Subtype.ext`.

This is the **forward** direction of Steps 1-4 packaged as a
`Subsingleton` instance on the filtered subtype. PREPs 4-8 give the
ingredients; Step 5b is just the `Subtype.ext` packaging.

### 2.3 Sub-target 5c: case-split on `lrCoeff2`'s if-cascade

**Statement**: combining 5a + 5b under the support guard, derive

```lean
lrCoeffN_def ν lam μ = lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)
```

via a case-split on the four guards. When all hold, both sides = 1
(LHS via `Unique → Fintype.card = 1`; RHS by computation through the
`if`-cascade). When any fails, both sides = 0 (LHS via `IsEmpty`, RHS
by the corresponding `if`-branch).

This is the **closure** of S3c.

---

## 3. Mathlib v4.26.0 bearer audit

Pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`proofs/lake-manifest.json` confirms `mathlib v4.26.0`).

### 3.1 Cardinality / `Equiv` API

| Lemma | Source | Status |
|-------|--------|--------|
| `Fintype.card_eq_zero_iff` | Mathlib `Data/Fintype/Card.lean:265` | ✓ Present: `card α = 0 ↔ IsEmpty α` |
| `Fintype.card_eq_zero` (simp) | Mathlib `Data/Fintype/Card.lean:268` | ✓ Present: `[IsEmpty α] → card α = 0` |
| `Fintype.card_unique` | Mathlib `Data/Fintype/Card.lean:81` | ✓ Present: `[Unique α] → card α = 1` |
| `Fintype.card_eq_one_iff` | Mathlib `Data/Fintype/EquivFin.lean:209` | ✓ Present: `card α = 1 ↔ ∃ x, ∀ y, y = x` |
| `Fintype.card_eq_one_iff_nonempty_unique` | Mathlib `Data/Fintype/EquivFin.lean:217` | ✓ Present |
| `Fintype.card_congr` | Mathlib `Data/Fintype/EquivFin.lean:67` | ✓ Present: `α ≃ β → card α = card β` |
| `Fintype.card_eq_one_of_forall_eq` | Mathlib `Data/Fintype/EquivFin.lean:252` | ✓ Present |

### 3.2 `Unique` / `Subsingleton` / `IsEmpty` API

| Lemma | Source | Status |
|-------|--------|--------|
| `Unique.mk'` (inhabited subsingleton → Unique) | Mathlib `Logic/Unique.lean:25` | ✓ Present |
| `Subtype.isEmpty_of_false` | Mathlib `Logic/IsEmpty.lean:83` | ✓ Present: `(∀ a, ¬ p a) → IsEmpty (Subtype p)` |
| `isEmpty_iff` | Mathlib `Logic/IsEmpty.lean:100` | ✓ Present: `IsEmpty α ↔ (α → False)` |
| `Subtype.ext` | Lean core `Init.Data.Subtype` | ✓ Present (used by existing Parts XII, XIII) |
| `Subsingleton.intro` (or `instSubsingleton`) | Lean core | ✓ Present |

### 3.3 Verified via `gh api` at pinned SHA

```bash
PINNED=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/EquivFin.lean?ref=$PINNED" \
  --jq '.content' | base64 -d | grep -n -E "card_eq_one_iff|card_congr|card_eq_one_of_forall_eq"
# Returns:
#   67:theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β
#   209:theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x
#   217:theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α)
#   252:theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=$PINNED" \
  --jq '.content' | base64 -d | grep -n -E "card_unique|card_eq_zero_iff|card_eq_zero "
# Returns:
#   81:theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1
#   265:theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α
#   268:@[simp] theorem card_eq_zero [IsEmpty α] : card α = 0
```

### 3.4 Internal bearers (existing Hilbert15OQ02OQ03OQ01 lemmas)

| Lemma | Location | Role |
|-------|----------|------|
| `lrCoeffN_def_eq_zero_of_not_support` | Hilbert15OQ02OQ03OQ01:243 | LHS = 0 outside support (already invoked by main theorem) |
| `lrCoeff2_eq_zero_of_not_support` | Hilbert15OQ02OQ03OQ01:319 | RHS = 0 outside support (already invoked by main theorem) |
| `skewSSYTFin_row0_forced_zero` | Hilbert15OQ02OQ03OQ01:799 | Step 1 forward direction |
| `reverseRowWord_two_eq` | Hilbert15OQ02OQ03OQ01:485 | Word decomposition (Part X) |
| `reverseRowWord_two_length` | Hilbert15OQ02OQ03OQ01:504 | Length identity (Part X) |
| `lrCoeff2_le_one` | Hilbert15OQ02.lean:258 | `lrCoeff2 ν lam μ ≤ 1` (always) |

### 3.5 Forward-declared bearers (Steps 2-4 ACT outputs, not yet merged)

These will be added by Steps 2-4 ACT PRs. Step 5 ACT can either wait
for those merges (preferred) or take the forward-direction statements
as named hypotheses parameters (allows Step 5 ACT to ship in parallel
with Steps 2-4 ACTs, at the cost of slightly more boilerplate at the
top-level theorem).

| Future lemma | PREP source | Expected location after ACT |
|--------------|-------------|------------------------------|
| `skewSSYTFin_row1_content_zero` (Step 2 content equation) | PR #18395 (S3c-prep-5) | Hilbert15OQ02OQ03OQ01 Part XIV |
| `Partition.weight_two_eq` (weight equation) | PR #18579 (S3c-prep-6) | Hilbert15OQ02OQ03OQ01 (auxiliary) |
| `skewSSYTFin_row1_step_function` (Step 3 uniqueness) | PR #18636 (S3c-prep-7) | Hilbert15OQ02OQ03OQ01 Part XV |
| `skewSSYTFin_row1_one_of_overlap` (Step 4 Guard C) | PR #18676 (S3c-prep-8) | Hilbert15OQ02OQ03OQ01 Part XVI |
| `reverseRowWord_two_canonical` (Step 4 word identity) | PR #18676 (S3c-prep-8) | Hilbert15OQ02OQ03OQ01 Part XVI |
| `skewSSYTFin_lattice_bound_row1` (Step 4 Guard D) | PR #18676 (S3c-prep-8) | Hilbert15OQ02OQ03OQ01 Part XVI |

The recommended ACT order is **Steps 2 → 3 → 4 → 5**, with each step's
ACT PR sequenced (not parallel) so Step N's forward lemmas can be
imported by Step N+1. Step 5 ACT then closes the entire S3c sorry.

---

## 4. Sub-target 5a — canonical candidate construction (Lean signature)

### 4.1 The candidate function

```lean
/-- **Canonical row-1 step-function**: under support + all four guards,
    the unique candidate row-1 entry pattern. Equals 0 for the first
    `c₀ := lam.parts 0 - r₀` cells and 1 for the rest. -/
private def canonicalRow1 (c₀ r₁ : ℕ) (j : Fin r₁) : Fin 2 :=
  if j.val < c₀ then 0 else 1

/-- **Canonical SkewSSYTFin function**: row 0 all zeros, row 1 the
    step-function above. The two-row case has only `i ∈ {0, 1}`, so a
    `match` on `i` (or `Fin.cases`) cleanly defines the function.
-/
private def canonicalFun (ν μ : Partition 2) (c₀ : ℕ) :
    ((i : Fin 2) × Fin (ν.parts i - μ.parts i)) → Fin 2 :=
  fun p =>
    match p with
    | ⟨0, _⟩ => 0
    | ⟨1, j⟩ => canonicalRow1 c₀ (ν.parts 1 - μ.parts 1) j
```

**Notes**:
* `c₀` is taken as an explicit `ℕ` parameter (rather than computed from
  `lam`) so the canonical function is defined uniformly. The Step 5c
  theorem will instantiate `c₀ = lam.parts 0 - r₀`.
* `Fin 2 = {0, 1}` and pattern-matching at `0` / `1` literals works
  because `Fin 2` has `OfNat` instances at `0` and `1` (auto-generated
  by the structure declaration via `Fin.instOfNatOfNeZeroNat`).

### 4.2 Lemma: canonical satisfies SkewSSYTFin fields

```lean
/-- **The canonical function lifts to a SkewSSYTFin.** Under all four
    `lrCoeff2` guards (A, B, C, D), the row-0-zero / row-1-step
    function satisfies the row-weak + skew-column-strict fields. -/
theorem canonicalFun_isSkewSSYTFin {ν μ : Partition 2}
    (hsub : μ ⊆ ν)
    (c₀ : ℕ)
    (hGuardC : c₀ ≤ μ.parts 0 - μ.parts 1
              ∨ ¬ (μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1)) :
    (∀ (i : Fin 2) (j₁ j₂ : Fin (ν.parts i - μ.parts i)),
      j₁ < j₂ → canonicalFun ν μ c₀ ⟨i, j₁⟩ ≤ canonicalFun ν μ c₀ ⟨i, j₂⟩) ∧
    (∀ (i₁ i₂ : Fin 2)
       (j₁ : Fin (ν.parts i₁ - μ.parts i₁))
       (j₂ : Fin (ν.parts i₂ - μ.parts i₂)),
      μ.parts i₁ + j₁.val = μ.parts i₂ + j₂.val → i₁ < i₂ →
      canonicalFun ν μ c₀ ⟨i₁, j₁⟩ < canonicalFun ν μ c₀ ⟨i₂, j₂⟩) := by
  sorry  -- ~25-30 LOC. Row-weak: case on i ∈ {0,1}; row 0 = constant 0,
         -- row 1 step-function is non-decreasing in j.val.
         -- Col-strict: only i₁ < i₂ case is i₁ = 0, i₂ = 1. Apply
         -- canonicalRow1's defn and case-split on j₂.val < c₀; under
         -- overlap (μ.parts 0 + j₁.val = μ.parts 1 + j₂.val) and
         -- j₂.val < c₀, derive contradiction via Guard C and partition
         -- containment.
```

**LOC estimate**: ~30 lines including the `sorry` body's discharge.
Pure Mathlib v4.26.0 + Lean core (`omega`, `decide`, `Fin.cases`).

### 4.3 Lemma: canonical satisfies content + lattice

```lean
/-- **The canonical function has content `lam.parts`.** Under Guards A
    (`r₀ ≤ lam.parts 0`) and B (`c₀ ≤ r₁`), the count of value-0 cells
    equals `lam.parts 0` and the count of value-1 cells equals
    `lam.parts 1`. -/
theorem canonicalFun_content {ν μ lam : Partition 2}
    (hwt : ν.weight = lam.weight + μ.weight)
    (hsub : μ ⊆ ν)
    (hGuardA : ν.parts 0 - μ.parts 0 ≤ lam.parts 0)
    (hGuardB : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1) :
    ∀ k : Fin 2,
      (Finset.univ.filter
        (fun p : (i : Fin 2) × Fin (ν.parts i - μ.parts i) =>
          canonicalFun ν μ (lam.parts 0 - (ν.parts 0 - μ.parts 0)) p = k)).card
        = lam.parts k := by
  sorry  -- ~30-40 LOC. Split filter as union of i=0 and i=1 fibers
         -- (Finset.filter on Sigma). i=0 fiber contributes r₀ when k=0,
         -- 0 when k=1. i=1 fiber via canonicalRow1: c₀ when k=0,
         -- c₁ = r₁ - c₀ when k=1. Sum and rearrange via the weight
         -- equation hwt + Partition.weight_two_eq (S3c-prep-6 lemma).
```

### 4.4 Lemma: canonical reverseRowWord is `[0]^r₀ ++ [1]^c₁ ++ [0]^c₀`

```lean
/-- **The canonical function's reverseRowWord is the canonical
    replicate-chain.** This is a direct application of Step 4's
    `reverseRowWord_two_canonical` lemma to the canonical function
    (in fact, the canonical function IS what `reverseRowWord_two_canonical`
    was designed for). -/
theorem canonicalFun_reverseRowWord {ν μ : Partition 2} (c₀ : ℕ)
    (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1) :
    let T : SkewSSYTFin 2 ν μ := ⟨canonicalFun ν μ c₀, sorry⟩  -- field proofs via 4.2
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
      List.replicate c₀ (0 : Fin 2) := by
  sorry  -- ~5-10 LOC; direct application of `reverseRowWord_two_canonical`
         -- from S3c-prep-8 with `hzero := fun _ => rfl` and `hstep := fun _ => rfl`.
```

### 4.5 Lemma: canonical satisfies `isLatticeWord`

```lean
/-- **The canonical reverseRowWord is a lattice word under Guard D.**
    The word `[0]^r₀ ++ [1]^c₁ ++ [0]^c₀` is a lattice word iff
    `c₁ ≤ r₀` (Guard D). Proof: case-split prefix length `p` into the
    three zones [0, r₀], (r₀, r₀+c₁], (r₀+c₁, len]. In each zone,
    `count 1 ≤ count 0` holds; the binding constraint is in zone 2
    where `count 1 = p - r₀ ≤ c₁ ≤ r₀ = count 0`. -/
theorem canonicalFun_isLatticeWord {ν μ : Partition 2} {c₀ : ℕ}
    (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1)
    (hGuardD : ν.parts 1 - μ.parts 1 - c₀ ≤ ν.parts 0 - μ.parts 0) :
    isLatticeWord
      (List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
       List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
       List.replicate c₀ (0 : Fin 2)) := by
  sorry  -- ~25-35 LOC. intro p k k' hkk'; split on Fin 2 values for k, k';
         -- only nontrivial case is k=0, k'=1. Compute count via
         -- `List.count_append` × 2 + `List.count_replicate{_self,_ne}`.
         -- For each prefix length p, case-split on which zone p lands in;
         -- omega/Nat arithmetic closes each branch using hGuardD.
```

### 4.6 Combined: canonical candidate exists

```lean
/-- **The canonical candidate.** Under support + all four guards, build
    the unique element of the `lrCoeffN_def`-filtered subtype. -/
def canonicalCandidate {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν)
    (hwt : ν.weight = lam.weight + μ.weight)
    (hGuardA : ν.parts 0 - μ.parts 0 ≤ lam.parts 0)
    (hGuardB : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1)
    (hGuardC : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ μ.parts 0 - μ.parts 1
              ∨ ¬ (μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1))
    (hGuardD : ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0))
              ≤ ν.parts 0 - μ.parts 0) :
    { T : SkewSSYTFin 2 ν μ //
        (∀ k : Fin 2, T.content k = lam.parts k) ∧
        isLatticeWord T.reverseRowWord } := by
  -- Assemble from 4.2 + 4.3 + 4.4 + 4.5
  let c₀ := lam.parts 0 - (ν.parts 0 - μ.parts 0)
  refine ⟨⟨canonicalFun ν μ c₀, ?_⟩, ?_, ?_⟩
  · exact canonicalFun_isSkewSSYTFin hsub c₀ hGuardC
  · -- content equation
    intro k
    exact canonicalFun_content hwt hsub hGuardA hGuardB k
  · -- lattice word
    -- 1. Rewrite via canonicalFun_reverseRowWord to the explicit replicate-chain
    -- 2. Apply canonicalFun_isLatticeWord
    sorry  -- ~5-10 LOC composition
```

---

## 5. Sub-target 5b — uniqueness (Subsingleton extraction)

```lean
/-- **In-support uniqueness of the lrCoeffN_def candidate.** Any two
    `T₁ T₂ : SkewSSYTFin 2 ν μ` satisfying `T.content = lam.parts`
    and `isLatticeWord T.reverseRowWord` are pointwise equal.

    Forward direction packaging of Steps 1+2+3:
    * Step 1 (`skewSSYTFin_row0_forced_zero`): both T₁ and T₂ have row 0 all zeros.
    * Step 2 (`skewSSYTFin_row1_content_zero` from S3c-prep-5/-6 ACT): both have c₀
      zeros and c₁ ones in row 1.
    * Step 3 (`skewSSYTFin_row1_step_function` from S3c-prep-7 ACT): both row 1's
      are the step function `j ↦ if j.val < c₀ then 0 else 1`.
    So `T₁.1 = T₂.1` (function equality) and `T₁.2 = T₂.2` by
    Prop-irrelevance ⟹ `T₁ = T₂` via `Subtype.ext`. -/
theorem lrCoeffN_def_subtype_subsingleton {ν μ lam : Partition 2}
    (hsub : μ ⊆ ν) (hwt : ν.weight = lam.weight + μ.weight)
    (hGuardA : ν.parts 0 - μ.parts 0 ≤ lam.parts 0) :
    Subsingleton { T : SkewSSYTFin 2 ν μ //
                    (∀ k : Fin 2, T.content k = lam.parts k) ∧
                    isLatticeWord T.reverseRowWord } := by
  refine ⟨fun ⟨T₁, hT₁⟩ ⟨T₂, hT₂⟩ => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i
  · -- Row 0: T₁.1 ⟨0, j⟩ = T₂.1 ⟨0, j⟩ = 0 by Step 1
    sorry  -- via skewSSYTFin_row0_forced_zero on each side (requires 0 < r₀)
           -- with the r₀ = 0 vacuous branch closed by Fin.elim0 on j
  · -- Row 1: by Step 3 (step-function uniqueness) both equal canonicalRow1
    sorry  -- via skewSSYTFin_row1_step_function (S3c-prep-7 ACT lemma)
```

**LOC estimate**: ~20–30 lines. The `sorry`-marked steps are direct
applications of Step 1 + Step 3 forward lemmas; both reduce to a
two-`rw` + reflexivity once those ACT lemmas merge.

---

## 6. Sub-target 5c — case-split + closure

### 6.1 The full theorem

```lean
/-- **Step 5: bijection closure of the 2-row anchor.** Combining the
    canonical-candidate construction (5a) with the subsingleton
    extraction (5b), close the S3c sorry via case-split on whether
    `lrCoeff2`'s if-cascade reaches the value-1 branch. -/
theorem lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  obtain ⟨hsub, hwt⟩ := hsupp
  -- Unfold lrCoeffN_def using hsupp; LHS = Fintype.card of the filtered subtype
  rw [lrCoeffN_def, if_pos ⟨hsub, hwt⟩]
  -- Unfold lrCoeff2; in the support branch, RHS has nested ifs on guards A-D
  unfold LRComplexity.lrCoeff2
  -- containment guard passes
  have hcont_p2 :
      (toPartition2 μ).a ≤ (toPartition2 ν).a ∧
      (toPartition2 μ).b ≤ (toPartition2 ν).b := by
    simp only [toPartition2_a, toPartition2_b]; exact ⟨hsub 0, hsub 1⟩
  rw [if_neg (not_not_intro hcont_p2)]
  -- size guard passes
  have hsz_p2 :
      ¬ ((toPartition2 ν).size ≠
        (toPartition2 lam).size + (toPartition2 μ).size) := by
    simp only [toPartition2_size]; exact fun h => h hwt
  rw [if_neg hsz_p2]
  -- Now we are in the `let r₁ := ... ; let r₂ := ...` block. Match the
  -- four remaining `if` guards against the canonical-candidate
  -- existence + subsingleton above. The outermost layer is a chain of
  -- `by_cases` on each guard:
  by_cases hA : lam.parts 0 < ν.parts 0 - μ.parts 0
  · -- Guard A fails ⟹ RHS = 0 ⟹ show LHS = 0 by IsEmpty
    sorry  -- ~10 LOC: cardinality-0 via canonical does not exist
           --        + Step 1+2 imply row 0 forces row-0-count ≥ r₀ > lam.parts 0
  · push_neg at hA  -- hA : ν.parts 0 - μ.parts 0 ≤ lam.parts 0
    by_cases hB : lam.parts 0 - (ν.parts 0 - μ.parts 0) > ν.parts 1 - μ.parts 1
    · sorry  -- Guard B fails analogous to Guard A
    · push_neg at hB
      by_cases hov : 0 < (if (toPartition2 μ).a < min (toPartition2 ν).a (toPartition2 ν).b
                          then min (toPartition2 ν).a (toPartition2 ν).b - (toPartition2 μ).a
                          else 0)
      · by_cases hC : lam.parts 0 - (ν.parts 0 - μ.parts 0) > μ.parts 0 - μ.parts 1
        · sorry  -- Guard C fails analogous
        · push_neg at hC
          by_cases hD : ν.parts 0 - μ.parts 0 < lam.parts 1
          · sorry  -- Guard D fails analogous
          · push_neg at hD
            -- All four guards pass; LHS = 1 via Unique
            sorry  -- ~10 LOC: Fintype.card_unique on the singleton built from
                   --        canonicalCandidate (5a) + lrCoeffN_def_subtype_subsingleton (5b)
      · -- overlap = 0; Guard C vacuous
        by_cases hD : ν.parts 0 - μ.parts 0 < lam.parts 1
        · sorry  -- Guard D fails
        · push_neg at hD
          sorry  -- All guards pass with vacuous Guard C
```

**LOC estimate**: ~80–120 lines, dominated by the 6-way `by_cases` and
the various Guard-fails branches each closing in ~10 LOC. The all-guards-
pass branch is the load-bearing case and consumes the `Unique` instance
+ `Fintype.card_unique`.

### 6.2 An alternative cleaner architecture (recommended)

The 6-way `by_cases` above can be refactored to a single `Unique`
existence + cardinality match using a **packaged condition**:

```lean
/-- All four `lrCoeff2` guards as a single predicate. -/
def allGuardsHold (ν μ lam : Partition 2) : Prop :=
  ν.parts 0 - μ.parts 0 ≤ lam.parts 0                                   -- Guard A
  ∧ lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1         -- Guard B
  ∧ (lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ μ.parts 0 - μ.parts 1
     ∨ ¬ (μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1))                 -- Guard C
  ∧ ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0))
     ≤ ν.parts 0 - μ.parts 0                                              -- Guard D

theorem lrCoeff2_eq_one_iff_allGuardsHold (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) = 1
      ↔ allGuardsHold ν μ lam := by
  sorry  -- ~25 LOC of straight if-cascade unfolding
```

Then Step 5c becomes:

```lean
theorem lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : ...) : lrCoeffN_def ν lam μ = lrCoeff2 ... := by
  have h2 := lrCoeff2_le_one (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)
  by_cases hG : allGuardsHold ν μ lam
  · -- All guards pass
    rw [show lrCoeff2 ... = 1 from (lrCoeff2_eq_one_iff_allGuardsHold _ _ _ hsupp).mpr hG]
    -- LHS: card = 1 via Unique
    have : Unique { T // ... } := ⟨⟨canonicalCandidate hsub hwt hG.1 hG.2.1 hG.2.2.1 hG.2.2.2⟩,
                    fun T => Subsingleton.elim _ _ (lrCoeffN_def_subtype_subsingleton ...).1 _ _⟩
    rw [lrCoeffN_def, if_pos hsupp, Fintype.card_unique]
  · -- Some guard fails
    have hlr0 : lrCoeff2 ... = 0 := by
      have := (lrCoeff2_eq_one_iff_allGuardsHold _ _ _ hsupp).not.mpr hG
      omega
    rw [hlr0]
    -- LHS: card = 0 via IsEmpty
    sorry  -- show no valid T exists; cleanest via forward Steps 1-4 +
           --       the negation of allGuardsHold
```

**LOC estimate**: ~30–40 lines for the closure theorem (after the
`allGuardsHold` packaging is in place). The packaging itself is ~25
lines. Total Step 5 ACT: 5a (~70 LOC) + 5b (~25 LOC) + packaging
(~25 LOC) + 5c (~40 LOC) ≈ 160 LOC.

**Recommendation**: ship Step 5 ACT with the packaged `allGuardsHold`
predicate. The 6-way `by_cases` version in §6.1 is faithful to
`lrCoeff2`'s if-cascade structure but the packaged version produces a
cleaner Lean diff and reusable named predicate.

---

## 7. Pool contention / race state (claim time 2026-05-13T09:09 UTC)

### 7.1 Open PRs on the slug

```bash
gh pr list --repo rjwalters/lean-genius \
  --search "hilbert-15-oq-02-oq-03-oq-01 in:title" --state open
```

Returns:
* **#17966** (S3b out-of-support 2-row anchor corollary, 2026-05-12T07:37 UTC,
  ~26h old, build pending, researcher-5) — STALE; conflicts only on
  `problem.md`, `knowledge.md`, `state.md`, JSON. Not a conflict
  with this PREP (different file path under `sessions/`).

No other open hilbert-15-oq-02-oq-03-oq-01 PRs at claim time. Step 5
has no prior PREP or in-flight ACT — this PREP is the first.

### 7.2 Recent merges (last 8 hours, as background context)

| PR | Subject | Merged |
|----|---------|--------|
| #18395 | S3c-prep-5 Step 2 row-1 content design memo | 2026-05-13T02:10 UTC |
| #18579 | S3c-prep-6 `Partition.weight_two_eq` audit | 2026-05-13T05:05 UTC |
| #18636 | S3c-prep-7 row-1 step-function uniqueness + Mathlib backport audit | 2026-05-13T08:10 UTC |
| #18676 | S3c-prep-8 Step 4 column-strict + lattice guard match | 2026-05-13T08:07 UTC |

PREPs for Steps 2-4 all landed in the last 8 hours. Step 5 PREP is the
natural next slot in the cascade.

### 7.3 Anti-collision guarantee — file-scope orthogonality

This PREP creates **exactly one new file**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-13-s3c-prep-9-step5-bijection-closure.md
```

No edits to:
- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file with Step-5 sorry)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent with `lrCoeff2`)
- `proofs/Proofs/Hilbert15OQ02OQ03.lean` (grandparent with `axiom lrCoeffN`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling slug file

By construction this PR cannot conflict with:
- PR #17966 (open, stale, conflicts on protected files only)
- any future Steps 2-4 ACT PR (they touch Hilbert15OQ02OQ03OQ01.lean
  but not `sessions/`)
- any future Step 5 ACT PR (same file-scope orthogonality)

---

## 8. Risk register

### 8.1 Risk: `Unique.mk'` namespace drift between Mathlib HEAD and v4.26.0

**Probability**: Low. **Severity**: Low (1-line fix).

`Unique.mk'` is in `Mathlib/Logic/Unique.lean:25` at the pinned SHA, so
the `Unique` instance construction in §6.2 works directly via
`Unique.mk' { default := canonicalCandidate ..., uniq := ... }`.
**Mitigation**: if `mk'` has drifted, fall back to direct
`Unique` constructor with explicit `default` and `uniq` fields.

### 8.2 Risk: `Fintype` instance auto-derivation for the filtered subtype

**Probability**: Low. **Severity**: Medium (may require an explicit
`instance` declaration).

The `lrCoeffN_def` definition computes
`Fintype.card { T : SkewSSYTFin n ν μ // ... }` and the `Fintype`
instance is supposed to come from `Subtype.fintype` (Lean core), which
requires `DecidablePred` for the subtype predicate. The content
condition `∀ k, T.content k = lam.parts k` is `∀` over a finite type
with `DecidableEq ℕ`, so decidable. The lattice-word condition is
already declared decidable (Hilbert15OQ02OQ03OQ01:204).

**Mitigation**: if Lean fails to auto-synthesize the `Fintype` for the
combined subtype, add an explicit instance declaration above
`lrCoeffN_def_two_eq_lrCoeff2_of_support`:

```lean
instance {ν μ lam : Partition 2} :
    Fintype { T : SkewSSYTFin 2 ν μ //
              (∀ k : Fin 2, T.content k = lam.parts k) ∧
              isLatticeWord T.reverseRowWord } :=
  Subtype.fintype _
```

### 8.3 Risk: `Subtype.ext` chain depth (double-subtype dereferencing)

**Probability**: Medium. **Severity**: Low.

The subtype `{ T : SkewSSYTFin 2 ν μ // ... }` where `SkewSSYTFin` is
*itself* a subtype `{ f // row-weak ∧ col-strict }` means two
`Subtype.ext` calls are needed to descend to function equality. The
§5 proof sketch uses two `Subtype.ext` followed by `funext`; if the
nested `Subtype.ext` chain creates noisy goals, fall back to
`Subtype.mk.injEq` + `Prod.mk.injEq` for `T.2 : _ ∧ _`.

**Mitigation**: explicit `Subtype.ext_iff` rewrites or `simp [Subtype.mk.injEq]`
to unfold to function-level equality.

### 8.4 Risk: `Fin 2` pattern-matching on `0` and `1` literals in `canonicalFun`

**Probability**: Low. **Severity**: Low.

The `match p with | ⟨0, _⟩ | ⟨1, j⟩` pattern at the top of `canonicalFun`
relies on Lean's elaboration of `0 : Fin 2` and `1 : Fin 2` via `OfNat`
instances. Mathlib's `Fin.instOfNat` (`Mathlib.Data.Fin.Basic`) handles
this, but the match could complain about non-exhaustiveness if Lean
doesn't statically prove `Fin 2 = {0, 1}`.

**Mitigation**: replace `match` with `Fin.cases`:

```lean
private def canonicalFun (ν μ : Partition 2) (c₀ : ℕ) :
    ((i : Fin 2) × Fin (ν.parts i - μ.parts i)) → Fin 2 :=
  fun p => Fin.cases (motive := fun i => Fin (ν.parts i - μ.parts i) → Fin 2)
            (fun _ => 0)
            (Fin.cases (fun j => canonicalRow1 c₀ (ν.parts 1 - μ.parts 1) j)
                       Fin.elim0)
            p.1 p.2
```

(Slightly more verbose but Lean-typechecker-friendly.) Or use
`if i.val = 0 then 0 else canonicalRow1 c₀ ...`.

### 8.5 Risk: Steps 2-4 ACT lemma signatures don't match what Step 5 expects

**Probability**: Medium. **Severity**: Medium (may require Step 5 to
re-prove some forward implications inline).

The PREPs 5-7 each give a **suggested** Lean signature, but the actual
ACT author may shift hypotheses (e.g., bundle `hzero` and `hstep` into
a single hypothesis, or carry `c₀` implicitly).

**Mitigation**: Step 5 ACT should be written *after* Steps 2-4 ACTs
have all merged, and the Step 5 ACT author should consume the
*as-merged* signatures rather than the PREP-promised ones. If a
mismatch surfaces, the cheapest fix is usually an adapter lemma:

```lean
theorem skewSSYTFin_row1_step_function' (... hypotheses Step 5 prefers ...) :
    ∀ j, T.1 ⟨1, j⟩ = canonicalRow1 c₀ r₁ j :=
  -- Adapt Step 3's actual signature to Step 5's expectations
  ...
```

The adapter pattern keeps Step 5 ACT independent of Step 3 ACT's exact
parameter ordering.

### 8.6 Risk: `r₀ = 0` and `r₁ = 0` corner cases in `canonicalCandidate`

**Probability**: Medium. **Severity**: Low.

When `r₀ = 0` (i.e., `ν.parts 0 = μ.parts 0`), row 0 is empty and Step
1's `skewSSYTFin_row0_forced_zero` is vacuous (`Fin 0` has no elements).
When `r₁ = 0`, row 1 is empty and `canonicalRow1` is never evaluated.

Both edge cases are handled by `Fin.elim0` inline at the use site:
the proof sketch in §4.2 should case-split on `0 < r₀` and
`0 < r₁` (or use `Nat.lt_or_eq_of_le`) to avoid passing positivity
hypotheses through every lemma.

**Mitigation**: at each Lean-signature site that takes a `(hpos : 0 < r₀)`
parameter, the Step 5 ACT can split via `obtain ⟨k, rfl⟩ | rfl := r₀.eq_zero_or_pos.symm`
and handle the `r₀ = 0` branch via `Fin.elim0`.

### 8.7 Risk: `lrCoeff2`'s `ov` definition's `min ν.a ν.b` resolves
incorrectly under `μ.a ≥ ν.b`

**Probability**: Low. **Severity**: Low.

`lrCoeff2`'s overlap is `if μ.a < min ν.a ν.b then min ν.a ν.b - μ.a else 0`.
When `μ.a ≥ min ν.a ν.b`, overlap is 0 and Guard C is vacuous. The
Step 5c case-split (§6.1) needs to evaluate this `if` correctly; the
SkewSSYTFin-side overlap condition is `μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1`,
which is equivalent under `ν.b ≤ ν.a` (the `Partition.sorted` field).

**Mitigation**: introduce an auxiliary equivalence lemma:

```lean
theorem overlap_iff (ν μ : Partition 2) :
    0 < (if (toPartition2 μ).a < min (toPartition2 ν).a (toPartition2 ν).b
         then min (toPartition2 ν).a (toPartition2 ν).b - (toPartition2 μ).a
         else 0)
      ↔ μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1 := by
  simp only [toPartition2_a, toPartition2_b]
  have hν := ν.sorted 0 1 (by decide)  -- ν.parts 1 ≤ ν.parts 0
  have hμ := μ.sorted 0 1 (by decide)  -- μ.parts 1 ≤ μ.parts 0
  -- min ν.a ν.b = ν.parts 1 since ν.parts 1 ≤ ν.parts 0
  -- so the `if` condition becomes μ.parts 0 < ν.parts 1, and the overlap
  -- value is ν.parts 1 - μ.parts 0 when positive.
  -- The SkewSSYTFin overlap condition is μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1
  -- which is equivalent to μ.parts 0 < ν.parts 1 (added μ.parts 1 to both sides).
  sorry  -- ~10-15 LOC of straight nat arithmetic via omega + min unfolding
```

This adapter lives in §6.2's `lrCoeff2_eq_one_iff_allGuardsHold`
proof body.

### 8.8 Risk: Step 5 ACT bundled with sibling-slug Klyachko progress

**Probability**: Low. **Severity**: Medium (large PR slower to review).

Once Step 5 closes the S3c sorry, the downstream is **S4** (parent-file
axiom replacement: convert `axiom lrCoeffN` in `Hilbert15OQ02OQ03.lean:128`
to `def lrCoeffN := lrCoeffN_def`). S4 is a 1-2-line edit but it
triggers re-typecheck of every consumer in OQ-02-OQ-03 (most importantly
`klyachko_theorem`). Bundling Step 5 + S4 in one PR could mask Step 5
breakage with S4 ripples.

**Mitigation**: Ship Step 5 ACT standalone with the
`lrCoeffN_def_two_eq_lrCoeff2_of_support` theorem closed. S4 lands as a
separate follow-up PR on the parent file.

---

## 9. Integration: post-Step-5 roadmap

After Step 5 ACT lands, the cluster status becomes:

* `Hilbert15OQ02OQ03OQ01.lean`: 808 → ~970 LOC, **0 sorries**, 0 axioms
  (Step 5 ACT closes the remaining sorry in
  `lrCoeffN_def_two_eq_lrCoeff2_of_support`; the main theorem
  `lrCoeffN_def_two_eq_lrCoeff2` is then unconditionally proved).

* **S3d** (downstream): The 7 verified `lrCoeff2 ... = 1` (resp. = 0)
  results in `Hilbert15OQ02.lean:166-209` lift mechanically to
  `lrCoeffN_def`-form by rewriting with `lrCoeffN_def_two_eq_lrCoeff2`
  and re-discharging via `native_decide`. ~7 lines per constant; ~50
  LOC total.

* **S4** (parent-file axiom replacement): Modify
  `proofs/Proofs/Hilbert15OQ02OQ03.lean:128` from `axiom lrCoeffN` to
  `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`. Verify
  `klyachko_theorem` (still an axiom — separate target) and
  `lr_polytime_positivity` still typecheck. The `decide` call in the
  latter is what made the Decidable instance non-negotiable in S2.
  Net effect: parent file axiom count 3 → 2 (eliminating axiom 1,
  `lrCoeffN`).

* **OQ-02 / OQ-03 proper**: Klyachko/Horn chain. Out of scope for this
  slug.

---

## 10. Honesty log

* No Lean files edited.
* No Mathlib bearer needs to be added (per §3.1, §3.2 audits).
* Mathlib lemma sources verified via direct `gh api` calls to
  `repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (pinned SHA from `proofs/lake-manifest.json`):
  * `Fintype.card_unique` at `Mathlib/Data/Fintype/Card.lean:81`
  * `Fintype.card_eq_zero_iff` at `Mathlib/Data/Fintype/Card.lean:265`
  * `Fintype.card_eq_one_iff` at `Mathlib/Data/Fintype/EquivFin.lean:209`
  * `Fintype.card_congr` at `Mathlib/Data/Fintype/EquivFin.lean:67`
  * `Unique.mk'` at `Mathlib/Logic/Unique.lean:25`
  * `Subtype.isEmpty_of_false` at `Mathlib/Logic/IsEmpty.lean:83`
  * `Equiv.equivPUnit` at `Mathlib/Logic/Equiv/Defs.lean:434`
* `lrCoeff2_le_one` at `Hilbert15OQ02.lean:258` confirmed via Grep
  in the worktree's checked-out main copy.
* The §4 / §5 / §6 Lean signatures all carry explicit `sorry` markers
  for ACT-author discharge. The PREP designs the API surface and the
  proof outline but does not pre-commit to specific tactic incantations;
  the ACT author has freedom to deviate from the suggested proof
  structure as long as the lemma statements match.
* Step 5 ACT is **sequential** in the dependency DAG with Steps 2-4
  ACTs (it consumes their forward forms as imports). Ship order:
  Step 2 ACT → Step 3 ACT → Step 4 ACT → Step 5 ACT. Parallel
  shipping is feasible if Step 5 ACT carries the forward forms as
  hypotheses, but then a final follow-up "discharge hypotheses" PR is
  needed.
* Pool contention: 1 open PR on the slug (#17966 stale, file-scope
  orthogonal). Step 5 PREP slot is uncontested.
* This file is ~720 LOC of design memo + bearer audit + Lean target
  skeletons, written from one researcher session in the
  `.loom/worktrees/researcher-1` worktree at `origin/main` commit
  `0cbd962f6bc`.

🤖 Generated by researcher-1
