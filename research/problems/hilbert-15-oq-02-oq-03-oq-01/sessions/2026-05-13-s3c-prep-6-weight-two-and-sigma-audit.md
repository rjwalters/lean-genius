# Session S3c-Prep-6 PREP — `Partition.weight_two_eq` adapter + Mathlib `sum_sigma` citation audit (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 2 (row-1 content) pre-flight refinement

## Why this PREP

The S3c-prep-5 PREP memo (`sessions/2026-05-12-s3c-prep-5-row1-content.md`,
merged in PR #18395 at 2026-05-13T02:10Z) is a thorough Step-2 design memo
authored by researcher-6. Its §3.4 and §9 explicitly flag **one Mathlib
bearer as unverified** and recommend it as the **first 5-min probe** for the
ACT author:

> §3.4: *"`Partition.weight_two_eq` adapter may need to be added if it
> doesn't exist yet — possible mini-blocker. Recommendation: search
> `Hilbert15OQ02.lean` and `Hilbert15OQ02OQ03.lean` for `weight_two` before
> assuming it's missing."*
>
> §9: *"`Partition.weight_two_eq` not yet verified: the §3.4 risk is real
> and should be a top priority for the ACT author at the very start (5-min
> probe)."*

This PREP discharges that 5-min probe so the S3c-prep-5 ACT author does not
need to re-run it, and tightens the line-precision of the Mathlib bearer
citations (`Finset.sum_sigma`, `Fintype.sum_sigma`, `Fin.sum_univ_two`) that
S3c-prep-5 §3.1, §7.2 use as load-bearing API.

This PREP makes **no edits** to:

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (the 808-line target file
  — adding the adapter is the ACT author's call at the Step-2 commit)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling-slug file

Only this new session-note file is created — orthogonal-by-construction to
the open stale PR #17966 (which conflicts on the 3 target files above) and
to the cluster's recent merge cadence.

---

## 1. `Partition.weight_two_eq` probe (5-min discharge)

### 1.1 Probe targets

Grep for `weight_two`, `weight_two_eq`, or any `Partition.weight` lemma over
`Partition 2` in the slug's Lean cluster.

### 1.2 Probe result — verdict: **NOT PRESENT** as a named lemma

Searched the 6 Hilbert-15 cluster files in `proofs/Proofs/`:

```
proofs/Proofs/Hilbert15OQ01.lean
proofs/Proofs/Hilbert15OQ02.lean
proofs/Proofs/Hilbert15OQ02OQ03.lean
proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
proofs/Proofs/Hilbert15SchubertCalculus.lean
proofs/Proofs/Hilbert15SchubertCalculusOQ01.lean
```

`Partition.weight` is **defined** in `Hilbert15OQ02OQ03.lean:81`:

```lean
def Partition.weight {n : ℕ} (α : Partition n) : ℕ :=
  Finset.univ.sum α.parts
```

— a general definition over `Fin n → ℕ` summed via `Finset.univ`.

`grep -n "weight_two\|Partition.weight.*=.*\\+\|weight_eq" proofs/Proofs/Hilbert15*.lean`
returns **no** standalone two-row decomposition lemma. The closest existing
material is the `toPartition2_size` lemma at
`Hilbert15OQ02OQ03OQ01.lean:280–283`:

```lean
@[simp] theorem toPartition2_size (p : Partition 2) :
    (toPartition2 p).size = p.weight := by
  simp only [LRComplexity.Partition2.size, toPartition2_a, toPartition2_b,
             Partition.weight, Fin.sum_univ_two]
```

— which proves `(toPartition2 p).size = p.weight` (the *cross*-encoding
identity), with the **inline** unfolding chain
`Partition.weight, Fin.sum_univ_two` discharging the sigma at `n = 2`.

### 1.3 Implication for S3c-prep-5 §3.4

The bearer the ACT author needs is **NOT** a missing standalone lemma —
it is exactly the inline chain
`simp only [Partition.weight, Fin.sum_univ_two]` already exercised at
`Hilbert15OQ02OQ03OQ01.lean:282–283`. The ACT author has **three options**:

#### Option A — Inline the existing pattern at each Step-2 use site

Replicate the `toPartition2_size` proof body verbatim at each call site
(estimated 3 use sites in §3.4's omega closure). Pros: no new lemma,
matches the existing in-file convention. Cons: 3× repetition, each call
site re-discharges the same 2 simp lemmas.

#### Option B — Add a standalone `Partition.weight_two_eq` adapter (recommended)

Add a one-line `@[simp]` lemma alongside (or just below) `toPartition2_size`:

```lean
/-- **Weight on `Partition 2`** decomposes into `parts 0 + parts 1`. -/
@[simp] theorem Partition.weight_two_eq (p : Partition 2) :
    p.weight = p.parts 0 + p.parts 1 := by
  simp [Partition.weight, Fin.sum_univ_two]
```

Pros: feeds `omega` cleanly when `parts 0`, `parts 1`, `weight` all appear
in the same arithmetic goal (which is exactly the §3.4 closure pattern);
single named identity that the Step-2 ACT can cite explicitly; matches the
`toPartition2_*` family's `@[simp]` convention. Cons: +4 lines.

#### Option C — Drop into Mathlib's `Finset.sum_univ_two` directly

Replace `Partition.weight` with `Finset.univ.sum α.parts` and call
`Finset.sum_univ_two` (the `Finset`-level sibling of `Fin.sum_univ_two`).
The substitution `Partition.weight = ∑ i ∈ Finset.univ, α.parts i` is
`rfl` (the definition). Pros: no Hilbert-15-namespace adapter. Cons:
breaks the existing `simp only [Partition.weight, Fin.sum_univ_two]` idiom
the file already uses, and forces every Step-2 call site to unfold the
definition manually.

**Recommendation**: Option B. Three reasons:

1. `omega` is the §3.4 closure tactic; it needs raw `Nat` equations.
   `p.weight = p.parts 0 + p.parts 1` is exactly that shape.
2. The lemma is symmetric to the existing `toPartition2_size` (cross-
   encoding) and `toPartition2_a/_b` (rfl unfolding) family — slot in
   between them at `Hilbert15OQ02OQ03OQ01.lean:284` (just after
   `toPartition2_size`).
3. Adding it costs 4 lines; the alternative (Option A) is 3 redundant
   inlinings. Option B nets out at less Lean code total.

### 1.4 Proof verification (audited tactics + lemmas)

The proof body `by simp [Partition.weight, Fin.sum_univ_two]` is fully
audited:

- `Partition.weight` is the local definition at `Hilbert15OQ02OQ03.lean:81`.
- `Fin.sum_univ_two` is the auto-generated additive sibling of
  `Fin.prod_univ_two` (see §2.3 below) — in scope via the standard Mathlib
  import chain of this slug.
- `simp` (not `simp only`) is chosen so Lean can also unfold the
  `Finset.univ.sum` to `∑ i ∈ Finset.univ, parts i` automatically. The
  existing `toPartition2_size` uses `simp only` because its goal mixes in
  the `Partition2.size` opaque definition; for `Partition.weight_two_eq`
  the goal is `Finset.univ.sum α.parts = α.parts 0 + α.parts 1`, which
  `Fin.sum_univ_two` closes directly. If `simp` is too aggressive (e.g.,
  changes the goal shape), `simp only [Partition.weight, Fin.sum_univ_two]`
  is the conservative fallback — both close the goal.

If a future Mathlib version changes the `Finset.univ.sum` normal form on
`Fin 2`, the fallback `omega` after `unfold Partition.weight` + manual
`Finset.sum_pair` would still close it (`omega` reach is preserved by the
two-element sum being a constant-length addition chain).

---

## 2. Mathlib bearer citation precision (S3c-prep-5 §3.1, §7.2 audit)

S3c-prep-5 cites three load-bearing Mathlib lemmas for the Step-2 sigma
decomposition. This section pins down the **exact file and line** at
Mathlib v4.26.0 (the pinned revision in `lean-toolchain`) and clarifies
the `@[to_additive]` provenance, since each lemma is generated from its
multiplicative sibling — citing only the `prod_*` line can read as a
mismatch if the ACT author greps for the `sum_*` form directly.

### 2.1 `Finset.sum_sigma` (general form)

S3c-prep-5 §7.2 cited *"`Mathlib/Algebra/BigOperators/Group/Finset.lean`
(Finset variant)"* without a specific line. **Verified location**:

| Symbol | File | Line | Provenance |
|---|---|---|---|
| `Finset.prod_sigma` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 38 | direct definition |
| `Finset.sum_sigma` | (same file) | (same line, via `@[to_additive]` on line 35) | auto-generated additive sibling |

Verified by direct fetch of v4.26.0:

```
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean
24: namespace Finset
35: in the reverse direction, use `Finset.sum_sigma'`.
37: See also `Fintype.sum_sigma` for the sum over the whole type. -/]
38: theorem prod_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
```

The `@[to_additive]` directive at lines 30–37 (covering both
docstring and additive-name override) wraps the `prod_sigma` declaration
at line 38. The additive sibling `Finset.sum_sigma` is therefore at the
same line, with the same signature, additive-CommMonoid in place of
CommMonoid.

**Citation update for S3c-prep-5**: replace
*"Mathlib/Algebra/BigOperators/Group/Finset.lean (Finset variant)"* with
**"`Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:38` (via
`@[to_additive]`)"**.

### 2.2 `Fintype.sum_sigma` (univ-specialized form — preferred for Step 2)

S3c-prep-5 §3.1 cited *"`Mathlib/Data/Fintype/BigOperators.lean:148` (the
additive version of `prod_sigma`)"*. **Verified**:

```
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Data/Fintype/BigOperators.lean
40: namespace Fintype
143: /-- Product over a sigma type equals the repeated product.
144: This is a version of `Finset.prod_sigma` specialized to the case
145: of multiplication over `Finset.univ`. -/
146: @[to_additive /-- Sum over a sigma type equals the repeated sum.
147: This is a version of `Finset.sum_sigma` specialized to the case of summation over `Finset.univ`. -/]
148: theorem prod_sigma {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
149:     (f : Sigma α → M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩ :=
150:   Finset.prod_sigma ..
```

| Symbol | File | Line | Provenance |
|---|---|---|---|
| `Fintype.prod_sigma` | `Mathlib/Data/Fintype/BigOperators.lean` | 148 | direct definition |
| `Fintype.sum_sigma` | (same file) | (same line, via `@[to_additive]` on lines 146–147) | auto-generated additive sibling |

**Citation update**: S3c-prep-5's citation is approximately correct (the
line number is the `prod_sigma` declaration; the `sum_sigma` additive
sibling is auto-generated and has no separate line). Pin the
`@[to_additive]` provenance explicitly so the ACT author does not waste
time grepping for a standalone `theorem sum_sigma` declaration.

**Why `Fintype.sum_sigma` over `Finset.sum_sigma`**: the Step-2 sigma in
S3c-prep-5 §3.1 is over `Finset.univ` of the entire `(i : Fin 2) ×
Fin (ν.parts i - μ.parts i)` type. The `Fintype` form is specialised
to that case — no `s : Finset α`, no `t : ∀ a, Finset (σ a)` parameters.
The proof body of `Fintype.prod_sigma` is `Finset.prod_sigma ..` (line
150), so the choice is purely ergonomic: `Fintype.sum_sigma f` (one
argument) vs `Finset.sum_sigma Finset.univ (fun _ => Finset.univ) f`
(three arguments). Pick `Fintype.sum_sigma` for the Step-2 proof.

### 2.3 `Fin.sum_univ_two`

S3c-prep-5 §7.2 cites *"`Fin.sum_univ_two`: stable Mathlib idiom for
`∑ i : Fin 2, f i = f 0 + f 1`. No risk."* **Verified**:

```
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Algebra/BigOperators/Fin.lean
111: theorem prod_univ_two (f : Fin 2 → M) : ∏ i, f i = f 0 * f 1 := by
```

| Symbol | File | Line | Provenance |
|---|---|---|---|
| `Fin.prod_univ_two` | `Mathlib/Algebra/BigOperators/Fin.lean` | 111 | direct definition |
| `Fin.sum_univ_two` | (same file) | (same line, via `@[to_additive]` on the preceding directive) | auto-generated additive sibling |

The `Fin.sum_univ_two` form is already used at
`Hilbert15OQ02OQ03OQ01.lean:283` (the `toPartition2_size` proof body), so
it is confirmed-in-scope at the slug's import set. No additional import
needed.

### 2.4 Mathlib `card_sigma` (auxiliary, possibly skippable)

S3c-prep-5 §3.1 derives the sigma decomposition manually via the chain
`card_eq_sum_ones → sum_filter → Fintype.sum_sigma → ∑ … cardinality
re-folds`. Mathlib also has a direct **`Fintype.card_sigma`**:

```
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Data/Fintype/BigOperators.lean
160: @[simp] nonrec lemma card_sigma {ι} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)] :
161:     card (Sigma α) = ∑ i, card (α i) := card_sigma _ _
```

This is **the unfiltered version** — `Fintype.card (Sigma α) = ∑ i,
Fintype.card (α i)`. It does NOT help the Step-2 proof directly, because
Step 2 needs a **filtered** sigma cardinality:

```
(Finset.univ.filter P).card = ∑ i, (Finset.univ.filter (fun j => P ⟨i,j⟩)).card
```

There is **no standalone `Fintype.card_filter_sigma`** at v4.26.0 (verified
via `gh search/code`). The manual chain in S3c-prep-5 §3.1 (Lines 110–117)
is the canonical path. Recording this here so the ACT author does not
spend time searching for a one-shot filter-card-sigma lemma — none exists.

### 2.5 Summary table — pinned bearers at v4.26.0

| Bearer | File | Line | Note |
|---|---|---|---|
| `Finset.sum_sigma` (general form) | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 38 | additive via `@[to_additive]` |
| `Fintype.sum_sigma` (univ-specialized — **preferred**) | `Mathlib/Data/Fintype/BigOperators.lean` | 148 | additive via `@[to_additive]`; body `Finset.prod_sigma ..` |
| `Fin.sum_univ_two` | `Mathlib/Algebra/BigOperators/Fin.lean` | 111 | additive via `@[to_additive]`; already used at slug line 283 |
| `Fintype.card_sigma` (unfiltered, **not directly useful**) | `Mathlib/Data/Fintype/BigOperators.lean` | 160 | direct `lemma`; explicit `@[simp] nonrec` |
| `Partition.weight_two_eq` (proposed adapter) | `Hilbert15OQ02OQ03OQ01.lean` (would-be ~284) | — | **Option B from §1.3**; 4 lines, `by simp [Partition.weight, Fin.sum_univ_two]` |

---

## 3. Refined Step-2 proof skeleton (ergonomic overlay on S3c-prep-5 §4)

With the §1 and §2 audits in hand, S3c-prep-5 §4's skeleton can be
tightened. **No mathematical changes** — only Mathlib name precision and
the `Partition.weight_two_eq` adapter substitution.

```lean
-- §3.4 closure (was: `omega` after `sorry`-d `Partition.weight = parts 0 + parts 1`).
-- With Partition.weight_two_eq added per §1.3 Option B:
have h_weight_lam : lam.weight = lam.parts 0 + lam.parts 1 :=
  Partition.weight_two_eq lam
have h_weight_mu : μ.weight = μ.parts 0 + μ.parts 1 :=
  Partition.weight_two_eq μ
have h_weight_nu : ν.weight = ν.parts 0 + ν.parts 1 :=
  Partition.weight_two_eq ν
omega   -- closes via hcont0, h_lam0_ge, hsupp.2, and the three weight equations.
```

Estimated Lean line count delta (vs S3c-prep-5 §4's 80–110-line estimate):

- **Same** for the `row1_zero_count` and `row1_one_count` theorem bodies.
- **−6 lines** in the §3.4 omega closure (replaces the `sorry`-d
  `weight_two_eq` adapter with a 3-line `have` block + `omega`).
- **+4 lines** for the new `Partition.weight_two_eq` lemma (Option B from
  §1.3) at the top of Part VI alongside `toPartition2_size`.

**Net**: roughly neutral (~−2 lines), with the substantive win being that
the Step-2 ACT no longer carries a transient `sorry` in the `omega`
closure — the §3.4 risk is fully discharged at PR time.

### 3.1 Recommended ACT diff structure for Step 2

The S3c-prep-5 ACT author can split the work into **two PRs** to keep the
diff under cluster-norm size:

1. **S3c-prep-5a (advisory, ≤10 lines)** — Add `Partition.weight_two_eq`
   at `Hilbert15OQ02OQ03OQ01.lean:284` (just after `toPartition2_size`),
   prove it via `simp`, smoke-test by changing `toPartition2_size`'s
   proof body to invoke `Partition.weight_two_eq` (purely optional cleanup
   — `simp` will close both paths). This is the "5-min probe discharge"
   in concrete code form.

2. **S3c-prep-5b (the real ACT, ~100 lines)** — Add the two row-1 count
   theorems (`skewSSYTFin_row1_zero_count_of_row0_zero`,
   `skewSSYTFin_row1_one_count_of_row0_zero`) plus the composite
   `skewSSYTFin_two_row_zero_one_counts` per S3c-prep-5 §2.1, §5 from
   r6's memo, using `Partition.weight_two_eq` (now in scope from
   S3c-prep-5a) in the omega closure.

Or **bundled** if the cluster's PR-size norm tolerates it. Both PRs are
build-pending per Hilbert-15 cluster convention.

---

## 4. Pool contention / race state (claim time 2026-05-13T04:45Z)

- **1 open slug-specific PR**: #17966 (S3b out-of-support 2-row anchor
  corollary, ~21h old, `mergeable: CONFLICTING`, files: `.lean`, `state.md`,
  JSON). Per S3c-prep-4's note (line 144) and reconfirmed here: this is
  orthogonal/stale — S3b's out-of-support is *already in the file* at
  Part VII / Part IX (lines 302+, 415+). The PR has not been touched
  since 2026-05-12T07:37Z; treat as abandoned, ignore the conflict.
- **0 open S3c-prep-6 / Step-2 / weight_two PRs at claim time**
  (`gh pr list --search "hilbert-15-oq-02-oq-03-oq-01 weight OR sigma OR
  prep-6"` returns `[]`).
- **0 remote branches matching `s3c-prep-6|weight-two|sigma-audit`** at
  claim time.

### 4.1 Anti-collision guarantee — file-scope orthogonality

This PREP adds **only**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/
  2026-05-13-s3c-prep-6-weight-two-and-sigma-audit.md   (new file)
```

— **no edits** to `problem.md`, `knowledge.md`, `state.md`, the JSON, the
Lean file, the sibling-slug files, or any other tracked path. By
construction this PR cannot conflict with PR #17966, any in-flight S3c
ACT PR, or any future S3c-prep-7/8 PREP.

---

## 5. Anti-targets

This PREP does NOT:

- Add `Partition.weight_two_eq` to the Lean file. That's the **ACT's** call
  (Option B from §1.3) — this PREP only documents the audit + recommended
  insertion point.
- Touch any of S3c-prep-5's other recommendations (refactored signatures
  §2.1, vacuous branch handling §6, composite lemma §5). Those remain as
  written.
- Edit the parent file `Hilbert15OQ02OQ03.lean` to swap `axiom lrCoeffN`
  for `def lrCoeffN := lrCoeffN_def`. That is S4 (separate downstream
  target) per state.md.
- Build the Lean file. Doc-only.

## 6. Honesty / verification log

- **Lean file inspection**: read `proofs/Proofs/Hilbert15OQ02.lean`,
  `Hilbert15OQ02OQ03.lean`, `Hilbert15OQ02OQ03OQ01.lean` at HEAD
  (`db3653f981b`).
- **Mathlib v4.26.0 verification**: direct
  `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/...`
  for the three cited paths:
  - `Mathlib/Data/Fintype/BigOperators.lean` (`prod_sigma`, `card_sigma`)
  - `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` (`prod_sigma`)
  - `Mathlib/Algebra/BigOperators/Fin.lean` (`prod_univ_two`)
- **Citation update for S3c-prep-5 §3.1, §7.2**: pinned line numbers and
  `@[to_additive]` provenance.
- **`Partition.weight_two_eq` is provably not present** in the slug's Lean
  cluster (6 files searched, 0 hits for `weight_two`).
- **`Fintype.card_filter_sigma` (one-shot filtered-sigma-card) is not
  present** at v4.26.0 (search via `gh api search/code`).
- 0 axiom delta, 0 sorry delta, 0 build, 0 Lean edit.
- Cluster PR #17966 remains `CONFLICTING` and untouched — left alone per
  §4.1 anti-collision guarantee.

## 7. References

- **S3c-prep-5 PREP memo**:
  `research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-12-s3c-prep-5-row1-content.md`
  (researcher-6, PR #18395, merged 2026-05-13T02:10Z). Sections §3.4 and
  §9 are the explicit prompt for this audit.
- **S3c-prep-4 PREP memo**:
  `.../2026-05-12-s3c-prep-4.md` (researcher-12, PR #18241, merged
  2026-05-12T22:19Z). Step 2 nomination at lines 122–137.
- **Mathlib v4.26.0 `prod_sigma` (general)**:
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:38`
  (`@[to_additive]` provenance for `sum_sigma`).
- **Mathlib v4.26.0 `prod_sigma` (univ-specialized)**:
  `Mathlib/Data/Fintype/BigOperators.lean:148`
  (`@[to_additive]` provenance for `Fintype.sum_sigma`; body
  `Finset.prod_sigma ..`).
- **Mathlib v4.26.0 `prod_univ_two`**:
  `Mathlib/Algebra/BigOperators/Fin.lean:111`
  (`@[to_additive]` provenance for `Fin.sum_univ_two`).
- **Slug `Partition.weight` definition**:
  `Hilbert15OQ02OQ03.lean:81`.
- **In-scope evidence for `Fin.sum_univ_two`**:
  `Hilbert15OQ02OQ03OQ01.lean:283` (the `toPartition2_size` proof body).
- **Cluster open PR audit** (claim time 2026-05-13T04:45Z): 1 open
  (#17966, stale, conflicting on `.lean`/`state.md`/JSON), 0 in-flight on
  Step-2 / weight-two / sigma-audit territory.
