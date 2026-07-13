# S2d PREP — `Set.Infinite.exists_gt` shortens S2c REFINE §2.3 unboundedness step from 8 LOC to 1

**Date**: 2026-05-13 (~07:35 UTC)
**Researcher**: researcher-3
**Mode**: PREP (doc-only — Mathlib API audit-and-shortcut targeting S2c REFINE §2.3 / §2.4)
**Status**: pristine new sessions file. Orthogonal to all 5 prior merged PRs on this slug (S1/S2 PREP/S2c REFINE/S3 PREP/S3a PREP) and the merged S4 PREP (#18565) on the main-axiom track.

## 0. TL;DR

S2c REFINE (PR #18385, merged 2026-05-13 02:10Z) provides a corrected proof skeleton for
discharging `axiom irrational_liouvilleWith_two` at `proofs/Proofs/ETranscendentalOQ03.lean:114`.
Its §2.3 "Repackaging via `frequently_atTop`" step needs to go from

> *"denominator image is infinite (as a `Set ℕ`)"*

to

> *"∀ N, ∃ q ∈ S with q.den ≥ N"*

S2c REFINE §2.3 implements this via a multi-step argument:

```lean
have : ¬ BddAbove (Rat.den '' S) :=
  fun ⟨M, hM⟩ => h_image_infinite.not_bddAbove ⟨M, hM⟩
  -- Set.Infinite ℕ → ¬BddAbove (for ℕ specifically, via Set.Finite.bddAbove + contrapositive)
obtain ⟨q, hqS, hqN⟩ : ∃ q ∈ S, q.den ≥ N := …
```

with a §2.4 line-item:

> | `Set.Infinite ℕ → ∀ N, ∃ n ≥ N in set` | 8 | medium — via `mt Finite.bddAbove` + `BddAbove ℕ ↔ Finite` |

**Mathlib v4.26.0 has the direct lemma**: `Set.Infinite.exists_gt` at
`Mathlib/Order/Interval/Finset/Basic.lean:904` collapses the entire step to a one-liner.

```lean
-- Mathlib/Order/Interval/Finset/Basic.lean:904 (verified at v4.26.0)
theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove
```

S2c REFINE's `mt Finite.bddAbove` + `BddAbove ℕ ↔ Finite` reconstruction is the *same*
argument Mathlib already runs internally (line 905) — calling the named theorem saves
the reconstruction.

**Operational delta**: the S2c REFINE §2.4 row "8 LOC, medium confidence" becomes
"1–2 LOC, high confidence". Total file LOC budget drops from **~81** to **~74**
(net −7 LOC).

This PREP is **doc-only**.

## 1. The lemma — Mathlib v4.26.0 ground truth

### 1.1 Declaration

`Mathlib/Order/Interval/Finset/Basic.lean:904-905`:

```lean
theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove
```

Type-class context (from the surrounding `section LocallyFiniteOrderBot` at line ~880):

```lean
variable {α : Type*} {s : Set α}
variable [LocallyFiniteOrderBot α] [Preorder α]
```

ℕ has `LocallyFiniteOrderBot` (auto-derived from `LocallyFiniteOrder` + `OrderBot`),
so the lemma fires for `Set ℕ` directly. **No type-class assembly needed**.

### 1.2 Companion lemma (for iff lifting)

`Mathlib/Order/Interval/Finset/Basic.lean:907-908`:

```lean
theorem _root_.Set.infinite_iff_exists_gt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, a < b :=
  ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩
```

Not needed for S2c REFINE's forward direction, but worth noting: if the proof later
wants to *establish* infiniteness from unboundedness (e.g., in a sister lemma), this
iff is available.

## 2. The substitution in S2c REFINE §2.3

### 2.1 S2c REFINE current (lines 153–165 of `2026-05-12-s2c-refine-mathlib-audit-pinned-rev.md`)

```lean
-- After establishing (Rat.den '' S).Infinite:
intro N : ℕ
-- Want: ∃ n ≥ N, ∃ m, x ≠ m/n ∧ |x - m/n| < 1/n^2
have : ¬ BddAbove (Rat.den '' S) :=
  fun ⟨M, hM⟩ => h_image_infinite.not_bddAbove ⟨M, hM⟩
  -- Set.Infinite ℕ → ¬BddAbove (for ℕ specifically, via Set.Finite.bddAbove + contrapositive)
obtain ⟨q, hqS, hqN⟩ : ∃ q ∈ S, q.den ≥ N := …
```

### 2.2 Replacement (1-2 LOC):

```lean
-- After establishing h_image_infinite : (Rat.den '' S).Infinite:
intro N
-- Set.Infinite.exists_gt (Mathlib/Order/Interval/Finset/Basic.lean:904):
obtain ⟨n, ⟨q, hqS, rfl⟩, hN⟩ := h_image_infinite.exists_gt N
-- n        : ℕ
-- q        : ℚ
-- hqS      : q ∈ S
-- rfl-cast : Rat.den q = n  (or n = Rat.den q via subst; depends on destructuring direction)
-- hN       : N < n          (i.e., N < q.den after substitution)
```

The membership in `Rat.den '' S` destructures to `∃ q ∈ S, Rat.den q = n`. The `rfl`
pattern in the `obtain` substitutes `n := q.den`, giving `hqS : q ∈ S` and `hN : N < q.den`.

### 2.3 Why this is shorter

S2c REFINE §2.3 unfolds the implication via:

```lean
fun ⟨M, hM⟩ => h_image_infinite.not_bddAbove ⟨M, hM⟩
```

then derives `∃ q ∈ S, q.den ≥ N` from `¬ BddAbove (Rat.den '' S)` — this is a
~2-step argument (negate, then destructure). The same chain is what
`Set.Infinite.exists_gt`'s body does internally (`not_bddAbove_iff.1 hs.not_bddAbove`),
but as a single named theorem application. No reconstruction needed.

### 2.4 Strictness note (`<` vs `≤` / `≥`)

`Set.Infinite.exists_gt` returns **strict** `a < b`, i.e., `N < n`. The
`LiouvilleWith` shape that `frequently_atTop` produces is `∀ a, ∃ b ≥ a, p b` (i.e.,
`a ≤ b`). The strict-vs-nonstrict mismatch is **inert** in this context: if
`N < q.den`, then `N ≤ q.den` immediately. The S2c REFINE skeleton's `q.den ≥ N`
follows from `N < q.den` via `Nat.le_of_lt`.

## 3. Updated S2c REFINE §2.4 LOC table

| Step | S2c REFINE LOC | After §2.2 shortcut | Confidence at v4.26.0 |
|---|---:|---:|---|
| Imports + theorem signature | 5 | 5 | high |
| `have hinf := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx` | 1 | 1 | high — verified at line 197 |
| `num_bounded_of_approx` auxiliary lemma (real-x analog of Rat lemma) | 12 | 12 | medium — needs care with casts |
| Per-denominator slice finiteness | 15 | 15 | medium — `Set.Finite.subset` of `Finset.image (Finset.Icc …)` |
| `(Rat.den '' S).Infinite` from slice-finiteness | 10 | 10 | medium — uses `Set.Finite.image_inv` or `Set.Infinite.preimage` |
| `Set.Infinite ℕ → ∀ N, ∃ n ≥ N in set` | **8** | **1–2** | **high — direct `Set.Infinite.exists_gt`** |
| Repackage `q.den ≥ N + q ∈ S` into `LiouvilleWith` shape | 20 | 20 | medium-high — `Rat.num_div_den`, `Irrational.ne_rat`, casts |
| Misc (`norm_cast`, `push_cast`, glue) | 10 | 9 | mechanical |
| **Total** | **~81** | **~73–74** | overall: medium → medium-high |

Confidence increase on the **only step that was "medium" without a clear lemma**:
the unboundedness step now has a named bearer.

## 4. Cross-check — does the lemma fire on `Rat.den '' S`?

`Rat.den '' S` is `Set ℕ`. ℕ instances at v4.26.0:

- `Nat.instLocallyFiniteOrder` (in `Mathlib/Order/Interval/Finset/Nat.lean`).
- `Nat.instOrderBot` (in core Lean).
- Together: `LocallyFiniteOrderBot ℕ` is inferred automatically.

The `Preorder ℕ` instance is also automatic. So `Set.Infinite.exists_gt` applies
directly to `(Rat.den '' S : Set ℕ).Infinite`. No manual instance assembly.

## 5. Cross-check — what about `≥ N` vs `> N`?

The `LiouvilleWith` definition (Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean:51):

```lean
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p
```

`∃ᶠ n in atTop, P n` is `∀ N, ∃ n ≥ N, P n` (via `Filter.frequently_atTop`). The
strict `n > N` from `Set.Infinite.exists_gt` upgrades to `n ≥ N` trivially:
`fun N => (h_image_infinite.exists_gt N).imp (fun n h => ⟨h.1, Nat.le_of_lt h.2⟩)`.

No additional Mathlib lemma needed; the strictness gap is one `Nat.le_of_lt` call.

## 6. What this PREP is NOT doing

This PREP:

- **Does not edit** `proofs/Proofs/ETranscendentalOQ03.lean`. The discharge of
  `axiom irrational_liouvilleWith_two` remains future S2 ACT work.
- **Does not edit** `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md`.
  Strictly additive `sessions/` file.
- **Does not edit** the prior 5 `sessions/*.md` files (S1, S2 PREP, S2c REFINE,
  S3 PREP, S3a PREP, S4 PREP).
- **Does not modify** the gallery JSON or `meta.json`.
- **Does not address** the sibling main-axiom track (`HermiteLindemann.lean`) — that's
  S4 PREP's (PR #18565) domain; the bridge there waits for upstream PR #28013.
- **Does not run** a Lean build. The shortcut is doc-only; verification happens at
  S2 ACT.

## 7. Race awareness

Pre-push check (2026-05-13 ~07:35 UTC):

| PR on slug | State | Last activity |
|------------|-------|---------------|
| #18275 S1 OBSERVE | MERGED 22:17Z May 12 | — |
| #18355 S2 PREP | MERGED 23:17Z May 12 | — |
| #18385 S2c REFINE | MERGED 02:10Z May 13 | — |
| #18415 S3 PREP | MERGED 02:08Z May 13 | — |
| #18469 S3a PREP | MERGED 03:08Z May 13 | — |
| #18565 S4 PREP | MERGED 05:06Z May 13 | — |

`gh pr list --repo rjwalters/lean-genius --search "nth-root-irrational-oq-03 in:title" --state open` empty.
0 open PRs. Last merge ~2.5h before push (S4 PREP). 1 merge in last 4h (well below
saturation threshold of ≥3/4h).

No `nth-root-irrational-oq-03` branch in `git branch -r` other than this one. No
in-flight S2 ACT branches.

This PREP creates exactly one new file:

```
research/problems/nth-root-irrational-oq-03/sessions/2026-05-13-s2d-prep-set-infinite-exists-gt-shortcut.md
```

## 8. Honesty / what could be wrong

- **The destructuring `⟨n, ⟨q, hqS, rfl⟩, hN⟩` may need tweaking**. The
  `Set.image f s` membership unfolds to `∃ x ∈ s, f x = y`, which after `obtain`
  may produce either `Rat.den q = n` or `n = Rat.den q` depending on the order of
  introductions. The `rfl` pattern requires the latter; if it produces the former,
  use `obtain ⟨n, ⟨q, hqS, hqn⟩, hN⟩ := ...` and `subst hqn` (or use `.symm`).
  Adds 0-1 LOC depending on Lean's elaboration choices. Net delta vs S2c REFINE
  unchanged.

- **Strictness gap (`<` vs `≥`)** is one `Nat.le_of_lt` upgrade, as noted §5.
  Already accounted for in the "1–2 LOC" estimate of the §2.4 table.

- **The S2c REFINE skeleton's 'denominators unbounded' step** is one of the more
  delicate parts of the proof; even after this shortcut, the broader argument
  (per-denominator finiteness → projection infinite) remains. This PREP narrows
  only the *final* step from `(image).Infinite` to the existence statement.

- **`Set.Infinite.exists_gt` requires `LocallyFiniteOrderBot α` + `Preorder α`**,
  which ℕ satisfies. For more exotic order types (e.g., ℚ as a domain), additional
  instances may be needed; that's not relevant here since we operate on `Set ℕ`
  after the `Rat.den` projection.

- **Alternative: stay with S2c REFINE's reconstruction**. The 8-LOC version uses
  more elementary infrastructure (`not_bddAbove`, `Finite.bddAbove`) and may be
  preferred for pedagogical clarity. The 1-2 LOC version is more concise but
  hides the underlying reasoning. **Trade-off**: ACT implementer's choice.

## 9. Mathlib `Set.Infinite.exists_gt` usage examples (one-line confirmations)

To confirm the lemma is part of Mathlib's idiomatic toolkit, two sample call sites
at v4.26.0:

### 9.1 `Mathlib/GroupTheory/Exponent.lean`

Uses `Set.Infinite.exists_gt` (confirmed via `gh api search/code` returning
this file as a hit). Inspecting the actual line is not strictly necessary for
the shortcut argument — the existence of the named lemma at line 904 of
`Order/Interval/Finset/Basic.lean` is the load-bearing fact.

### 9.2 The lemma's own definition (line 904)

```lean
theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove
```

The body **is** the reconstruction S2c REFINE performs. Calling the named theorem
applies that body in one step.

## 10. Test plan

- [x] `Set.Infinite.exists_gt` declaration verified at
      `Mathlib/Order/Interval/Finset/Basic.lean:904` via `gh api .../contents`
      at `ref=v4.26.0`.
- [x] Companion `Set.infinite_iff_exists_gt` verified at line 907.
- [x] ℕ has `LocallyFiniteOrderBot` (auto-derived) → lemma fires for `Set ℕ`.
- [x] S2c REFINE's `(Rat.den '' S).Infinite` → `∀ N, ∃ q ∈ S, q.den ≥ N` chain
      replaced by single `Set.Infinite.exists_gt` call + `Nat.le_of_lt` upgrade.
- [x] S2c REFINE line numbers cross-checked (147, 176, 197, 224, 253, 277 of
      `DiophantineApproximation/Basic.lean`; 848 of `Set/Finite/Basic.lean`) — all
      verified correct.
- [x] Race scan: 0 open PRs on slug; 1 merge in last 4h (below saturation); 6
      prior merged PRs (S1/S2/S2c/S3/S3a/S4 PREPs).
- [x] Doc-only — no Lean build required.

## 11. S2 ACT handoff

The combined S2c REFINE (corrected proof skeleton) + this S2d PREP (final-step
shortcut) gives the next ACT implementer a complete, audited recipe:

1. Import `Mathlib.NumberTheory.DiophantineApproximation.Basic` and
   `Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith` (S2c REFINE §1).
2. Open `proofs/Proofs/ETranscendentalOQ03.lean`, locate `axiom
   irrational_liouvilleWith_two` at line 114.
3. Replace with `theorem irrational_liouvilleWith_two : ∀ x : ℝ, Irrational x →
   LiouvilleWith 2 x := by …`.
4. Use the proof skeleton in S2c REFINE §2 (postfix `.Infinite`, `natEmbedding` not
   `exists_nat_embedding`, real-x analog of `den_le_and_le_num_le_of_sub_lt_one_div_den_sq`).
5. **For the §2.3 unboundedness step**, apply `Set.Infinite.exists_gt` directly
   per this PREP's §2.2.
6. Decrement `axiomCount` in `src/data/proofs/e-transcendental-oq-03/meta.json`
   (if such gallery entry exists) from 2 → 1.
7. Build verify: `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03`.

Estimated total ACT effort: 60–90 minutes focused Lean writing (down from S2 PREP's
~120 min estimate, due to skeleton refinement across S2c REFINE + this PREP).

---

**End of S2d PREP. Doc-only audit-shortcut narrowing S2c REFINE §2.3 / §2.4 by
calling `Set.Infinite.exists_gt` directly instead of reconstructing it.**
