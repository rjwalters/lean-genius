# Knowledge Base: erdos-43-oq-05

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-05 asks: "Can the five `sorry` counting lemmas be proved using Mathlib's `Finset.card` API?"

Examination of the parent source `proofs/Proofs/Erdos43Problem.lean` (as of 2026-06-09)
shows that the five counting lemmas referenced in this question **are already proved
without any `sorry`** — i.e., the answer to OQ-05 is YES, and the proofs already exist
on disk. The lemmas are: `sidon_pair_bound`, `disjoint_diff_combined_bound`,
`tao_equal_size_bound`, `sidon_diff_injective`, `sidon_diff_count`.

The proofs use the `Finset.card` API as the question hoped, via the standard pattern:
1. Reduce the `Nat.choose 2` target to `n * (n - 1) ≤ 2 * N` (or analogous)
2. Bind `n * (n - 1)` to `|A.offDiag|` via `Finset.card_offDiag`
3. Inject the offDiag image under the difference map `(a,b) ↦ a - b` (Sidon ⇒ injective)
4. Bound the image by the integer interval `Icc (1 - N) (N - 1)` of cardinality `2N - 1`
5. Compose via `card_image_of_injOn` + `card_le_card`

---

## Insights

### The OQ-05 question is effectively answered by file inspection

The parent file's counting lemmas exist, are named, and contain no `sorry`s. The
question can therefore be marked resolved once the file rebuilds under current Mathlib.

### File does not build at HEAD (Mathlib v4.26.0)

`./proofs/scripts/docker-build.sh Proofs.Erdos43Problem` at HEAD produces 13+
errors:

- `Unknown constant 'Finset.card_offDiag'` × 3 — renamed in v4.26.0 to
  `Finset.offDiag_card`, but with a *different RHS form*: new lemma states
  `s.offDiag.card = s.card * s.card - s.card`, while the old `card_offDiag` was
  `s.offDiag.card = s.card * (s.card - 1)`. Renaming alone changes the rewrite
  target.
- `omega could not prove` / `linarith failed` × 4 — in the Real.sqrt-using
  `tao_equal_size_bound`; likely a `Real.sqrt_pos`/`Real.sqrt_lt_one` lemma rename.
- `overloaded, errors` × 1 — in `sidon_diff_injective` at line 239, likely a
  multiple-`Finset.ext` resolution ambiguity.
- `subst 'b' occurs at` × 1 — line 263, an elaboration-ordering issue with `subst`.
- `simp made no progress` × 1 — line 285, `simp` lemma rename.

These are routine Mathlib v4.26.0 compatibility breaks of identical shape to the
ones already-fixed in PR #22729 for Erdos406Problem.lean.

### Repair playbook (for future iteration)

1. Rename `Finset.card_offDiag` → `Finset.offDiag_card` (3 sites)
2. After each rename, the goal `A.card * (A.card - 1) = ?` becomes
   `A.card * A.card - A.card = ?`. Insert `Nat.mul_sub_one` (or `Nat.sub_one_mul`)
   to bridge — or rewrite the `n * (n - 1)` to `n * n - n` before the `offDiag_card`
   call.
3. For the `omega`/`linarith` failures: re-check Real.sqrt lemma signatures; likely
   need to materialize a hypothesis or split the cast first.
4. For the `subst` failure: replace `subst b` with `rcases hb with rfl` or an
   explicit `cases` on the equality.
5. For `simp made no progress`: the lemma being unfolded may have been renamed;
   replace with explicit rewrite.

---

## Dead Ends

None substantive — only the in-progress partial rename in this OBSERVE iteration was
reverted (would have left the file in a worse state than untouched given the
unaddressed downstream form-change consequence of `offDiag_card`'s new RHS).

---

## Sessions

### 2026-06-09 — researcher-1 (iter-2): OBSERVE — answer already on disk; v4.26.0 build broken

OBSERVE-only iteration. Released claim without a code change. See state.md for the
detailed finding: the OQ-05 question is effectively answered (YES, the 5 counting
lemmas can be proved with `Finset.card`, and they already are on disk), but the
file does not build at HEAD due to ~13 routine Mathlib v4.26.0 compatibility breaks.
A future iteration should do the build repair following the playbook above (modeled
on PR #22729 for Erdos406Problem.lean).

No new theorems, no new axioms, no PR.
