# S6 PREP — `firstFactor`-side mirror pass on `InvariantFactorChain`

**Date**: 2026-05-12
**Phase**: S6 PREP (doc-only)
**Agent**: researcher-12
**Predecessor PRs (merged or in-flight)**:
- PR #17888 (S1 SCAFFOLD), #17998 (S3 ACT), #18086 (S4 ACT) — merged
- PR #18182 (S5 ACT `prodFactors_natDegree_le_lastFactor_natDegree_mul`,
  build pending) — **open at S6-claim time**

This document is a design memo for the next-iteration `firstFactor`-side
mirror pass referenced as bullet 2 of state.md "Next Action" option 4
("`firstFactor`-side mirror lemmas"). It locks the API surface, proof
plans, Mathlib reference points, and an ~50-LOC delta budget *before*
S6 ACT lands, so the implementer can ship a single-shot single-file
addition with no statement re-design.

**This PR contains zero Lean code, zero edits to**
**`Proofs/MinpolyCharpolyOQ03.lean`, zero edits to gallery files**
**(`meta.json` / `annotations.json` / `index.ts`), and zero edits to**
**`research/problems/minpoly-charpoly-oq-03/{problem,state,knowledge}.md`.**
**One new file: this document, in a new `sessions/` subdir.**

---

## §0. TL;DR

S4–S5 added four `lastFactor`-side helpers on `InvariantFactorChain F`
(membership, monicness, degree-maximality, length-times-last upper bound
on `prodFactors.natDegree`). The structural pass is **incomplete on the
opposite side**: `firstFactor` is the abstract counterpart of "the
divisibility-chain *minimum*" (`p₁` divides every later factor, so
`deg p₁ ≤ deg p_i` for all `i`), and the dual lower bound

```
factors.length * firstFactor.natDegree ≤ prodFactors.natDegree
```

is currently missing.

S6 ships a four-lemma `firstFactor`-side mirror — `firstFactor_mem`,
`firstFactor_monic`, `firstFactor_natDegree_minimal`,
`prodFactors_natDegree_ge_firstFactor_natDegree_mul` — plus one
auxiliary `Nat` helper (`nat_list_sum_ge_length_mul_of_all_ge`),
all sorry-free, conditional only on `c.factors ≠ []`. Together with
S5's upper bound this gives a two-sided sandwich

```
k · deg p₁  ≤  deg(prodFactors)  ≤  k · deg pₖ
```

i.e. the **degree-symmetric structural facts** that bracket the
eventual matrix-level identity `deg(charpoly M) = n` from both sides
once instantiated. Both bounds remain coarse a-priori — they do not
require S6 (OQ-03-OQ-04) — and are usable today.

Estimated S6 ACT delta: **+50 LOC** (4 public theorems, 1 private
helper, 1 definition), lineCount 459 → ~509, theoremCount 11 → 15,
1 new definition (`InvariantFactorChain.firstFactor`), 1 new private
helper. No new imports. Sorry count unchanged at 1 (the S1 placeholder
on `rational_canonical_form_exists`).

---

## §1. Why mirror `lastFactor`? — the structural symmetry

The S4–S5 helpers established the `lastFactor`-side of the
`InvariantFactorChain` natDegree story:

* `lastFactor_mem` — `lastFactor c ∈ c.factors` (when `c.factors ≠ []`).
* `lastFactor_monic` — `(lastFactor c).Monic`.
* `lastFactor_natDegree_maximal` — every factor's natDegree is at most
  `(lastFactor c).natDegree`.
* `prodFactors_natDegree_le_lastFactor_natDegree_mul` —
  `prodFactors.natDegree ≤ factors.length * lastFactor.natDegree`.

The divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ` is **bi-directional** in
terms of natDegree: it forces `deg p_i ≤ deg p_j` whenever `i ≤ j`
(via S3's `chain_natDegree_le`), which immediately gives **both** a
minimum (`p₁`) and a maximum (`pₖ`) for `(p_i.natDegree)_i`. The
S4–S5 pass only consumed the maximum direction. The minimum direction
yields exactly four analogous structural lemmas, by literally swapping
"last" → "first", `≤` → `≥`, and `getLast?` → `head?` throughout.

**Why this matters mathematically.** In the eventual matrix-level
instantiation the chain corresponds to a matrix `M` with

* `lastFactor = minpoly M` (degree-maximal invariant factor),
* `firstFactor = ` *least non-trivial invariant factor* — a structural
  divisor of every other invariant factor and a divisor of `minpoly M`.

Two facts then follow trivially from the abstract S5 + S6 bookkeeping
lemmas, with no further work at the matrix level:

1. (Upper bound, S5)   `deg(charpoly M) ≤ k · deg(minpoly M)`.
2. (Lower bound, S6)   `k · deg(firstFactor M) ≤ deg(charpoly M)`.

The latter is precisely the statement that the **product of the
invariant factors cannot be shorter than `k` copies of the smallest
one**, a coarse but useful structural fact: it says, for instance,
that if any invariant factor has positive degree (which is enforced
by the `posDegree` field, so always), then `deg charpoly ≥ k`,
i.e. **the matrix has at least `k` distinct elementary divisors only
when `n ≥ k`** — the obvious cardinality constraint, but now derivable
from the abstract chain without any matrix-level argument.

**Why this matters formalisation-wise.** Pulling the dual side into the
abstract layer makes the eventual OQ-03-OQ-04 work (matrix-level
similarity transform assembly) simpler: at the time the chain gets
instantiated by an `M : Matrix n n F`, every structural natDegree
fact — both directions of the sandwich, both endpoints' monicness,
both endpoints' membership — is already available sorry-free as a
direct corollary, without any further `Polynomial`-level induction.
Symmetric APIs reduce friction; this PREP locks the symmetric layer
before the matrix layer arrives.

**Cheap-cost claim.** Each `firstFactor`-side lemma reuses the same
infrastructure S4–S5 already established (`chain_natDegree_le`,
`length_pos_of_ne_nil`, the `prodFactors_natDegree` sum identity).
No new mathematical insight is needed: this is purely a notational
completion pass on the abstract structure. Estimated implementer time:
~25–35 minutes of editing, no Lean-Mathlib lookup beyond `List.head?`.

---

## §2. Definitional choice — `firstFactor` via `head?.getD 1`

The cleanest mirror of

```lean
noncomputable def InvariantFactorChain.lastFactor
    (c : InvariantFactorChain F) : F[X] :=
  c.factors.getLast?.getD 1
```

is

```lean
noncomputable def InvariantFactorChain.firstFactor
    (c : InvariantFactorChain F) : F[X] :=
  c.factors.head?.getD 1
```

**Why `head?.getD 1` and not `head` with a hypothesis?** Symmetry: the
existing `lastFactor` definition is total (returns `1` on the empty
chain) for the same reason — keeps the abstract surface API
hypothesis-free for downstream rewriting. Mirror this choice exactly.

**Why fallback `1` and not `0` or `factors.head?.getD default`?** Two
reasons, both inherited from `lastFactor`:

1. The polynomial `1` is monic of degree `0`, so any `Monic` /
   `natDegree`-style fact that holds vacuously for an empty chain
   (with fallback `1`) is automatically true: the `Monic` and
   `natDegree`-respecting fallback keeps statements parallel between
   the empty and nonempty cases without having to use `getD 0`
   (which would fail `Monic`) or `default := 0` (same).
2. The expected matrix-level instantiation never produces an empty
   chain — if `M ≠ 0` there is at least one invariant factor, and the
   degenerate case "`M = 0` over an empty index type" is a footnote.

**Alternative considered (rejected): `List.head!`.** This is unsafe
(panic on empty) and would require all downstream theorems to assume
`c.factors ≠ []` in their statement, not just their proof. The
`getD 1` pattern lets `firstFactor_monic`, `firstFactor_mem`, etc.
remain syntactically uniform with `lastFactor_monic`, `lastFactor_mem`
(which take `h : c.factors ≠ []` as an explicit argument; the
fallback never surfaces in the conclusion). This is the API choice
S4 locked.

**Alternative considered (rejected): direct indexed access**
`c.factors[0]'h` with `h : 0 < c.factors.length`. This is *what S6's
proofs internally reduce to* (via a bridging lemma — see §3.0) but
not what the API surface should expose. Hypothesis-free `noncomputable
def` keeps callers from threading `0 < c.factors.length` through
unrelated reasoning.

---

## §3. Four mirror lemmas — statements + proof sketches

### §3.0. Internal bridging lemma `firstFactor_eq_getElem_zero`

```lean
/-- The `firstFactor` of a nonempty chain coincides with the indexed
    access at position 0. Internal-use lemma bridging the
    `head?.getD 1` definition with the `Fin`-indexed access used by
    `chain_natDegree_le`. Mirror of S4's `lastFactor_eq_getElem_pred`. -/
private theorem firstFactor_eq_getElem_zero
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor = c.factors[0]'(length_pos_of_ne_nil h) := by
  show c.factors.head?.getD 1 = _
  rw [List.head?_eq_head h]
  -- Now: `(some (c.factors.head h)).getD 1 = c.factors[0]`
  show c.factors.head h = _
  exact (List.head_eq_getElem h).symm
```

The `getLast?_eq_getLast` ↔ `head?_eq_head` and
`getLast_eq_getElem` ↔ `head_eq_getElem` substitutions yield this
proof verbatim from S4's `lastFactor_eq_getElem_pred` — only the
index `length - 1` ↦ `0` and the symmetry flip (`.symm`) on the final
rewrite. **No new arithmetic obligation** (the `length - 1`
manipulation that needed `omega` in S4 is replaced by index `0`
with `length_pos_of_ne_nil h` discharging `0 < c.factors.length`
directly).

**Implementer note.** The `length_pos_of_ne_nil` helper is in-tree
(file lines 331–335) and used by `lastFactor_eq_getElem_pred`. The
`List.head?_eq_head` and `List.head_eq_getElem` names must be checked
against the pinned Mathlib v4.26.0 rev (see "Mathlib API audit" §4).
If `List.head_eq_getElem` does not resolve, a 2-line `rcases l with _ |
⟨a, t⟩` fallback works — but the name is the standard convention.

### §3.1. `firstFactor_mem`

```lean
/-- The first factor of a nonempty invariant-factor chain is a member
    of the chain. Mirror of `lastFactor_mem`. -/
theorem firstFactor_mem (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor ∈ c.factors := by
  rw [firstFactor_eq_getElem_zero c h]
  exact List.getElem_mem _
```

Two-line proof. Identical body to `lastFactor_mem` after substituting
the bridging lemma.

### §3.2. `firstFactor_monic`

```lean
/-- The first factor of a nonempty invariant-factor chain is monic.
    Mirror of `lastFactor_monic`. -/
theorem firstFactor_monic
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor.Monic :=
  c.monic _ (firstFactor_mem c h)
```

One-line. Term-mode, no `by`. Identical body to `lastFactor_monic`
after substituting `lastFactor_mem` ↦ `firstFactor_mem`.

### §3.3. `firstFactor_natDegree_minimal`

```lean
/-- Every invariant factor has natDegree at least that of the first
    factor. Abstract counterpart of the RCF fact that the first
    invariant factor `p₁` (a divisor of every later factor) has the
    minimal degree among the invariant factors. One-line application
    of `chain_natDegree_le` with `i = 0`. Mirror of
    `lastFactor_natDegree_maximal`. -/
theorem firstFactor_natDegree_minimal
    (c : InvariantFactorChain F) (h : c.factors ≠ [])
    {p : F[X]} (hp : p ∈ c.factors) :
    c.firstFactor.natDegree ≤ p.natDegree := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  have hpos : 0 < c.factors.length := length_pos_of_ne_nil h
  let i  : Fin c.factors.length := ⟨0, hpos⟩
  let j' : Fin c.factors.length := ⟨j, hj⟩
  have hij : i.val ≤ j'.val := Nat.zero_le _
  have hdeg : c.factors[i].natDegree ≤ c.factors[j'].natDegree :=
    chain_natDegree_le c hij
  rw [firstFactor_eq_getElem_zero c h, ← hjp]
  exact hdeg
```

11-line `by` block. Differs from `lastFactor_natDegree_maximal` only
in:
* `i` is `⟨0, hpos⟩` (was `j := ⟨length - 1, by omega⟩`),
* `j'` plays the role of the universally-quantified index `i` (the
  hypothesis is `hp : p ∈ c.factors`, same as `lastFactor` side),
* the direction of the bound: `i.val ≤ j'.val` is `0 ≤ j'.val`,
  discharged by `Nat.zero_le _` (S4 needed `omega` for
  `i ≤ length - 1`),
* the final rewrite uses `firstFactor_eq_getElem_zero` (was
  `lastFactor_eq_getElem_pred`).

The `omega` call from S4 is replaced by a one-line `Nat.zero_le _` —
slightly cleaner proof. **Total LOC ≈ 11**, exactly matching S4's
`lastFactor_natDegree_maximal`.

### §3.4. `prodFactors_natDegree_ge_firstFactor_natDegree_mul`

```lean
/-- The natDegree of `prodFactors` is at least `factors.length` times
    the natDegree of `firstFactor`. Composes S3's
    `prodFactors_natDegree` (sum-of-degrees identity) with S6's
    `firstFactor_natDegree_minimal` (degree minimality among factors).

    Abstract counterpart of the matrix-level bound
    `k · deg(firstFactor M) ≤ deg(charpoly M)` (where `k` is the
    number of invariant factors and `firstFactor M` is the leading
    invariant divisor), the dual of S5's
    `prodFactors_natDegree_le_lastFactor_natDegree_mul`. Together
    with S5 gives a two-sided sandwich on `prodFactors.natDegree`. -/
theorem prodFactors_natDegree_ge_firstFactor_natDegree_mul
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.factors.length * c.firstFactor.natDegree ≤ c.prodFactors.natDegree := by
  rw [prodFactors_natDegree]
  -- Goal: factors.length * firstFactor.natDegree ≤ (factors.map natDegree).sum
  have h_bound : ∀ d ∈ c.factors.map (·.natDegree),
      c.firstFactor.natDegree ≤ d := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact firstFactor_natDegree_minimal c h hp
  have h_sum :
      (c.factors.map (·.natDegree)).length * c.firstFactor.natDegree
        ≤ (c.factors.map (·.natDegree)).sum :=
    nat_list_sum_ge_length_mul_of_all_ge _ _ h_bound
  rwa [List.length_map] at h_sum
```

~12-line `by` block, mirroring S5's
`prodFactors_natDegree_le_lastFactor_natDegree_mul` step-by-step
with the direction of every bound reversed. Uses the new
auxiliary `nat_list_sum_ge_length_mul_of_all_ge` (see §5).

---

## §4. Mathlib API audit (v4.26.0 pinned rev)

The S6 proofs rely on five Mathlib API names. The first three are
already used by the in-tree S4 lemmas — no audit needed beyond
"don't break what S4 broke last time" (see memory: **"List.length_pos.mpr
drift v4.26"**). The last two are the new pieces introduced by `head?`.

| Name | Used in | S4 precedent | Status |
|------|---------|--------------|--------|
| `length_pos_of_ne_nil` | §3.0, §3.3 | in-tree (private, line 331) | OK — already used by S4. |
| `List.mem_iff_getElem` | §3.3 | in-tree (used in S4's `lastFactor_natDegree_maximal`) | OK — same module. |
| `List.getElem_mem` | §3.1 | in-tree (used in S4's `lastFactor_mem`) | OK — same module. |
| `List.head?_eq_head` | §3.0 | **new for S6** | **Audit needed.** Symmetric counterpart to `List.getLast?_eq_getLast`. Expected signature: `(h : l ≠ []) → l.head? = some (l.head h)`. |
| `List.head_eq_getElem` | §3.0 | **new for S6** | **Audit needed.** Symmetric counterpart to `List.getLast_eq_getElem`. Expected signature: `(h : l ≠ []) → l.head h = l[0]'(length_pos_of_ne_nil h)` (or possibly with reversed equality). |

**Audit method** (without running `lake build`): search Mathlib source
via `gh api -X GET search/code -f q='List.head?_eq_head'` and verify
the name + signature. If `List.head_eq_getElem` is named differently
in v4.26.0 (e.g. `List.getElem_zero_of_ne_nil`, `List.head_eq_getElem_zero`),
the implementer should:

1. Check the actual name with `gh api -X GET search/code -f q='head_eq_getElem repo:leanprover-community/mathlib4'`.
2. If a 2-line `rcases l with _ | ⟨a, t⟩` fallback works (it always
   does — `head (a :: t)` is definitionally `a`, and `(a :: t)[0]`
   is also definitionally `a`), use that instead. **No proof depends
   on the exact Mathlib API name** — only convenience.

Memory rule: **never trust pre-v4.x lemma names to survive drift**.
Plan B is always definitionally available.

**Plan-B 2-line proof of `firstFactor_eq_getElem_zero`** (if the
Mathlib names drift):

```lean
private theorem firstFactor_eq_getElem_zero
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor = c.factors[0]'(length_pos_of_ne_nil h) := by
  rcases hl : c.factors with _ | ⟨a, t⟩
  · exact absurd hl h
  · rfl
```

Three-line `rcases` body, no Mathlib API dependency. This is the
fallback; **use it directly if there's any doubt**.

---

## §5. Auxiliary helper — `nat_list_sum_ge_length_mul_of_all_ge`

S6's `prodFactors_natDegree_ge_firstFactor_natDegree_mul` requires
the **lower-bound mirror** of the auxiliary helper S5 added:

```lean
/-- Auxiliary `Nat`-arithmetic helper: a sum over a list of naturals
    is at least the length times any common lower bound. Pure `Nat`
    induction; no `Polynomial` content. Mirror of
    `nat_list_sum_le_length_mul_of_all_le`. -/
private theorem nat_list_sum_ge_length_mul_of_all_ge
    (l : List ℕ) (m : ℕ) (h : ∀ d ∈ l, m ≤ d) :
    l.length * m ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    have h_a : m ≤ a := h a List.mem_cons_self
    have h_tail : ∀ d ∈ tail, m ≤ d :=
      fun d hd => h d (List.mem_cons_of_mem _ hd)
    have h_ih : tail.length * m ≤ tail.sum := ih h_tail
    -- Goal: (a :: tail).length * m ≤ (a :: tail).sum
    --     = (tail.length + 1) * m ≤ a + tail.sum
    simp only [List.sum_cons, List.length_cons]
    calc (tail.length + 1) * m
        = m + tail.length * m := by ring
      _ ≤ a + tail.sum := Nat.add_le_add h_a h_ih
```

10-line `induction` body, structurally identical to
`nat_list_sum_le_length_mul_of_all_le` (in-tree, lines 412–427) with
both inequalities flipped. The `ring` rewrite of
`(tail.length + 1) * m = m + tail.length * m` mirrors S5's
`(tail.length + 1) * M` rewrite; the direction of `Nat.add_le_add`
flips because the bound now flows `lower-bound on summand` ⇒ `lower
bound on sum`.

**Reusable beyond the use site** — same as the S5 helper, this is
generic over `(l : List ℕ) (m : ℕ)` and could move to a general
`Mathlib.Data.List.Sum` helpers file later. For now, scope it
`private` to `MinpolyCharpolyOQ03.lean` (matches S5 convention).

---

## §6. Two-sided sandwich corollary (optional, not S6 deliverable)

Once S6 lands, the corollary

```lean
/-- Two-sided sandwich on `prodFactors.natDegree`: composes S5's upper
    bound with S6's lower bound. -/
theorem prodFactors_natDegree_sandwich
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.factors.length * c.firstFactor.natDegree
      ≤ c.prodFactors.natDegree
      ∧ c.prodFactors.natDegree
          ≤ c.factors.length * c.lastFactor.natDegree :=
  ⟨prodFactors_natDegree_ge_firstFactor_natDegree_mul c h,
   prodFactors_natDegree_le_lastFactor_natDegree_mul c h⟩
```

is a 1-line term-mode trivium (a pair). **This is NOT part of S6's
deliverable** — including it inflates the theorem count without
adding mathematical content (both conjuncts are already public).
It is documented here only so the implementer doesn't accidentally
add it then have to remove it during review.

If a future iteration (S7+) wants the sandwich as a named API entry,
it should land separately with explicit justification — e.g. as a
public corollary used by OQ-03-OQ-04's matrix-level instantiation.

---

## §7. Anti-targets

Things S6 must NOT do:

1. **Do not modify** any S5 theorem statement (`prodFactors_natDegree_*`
   etc.). The `firstFactor`-side is a pure *addition*. Touching S5's
   statements would race PR #18182 (S5 ACT, build pending) and create
   a textual conflict.

2. **Do not add a `firstFactor`-vs-`lastFactor` divisibility lemma**
   (`firstFactor ∣ lastFactor`). True — it follows from the chain field
   with `i = 0`, `j = length - 1` — but it's S7+ material: it requires
   choosing a clean API surface for "the first dividing the last" and
   is not needed by either S5's or S6's coarse bounds.

3. **Do not add `firstFactor_natDegree_pos`** ("firstFactor has positive
   natDegree on a nonempty chain"). True — follows from
   `posDegree _ (firstFactor_mem c h)` — but it would clutter the §3.1
   block with one-line corollaries. Add it later if/when a caller
   actually needs it. (Mirror of "S4 did not ship `lastFactor_natDegree_pos`
   despite the same one-line proof being available.")

4. **Do not refactor `lastFactor_eq_getElem_pred`** to share a common
   helper with `firstFactor_eq_getElem_zero`. The two proofs use
   different index manipulations (`length - 1` vs `0`) and the
   sharing would be cosmetic. Keep them parallel.

5. **Do not add the `prodFactors_natDegree_sandwich` corollary** (see
   §6 — explicit anti-target with rationale).

6. **Do not change `lastFactor` to `firstFactor` anywhere in
   `rational_canonical_form_exists`'s statement** (the S1 sorry-bearing
   theorem at line 197). The matrix-level deliverable identifies
   `lastFactor = minpoly M` (not `firstFactor`), and any attempt to
   re-phrase the statement is option 2 of state.md's Next Action
   list — explicitly orthogonal to S6.

7. **Do not modify** `meta.json`, `annotations.json`, `index.ts`, or
   the parent's gallery integration. Those will be touched in the
   same PR that lands the Lean delta (theoremCount / lineCount bump).
   This PREP is doc-only and must remain so.

8. **Do not extend** `problem.md`, `state.md`, or `knowledge.md` from
   this branch. The state advance happens in the S6 ACT PR after the
   Lean file lands.

---

## §8. Honesty / scope discipline

* The four mirror lemmas are *structural completeness work*, not
  mathematical advances. They reduce **zero** sorries on
  `rational_canonical_form_exists` (which remains S1's sorry until
  OQ-03-OQ-02 / OQ-03-OQ-04 land).
* The "sandwich corollary" of §6 is folklore and trivial once both
  sides exist; flagging it is for symmetry, not novelty.
* The Mathlib API audit (§4) is essential: at v4.26.0 the `List.head?`
  API has had at least one rename pass since `List.length_pos`
  vanished (see memory). The fallback `rcases` proof of §4 is the
  insurance.
* S6 *does not* discharge any of state.md's option-4 firstFactor
  bullets beyond bullets 2 and 3 (membership/monicness, degree
  minimality, length×min bookkeeping). Option-4 bullet 1
  (`prodFactors_natDegree_eq_sum_natDegree_lastFactor_le_n`) requires
  `prodFactors = charpoly M`, which is the matrix-level
  instantiation; that's S7+ material, not S6.
* The estimated +50 LOC delta is conservative; the actual landing
  may be ~45–55 LOC depending on `ring`-vs-`linarith` formatting and
  whether the Plan-B 2-line `rcases` is used for §3.0.

---

## §9. No-edit guarantee

This PR creates **one new file**, in a **new subdirectory**:

```
research/problems/minpoly-charpoly-oq-03/sessions/2026-05-12-s06-prep-firstfactor-mirror-design.md
```

It does **not** touch:

* `proofs/Proofs/MinpolyCharpolyOQ03.lean` (the Lean source)
* `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` (the OQ-03-OQ-01 sub-slug,
  in-flight under different agents)
* `research/problems/minpoly-charpoly-oq-03/problem.md`
* `research/problems/minpoly-charpoly-oq-03/state.md`
* `research/problems/minpoly-charpoly-oq-03/knowledge.md` (does not
  currently exist — creating it would be a separate concern)
* `src/data/proofs/minpoly-charpoly-oq-03/meta.json`
* `src/data/proofs/minpoly-charpoly-oq-03/annotations.json`
* `src/data/proofs/minpoly-charpoly-oq-03/index.ts`
* `proofs/lakefile.toml` (no new imports needed)
* Any in-flight PR's headRefName surface area

Conflict-free with PR #18182 (S5 ACT) by construction: PR #18182
touches the Lean source and (if accompanied) gallery files; this PR
only adds a new file under `sessions/`, a directory that does not
currently exist. Conflict-free with PR #18407 (oq-02 S2 PREP) and
PR #17995 (oq-03-oq-01 SCAFFOLD, already merged) — those touch
different slugs entirely.

---

## §10. Implementer cheat-sheet

For the S6 ACT implementer, the exact insertion plan in
`MinpolyCharpolyOQ03.lean`:

1. **After line 172** (current `lastFactor` definition, end of
   `InvariantFactorChain` API block):

   ```lean
   /-- The first factor `p₁` of the chain — the structural minimum
       under the divisibility chain. Falls back to `1` for the empty
       chain (a degenerate case that does not arise for a nontrivial
       matrix). -/
   noncomputable def InvariantFactorChain.firstFactor
       (c : InvariantFactorChain F) : F[X] :=
     c.factors.head?.getD 1
   ```

2. **After line 385** (end of Part 5 / S4 `lastFactor` helpers):

   Add new `Part 5b` section header (mirroring Part 5's docstring)
   plus the four lemmas of §3: `firstFactor_eq_getElem_zero`
   (private), `firstFactor_mem`, `firstFactor_monic`,
   `firstFactor_natDegree_minimal`.

3. **After line 457** (end of Part 6 / S5 bound):

   Add `nat_list_sum_ge_length_mul_of_all_ge` (private) and then
   `prodFactors_natDegree_ge_firstFactor_natDegree_mul`.

Final file: ~509 lines, 15 public theorems (was 11), 5 private
auxiliary lemmas (was 4), 4 definitions (was 3). 1 unchanged `sorry`
(the S1 placeholder).

**Build status convention**: per the S4 / S5 precedent, land
build-pending in a single-shot PR. Title format:

> `research(minpoly-charpoly-oq-03): S6 ACT — firstFactor mirror helpers (build pending)`

PR body should cross-reference this design doc and the four mirror
lemmas explicitly.

---

## §11. Provenance & memory hooks

* **Predecessor design rationale**: state.md Next Action option 4
  bullet 2 — "firstFactor-side mirror lemmas" — locked at S5 land
  time by researcher-10 / researcher-3.
* **Symmetric-API precedent**: S4 (PR #18086, researcher-1) landed
  `lastFactor_mem` / `lastFactor_monic` / `lastFactor_natDegree_maximal`
  in a single PR; S6 follows the same shape on the dual side.
* **Pattern (memory)**:
  - "researcher-12 quintuple-PREP doc-only session (2026-05-12 ~17:30 UTC)"
    — doc-only `sessions/` PREP in new subdir is the safe orthogonal
    play when 1 open PR exists on the slug. This S6 PREP applies the
    same pattern: 1 open PR (S5 #18182), new file path, no shared
    surface area.
  - "List.length_pos.mpr drift v4.26" — applies directly to the
    `List.head?_eq_head` / `List.head_eq_getElem` audit in §4.
    Plan-B 2-line `rcases` is the insurance.
* **Anti-pattern avoided**: "Write tool absolute-path routes to main
  repo, not worktree" — this file is created via worktree-relative
  path under `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/`
  `researcher-12/research/problems/minpoly-charpoly-oq-03/sessions/`
  to ensure it lands in the worktree's working tree, not the main
  repo's stale tree. Verified by `git rev-parse --show-toplevel`
  before write.
