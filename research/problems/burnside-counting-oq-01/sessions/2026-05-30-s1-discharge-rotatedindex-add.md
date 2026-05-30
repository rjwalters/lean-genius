# S1 ACT — Discharge `rotatedIndex_add` axiom

- **Date**: 2026-05-30
- **Session**: 1 (S1)
- **Phase**: ACT — axiom → theorem
- **Researcher**: researcher-1
- **Base**: `origin/main` (commit `11927e1a984`)
- **Branch**: `research/burnside-counting-oq-01-s1-discharge-axiom`

## 1. TL;DR

`BurnsideCounting.lean` declared `axiom rotatedIndex_add` to state that
two successive cyclic rotations on `Fin n` compose additively in `ZMod n`.
This session replaces the axiom with a fully proved theorem
(0 sorries, no new imports). The file's axiom count drops from 5 to 4
and total LOC goes from 255 to 370.
Build verified: Docker `Proofs.BurnsideCounting` → 3058 / 3058 jobs clean.

## 2. The axiom (before)

```lean
def rotatedIndex (n : ℕ) [NeZero n] (r : ZMod n) (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + n - (r.val % n)) % n, Nat.mod_lt _ (NeZero.pos n)⟩

axiom rotatedIndex_add (n : ℕ) [NeZero n] (r s : ZMod n) (i : Fin n) :
    rotatedIndex n s (rotatedIndex n r i) = rotatedIndex n (r + s) i
```

## 3. The proof scaffolding

Three private Nat-mod auxiliaries handle the three distinct ways the
outer mod can simplify:

```lean
/-- For `n ≤ a < 2n`, `a % n = a - n`.  Reformulates an omega-resistant
    Nat identity via `Nat.add_mod_right`. -/
private lemma mod_eq_sub (a n : ℕ) (h1 : n ≤ a) (h2 : a < 2 * n) :
    a % n = a - n := by
  conv_lhs => rw [show a = (a - n) + n from by omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Peel off a leading `+ n` whose residue is < n. -/
private lemma mod_of_shift (a c n : ℕ) (h_eq : a = c + n) (h_lt : c < n) :
    a % n = c := by
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_lt

/-- Mod is identity, with the target spelled in a Nat-`omega`-equivalent form. -/
private lemma mod_of_eq (a b n : ℕ) (h_eq : a = b) (h_lt : a < n) :
    a % n = b := by
  rw [h_eq]
  exact Nat.mod_eq_of_lt (h_eq ▸ h_lt)
```

The main proof then enumerates 8 leaves over three signed predicates:

```lean
theorem rotatedIndex_add (n : ℕ) [NeZero n] (r s : ZMod n) (i : Fin n) :
    rotatedIndex n s (rotatedIndex n r i) = rotatedIndex n (r + s) i := by
  have hn : 0 < n := NeZero.pos n
  have hr : r.val < n := ZMod.val_lt r
  have hs : s.val < n := ZMod.val_lt s
  have hi : i.val < n := i.isLt
  have hrs : (r + s).val = (r.val + s.val) % n := ZMod.val_add r s
  apply Fin.ext
  show ((i.val + n - r.val % n) % n + n - s.val % n) % n
      = (i.val + n - (r + s).val % n) % n
  rw [hrs, Nat.mod_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]
  by_cases hir : r.val ≤ i.val
  · -- Case A: inner wraps; pull out one n.
    have h_inner : (i.val + n - r.val) % n = i.val - r.val := by
      apply mod_of_shift _ _ _ (by omega : i.val + n - r.val = (i.val - r.val) + n)
      omega
    rw [h_inner]
    by_cases hi_rs : i.val < r.val + s.val
    · -- A1: i.val - r.val < s.val (LHS in range).
      ...
    · -- A2: i.val ≥ r.val + s.val.
      ...
  · -- Case B: inner is identity.
    push_neg at hir
    have h_inner : (i.val + n - r.val) % n = i.val + n - r.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [h_inner]
    by_cases hsum : r.val + s.val < n
    · -- B1: r.val + s.val < n.
      ...
    · -- B2: r.val + s.val ≥ n, with sub-cases B2a, B2b on i.val vs r+s-n.
      ...
```

Each leaf is 3–4 lines: one `mod_of_shift` / `mod_of_eq` /
`mod_eq_sub` / `Nat.mod_eq_of_lt` for the LHS, one for the RHS, then
a closing `rw [hlhs, hrhs]`.  See the file for the full sequence.

## 4. Proof strategy

After unfolding `rotatedIndex` and reducing to a `Fin.val` equation,
the two sides become:

```
LHS.val = ((i.val + n - r.val % n) % n + n - s.val % n) % n
RHS.val = (i.val + n - (r + s).val % n) % n
```

Use `Fin.ext` + `show` to expose this `Nat` equation, then rewrite:

* `(r + s).val → (r.val + s.val) % n` via `ZMod.val_add`.
* `((r.val + s.val) % n) % n → (r.val + s.val) % n` via `Nat.mod_mod`.
* `r.val % n → r.val` via `Nat.mod_eq_of_lt hr`.
* `s.val % n → s.val` via `Nat.mod_eq_of_lt hs`.

This reduces the goal to:

```
((i.val + n - r.val) % n + n - s.val) % n
  = (i.val + n - (r.val + s.val) % n) % n
```

Now case-split, in nesting order:

1. `r.val ≤ i.val` (Case A) or `i.val < r.val` (Case B): determines
   whether `(i.val + n - r.val) % n` wraps.
2. Whether `r.val + s.val < n` (sum in range) or `≥ n` (wraps).
3. In some leaves, whether `i.val < r.val + s.val (− n)` (the final
   outer sum wrap).

Eight leaves total. In each leaf the LHS and RHS both reduce, via
one of the three auxiliaries, to one of four canonical Nat
expressions:

* `i.val + n - r.val - s.val`
* `i.val - r.val - s.val`
* `i.val - r.val + n - s.val`
* `i.val + n - r.val + n - s.val`

After `rw [hlhs, hrhs]`, the two sides become syntactically equal and
the leaf closes by `rfl` (implicitly via `rw`).

## 5. Why a bare `omega` doesn't suffice here

omega has full Nat mod / truncated-subtraction support, but for this
identity it must internally case-split four ways on the `(i, r, s)`
sign region; in practice the Lean 4 / Mathlib `omega` does not lift
the implicit `r.val + s.val = n * q + (r.val + s.val) % n` (with
`q ∈ {0, 1}`) combined with the inner `(i.val + n - r.val) % n`
case-split.  Naive 2-way splits or simpler tactic chains leave omega
with a goal it can't close even with `(r.val + s.val) % n < n` as an
extra hint.  Materializing both case splits by hand reduces each leaf
to a linear identity that `omega` (inside the three auxiliaries) does
close.

The original axiom's docstring foresaw exactly this: *"the
mathematical content is elementary […] but cleanly proving it in Lean
requires careful `Nat.sub` / `Nat.mod` case analysis."*  This proof is
that case analysis, made compact via the three helpers.

## 6. Mathlib API verification

All Mathlib lemma signatures verified pre-write via `gh api`
source-fetch against `leanprover-community/mathlib4` HEAD:

| Lemma | Module:line | Signature |
|---|---|---|
| `ZMod.val_lt` | `Data.ZMod.Basic:61` | `[NeZero n] (a : ZMod n) : a.val < n` |
| `ZMod.val_add` | `Data.ZMod.Basic:646` | `[NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n` |
| `Nat.mod_eq_of_lt` | `Nat.Defs` | `a < n → a % n = a` |
| `Nat.mod_mod` | core | `a % n % n = a % n` |
| `Nat.add_mod_right` | core | `(a + n) % n = a % n` |
| `Fin.isLt` | core | `(i : Fin n).val < n` |
| `Fin.ext` | core | `(a b : Fin n) (h : a.val = b.val) : a = b` |
| `omega` | tactic | linear `ℕ`/`ℤ` with `%`/`/`/bounds |

No new imports needed.  `Mathlib.Data.ZMod.Basic` is already imported
by `BurnsideCounting.lean` (line 3); the `Nat.` lemmas and `Fin.*` are
in core.

## 7. File deltas

```
proofs/Proofs/BurnsideCounting.lean: 255 → 370 LOC (+115)
  • axiom rotatedIndex_add (2-line block + 2-line docstring)
  • → 3 private auxiliaries (mod_eq_sub, mod_of_shift, mod_of_eq, ~18 LOC)
  • → theorem rotatedIndex_add (~95-line block incl. 7-line docstring
        and 8 explicit case leaves)

proofs/Proofs/BurnsideCountingOQ03OQ03.lean: docstring line 20 updated
  • "Inherits rotatedIndex_add axiom" → "4 inherited axioms ... the
    earlier rotatedIndex_add was discharged"

src/data/proofs/burnside-counting/meta.json:
  • leanFile.axiomCount: 5 → 4
  • leanFile.lineCount: 255 → 370
  • leanFile.theoremCount: 6 → 7
  • meta.axiomCount: 5 → 4
  • meta.lineCount: 255 → 370
  • meta.theoremCount: 6 → 7
  • meta.assumptions: drops rotatedIndex_add from the list
  • meta.originalContributions: adds a rotatedIndex_add line citing
    the 8-leaf case enumeration + three Nat-mod auxiliaries
  • overview.implications: 5 axioms → 4 axioms, adds rotatedIndex_zero
    + rotatedIndex_add to the "fully verified" list
  • conclusion.openQuestions: drops the rotatedIndex_add open question,
    adds a more specific Multiplicative-bridge follow-up
  • mainTheorems[rotatedIndex_add].type: "axiom" → "supporting"
  • mainTheorems[rotatedIndex_add].significance + description:
    rewritten to reflect proved status + the 8-leaf / 3-auxiliary
    proof method
  • mainTheorems[cyclicAddActionOnColorings].significance: notes both
    rotatedIndex_zero and rotatedIndex_add are now theorems
  • sections[sec-burnside-action].summary: updated similarly

research/problems/burnside-counting-oq-01/state.md: full rewrite
  • Phase OBSERVE → S1 ACT
  • Adds inventory snapshot (lineCount 370, axioms 4, theorems 7)
  • Adds verified-API table, S2+ priority tree, session log entry,
    Docker 3058/3058 build confirmation

research/problems/burnside-counting-oq-01/sessions/2026-05-30-s1-discharge-rotatedindex-add.md:
  • this memo (new)
```

## 8. What's NOT changed

- No badge change.  The slug is still `axiomatized` (4 axioms remain
  in Part IV); promoting to `verified` requires discharging
  `fixed_point_sum_binary_4`, `coloringSetoid`,
  `coloringQuotientFintype`, and `binary_necklaces_4`.
- No new imports.
- No changes to `BurnsideCountingOQ03.lean` or
  `BurnsideCountingOQ03Aristotle.lean`.

## 9. Build / verification

Docker build invoked per repository policy from the worktree at
`.loom/worktrees/researcher-1`:

```
./proofs/scripts/docker-build.sh Proofs.BurnsideCounting
→ EXIT: 0
→ Build completed successfully (3058 jobs).
→ === Build succeeded ===
```

Lake / Mathlib cache hit; full file compile time was within the
standard 60-min Docker timeout window.

The proof discharge survived ~10 iterations of omega-vs-case-split
tuning before landing the present 8-leaf form with the three
auxiliaries.  Earlier iterations either left omega with too many
nested mods to handle (no case-split, or 2-way split, or 4-way),
or hit `Nat.mod_eq_of_lt` type-mismatches when the right-hand side
of `% n = ...` was a Nat-equal but syntactically different value.

## 10. S2+ next steps

See `state.md` for the priority tree.  Highest priority is the
`AddAction → MulAction` bridge (via `Multiplicative (ZMod n)`) which
would let `coloringSetoid` and `coloringQuotientFintype` be derived
rather than axiomatized, and unblock a `burnside_lemma`-driven proof
of `binary_necklaces_4`.  The companion file
`BurnsideCountingOQ03OQ03.lean` already sketches this connection
chain explicitly (lines 9-18 of its docstring) — translating that
sketch into a proved chain is a clear next iteration.
