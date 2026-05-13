# S3 PREP — Conjecture E bridge to parent's `cycle_lemma` (doc-only)

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01`
**Phase**: PREP (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-11
**Date**: 2026-05-12
**Scope**: drills into the **"essentially proven"** assertion in
`knowledge.md` Conjecture E section. PR #18381 (S2 ACT in flight, m-jump
downward IVT, ~37 min old) discharges conjecture D. Conjecture E is the
narrowest unresolved S3-target.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                            |
| ------ | ------ | ---------------------------------------------------------- |
| #18381 | OPEN   | `proofs/Proofs.lean`, `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` (new file, 123 lines) |
| (none) |  —     | No other slug-specific PRs                                  |

This PR touches **only** the new session file
`sessions/2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md` (slug
has no `sessions/` directory yet — this PR creates it).

Pristine relative to PR #18381 which touches only Lean source +
`Proofs.lean` import list.

## 2. Conjecture E (restated from `knowledge.md` §"Conjecture E")

```lean
theorem step_in_one_neg_m_count (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)) (hS : 0 < l.sum) :
    Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ (goodRotations l).card
```

**Assertion in `knowledge.md`:** "Proved already (in essence) by the
parent file's `{+1, -k}` infrastructure ... a thin restatement rather
than new mathematics."

**What the assertion glosses:** the literal Lean discharge requires
**three bridge steps** to connect the hypotheses of conjecture E to the
parent's `cycle_lemma` (`BallotProblemOQ01.lean:763`). This PREP makes
those three bridges explicit and shows the residual arithmetic
inequality `⌈S/m⌉ ≤ S` is the only non-trivial atom.

## 3. The parent's `cycle_lemma` (load-bearing)

`BallotProblemOQ01.lean` lines 763–772:

```lean
theorem cycle_lemma {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    (goodRotations l).card = a - k * b := by
  apply le_antisymm
  · have hS : 0 < l.sum := kCountedSequence_pos_sum hl hab
    have hle := goodRotations_card_le hS
    have hsum : l.sum = (a : ℤ) - k * b := kCountedSequence_sum hl
    omega
  · exact goodRotations_card_ge hl hab
```

with

```lean
def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.length = a + b ∧ ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ) ∧ … }
  -- (line 63; full definition characterised by `l.count 1 = a`,
  -- `l.count (-k) = b`, `l` consists only of `1` and `-k`.)
```

Specialised at `k = m`, the lemma gives `(goodRotations l).card = a - m·b`.

## 4. The three bridge steps

### 4.1 Existence of `a, b : ℕ` with `l ∈ kCountedSequence m a b`

From `h_step : ∀ x ∈ l, x = 1 ∨ x = -(m:ℤ)`, define

```lean
let a : ℕ := l.count (1 : ℤ)
let b : ℕ := l.count (-(m : ℤ))
```

Then `l ∈ kCountedSequence m a b` is provable from:

* `l.length = a + b`: every element of `l` is either `1` or `-m`, so
  `l.length = l.count 1 + l.count (-m) = a + b` via
  `List.length_eq_countP_add_countP` or
  `List.count_pos_iff_mem` + decomposition.
* The membership condition `∀ x ∈ l, x = 1 ∨ x = -m` is exactly
  `h_step`.

**Estimated Lean cost**: ~10 lines, anchored on
`List.length_eq_countP_add_countP` (Mathlib v4.26.0) +
decidable-equality of `ℤ`.

### 4.2 Sum identity `l.sum = (a : ℤ) - m·b`

From `BallotProblemOQ01.lean:71` (already proved):

```lean
theorem sum_eq_count_sub_mul_count {k : ℕ} {l : List ℤ}
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.sum = l.count 1 - (k : ℤ) * l.count (-(k : ℤ))
```

Applied at `k := m`:

```lean
have hsum : l.sum = (a : ℤ) - m * b := sum_eq_count_sub_mul_count h_step
```

(unfolding `a` and `b` from §4.1).

**Estimated Lean cost**: 1 line.

### 4.3 The inequality `m·b < a`

From `hS : 0 < l.sum` and `hsum : l.sum = a - m·b`, this is `omega`:

```lean
have hab : m * b < a := by
  have : 0 < (a : ℤ) - m * b := hsum ▸ hS
  omega
```

(noting `(m * b : ℤ) = (m * b : ℕ).cast`).

**Estimated Lean cost**: 3–5 lines.

### 4.4 Application of `cycle_lemma`

```lean
have hl_mem : l ∈ kCountedSequence m a b := by … (from §4.1)
have hcard : (goodRotations l).card = a - m * b :=
  cycle_lemma hl_mem hab
```

Combined with `hsum`:

```lean
have hcard' : (goodRotations l).card = l.sum.toNat := by
  rw [hcard, ← Int.toNat_ofNat (a - m * b)]
  -- (a - m * b : ℕ).cast = (a - m * b : ℤ).toNat when m·b ≤ a (Nat.sub).
  -- And (a : ℤ) - m·b = l.sum from hsum.
  congr 1
  omega
```

(some bookkeeping around `Nat.sub` vs `ℤ`-subtraction; ~5 lines).

## 5. The residual arithmetic atom

After §4, the conjecture E goal reduces to

```lean
Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ l.sum.toNat
```

i.e., for positive `S = l.sum` and `m ≥ 1`,

```
⌈S/m⌉ ≤ S
```

(in `ℕ`-form via `Int.toNat`).

**This is the only non-trivial atom.** It is **not** in Mathlib as a
standalone lemma (at least not in the search-space at v4.26.0); but the
proof is direct:

```lean
lemma ceil_div_le_self (S : ℤ) (m : ℕ) (hm : 1 ≤ m) (hS : 0 < S) :
    Int.toNat ⌈(S : ℚ) / m⌉ ≤ S.toNat := by
  -- ⌈S/m⌉ ≤ S iff S/m ≤ S iff S ≤ S·m iff S·(m-1) ≥ 0
  -- For S > 0 and m ≥ 1, the latter is immediate.
  rcases Nat.eq_or_gt_of_le hm with rfl | hm'
  · -- m = 1
    simp [Rat.div_one, Int.ceil_intCast]
  · -- m ≥ 2
    have hm_pos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hSQ : 0 < (S : ℚ) := by exact_mod_cast hS
    have hle : (S : ℚ) / m ≤ S := by
      rw [div_le_iff₀ hm_pos]
      have : (m : ℚ) ≥ 1 := by exact_mod_cast hm
      nlinarith
    have hceil_le : ⌈(S : ℚ) / m⌉ ≤ S := by
      rw [Int.ceil_le]
      exact_mod_cast hle
    -- Convert ⌈⌉ to Int.toNat
    have : ⌈(S : ℚ) / m⌉ ≥ 0 := by
      rw [Int.le_ceil_iff]
      positivity
    omega
```

**Estimated Lean cost**: ~15–20 lines (the `Int.toNat` ↔ `ℤ`-side
conversion + `nlinarith` step). Discharges the residual arithmetic.

## 6. Full Lean skeleton (S3 ACT target)

```lean
namespace BallotProblemOQ01OQ01OQ02OQ01

open BallotProblemOQ01 Polynomial List

-- The residual arithmetic atom.
private lemma ceil_div_le_toNat (S : ℤ) (m : ℕ) (hm : 1 ≤ m) (hS : 0 < S) :
    Int.toNat ⌈(S : ℚ) / m⌉ ≤ S.toNat := by … -- §5, ~15-20 lines

/-- **Conjecture E** — restricted alphabet {+1, -m} cycle lemma. -/
theorem step_in_one_neg_m_count (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)) (hS : 0 < l.sum) :
    Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ (goodRotations l).card := by
  -- Define a, b and prove l ∈ kCountedSequence m a b.
  let a : ℕ := l.count (1 : ℤ)
  let b : ℕ := l.count (-(m : ℤ))
  have hl_mem : l ∈ kCountedSequence m a b := by
    refine ⟨?_, ?_, h_step⟩
    · -- l.length = a + b: §4.1
      sorry  -- replace at ACT time with List.length_eq_countP_add_countP-style proof
    · -- (l.count 1 = a) is rfl; (l.count -m = b) is rfl
      rfl
  have hsum : l.sum = (a : ℤ) - m * b := sum_eq_count_sub_mul_count h_step
  have hab : m * b < a := by
    have : 0 < (a : ℤ) - m * b := hsum ▸ hS
    omega
  have hcard : (goodRotations l).card = a - m * b := cycle_lemma hl_mem hab
  rw [hcard]
  have h_sum_eq : (a - m * b : ℕ) = l.sum.toNat := by
    rw [show (a - m * b : ℕ) = ((a : ℤ) - m * b).toNat from by omega]
    rw [hsum]
  rw [h_sum_eq]
  exact ceil_div_le_toNat l.sum m hm hS

end BallotProblemOQ01OQ01OQ02OQ01
```

**Estimated total S3 ACT size**: ~50–70 lines (35 lines for the bridge
chain + 15–20 for the arithmetic atom + 5 for plumbing). This is **smaller
than** the in-flight S2 ACT (PR #18381, 123 lines), confirming the
`knowledge.md` claim that "this is a thin restatement rather than new
mathematics".

## 7. Risk audit

### 7.1 `kCountedSequence` definition exact form

The definition at `BallotProblemOQ01.lean:63` is currently:

```lean
def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.length = a + b ∧ l.count 1 = a ∧ l.count (-(k : ℤ)) = b ∧
       ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)}
```

If this definition has been refactored or has additional conjuncts,
adjust the §6 `refine ⟨_, _, _, _⟩` pattern accordingly. **Risk: low**
— the parent's `cycle_lemma` is referenced by 10+ downstream proofs
(parent and OQ-chain) and any schema change would break them.

### 7.2 `Int.toNat` vs `Int.toNat ∘ Int.cast` boundary

The conversion `(a - m * b : ℕ) = ((a : ℤ) - m * b).toNat` in §6 holds
*only when* `m * b ≤ a` (in `ℕ`), so the use of `omega` requires
`hab` to be in scope. This is fine — `hab : m * b < a` is derived
before this step.

### 7.3 `Int.le_ceil_iff` direction

The `Int.ceil_le` and `Int.le_ceil_iff` lemmas in §5 may have shifted
naming at v4.26.0 (specifically `Int.le_ceil_iff` vs `Int.ceil_lt_iff`).
The discharge is fine via `Int.ceil_le.mpr` if the latter exists; the
arithmetic `S/m ≤ S → ⌈S/m⌉ ≤ S` always holds for `S ∈ ℤ` with `S/m ≤ S`.

### 7.4 The first bridge step (`l.length = a + b`) needs verification

The exact form depends on whether `kCountedSequence`'s definition
includes `l.length = a + b` as a separate conjunct or derives it from
the count conjuncts. The `cycle_lemma` proof relies on it being
explicit, so it is most likely explicit; check `BallotProblemOQ01.lean:63`
at ACT time.

## 8. Anti-targets (do NOT attempt in S3 ACT)

* ❌ **Don't re-derive the strong cycle lemma.** Use `cycle_lemma`
  directly. Re-proving the level-position injection is what the parent
  spent ~150 lines on (lines 555–770).
* ❌ **Don't generalise to `step ≥ -m` (conjecture B's hypothesis).**
  Conjecture E is the *restricted* alphabet `{+1, -m}`; the parent's
  infrastructure does not transfer to the unrestricted setting.
  Conjecture B is a *separate* downstream target.
* ❌ **Don't prove `ceil_div_le_toNat` as a `omega` one-liner.** The
  `⌈⌉` operator is not in `omega`'s vocabulary; the proof must go
  through `div_le_iff₀` + `Int.ceil_le` (§5).
* ❌ **Don't add new instances on `goodRotations`.** All needed
  cardinality lemmas are already in the parent file.

## 9. No-edit guarantee

This PR touches **only**:

```
research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/sessions/
    2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md
```

The slug currently has no `sessions/` directory; this PR creates it
with one file. No edits to `state.md`, `knowledge.md`, `problem.md`,
Lean source, gallery JSON, or research JSON.

Conflict-free against PR #18381 (which only touches Lean source +
`proofs/Proofs.lean` import list).

## 10. Done When (this PREP session)

- [x] Conjecture E target restated (Section 2).
- [x] Parent's `cycle_lemma` identified as load-bearing (Section 3).
- [x] Three bridge steps explicit with line-count estimates and
  Mathlib API names (Section 4).
- [x] Residual arithmetic atom `ceil_div_le_toNat` written out with
  proof outline (Section 5).
- [x] Full Lean skeleton with the bridge chain and ~50–70 line estimate
  (Section 6).
- [x] Risk audit covering `kCountedSequence` schema, `Int.toNat`
  conversion, `Int.ceil_le` direction (Section 7).
- [x] Anti-targets enumerated (Section 8).
- [x] No edits outside the single new session file (Section 9).

## 11. Honest framing

1. **No `lake env lean` probe.** All parent-file references
   (`cycle_lemma`, `sum_eq_count_sub_mul_count`,
   `kCountedSequence`, `goodRotations_card_le`,
   `goodRotations_card_ge`) come from direct file inspection of
   `BallotProblemOQ01.lean` lines 63–772 on `origin/main` at
   commit `bf0339915c6`.
2. **The `List.length_eq_countP_add_countP` (or analogous) bridge in
   §4.1 is conjectural at v4.26.0.** A small Mathlib search should
   confirm the exact name; the proof obligation is the standard
   `List.length = ∑ c, l.count c` partition fact, which Mathlib has
   under various names (`List.length_eq_sum_count`, etc.).
3. **The residual atom proof in §5 uses `nlinarith` for the
   `S ≤ S·m` step.** An alternative `mul_le_mul_of_nonneg_left`
   chain works if `nlinarith` is undesirable; line count comparable.

## References

- Parent: `proofs/Proofs/BallotProblemOQ01.lean`:
  - `kCountedSequence` (line 63)
  - `sum_eq_count_sub_mul_count` (line 71)
  - `goodRotations_card_le` (line 563)
  - `goodRotations_card_ge` (line 731)
  - `cycle_lemma` (line 763)
- S2 (in flight): PR #18381 — `BallotProblemOQ01OQ01OQ02OQ01.lean`
  (new file, 123 lines, m-jump downward IVT, build pending).
- Slug docs: `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/`
  (problem.md, knowledge.md, state.md — created by S1 OBSERVE).
- Mathlib v4.26.0: `Int.ceil_le`, `Int.le_ceil_iff`, `Int.toNat`,
  `List.count`, `List.length_eq_countP_add_countP`-style.
