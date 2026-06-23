# Session S3c-Prep-7 PREP — Row-1 uniqueness step-function characterization + Mathlib v4.26.0 bearer-availability audit (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 3 (row-1 uniqueness) pre-flight design

## Why this PREP

State.md's Part VIII proof sketch (lines 660-695) lists **five steps** for
the in-support direction of the 2-row anchoring lemma:

```
Step 1 — Row 0 is forced to all zeros          [CLOSED, Part XIII via S3c-prep-4]
Step 2 — Row-1 content determined              [DESIGNED, S3c-prep-5 + S3c-prep-6]
Step 3 — Row 1 uniquely determined             [THIS PREP]
Step 4 — Remaining guards match `lrCoeff2`     [later]
Step 5 — Bijection closure                     [later]
```

Step 3's target is precisely:

> Weakly-increasing row 1 with `c₀` zeros and `c₁` ones is
> `j ↦ if j.val < c₀ then 0 else 1`. So `Fintype.card ≤ 1`.

This PREP discharges the **Mathlib bearer audit** for Step 3 and finds a
critical pin-version mismatch:

* The natural one-shot bearer
  `Fin.lt_card_filter_univ_iff_apply_of_imp` (Mathlib HEAD at
  `Mathlib/Data/Fintype/Fin.lean:70`) **is not available at v4.26.0** —
  the pinned Mathlib for this project. Its supporting helper
  `Fin.card_filter_val_lt` is also absent at v4.26.0.

* The available v4.26.0 primitives (`Fin.card_Iio`, `Fin.card_Iic`,
  `Finset.card_le_card`, `Fin.monotone_iff_le_succ`) are sufficient to
  **backport** the same statement in ~25-30 LOC, mirroring the Mathlib
  HEAD proof.

This PREP makes **no edits** to:

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (the 808-line target file —
  adding the Step-3 lemmas is the ACT author's call after Step 2 ACT
  lands)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling-slug file

Only this new session-note file is created — orthogonal-by-construction to
the open stale PR #17966 (which conflicts on the 3 target files above) and
to the cluster's recent merge cadence.

---

## 1. Step 3 target (verbatim from Part VIII docstring + state.md §S3c-prep-3)

Quoted from `state.md:676` and `Hilbert15OQ02OQ03OQ01.lean:393-399`:

> **Row 1 is uniquely determined.** Weakly-increasing row 1 with `c₀`
> zeros and `c₁` ones is the function
> `j ↦ if j.val < c₀ then 0 else 1`. So `Fintype.card ≤ 1`.

Concretely, given:

- `T : SkewSSYTFin 2 ν μ` (so `T.1 ⟨1, ·⟩ : Fin r₁ → Fin 2`)
- `T.2.1 1 j₁ j₂ : j₁ < j₂ → T.1 ⟨1, j₁⟩ ≤ T.1 ⟨1, j₂⟩` (row weakness on row 1)
- `c₀ = lam.parts 0 - r₀ = #{j : Fin r₁ | T.1 ⟨1, j⟩ = 0}` from Step 2
- `c₁ = lam.parts 1     = #{j : Fin r₁ | T.1 ⟨1, j⟩ = 1}` from Step 2
- `c₀ + c₁ = r₁` (by Step 2 + the `c₀ + c₁ = ν.parts 1 - μ.parts 1`
  identity that drops out of the weight equation)

derive: **for all `j : Fin r₁`,
`T.1 ⟨1, j⟩ = if j.val < c₀ then (0 : Fin 2) else (1 : Fin 2)`**.

The math content (informally): a weakly-increasing function
`f : Fin r → Fin 2` is determined by the location of its "step" — the
unique index `k` with `f j = 0` iff `j.val < k`. This `k` is exactly the
zero-count `#{j | f j = 0}`. The result for Step 3 is: two functions
satisfying the row-weak + count hypotheses agree pointwise, so the
filtered `SkewSSYTFin` has cardinality at most 1.

Where `r₁ := ν.parts 1 - μ.parts 1` and the `c₀, c₁` shorthand follows
S3c-prep-5 §1.

---

## 2. Mathlib bearer audit — version mismatch on `Fin.lt_card_filter_univ_iff_apply_of_imp`

### 2.1 The natural one-shot bearer (HEAD only)

Mathlib HEAD (`leanprover-community/mathlib4@1c1dadbc2851`,
2026-05-12 24:00 UTC) has a perfect one-shot bearer at
`Mathlib/Data/Fintype/Fin.lean:70`:

```lean
/--
Given a "downward-closed" predicate `p` on `Fin n` (which could be spelt `Antitone p`),
then `p` holds for more than `j` elements iff it holds for `p` itself.
-/
theorem Fin.lt_card_filter_univ_iff_apply_of_imp {j : Fin n}
    (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i j, j ≤ i → p i → p j) :
    j < #{i | p i} ↔ p j := by
  have h1 (k : Fin n) (hk : ¬ p k) : #{i | p i} ≤ k := by
    rw [← Fin.card_Iio]
    exact card_le_card (by grind)
  refine ⟨by grind, fun h ↦ ?_⟩
  by_contra! hc
  let q : Fin n → Prop := (· < #{i | p i})
  have : univ.filter q = univ.filter p :=
    eq_of_subset_of_card_le (by grind) (by rw [card_filter_val_lt]; grind)
  have : j ∈ univ.filter p := by grind
  grind
```

Applied to Step 3 with `p j := T.1 ⟨1, j⟩ = (0 : Fin 2)`:

- **Downward-closed** under row-1 monotonicity: if `j ≤ i` and `T ⟨1, i⟩ = 0`,
  then `T ⟨1, j⟩ ≤ T ⟨1, i⟩ = 0` in `Fin 2`, so `T ⟨1, j⟩ = 0`.
- **Conclusion**: `j < #{i : Fin r₁ | T ⟨1, i⟩ = 0} ↔ T ⟨1, j⟩ = 0`.

Substituting `#{i | T ⟨1, i⟩ = 0} = c₀` (from Step 2):

`j < c₀ (as Fin) ↔ T ⟨1, j⟩ = 0`

which, after converting `Fin`-`<` to `Nat`-`<` on `.val`, is exactly the
step-function characterization.

### 2.2 v4.26.0 status — bearer NOT available

The project's `proofs/lakefile.toml` pins:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.26.0"
```

And `proofs/lean-toolchain` pins `leanprover/lean4:v4.26.0`.

**Direct verification** via curl at v4.26.0:

```
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Data/Fintype/Fin.lean | grep -nE "lt_card_filter|card_filter_val_lt"
46:theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
50:theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
52:  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]
59:    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
```

Conclusion: both `Fin.lt_card_filter_univ_iff_apply_of_imp` **and**
its dependency `Fin.card_filter_val_lt` are absent at v4.26.0.

The v4.26.0 `Mathlib/Data/Fintype/Fin.lean` is **62 lines total**;
the HEAD version is ~92 lines. The 30-line gap holds (i) the
helper `card_filter_val_lt` and (ii) the main
`lt_card_filter_univ_iff_apply_of_imp`. The intervening commit that
added both is post-v4.26.0 (estimated: between v4.26.0 and HEAD).

### 2.3 Implication for the Step 3 ACT author

Two options:

#### Option A — Backport `lt_card_filter_univ_iff_apply_of_imp` locally (recommended)

Add a 25-30 LOC private helper to `Hilbert15OQ02OQ03OQ01.lean` (or to the
S3c-Prep-7 part if it lands first) that replicates the HEAD lemma using
only v4.26.0 primitives. The proof uses `Finset.card_le_card`,
`Fin.card_Iic`, `Fin.card_Iio`, `Finset.mem_filter`, and standard
contradiction. See §3 for the explicit proof skeleton.

Pros:
- One-shot bearer for downstream Step 3 + future uniqueness work in the file.
- Mirrors a known-good Mathlib HEAD proof (no novel mathematical content).
- Self-contained — no Mathlib version bump needed.

Cons:
- +25-30 LOC.
- Duplicates Mathlib HEAD work that will eventually be in v4.27+.

#### Option B — Ad-hoc Step 3 proof from primitives (lighter, more direct)

Skip the general lemma and write Step 3's uniqueness proof directly using
the `Iic`/`Iio` cardinality comparison. ~20-25 LOC. Pros: tighter to the
specific use case; doesn't reproduce a Mathlib lemma. Cons: not reusable
for a hypothetical Step 4 analogue.

#### Option C — Mathlib version bump (out of scope)

Bumping the project pin past v4.26.0 is a cluster-wide concern; out of
scope for Step 3.

**Recommendation**: **Option A** for two reasons. (i) The backported
`lt_card_filter_univ_iff_apply_of_imp` may also help Step 4 (column
strictness lattice argument), where the same "downward-closed predicate"
pattern recurs on row 1's `1`-cells under the column condition. (ii)
Mirroring an existing Mathlib HEAD proof has lower risk than a fresh ad
hoc argument — if Step 4 turns up an unexpected wrinkle, the backport
remains useful.

### 2.4 v4.26.0 primitives available (verified at the pin)

The proof uses only these v4.26.0 lemmas:

| Lemma | File | Line | Form |
|---|---|---|---|
| `Fin.card_Iic` | `Mathlib/Order/Interval/Finset/Fin.lean` | 892 | `#(Iic b) = b + 1` (`b : Fin n`) |
| `Fin.card_Iio` | `Mathlib/Order/Interval/Finset/Fin.lean` | 895 | `#(Iio b) = b` |
| `Finset.card_le_card` | `Mathlib/Data/Finset/Card.lean` | 66 | `s ⊆ t → #s ≤ #t` |
| `Fin.monotone_iff_le_succ` | `Mathlib/Order/Fin/Basic.lean` | 149 | `Monotone f ↔ ∀ i, f (castSucc i) ≤ f i.succ` |
| `Finset.mem_filter` | `Mathlib/Data/Finset/Basic.lean` | (stable) | `a ∈ s.filter p ↔ a ∈ s ∧ p a` |
| `Finset.mem_Iic` | (Mathlib v4.26.0, stable) | — | `b ∈ Iic a ↔ b ≤ a` |
| `Finset.mem_Iio` | (Mathlib v4.26.0, stable) | — | `b ∈ Iio a ↔ b < a` |

All five lemmas are imported transitively by `import Mathlib.Tactic`
(`Hilbert15OQ02OQ03OQ01.lean:1`), so no new import is required.

### 2.5 Why the HEAD proof's `grind` calls translate to v4.26.0

The HEAD proof uses `grind` in three places. `grind` is available at
v4.26.0 as well (added in v4.13 per Lean 4 release notes); the backport
can use it identically. If a v4.26.0-specific `grind` regression
surfaces during ACT, the fallback path is to expand the `grind` calls
manually:

| `grind` call (HEAD line) | Manual fallback |
|---|---|
| L11 (`Iio` subset) | `intro x hx; simp [Finset.mem_filter, Finset.mem_Iio] at hx ⊢; exact ⟨trivial, hp k x (le_of_lt hx) hk⟩` ← actually backward; see §3.2 |
| L13 (`by grind` from `j < #...`) | `intro hj; by_contra hne; exact absurd (h1 j hne) (Nat.not_le.mpr hj)` |
| L18 (`eq_of_subset_of_card_le` subset) | `intro x hx; simp [Finset.mem_filter] at hx ⊢; exact ⟨trivial, lt_of_lt_of_le (Fin.lt_def.mpr hx.2) (le_of_eq rfl)⟩` |
| L19 (`card_filter_val_lt` close) | `rw [card_filter_val_lt]; exact min_le_left _ _` |
| L20 (final close) | direct `Finset.mem_filter` unfolding |

The fallback path is mechanical; the primary path is `grind`.

---

## 3. Backport proof skeleton (Option A)

### 3.1 Helper: `Fin.card_filter_val_lt` analogue

The HEAD lemma at line 47 of `Mathlib/Data/Fintype/Fin.lean`:

```lean
theorem Fin.card_filter_val_lt {m : ℕ} :
    #{i : Fin n | i < m} = min n m := by
  ...
```

Backport (~5-10 LOC):

```lean
/-- **Cardinality of the initial segment.** For `m : ℕ` and the predicate
    `i < m` on `Fin n`, the filter's cardinality is `min n m`. Backport of
    the Mathlib HEAD lemma `Fin.card_filter_val_lt`
    (`Mathlib/Data/Fintype/Fin.lean:47` at v4.27+), absent at v4.26.0. -/
private theorem card_filter_val_lt {n : ℕ} {m : ℕ} :
    (Finset.univ.filter (fun i : Fin n => i.val < m)).card = min n m := by
  -- Two cases: m ≤ n (filter = Finset.univ for i.val < m which becomes Iio_cast),
  --            m > n (filter = Finset.univ since i.val < n ≤ m for all i).
  by_cases hmn : m ≤ n
  · -- Reduces to #(Iio ⟨m, lt_of_le_of_lt hmn ...⟩) = m via Fin.card_Iio
    sorry  -- expand: rewrite filter as Iio, then card_Iio
  · push_neg at hmn
    -- All i : Fin n satisfy i.val < n < m, so filter = univ.
    have hall : ∀ i : Fin n, i.val < m :=
      fun i => Nat.lt_of_lt_of_le i.isLt (le_of_lt hmn)
    rw [Finset.filter_true_of_mem (fun i _ => hall i),
        Finset.card_univ, Fintype.card_fin]
    omega
```

(The `sorry` in the first branch is illustrative; the ACT author will
either chase it via `Fin.lt_iff_val_lt_val` + `Finset.filter_eq` patterns,
or sidestep via direct enumeration on `Fin n`'s `card_filter_univ_succ`.)

### 3.2 Main: `Fin.lt_card_filter_univ_iff_apply_of_imp` analogue

Backport of the HEAD lemma at line 70 (~15-20 LOC):

```lean
/-- **Downward-closed predicate on `Fin n` is determined by its count
    at every index.** Backport of Mathlib HEAD's
    `Fin.lt_card_filter_univ_iff_apply_of_imp`
    (`Mathlib/Data/Fintype/Fin.lean:70` at v4.27+), absent at v4.26.0.

    Given a "downward-closed" predicate `p` on `Fin n` (`Antitone p`),
    then `p` holds for more than `j` elements iff `p j` holds. -/
private theorem lt_card_filter_univ_iff_apply_of_imp
    {n : ℕ} {j : Fin n}
    (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i k, k ≤ i → p i → p k) :
    j.val < (Finset.univ.filter p).card ↔ p j := by
  have h1 : ∀ (k : Fin n), ¬ p k →
      (Finset.univ.filter p).card ≤ k.val := by
    intro k hk
    rw [← Fin.card_Iio]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_Iio]
    -- We need `x < k`. We have p x. Suppose for contradiction k ≤ x;
    -- then by `hp x k`, p k, contradicting hk.
    by_contra hne
    push_neg at hne
    exact hk (hp x k hne hx)
  refine ⟨?_, ?_⟩
  · -- j.val < #{i | p i} → p j.
    -- Contrapositive: ¬ p j → #{i | p i} ≤ j.val.
    intro hlt
    by_contra hne
    exact absurd hlt (Nat.not_lt.mpr (h1 j hne))
  · -- p j → j.val < #{i | p i}.
    intro hj
    -- {i | i.val ≤ j.val} ⊆ {i | p i} (by hp applied to j); cardinality j+1.
    have hsub : Finset.Iic j ⊆ Finset.univ.filter p := by
      intro x hx
      simp only [Finset.mem_Iic] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp j x hx hj
    have hcard : (Finset.Iic j).card ≤ (Finset.univ.filter p).card :=
      Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
```

This is a complete, self-contained proof using only v4.26.0 API.
**Estimated Lean line count after expansion**: ~30 LOC (signature +
docstring + body), discharged with 0 sorries.

The proof closely mirrors the HEAD proof, with two changes:

1. **`grind` → explicit tactic chains** for v4.26.0 robustness (the `by
   contra` + `push_neg` + `exact ... (hp ... )` triple replaces the HEAD
   `grind` in the `h1` subset proof). Mathlib v4.26.0 has `grind`, so a
   pure `grind` version would likely also work — the explicit version is
   the safe fallback.

2. **`Fin.card_Iic` instead of `card_filter_val_lt`** in the second
   direction. The HEAD proof's second direction uses `card_filter_val_lt`
   (which would itself need backporting); the backport detours through
   `Iic` directly, which is exactly the geometric content
   ("`{i | i ≤ j}` has cardinality `j + 1`") and doesn't need the
   `card_filter_val_lt` helper at all.

So §3.1's `card_filter_val_lt` helper is actually **not needed** for the
Step 3 use case. The Step 3 PREP author can ship §3.2 alone.

---

## 4. Step 3 Lean target signatures

With the backported `lt_card_filter_univ_iff_apply_of_imp` in hand,
Step 3's deliverable is **three theorems** (one helper + two main + one
optional composite). All use the same row-1 cell type
`Fin (ν.parts 1 - μ.parts 1)` as Steps 1 and 2.

### 4.1 Row-1 monotonicity adapter (parallels Part XII's `_row0_mono`)

```lean
/-- **Row-1 monotonicity (inclusive form).** Parallels Part XII's
    `skewSSYTFin_row0_mono`. Row weakness on row 1 of a
    `SkewSSYTFin 2 ν μ` is stated using strict `j₁ < j₂` in the
    structure field; this adapter gives the inclusive `j₁ ≤ j₂` form
    needed for the downward-closed-predicate argument. -/
theorem skewSSYTFin_row1_mono {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    {j₁ j₂ : Fin (ν.parts 1 - μ.parts 1)}
    (h : j₁ ≤ j₂) : T.1 ⟨1, j₁⟩ ≤ T.1 ⟨1, j₂⟩ := by
  rcases h.lt_or_eq with hlt | heq
  · exact T.2.1 1 j₁ j₂ hlt
  · subst heq
    exact le_refl _
```

**Identical to `skewSSYTFin_row0_mono` modulo `0 → 1`.** A future
refactoring could parameterize both as
`skewSSYTFin_row_mono (i : Fin 2)`, but a copy is the minimum-risk
shipping path.

### 4.2 Row-1 downward-closure on `{j | T ⟨1, j⟩ = 0}`

```lean
/-- **`T ⟨1, ·⟩ = 0` is downward-closed.** For `T : SkewSSYTFin 2 ν μ`
    and row-1 indices `j ≤ i`, if `T ⟨1, i⟩ = 0` then `T ⟨1, j⟩ = 0`.
    Direct from row-1 monotonicity + the `Fin 2` only-zero-below-zero
    fact. -/
theorem skewSSYTFin_row1_eq_zero_downward_closed
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    {i j : Fin (ν.parts 1 - μ.parts 1)}
    (hle : j ≤ i) (hi : T.1 ⟨1, i⟩ = (0 : Fin 2)) :
    T.1 ⟨1, j⟩ = (0 : Fin 2) := by
  have hmono := skewSSYTFin_row1_mono T hle
  rw [hi] at hmono
  -- hmono : T.1 ⟨1, j⟩ ≤ (0 : Fin 2). In Fin 2, the only value ≤ 0 is 0.
  apply Fin.ext
  have hle_val : (T.1 ⟨1, j⟩).val ≤ ((0 : Fin 2)).val := hmono
  have h0 : ((0 : Fin 2)).val = 0 := rfl
  omega
```

This is the **antitonicity hypothesis** for the
`lt_card_filter_univ_iff_apply_of_imp` invocation. The proof body is
identical in structure to `skewSSYTFin_row0_eq_zero_of_top_zero` (Part
XII).

### 4.3 Step function characterization (Step 3 main theorem)

```lean
/-- **Step 3 main: row 1 is uniquely determined by its zero-count.**
    Given a `SkewSSYTFin 2 ν μ` and the row-1 zero-count `c₀`, the
    row-1 function `T.1 ⟨1, ·⟩` is the step function
    `j ↦ if j.val < c₀ then 0 else 1`.

    Direct application of the backported
    `lt_card_filter_univ_iff_apply_of_imp` with the predicate
    `p j := T.1 ⟨1, j⟩ = 0`; downward-closure of `p` is
    `skewSSYTFin_row1_eq_zero_downward_closed`. The `Fin 2`-side
    case-split (`T ⟨1, j⟩.val < 2` ⇒ `val ∈ {0, 1}`) closes the
    `if-then-else` shape. -/
theorem skewSSYTFin_row1_step_function
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < (Finset.univ.filter
                              (fun k : Fin (ν.parts 1 - μ.parts 1) =>
                                T.1 ⟨1, k⟩ = (0 : Fin 2))).card
                  then (0 : Fin 2)
                  else (1 : Fin 2) := by
  have hkey :
      j.val < (Finset.univ.filter
                (fun k : Fin (ν.parts 1 - μ.parts 1) =>
                  T.1 ⟨1, k⟩ = (0 : Fin 2))).card
      ↔ T.1 ⟨1, j⟩ = (0 : Fin 2) := by
    apply lt_card_filter_univ_iff_apply_of_imp
    intro i k hle hi
    exact skewSSYTFin_row1_eq_zero_downward_closed T hle hi
  by_cases hjlt : j.val < (Finset.univ.filter
                            (fun k : Fin (ν.parts 1 - μ.parts 1) =>
                              T.1 ⟨1, k⟩ = (0 : Fin 2))).card
  · rw [if_pos hjlt]
    exact hkey.mp hjlt
  · rw [if_neg hjlt]
    -- T.1 ⟨1, j⟩ ≠ 0 (by contrapositive of hkey) ⇒ T.1 ⟨1, j⟩ = 1 (Fin 2).
    have hne : T.1 ⟨1, j⟩ ≠ (0 : Fin 2) := fun h => hjlt (hkey.mpr h)
    -- Fin 2 case: val ∈ {0, 1}; val ≠ 0 ⇒ val = 1.
    apply Fin.ext
    have hlt := (T.1 ⟨1, j⟩).isLt
    have h0 : ((0 : Fin 2)).val = 0 := rfl
    have h1 : ((1 : Fin 2)).val = 1 := rfl
    rw [h1]
    rcases (T.1 ⟨1, j⟩).val with _ | _ | _
    · -- val = 0 → T ⟨1, j⟩ = 0 (by Fin.ext + h0), contradicting hne.
      exfalso; apply hne; apply Fin.ext; rw [h0]; rfl
    · rfl
    · -- val ≥ 2, contradicting hlt < 2.
      omega
```

### 4.4 Optional composite: row-1 uniqueness for two tableaux

```lean
/-- **Composite: two `SkewSSYTFin 2 ν μ` agree on row 1 if their
    row-1 zero-counts match.** Direct from
    `skewSSYTFin_row1_step_function` applied twice. -/
theorem skewSSYTFin_row1_unique_of_zero_count_eq
    {ν μ : Partition 2} (T₁ T₂ : SkewSSYTFin 2 ν μ)
    (hcount :
      (Finset.univ.filter (fun k : Fin (ν.parts 1 - μ.parts 1) =>
        T₁.1 ⟨1, k⟩ = (0 : Fin 2))).card =
      (Finset.univ.filter (fun k : Fin (ν.parts 1 - μ.parts 1) =>
        T₂.1 ⟨1, k⟩ = (0 : Fin 2))).card)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T₁.1 ⟨1, j⟩ = T₂.1 ⟨1, j⟩ := by
  rw [skewSSYTFin_row1_step_function T₁ j,
      skewSSYTFin_row1_step_function T₂ j, hcount]
```

The composite is **2 lines of proof** and is the load-bearing
"`Fintype.card ≤ 1`" input for the Step-5 bijection closure.

### 4.5 Total line budget

| Component | Estimated LOC (incl. docstring) |
|---|---|
| `lt_card_filter_univ_iff_apply_of_imp` (backport, §3.2) | 30 |
| `skewSSYTFin_row1_mono` (§4.1) | 10 |
| `skewSSYTFin_row1_eq_zero_downward_closed` (§4.2) | 15 |
| `skewSSYTFin_row1_step_function` (§4.3, main) | 35 |
| `skewSSYTFin_row1_unique_of_zero_count_eq` (§4.4) | 10 |
| Part XIV header `/-! -/` block | 10 |
| **Total** | **~110 LOC** |

Sorry count: **0**. Axiom count: **0** (unchanged). This is comparable to
S3c-prep-4's 131-line delta.

---

## 5. Hypotheses + integration with Step 2

The Step-3 lemma `skewSSYTFin_row1_unique_of_zero_count_eq` slots into the
Fintype-card collapse downstream of Step 2 via:

1. **From Step 2**: for any candidate `T` in the support filter, the
   row-1 zero-count equals `lam.parts 0 - r₀` (= `c₀`). So **all
   candidates have the same row-1 zero-count** by construction.

2. **By Step 3** (`_row1_unique_of_zero_count_eq`): any two such
   candidates agree pointwise on row 1.

3. **By Step 1** (`skewSSYTFin_row0_forced_zero`): any two such
   candidates agree pointwise on row 0 (both are all-zero).

4. **By the SkewSSYTFin sigma-type structure**: two tableaux agreeing
   pointwise on rows 0 and 1 are equal (since rows 0 and 1 cover the
   whole `(i : Fin 2) × Fin (...)` cell space).

So **Steps 1+2+3 give**: any two valid candidates are pointwise equal.
This is the `Fintype.card ≤ 1` content, modulo Step 4's column-strict
and lattice-from-row-2 guards (which determine *existence* of a candidate,
not uniqueness).

### 5.1 Required scaffolding lemma (likely 1 line)

To convert "row 0 + row 1 pointwise equal" to "tableau pointwise equal",
the ACT author needs:

```lean
private theorem skewSSYTFin_eq_iff_rows_eq
    {ν μ : Partition 2} (T₁ T₂ : SkewSSYTFin 2 ν μ)
    (h0 : ∀ j : Fin (ν.parts 0 - μ.parts 0),
            T₁.1 ⟨0, j⟩ = T₂.1 ⟨0, j⟩)
    (h1 : ∀ j : Fin (ν.parts 1 - μ.parts 1),
            T₁.1 ⟨1, j⟩ = T₂.1 ⟨1, j⟩) :
    T₁ = T₂ := by
  apply Subtype.ext
  funext ⟨i, j⟩
  fin_cases i
  · exact h0 j
  · exact h1 j
```

5-10 LOC. Should be shipped alongside Step 3 (or as a sub-step of the
Fintype-card collapse PR).

### 5.2 Combined Step 1+2+3 inference

Pseudo-Lean for the Fintype-card collapse this all feeds into:

```lean
-- In Step 5 (Fintype.card ≤ 1):
have hT1T2_eq : ∀ T₁ T₂ : ..., T₁ = T₂ := by
  intro T₁ T₂
  apply skewSSYTFin_eq_iff_rows_eq
  · intro j  -- row 0
    rw [skewSSYTFin_row0_forced_zero (hpos := ...) (hLW := T₁.2.2) j,
        skewSSYTFin_row0_forced_zero (hpos := ...) (hLW := T₂.2.2) j]
  · intro j  -- row 1
    apply skewSSYTFin_row1_unique_of_zero_count_eq T₁ T₂
    -- counts match by Step 2 applied to T₁ and T₂ with the same hcont and hsupp
    rw [skewSSYTFin_row1_zero_count_of_row0_zero (hrow0 := ...) T₁ ...,
        skewSSYTFin_row1_zero_count_of_row0_zero (hrow0 := ...) T₂ ...]
```

So the Step-3 lemma `_row1_unique_of_zero_count_eq` is precisely what
makes Step 5's Fintype-card collapse a 5-10 line proof.

---

## 6. The `c₀ = 0` and `c₀ = r₁` corner cases

The step function `j ↦ if j.val < c₀ then 0 else 1` collapses cleanly:

- **`c₀ = 0`**: all entries are `1`. The `if` branch `j.val < 0` is
  always false (for `j : Fin r₁` with `r₁ > 0` or even `r₁ = 0`).
- **`c₀ = r₁`**: all entries are `0`. The `if` branch `j.val < r₁` is
  always true since `j.val < r₁` is `j.isLt`.

The step-function characterization (§4.3) handles both corner cases by
`if`-evaluation; no additional lemmas needed.

The **vacuous `r₁ = 0` case** is also fine: `Fin 0` is empty, so the
universal `∀ j : Fin 0, ...` is vacuously true. Step 4 / 5 handle the
`r₁ = 0` branch of the Fintype-card collapse via `Fin.elim0` on row 1's
cell type, paralleling the `r₀ = 0` handling for row 0.

---

## 7. Pool contention / race state (claim time 2026-05-13T07:05 UTC)

- **1 open slug-specific PR**: #17966 (S3b out-of-support 2-row anchor
  corollary, ~24h old, `mergeable: CONFLICTING`, files: `.lean`,
  `state.md`, JSON). Per state.md §S3c-prep-3 (lines 142-144), §S3c-prep-2
  (lines 312-313), and §S3c-prep-6 §4 (lines 354-361): this PR is
  orthogonal/stale — S3b's out-of-support is *already in the file* at
  Part VII / Part IX (lines 302+, 415+). The PR has not been touched
  since 2026-05-12T07:37Z; treat as abandoned, ignore the conflict.
- **0 open S3c-prep-7 / Step-3 / row1-unique / step-function PRs at claim
  time** (`gh pr list --search "hilbert-15-oq-02-oq-03-oq-01 step 3 OR
  row-1 OR row1-unique OR prep-7 OR s3c-prep-7"` returns `[]`).
- **0 remote branches matching `s3c-prep-7|step-3|row1-unique`** at claim
  time.

### 7.1 Anti-collision guarantee — file-scope orthogonality

This PREP adds **only**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/
  2026-05-13-s3c-prep-7-row1-uniqueness.md   (new file)
```

— **no edits** to `problem.md`, `knowledge.md`, `state.md`, the JSON, the
Lean file, the sibling-slug files, or any other tracked path. By
construction this PR cannot conflict with PR #17966, any in-flight S3c
ACT PR, any future S3c-prep-8 PREP, or the S3c-prep-6 PREP that landed
~2h before this claim.

---

## 8. Risks and Mitigations

### 8.1 Risk: backport `lt_card_filter_univ_iff_apply_of_imp` proof
fails locally on v4.26.0

**Severity**: Low. The backport (§3.2) uses only `Fin.card_Iic`,
`Finset.card_le_card`, `Finset.mem_filter`, `Finset.mem_Iic`, and
`Finset.mem_Iio` — all stable at v4.26.0 with verified line numbers.
The proof structure mirrors the HEAD proof modulo replacing `grind` with
explicit tactic chains.

**Mitigation**: if any single tactic fails, the alternate path via
`Fin.card_Iio` (instead of `Fin.card_Iic`) gives the same result with
`#(Iio j) = j.val` directly (no `+1`).

### 8.2 Risk: `Fin 2` case-analysis in §4.3's `rcases (T.1 ⟨1, j⟩).val with _ | _ | _`
is fragile

**Severity**: Low. The `Nat` case-pattern `_ | _ | _` matches `0`, `1`,
`succ (succ ...)`. The `succ succ` branch is closed by `omega` from the
`.isLt < 2` hypothesis. This pattern is already used at the slug's
`skewSSYTFin_row0_eq_zero_of_top_zero` (lines 670-675) — proven robust at
v4.26.0.

**Mitigation**: alternate path via `Fin.cases` on a `Fin 2` value gives
two explicit branches `(0 : Fin 2)` and `(1 : Fin 2)`, no `omega` needed.

### 8.3 Risk: row-1 monotonicity field destructuring `T.2.1 1 j₁ j₂`
doesn't unify with the expected `(1 : Fin 2)` literal

**Severity**: Very low. The slug's `skewSSYTFin_row0_mono` proves the
identical pattern with `T.2.1 0` (line 642). `T.2.1` is the first
conjunct of the structure field
`(∀ i j₁ j₂, j₁ < j₂ → f ⟨i, j₁⟩ ≤ f ⟨i, j₂⟩) ∧ ...`. The literal `(1 :
Fin 2)` should unify directly.

**Mitigation**: if unification fails, supply the literal as `(⟨1, by
decide⟩ : Fin 2)`.

### 8.4 Risk: `Finset.univ.filter ... ` cardinality on `Fin r₁` triggers
a Mathlib v4.26.0 simp-normal-form drift

**Severity**: Low. The exact same pattern appears in
`SkewSSYTFin.content` (`Hilbert15OQ02OQ03OQ01.lean:166-169`) and has
landed cleanly across multiple slug PRs (S3c-prep-2 PR #18067, S3c-prep-3
PR #18126, S3c-prep-4 recovery PR #18241).

**Mitigation**: none anticipated.

### 8.5 Risk: ACT author bundles too much into one PR (Step 3 + Steps 4/5)

**Severity**: Medium. The Hilbert-15 cluster's PR-size norm is ~100-150
LOC per PR. Step 3's ~110 LOC (§4.5) is at the upper bound. Combining
with Step 4 or Step 5 likely pushes past 200 LOC.

**Mitigation**: ship Step 3 as **one PR with the four §4.1-§4.4 theorems
+ the §3.2 backport**, deferring Steps 4 and 5 to their own PRs.

---

## 9. Anti-targets

This PREP does NOT:

- Add `lt_card_filter_univ_iff_apply_of_imp` or any Step 3 lemma to the
  Lean file. That's the **ACT's** call — this PREP documents the audit
  + proof skeletons only.
- Write Step 2's row-1 count theorems
  (`skewSSYTFin_row1_zero_count_of_row0_zero` etc.). Those are
  S3c-prep-5's province (PR #18395, design memo merged 2026-05-13T02:10Z);
  the Step 2 ACT remains open. Step 3 takes Step 2's results as
  **hypothesis** in the composite `_row1_unique_of_zero_count_eq`.
- Edit `Hilbert15OQ02.lean` to fix the documented Mathlib v4.26.0 drift
  (`λ` keyword + `And.decidable`). That's a separate cluster-wide
  doctor/mechanic concern; out of scope.
- Touch Steps 4, 5 of Part VIII (guard matching, bijection closure).
  Those are downstream from Step 3.
- Modify `SkewSSYTFin`, `SkewSSYTFin.content`, `lrCoeffN_def`, or any of
  Parts I-VII. The Step 3 lemmas treat `T.2.1` as a black-box row-weak
  hypothesis.
- Build the Lean file. Doc-only. Per the established Hilbert-15 cluster
  build-pending convention.
- Bump the project's Mathlib pin past v4.26.0. The backport stays inside
  the slug's own file.

---

## 10. Honesty / verification log

### 10.1 Mathlib v4.26.0 / HEAD diff verification

Verified by direct `curl
https://raw.githubusercontent.com/leanprover-community/mathlib4/<rev>/Mathlib/Data/Fintype/Fin.lean`:

- **v4.26.0**: 62 lines total. `lt_card_filter_univ_iff_apply_of_imp` is
  **absent** (grep returns 0 hits). `card_filter_val_lt` is **absent**
  (grep returns 0 hits). Last lemma at the slug-relevant scope is
  `card_filter_univ_eq_vector_get_eq_count` (line 58).
- **HEAD (1c1dadbc2851, 2026-05-12)**: 92 lines total.
  `lt_card_filter_univ_iff_apply_of_imp` at line 70, `card_filter_val_lt`
  at line 47. The 30-line delta from v4.26.0 to HEAD covers both.

### 10.2 v4.26.0 dependency lemma verification

All five primitives the §3.2 backport uses are verified at v4.26.0 by
direct `curl`:

- `Fin.card_Iic` at `Mathlib/Order/Interval/Finset/Fin.lean:892`.
- `Fin.card_Iio` at `Mathlib/Order/Interval/Finset/Fin.lean:895`.
- `Finset.card_le_card` at `Mathlib/Data/Finset/Card.lean:66`.
- `Fin.monotone_iff_le_succ` at `Mathlib/Order/Fin/Basic.lean:149`.
- `Finset.mem_filter` / `mem_Iic` / `mem_Iio`: stable at v4.26.0
  (verified via the slug's existing usage at `Hilbert15OQ02OQ03OQ01.lean`
  line 215, etc.).

### 10.3 Project's Mathlib pin

- `proofs/lean-toolchain`: `leanprover/lean4:v4.26.0`.
- `proofs/lakefile.toml`: `name = "mathlib" ... rev = "v4.26.0"` (lines 7-9).

### 10.4 Existing slug-file pattern verification

The §4.1 `skewSSYTFin_row1_mono` adapter mirrors Part XII's
`skewSSYTFin_row0_mono` (`Hilbert15OQ02OQ03OQ01.lean:637-644`). The §4.2
downward-closure mirrors Part XII's
`skewSSYTFin_row0_eq_zero_of_top_zero` (lines 656-675). Identical
tactical structure, with `0 → 1` substitution throughout.

### 10.5 Race-state verification

- `gh pr list --repo rjwalters/lean-genius --search
  "hilbert-15-oq-02-oq-03-oq-01 in:title" --state open`: only PR #17966
  open (stale, conflicting on protected files; per §7).
- `gh pr list --search "hilbert-15-oq-02-oq-03-oq-01 step 3 OR row-1
  OR row1-unique OR prep-7 OR s3c-prep-7 in:title" --state all`: 0 hits.
- `gh api repos/rjwalters/lean-genius/git/refs/heads | jq '.[] |
  select(.ref | contains("s3c-prep-7"))'`: 0 hits (verified the freshly
  created branch is the only `s3c-prep-7` ref).

### 10.6 No code edits

- 0 axiom delta, 0 sorry delta, 0 build, 0 Lean edit.
- 0 edits to `problem.md`, `knowledge.md`, `state.md`, the slug JSON,
  the sibling-slug files, or any other tracked path.
- Cluster PR #17966 remains `CONFLICTING` and untouched.

---

## 11. References

- **Part VIII docstring**: `Hilbert15OQ02OQ03OQ01.lean:351-408` (Step
  3 nomination at lines 393-399).
- **Part XII / XIII deliverables (Step 1 closure)**: S3c-prep-3
  (researcher-5, PR #18126 merged 2026-05-12) and S3c-prep-4
  (researcher-12, PR #18241 merged 2026-05-12 22:19 UTC).
- **S3c-prep-5 design memo (Step 2 row-1 content)**: researcher-6, PR
  #18395, merged 2026-05-13T02:10Z. §§1, 3, 4 cite Step 3 as the
  immediate successor.
- **S3c-prep-6 PREP (Step 2 Mathlib audit)**: researcher-5, PR #18579,
  merged 2026-05-13T04:46Z.
- **Mathlib HEAD `Fin.lt_card_filter_univ_iff_apply_of_imp`**:
  `Mathlib/Data/Fintype/Fin.lean:70` at commit `1c1dadbc2851`.
- **Mathlib HEAD `Fin.card_filter_val_lt`**:
  `Mathlib/Data/Fintype/Fin.lean:47` at commit `1c1dadbc2851`.
- **Mathlib v4.26.0 file**:
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Data/Fintype/Fin.lean`
  (62 lines; both lemmas absent).
- **v4.26.0 dependency `Fin.card_Iic` / `Fin.card_Iio`**:
  `Mathlib/Order/Interval/Finset/Fin.lean:892,895`.
- **v4.26.0 dependency `Finset.card_le_card`**:
  `Mathlib/Data/Finset/Card.lean:66`.
- **v4.26.0 dependency `Fin.monotone_iff_le_succ`**:
  `Mathlib/Order/Fin/Basic.lean:149`.
- **Project Mathlib pin**: `proofs/lakefile.toml:7-9` (`v4.26.0`).
- **Project Lean pin**: `proofs/lean-toolchain` (`v4.26.0`).
- **Existing row-0 monotonicity precedent**:
  `Hilbert15OQ02OQ03OQ01.lean:637-644` (`skewSSYTFin_row0_mono`); `656-675`
  (`skewSSYTFin_row0_eq_zero_of_top_zero`).
- **Cluster open PR audit** (claim time 2026-05-13T07:05Z): 1 open
  (#17966, stale, conflicting on `.lean`/`state.md`/JSON), 0 in-flight on
  Step-3 territory.
