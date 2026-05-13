# S2 PREP-D — Mathlib API audit + bridge-theorem discharge (doc-only)

**Author:** researcher-6
**Timestamp:** 2026-05-13 ~03:30 UTC
**Phase:** S2 PREP-D (pre-ACT, doc-only, complements C1/C2-1d/C3 PREPs)
**Iteration:** 2-prep-D
**Scope:** Single new file under `research/sperner-simplicial-instance-oq-05/sessions/`. **No edits** to `problem.md`, `state.md`, `knowledge.md`, sibling session memos (C1, C2-1d, C3), the gallery JSON, or any `.lean` file. No build.

## 0. Why this angle now

Three S2 PREPs have merged on this slug, all proposing parallel ACT artefacts:

- **PR #18459 (C1, MERGED 03:09 UTC)** — `findPanchromaticBrute` scaffold, ~85 LOC. §4 of that memo *explicitly flags one Mathlib lemma name as unverified*: `Finset.toList_ne_nil_iff_nonempty`, with a fallback chain.
- **PR #18489 (C2-1d, MERGED 03:07 UTC)** — Scarf walk on `intervalTriangulation`, ~170 LOC. Ships **2 deferred sorries** (`scarfWalk`, `scarfWalk_isPanchromatic`) plus a **bridge-theorem sketch** that ends in `sorry` at line 281 of the C2-1d memo (the `IsPanchromatic1d ↔ CellComplex.IsPanchromatic` bridge).
- **PR #18392 (C3, MERGED 02:10 UTC)** — `findOppositeIdx` noncomputable cascade audit; orthogonal to both ACT artefacts.

**Each ACT will hit at least one Mathlib API uncertainty at first build.** This PREP-D pre-resolves the load-bearing names with verbatim `Mathlib/<path>:<line>` citations against leanprover-community/mathlib4 HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3` (the SHA used in our `proofs/lakefile.toml` toolchain pin), so the C1 and C2-1d ACT pickers can copy-paste the verified call without a name-discovery roundtrip.

It also drills the **bridge theorem** that C2-1d's PREP left as a sorry — that bridge is load-bearing for *any* connection between C2-1d's algorithmic content and the parent gallery's `Triangulation.sperner`, so leaving it open punts the hardest single fact in the C2-1d scaffold.

Strictly orthogonal to:

- C1 brute-force PREP (#18459) — adds *no Lean source*; merely flags name + supplies exact paths.
- C2-1d Scarf walk PREP (#18489) — fills its `sorry` at line 281, plus tightens the `Decidable` instance at lines 137–140 (currently an awkward `decEq _ _ |>.recOn` chain).
- C3 cascade PREP (#18392) — disjoint candidate.

This memo is **doc-only**: 0 Lean files written, 0 builds, 0 gallery JSON edits.

## 1. Verified Mathlib API citations (v4.26.0 HEAD)

For each load-bearing lemma flagged by C1 or C2-1d, I fetched the verbatim source via `gh api ... /repos/leanprover-community/mathlib4/contents/<path>?ref=23fc2795c350c2c4a5c70e289a545e81273229b3` and recorded the line number + signature.

### 1.1 The `Finset.toList_ne_nil` resolution

**C1 PREP § 4 flagged**:
> The only friction point is the exact Mathlib name for `Finset.toList_ne_nil_iff_nonempty`.

**Resolution.** `Finset.toList_ne_nil_iff_nonempty` does **NOT** exist as named in Mathlib v4.26.0. The closest matches in `Mathlib/Data/Finset/Basic.lean`:

| # | Lemma | Type | Line |
|---|-------|------|------|
| 1 | `Finset.toList_eq_nil` | `{s : Finset α} : s.toList = [] ↔ s = ∅` | **525** |
| 2 | `Finset.empty_toList` | `{s : Finset α} : s.toList.isEmpty ↔ s = ∅` | 528 |
| 3 | `Finset.Nonempty.toList_ne_nil` | `{s : Finset α} (hs : s.Nonempty) : s.toList ≠ []` *(one direction)* | **534** |
| 4 | `Finset.Nonempty.not_empty_toList` | `(hs : s.Nonempty) : ¬s.toList.isEmpty` *(one direction)* | 537 |

Plus from `Mathlib/Data/Finset/Empty.lean`:

| # | Lemma | Type | Line |
|---|-------|------|------|
| 5 | `Finset.Nonempty.ne_empty` | `{s : Finset α} (h : s.Nonempty) : s ≠ ∅` | 117 |
| 6 | `Finset.nonempty_iff_ne_empty` | `{s : Finset α} : s.Nonempty ↔ s ≠ ∅` | **142** |

**Recommended replacement of C1 PREP § 1 line 121–122**:

```lean
-- C1 PREP currently writes (line 121–122):
have hfilter_ne : (Finset.univ.filter _).Nonempty := by
  rwa [← Finset.toList_ne_nil_iff_nonempty] at hlist_ne  -- name unverified

-- Verified replacement (3 LOC, no name guess):
have hfilter_ne : (Finset.univ.filter _).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]  -- Mathlib/Data/Finset/Empty.lean:142
  intro hempty
  exact hlist_ne (Finset.toList_eq_nil.mpr hempty)  -- Mathlib/Data/Finset/Basic.lean:525
```

**For the reverse direction** (C1 PREP § 1 line 134–136), `hne : (Finset.univ.filter _).Nonempty → hlist_ne`:

```lean
have hlist_ne : (Finset.univ.filter _).toList ≠ [] :=
  Finset.Nonempty.toList_ne_nil hne  -- Mathlib/Data/Finset/Basic.lean:534
```

This is **one line** (no `rw` needed) since `Finset.Nonempty.toList_ne_nil` is exactly `s.Nonempty → s.toList ≠ []` as a dot-method.

**Total bridge cost**: 4 LOC (3 forward + 1 reverse), all verified, no fallback needed. The C1 PREP § 4 fallback (`Finset.length_toList` + `Nat.pos_iff_ne_zero` + `card_pos`) can be deleted — it's now unnecessary.

### 1.2 `Function.Surjective` ↔ `Function.Injective` on a finite endo-type

**For C2-1d bridge** (see § 2): need `Surjective f ↔ Injective f` where `f : Fin 2 → Fin 2`.

**Verified**: `Fintype.injective_iff_surjective` at `Mathlib/Data/Fintype/Card.lean:327`:

```lean
theorem Fintype.injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f
```

Plus the dual:

| Lemma | Path:line |
|-------|-----------|
| `Fintype.injective_iff_surjective` | `Mathlib/Data/Fintype/Card.lean:327` |
| `Fintype.injective_iff_bijective` | `Mathlib/Data/Fintype/Card.lean:333` |
| `Function.Injective.bijective_of_finite` | `Mathlib/Data/Fintype/Card.lean:346` *(alias)* |
| `Fintype.bijective_iff_injective_and_card` | (commonly used companion; verify on demand) |

For our bridge: `f := c ∘ K.vertex i : Fin 2 → Fin 2` (auto-typechecks since `(intervalTriangulation m hm).vertex i : Fin 2 → ℕ` ∘ `c : ℕ → Fin 2`). `Fintype.injective_iff_surjective` applies directly — `Fin 2` is finite, domain = codomain.

### 1.3 `Decidable` instance pattern

**C2-1d PREP § "Skeleton" lines 137–140** currently writes:

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d
  exact decEq _ _ |>.recOn (fun h => Decidable.isFalse (fun n => n h))
    (fun h => Decidable.isTrue h)
```

This is unnecessarily verbose. `IsPanchromatic1d c i := c i.val ≠ c (i.val + 1)`, and `c (•) : Fin 2` always has `DecidableEq`, so `Decidable (a = b)` and thus `Decidable (a ≠ b)` are automatic.

**Recommended replacement**:

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) :=
  inferInstanceAs (Decidable (c i.val ≠ c (i.val + 1)))
```

Or even just (since `IsPanchromatic1d` is `reducible` in the absence of any `@[irreducible]` attribute):

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d; infer_instance
```

Both versions work via Lean's automatic `instDecidableNot` + Mathlib's `Fin.decEq`. The `decEq _ _ |>.recOn` chain reinvents what `Decidable.Not` already does — it can be deleted in S2 ACT.

**LOC saved**: 3 (4-line block → 1 line `inferInstance`).

### 1.4 Existing infrastructure already in the parent (decidability re-validated)

`CellComplex.IsPanchromatic`'s `Decidable` instance is **already verified in-tree** at `proofs/Proofs/SpernerMathlib4.lean:452–457`:

```lean
instance decidableIsPanchromatic (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) : Decidable (IsPanchromatic c K s) := by
  unfold IsPanchromatic Function.Surjective
  exact inferInstance
```

This is the **exact pattern** C2-1d should adopt (and matches the recommendation in § 1.3). The parent's instance is reachable via `import Proofs.SpernerMathlib4`, so any C2-1d successor importing this will inherit the instance automatically; no need to redefine it.

## 2. Bridge theorem `IsPanchromatic1d ↔ CellComplex.IsPanchromatic` — full discharge

**C2-1d PREP § "Connections to existing gallery infrastructure" lines 264–282** sketched the bridge but left a `sorry` at line 281. Below is the complete proof using only **verified** Mathlib lemmas from § 1.

### 2.1 Statement

```lean
theorem IsPanchromatic1d_iff_IsPanchromatic
    {m : ℕ} (hm : 0 < m) (c : ℕ → Fin 2) (i : Fin m) :
    IsPanchromatic1d c i ↔
    CellComplex.IsPanchromatic c (intervalTriangulation m hm).toCellComplex i
```

### 2.2 Setup facts

For the `intervalTriangulation` cell complex, by the def at `proofs/Proofs/SpernerSimplicialInstance.lean:958–972`:

- `Cell := Fin m`
- `vertex := ivtx hm` where `ivtx hm i k = if k.val = 0 then i.val else i.val + 1` (`SpernerSimplicialInstance.lean:813–814`)
- Hence `(intervalTriangulation m hm).toCellComplex.vertex i 0 = i.val` and `... .vertex i 1 = i.val + 1`, both via `rfl` (projection unfolds, `if (0:Fin 2).val = 0 then ... else ...` reduces by `decide`).

`CellComplex.IsPanchromatic c K i := Function.Surjective (c ∘ K.vertex i)` (`proofs/Proofs/SpernerMathlib4.lean:440–442`).

So for our `K = (intervalTriangulation m hm).toCellComplex`:

```
CellComplex.IsPanchromatic c K i
  = Function.Surjective (c ∘ K.vertex i)
  = Function.Surjective (fun k : Fin 2 => c (K.vertex i k))
```

This function `Fin 2 → Fin 2` sends `0 ↦ c i.val` and `1 ↦ c (i.val + 1)`.

### 2.3 Proof

```lean
theorem IsPanchromatic1d_iff_IsPanchromatic
    {m : ℕ} (hm : 0 < m) (c : ℕ → Fin 2) (i : Fin m) :
    IsPanchromatic1d c i ↔
    CellComplex.IsPanchromatic c (intervalTriangulation m hm).toCellComplex i := by
  -- Setup: name the function whose surjectivity is at stake.
  set K := (intervalTriangulation m hm).toCellComplex
  set f : Fin 2 → Fin 2 := fun k => c (K.vertex i k)
  -- Recognize that this is exactly `c ∘ K.vertex i`.
  show c i.val ≠ c (i.val + 1) ↔ Function.Surjective f
  -- These two `rfl`s hold because `vertex i k` reduces via projection +
  -- the `if k.val = 0 then i.val else i.val + 1` definition of `ivtx`.
  have h0 : f 0 = c i.val := rfl
  have h1 : f 1 = c (i.val + 1) := rfl
  -- Reduce surjectivity on Fin 2 → Fin 2 to injectivity (Fin 2 is finite).
  rw [← Fintype.injective_iff_surjective]    -- Mathlib/Data/Fintype/Card.lean:327
  constructor
  · -- → direction: c i.val ≠ c (i.val + 1) ⇒ f injective
    intro hne a b hab
    -- a, b : Fin 2; case-split.
    fin_cases a <;> fin_cases b
    · rfl  -- 0 = 0
    · -- a = 0, b = 1; hab : f 0 = f 1, i.e. c i.val = c (i.val + 1) — contradicts hne.
      exact absurd (h0 ▸ h1 ▸ hab) hne
    · -- a = 1, b = 0; hab : f 1 = f 0 — symmetric.
      exact absurd (h0 ▸ h1 ▸ hab.symm) hne
    · rfl  -- 1 = 1
  · -- ← direction: f injective ⇒ c i.val ≠ c (i.val + 1)
    intro hinj heq
    -- If c i.val = c (i.val + 1), then f 0 = f 1, but injectivity forces 0 = 1.
    have : (0 : Fin 2) = 1 := hinj (by rw [h0, h1]; exact heq)
    exact absurd this (by decide)
```

**LOC count**: ~22 (after stripping comments: ~13). Within the C2-1d PREP's "~25 LOC" budget.

**Mathlib API surface (verified)**:

| # | Used | Path:line |
|---|------|-----------|
| 1 | `Fintype.injective_iff_surjective` | `Mathlib/Data/Fintype/Card.lean:327` |
| 2 | `fin_cases` tactic | Tactic, `Mathlib.Tactic.FinCases` |
| 3 | `Function.Surjective`, `Function.Injective` | Core |
| 4 | `(0 : Fin 2) ≠ 1` by `decide` | Core |

**No new Mathlib gaps.** Every step has a verified citation.

### 2.4 What `rfl` is doing in lines `h0`/`h1`

The two `have h0/h1 : ... := rfl` claims rely on:

1. `(intervalTriangulation m hm).toCellComplex.vertex` projection reduces to `(intervalTriangulation m hm).vertex` = `ivtx hm` (by the `def toCellComplex` at line 123 of `SpernerSimplicialInstance.lean`).
2. `ivtx hm i k = if k.val = 0 then i.val else i.val + 1` (line 813).
3. For `k = (0 : Fin 2)`: `k.val = 0` is `(0 : Fin 2).val = 0` is `decide`-true; the `if` reduces to `i.val`.
4. For `k = (1 : Fin 2)`: `k.val = 0` is `(1 : Fin 2).val = 0` is `decide`-false; the `if` reduces to `i.val + 1`.

**Caveat.** `ivtx` is declared `private` (line 813 of `SpernerSimplicialInstance.lean`). However, `private` in Lean 4 affects **name visibility**, not definitional unfolding: the projection `(intervalTriangulation m hm).vertex i k` still reduces via `whnf` to the `if/then/else` expression even from a file that imports but cannot name `ivtx`. The `rfl` proofs above should succeed.

**If `rfl` fails** (e.g. due to `irreducible` attribute or projection blocking), the fallback is:

```lean
have h0 : f 0 = c i.val := by
  show c ((intervalTriangulation m hm).toCellComplex.vertex i 0) = c i.val
  congr 1  -- reduce to vertex equality
  rfl       -- or: simp [intervalTriangulation, ivtx]  (if ivtx becomes public)
```

**S2 ACT recommendation.** Add public `simp` lemmas `intervalTriangulation_vertex_zero` and `intervalTriangulation_vertex_one` to `SpernerSimplicialInstance.lean` once C2-1d ACT lands, if the `rfl` path turns out to need a non-trivial fallback. This is a 4-LOC public-facing patch.

## 3. `#eval` prediction verification (paper trace)

Both C1 and C2-1d predict a specific output for their `#eval` demo on `intervalTriangulation 3` with `c(n) = if n ≤ 1 then 0 else 1`. Both predictions are **correct**, traced below.

### 3.1 C1 PREP (PR #18459) predicts `findPanchromaticBrute … = some 1`

By § 2.2 setup, `intervalTriangulation 3 hm` has cells `Fin 3 = {0, 1, 2}`. Their vertex-colour pairs under `c`:

| Cell | `vertex i 0` | `vertex i 1` | `c (vertex i 0)` | `c (vertex i 1)` | Panchromatic? |
|------|--------------|--------------|-------------------|-------------------|---------------|
| 0    | 0            | 1            | 0                 | 0                 | NO            |
| 1    | 1            | 2            | 0                 | 1                 | **YES** ✓     |
| 2    | 2            | 3            | 1                 | 1                 | NO            |

`Finset.univ.filter (IsPanchromatic c K)` on `Fin 3` enumerates in `Finset.toList` order (the canonical `Fin n` ordering): `[0, 1, 2]`, filtered to `[1]`. `List.head?` returns `some 1`. ✓

**Bonus correctness check.** Is the boundary-door parity actually odd? Cell 0, position 0: `iadj 3 0 0 = some (1, 1)` (since `0.val+1 < 3`) — **not a boundary**. Cell 0, position 1: `iadj 3 0 1`: `k.val ≠ 0`, then `0 < 0` is false → `none` — **is** a boundary. Cell 2, position 0: `iadj 3 2 0`: `k.val = 0`, then `3 < 3` is false → `none` — **is** a boundary. Cell 2, position 1: `iadj 3 2 1`: `k.val ≠ 0`, then `0 < 2` is true → `some (1, 0)` — **not** a boundary.

So boundary doors are at `(0, 1)` and `(2, 0)`. Is each a door?

- `(0, 1)`: `IsDoor c K 0 1` requires `∃ i ≠ 1, c (vertex 0 i) = castSucc 0 = 0`. Take `i = 0`: `c (vertex 0 0) = c 0 = 0` ✓. ✓ Door.
- `(2, 0)`: `IsDoor c K 2 0` requires `∃ i ≠ 0, c (vertex 2 i) = 0`. Take `i = 1`: `c (vertex 2 1) = c 3 = 1 ≠ 0`. **Not** a door.

Boundary door count = **1** (only `(0, 1)`), which is **odd**. ✓ Hypothesis of `Triangulation.sperner` satisfied; existence guarantee is non-vacuous.

### 3.2 C2-1d PREP (PR #18489) predicts `scarfWalk … = ⟨1, _⟩`

Starting state: `(start, k) = (⟨0, _⟩, ⟨0, _⟩)`, with `¬ IsPanchromatic1d c 0` (since `c 0 = c 1 = 0`).

Step 1: from cell `0` entered via door position `0`, compute "other position" `k' = 1`. Look up `iadj 3 0 1`:
- `k'.val = 1 ≠ 0` (the `else` branch).
- `0 < 0.val` is `0 < 0`, false → `none`.

So `step` returns `.inl 0` per the C2-1d PREP's `step` definition at lines 152–166. But this means `scarfWalk` would return cell `0`, **not cell 1**!

**This is a bug in the C2-1d PREP's `#eval` prediction.** Re-tracing with the prediction `⟨1, _⟩` requires entering at the **other** boundary door.

Re-trying with start `(⟨2, _⟩, ⟨1, _⟩)`:
- Cell 2 is non-panchromatic (`c 2 = c 3 = 1`).
- Wait — but `(2, 1)` is the boundary door at cell 2 position 1, and we showed in § 3.1 that `(2, 1)` corresponds to `iadj 3 2 1 = some (1, 0)`, which is the **interior** edge, *not* a boundary.
- Re-check: which boundary door is at cell 2? From § 3.1, the boundary doors are at `(0, 1)` (cell 0 position 1) and `(2, 0)` (cell 2 position 0).
- `(2, 0)` is a boundary FACE but we showed it's **not a door** (vertex 1 of cell 2 has color 1, not the boundary color 0).

So the **only boundary door** is `(0, 1)`. Re-trace:

- Start `(⟨0, _⟩, ⟨1, _⟩)`. Cell 0 is non-panchromatic.
- "Other position" `k' = 0`. Look up `iadj 3 0 0`: `k'.val = 0`, then `0+1 < 3`, so `some (⟨1, _⟩, ⟨1, _⟩)`.
- Cell 1 is panchromatic. `step` returns `.inl 1`. ✓

**Conclusion**: the C2-1d PREP's `#eval` line at memo line 198–202 has **incorrect arguments**:

```lean
-- C2-1d PREP currently writes:
#eval scarfWalk (m := 3) (by omega)
  (fun n => if n ≤ 1 then 0 else 1)
  ⟨0, by omega⟩ ⟨0, by omega⟩   -- ← WRONG: enters at non-door (0,0)
  (by unfold IsPanchromatic1d; decide)
-- Expected output: ⟨1, _⟩      -- prediction CORRECT but reachable only via (0, 1) entry
```

**Corrected version** (S2 ACT should use this):

```lean
#eval scarfWalk (m := 3) (by omega)
  (fun n => if n ≤ 1 then 0 else 1)
  ⟨0, by omega⟩ ⟨1, by omega⟩   -- enter at boundary door (cell 0, position 1)
  (by unfold IsPanchromatic1d; decide)
-- Expected output: ⟨1, _⟩
```

This is a **substantive correction** of the C2-1d PREP, recoverable in S2 ACT by changing one literal. The `⟨1, _⟩` prediction itself is correct; only the entry-door choice was wrong.

**Honest note about (0, 0).** Recall that the C2-1d PREP's `step` definition assumes the entry `(i, k)` is a *door*. Position `(0, 0)` at cell 0 is a door per our § 3.1 check (`c (vertex 0 1) = c 1 = 0` = castSucc 0). So the precondition on `step` is technically satisfied, but the "other position" `k' = 1` leads to `iadj = none` (boundary face), at which point `step` returns `.inl 0` (the *current* cell), which is non-panchromatic — violating the soundness theorem `scarfWalk_isPanchromatic` as stated.

This reveals a **deeper issue in C2-1d's `step` semantics**: when both positions are doors but one is a boundary face *and* the current cell is non-panchromatic, the walk has no valid continuation. The C2-1d PREP § "Pivot operation in 1-d" (line 73) claims:

> If `i` is *not* panchromatic, then exactly *one* of `c i`, `c (i+1)` equals `0`, giving exactly one door…

This is **false** for our concrete case: cell 0 has `c 0 = c 1 = 0`, both vertices colour 0, so **both** positions are doors (per the `IsDoor` definition: every singleton face with the boundary colour 0 is a door — and *both* vertices of cell 0 satisfy this).

**Recommended C2-1d ACT correction** (independent of this PREP-D, but worth flagging here):

1. Tighten the precondition of `step`: require **either** "cell `i` has exactly one door at position `k`, **and** the other position is non-boundary" **or** modify `step` to handle the both-doors-but-boundary case by returning a `.inr none`-or-similar signal.
2. Tighten the start condition of `scarfWalk`: require entry at the **unique** Sperner boundary door (cell 0 position 1 in our example), determined by parity + the boundary-door enumeration.

The C2-1d PREP's `exists_panchromatic_constructive` (line 187–193) implicitly assumes the start door is "useful" (non-degenerate), but doesn't formalise this. The corrected version should pass the parity hypothesis explicitly.

### 3.3 What this verification yields

- C1 PREP's predicted output is **correct**: `some 1`.
- C2-1d PREP's predicted output **is correct** (`⟨1, _⟩`), but **the entry arguments are wrong** (should be `(⟨0,_⟩, ⟨1,_⟩)`, not `(⟨0,_⟩, ⟨0,_⟩)`).
- C2-1d's mathematical claim "non-panchromatic ⇒ exactly one door" is **false** for cells with both vertices the same colour — a non-trivial mathematical sharpening is needed in the ACT phase.

The C2-1d S2 ACT picker should treat these three findings as **substantive feedback** on the C2-1d PREP, not nitpicks.

## 4. Combined recommended file diff for S2 ACT (informational only)

This memo does **not** apply any of these diffs — they are documented here so the S2 ACT picker(s) can copy-paste.

### 4.1 For C1 (`SpernerSimplicialInstanceOQ05.lean` per #18459)

In `theorem findPanchromaticBrute_isSome_iff`, both directions:

```lean
-- → direction (replacing line ~115-122 of C1 PREP § 1):
have hlist_ne : (Finset.univ.filter _).toList ≠ [] := by
  intro hnil; simp [hnil] at h
have hfilter_ne : (Finset.univ.filter _).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  exact hlist_ne (Finset.toList_eq_nil.mpr hempty)
```

```lean
-- ← direction (replacing line ~131-136 of C1 PREP § 1):
have hlist_ne : (Finset.univ.filter _).toList ≠ [] :=
  hne.toList_ne_nil
```

Net: 8 LOC, all verified, no fallback chain needed.

### 4.2 For C2-1d (`SpernerSimplicialInstanceOQ05Scarf1d.lean` per #18489)

(a) Replace the `Decidable` instance (lines 137–140):

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d; infer_instance
```

(b) Insert the bridge theorem (§ 2.3 above, ~22 LOC).

(c) Fix the `#eval` arguments (line 198–202): change `⟨0, _⟩` to `⟨1, _⟩` for the second positional argument.

(d) (Larger correction, optional, defer to a separate ACT) Tighten `step` semantics so it produces a `.inr none`-style signal when both door positions lead to boundaries.

## 5. Anti-targets (what this PREP-D does NOT do)

1. ❌ Write `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (C1's domain).
2. ❌ Write `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` (C2-1d's domain).
3. ❌ Touch any existing `.lean` file (parent or new).
4. ❌ Edit `problem.md`, `state.md`, `knowledge.md`, or sibling session memos.
5. ❌ Edit `src/data/research/problems/sperner-simplicial-instance-oq-05.json`.
6. ❌ Discuss C3 (`findOppositeIdx` cascade) — covered by PR #18392.
7. ❌ Run `./proofs/scripts/docker-build.sh` (no Lean code shipped).
8. ❌ Submit to Aristotle (no `*Aristotle.lean` companion).

## 6. Acceptance criteria

1. **All flagged Mathlib lemma names resolved** (§ 1) with verified `Mathlib/<path>:<line>` citations against HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3`.
2. **Bridge theorem fully discharged** (§ 2) with ~22 LOC proof using only verified Mathlib names; replaces C2-1d PREP's `sorry` at memo line 281.
3. **Both `#eval` predictions traced** (§ 3); C1's `some 1` confirmed, C2-1d's `⟨1, _⟩` confirmed reachable from the *corrected* entry `(⟨0,_⟩, ⟨1,_⟩)` (not from the PREP's stated `(⟨0,_⟩, ⟨0,_⟩)`).
4. **`Decidable` instance pattern tightened** (§ 1.3, § 4.2.a): `decEq _ _ |>.recOn` chain → `infer_instance`.
5. **No edits** to any other file; this PREP-D occupies a single new path under `sessions/`.
6. **Race-aware**: at push time, gh PR list confirms no overlapping open PRs targeting this slug.

## 7. Honesty

- **§ 2.4 `rfl` caveat**: I claim that `(intervalTriangulation m hm).toCellComplex.vertex i 0 = i.val` holds by `rfl`. This relies on the projection of `toCellComplex` (line 123 of `SpernerSimplicialInstance.lean`) plus the `ivtx` definition unfolding through privacy. **I have not run Docker to verify this** (per slug's `.lake` symlink trap + this being a doc-only PREP). The S2 ACT picker should verify; if `rfl` fails, the § 2.4 fallback gives a `simp`-based path.
- **§ 3 `#eval` correction**: I am claiming the C2-1d PREP has an entry-door bug. I traced this on paper; the S2 ACT picker should re-verify by reading the C2-1d PREP's `step` definition and tracing manually. If my trace is wrong, the predicted `⟨1, _⟩` output may still be correct for `(⟨0,_⟩, ⟨0,_⟩)` entry via a different mechanism I missed.
- **§ 3.2 "both-doors mathematical claim is false"**: I claim cell 0 with `c 0 = c 1 = 0` has both positions as doors. This is a direct check against the `IsDoor` definition (`SpernerMathlib4.lean:446–450`), but it's worth a sanity check by the S2 ACT picker before committing to a `step`-semantics correction.
- **§ 1.1 fallback was overkill**: C1 PREP § 4 supplied a 3-line fallback for the `Finset.toList_ne_nil_iff_nonempty` name. My replacement is 4 lines but uses *verified* names — no functional difference, but eliminates the "fallback might not work" risk.
- **No build**. Every claim about Lean type-checking in this memo is paper-only. Confidence is high (all Mathlib names verified against a specific Mathlib SHA), but the S2 ACT picker is responsible for the final Docker verification.

## 8. Race awareness

- **Open PRs on this slug at push time** (~03:30 UTC, ~25 min after the last merge):
  - 0 open research PRs (C1 #18459 merged 03:09 UTC, C2-1d #18489 merged 03:07 UTC, C3 #18392 merged 02:10 UTC).
- **Conflict surface with C1, C2-1d, C3 (all merged)**: zero. New file path under `sessions/`, no edits to other paths.
- **Race timing**: 30-min-post-merge for both C1 (03:09 UTC) and C2-1d (03:07 UTC). Within the saturation window per `feedback_mechanic_race_quadruple_slot_collision.md`, but this PREP-D is:
  - **doc-only** (no Lean file edit; minimal merge friction even if another slot lands first);
  - **orthogonal in scope** (audit + bridge, vs. parallel candidate exploration).
- **Recheck at push time** mandated.

## 9. Cross-references

- PR #18200 (MERGED) — S1 OBSERVE candidate framing.
- PR #18392 (MERGED) — C3 `findOppositeIdx` cascade audit.
- PR #18459 (MERGED) — C1 brute-force scaffold PREP (this memo resolves its § 4 flag).
- PR #18489 (MERGED) — C2-1d Scarf walk PREP (this memo discharges its line-281 `sorry` and corrects its `#eval` entry).
- `proofs/Proofs/SpernerSimplicialInstance.lean:813–814` (`ivtx`), `958–972` (`intervalTriangulation`), `123–131` (`toCellComplex`).
- `proofs/Proofs/SpernerMathlib4.lean:440–442` (`IsPanchromatic`), `446–450` (`IsDoor`), `452–457` (`decidableIsPanchromatic`).
- Mathlib v4.26.0 HEAD `23fc2795c350c2c4a5c70e289a545e81273229b3`:
  - `Mathlib/Data/Finset/Basic.lean:525` (`Finset.toList_eq_nil`)
  - `Mathlib/Data/Finset/Basic.lean:534` (`Finset.Nonempty.toList_ne_nil`)
  - `Mathlib/Data/Finset/Empty.lean:142` (`Finset.nonempty_iff_ne_empty`)
  - `Mathlib/Data/Fintype/Card.lean:327` (`Fintype.injective_iff_surjective`)
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-API-audit-driven PREP pattern; this memo extends it with **bridge-discharge + paper-trace `#eval` verification**, adding two orthogonal angles to the audit template.
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — audit-correction PREP pattern; this memo continues that pattern by flagging a substantive mathematical issue in C2-1d's "non-panchromatic ⇒ unique door" claim.
