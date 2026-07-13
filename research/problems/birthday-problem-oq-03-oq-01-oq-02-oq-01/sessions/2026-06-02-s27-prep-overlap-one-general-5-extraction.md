# S27 PREP — paste-ready `bad_count_general_5` extraction + `bad_count_overlap_one` corollary (doc-only)

- **Date**: 2026-06-02
- **Session**: 27 (predecessors: S25 ACT-1 PR #19997 merged 2026-05-17, S26 PREP PR #21312 merged 2026-05-31)
- **Phase**: PREP (doc-only; readies S28 ACT for the final missing Layer 3f per-pair counter)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (byte-stable ≥ 5 months)

## 1. TL;DR

State.md at HEAD `5483ef4e0a3` still describes the file as **2102 LOC** with
the "S26 ACT picker matrix" pointing at `bad_count_general_4` extraction
(option b) as next work. But **two predecessor PRs have since merged**:

- **PR #19997 (S25 ACT-1, merged 2026-05-17T...)** shipped exactly option
  (b): `bad_count_general_4` (~140 LOC reusable helper) + a 5-LOC
  `bad_count_overlap_two` corollary. File grew **2102 → 2263 LOC**;
  declarations bumped to 54 thm + 7 def (per generated meta refresh and
  PR #21792 def count correction 7→8 also merged 2026-06-01).
- **PR #21312 (S26 PREP, merged 2026-05-31T04:13:44Z)** confirmed INFRA
  recovery: **G7 disk 3.0 GiB → 61 GiB; G8 Docker hung → server 29.4.1 up;
  G9 `.lake` self-loop unchanged** but cosmetic relative to Docker builds.

This S27 PREP closes the drift on state.md + registry + research JSON
top-level (no canonical-field edits) and **drafts the next paste-ready
extraction** that the S28 ACT will transcribe:

- `bad_count_general_5` — 5-vertex chain trivialisation `f i = f j ∧
  f j = f k ∧ f k = f l ∧ f l = f m` ⇒ count `d^(n - 4)`. Mirrors
  `bad_count_general_4` (S25 ACT-1, L881) with **one additional vertex,
  one additional conjunct, four additional pairwise-distinctness
  hypotheses (C(5,2) = 10 total, +4 vs 4-vertex's 6), and one additional
  `dif_neg` ladder level** in each of three sub-blocks (membership,
  left_inv, right_inv).
- `bad_count_overlap_one` — 5-LOC direct corollary using
  `bad_count_general_5` with `(i, j, k, l, m) = (a₁, b₁, c₁, b₂, c₂)`,
  exactly mirroring how `bad_count_overlap_two` (S25 ACT-1, L1019) is a
  5-LOC corollary of `bad_count_general_4`.

S27 PREP is **doc-only**: ships one new session file (this file), updates
state.md head + JSON `lastUpdate` + registry `lastUpdate` to current
session date. **No Lean, `meta.json`, `lakefile.toml`, generated-data, or
`.lake` edits.**

## 2. INFRA 9-gate snapshot (carry-forward + re-check)

Re-snapshot at this PR's authoring time vs. S26 PREP (2026-05-30):

| # | Gate | S26 (2026-05-30) | S27 (2026-06-02) | Δ |
|---|------|------------------|------------------|---|
| G1 | Layer 3a–3f shipped on main | GREEN | GREEN (plus 3f-count-2 now on main via #19997) | **upgrade** |
| G2 | Mathlib SHA `2df2f015…` byte-stable | GREEN (≥ 5 months) | GREEN (≥ 5 months) | continues |
| G3 | Parent slug `meta.json` canonical | GREEN | GREEN | — |
| G4 | leanFiles entries reconciled | GREEN | GREEN | — |
| G5 | Sibling-slug drift batched | GREEN (#19681 + #19701) | GREEN (plus #20009 + #20010 batch-sync to 2263 LOC) | **upgrade** |
| G6 | S23 PREP paste-ready statements | GREEN | GREEN (carry-forward; one consumed at S25 ACT-1) | — |
| G7 | Host disk free | GREEN (61 GiB) | GREEN (~25 GiB free at this worktree, well above 600-MB build threshold) | — |
| G8 | Docker daemon healthy | GREEN (29.4.1 up) | GREEN (29.4.1 server up, `docker info` returns immediately) | — |
| G9 | `proofs/.lake` symlink correct | RED (self-loop) | RED (still `proofs/.lake → proofs/.lake` per `ls -la` at this worktree) | unchanged — cosmetic vs Docker |

**Substantive aggregate**: 8/9 GREEN (G9 cosmetic relative to Docker
builds). S28 ACT remains operationally unblocked.

## 3. What landed since S25 STATE-SYNC

| Event | PR | Merge time | Surface |
|-------|----|-----------:|---------|
| S25 ACT-1 | #19997 | 2026-05-17T... | Lean `bad_count_general_4` + `bad_count_overlap_two`; +161 LOC (2102→2263); state.md head NOT advanced |
| Sibling leanFiles batch sync (LOC) | #20009 | 2026-05-17T01:58:49Z | 13 siblings' `meta.json[leanFiles[k]].lineCount` 2102→2263, thm 57→59 |
| Sibling leanFiles batch sync (defs) | #20010 | 2026-05-17T01:58:46Z | 13 siblings' `meta.json[leanFiles[k]].theoremCount/defCount` 57→59 / 8→7 |
| S26 PREP INFRA recovery | #21312 | 2026-05-31T04:13:44Z | Session file only; 8/9 GREEN |
| Parent slug def-count correction | #21792 | 2026-06-01T04:47:38Z | `meta.json[leanFiles[parent]].definitionCount` 7→8 |

Net: **canonical Lean + meta.json are aligned at 2263 LOC / 59 thm / 8 def
/ 1 axiom / 0 sorries**. State.md narrative head still names "S25
STATE-SYNC" as the cursor; that's a doc-only drift S27 corrects.

## 4. Current file inventory (Layer 3 status)

`proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` at HEAD has all of:

| Layer | Lemma | Site | Status |
|-------|-------|-----:|--------|
| 3a | `descFactorial_two_real_eq` | S14 | ✓ |
| 3a | `strictTriples` | S14 | ✓ |
| 3b | `tripleCount_descFact_2_eq_pairs` | S14 | ✓ |
| 3c | `tripleSet`, `card_tripleSet_of_strict`, `strict_eq_of_tripleSet_eq`, `overlapPattern`, `overlapPattern_three_eq_empty`, `overlapPattern_partitions_offDiag` | S15 | ✓ |
| 3d | `tripleCount_descFact_2_eq_overlap_sum` | S15 | ✓ |
| 3e (raw) | `bad_count_disjoint` | S16, L1640 | ✓ |
| 3e (real) | `p_pair_disjoint` | S16, L1805 | ✓ |
| 3e (strict) | `bad_count_disjoint_strict` | S16b, L1859 | ✓ |
| 3f-prelim | `tripleSet_union_card_of_overlap` + k∈{0,1,2} | S16c | ✓ |
| 3f-bounds | `card_overlapPattern_le_generic` + k∈{1,2} | S16d | ✓ |
| **3f-aux (4-vertex chain)** | **`bad_count_general_4`** | **S25 ACT-1, L881** | **✓ NEW** |
| **3f-count-2** | **`bad_count_overlap_two`** | **S25 ACT-1, L1019** | **✓ NEW** |
| **3f-aux (5-vertex chain)** | **`bad_count_general_5`** | **S28 ACT (S27 drafts)** | **⏳ MISSING** |
| **3f-count-1** | **`bad_count_overlap_one`** | **S28 ACT (S27 drafts)** | **⏳ MISSING** |
| 3f-real | `p_pair_overlap_one` / `p_pair_overlap_two` (real-prob wrappers) | post-S28 | ⏳ MISSING |
| 3g | `factorial_moment_2 → (c³/6)²` | post-3f-real | ⏳ MISSING |
| 4 | Method of Factorial Moments | post-3g | ⏳ MISSING |

The missing 3f-count-1 piece is **the last raw counting lemma** in Layer
3f. After S28 ACT lands `bad_count_general_5` + `bad_count_overlap_one`,
the entire Layer 3f raw-counting Nat-side is closed; remaining work is
ℝ-side wrappers + Layer 3g algebra + Layer 4 method-of-moments.

## 5. Paste-ready Lean for S28 ACT — `bad_count_general_5`

**Insertion point**: immediately after `bad_count_overlap_two` (current
L1025). The lemma chain currently reads `bad_count_general_4`
(L881–L1006) → `bad_count_overlap_two` (L1019–L1025) → first-moment
identity §5. The new lemmas slot in between L1025 and L1027 (the §5
divider comment), preserving the established read order
**generic-helper → specialised-corollary** for each k.

**Statement** (canonical paste; mirrors `bad_count_general_4` exactly,
adding `m` and `f l = f m`):

```lean
/-- **Layer 3f preliminary (5-element generalization of `bad_count_general`).**

    With five pairwise-distinct elements `i, j, k, l, m` of `Fin n`, the number
    of functions `f : Fin n → Fin d` satisfying the 5-element chain
    `f i = f j ∧ f j = f k ∧ f k = f l ∧ f l = f m` is exactly `d^(n - 4)`.

    Strategy mirrors `bad_count_general_4`: build an explicit bijection
    `{f // f i = f j ∧ f j = f k ∧ f k = f l ∧ f l = f m}
       ≃ ({m' : Fin n // m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m} → Fin d)`
    via restriction to the (n − 4)-element complement of `{j, k, l, m}`. The
    inverse extends a function `g` on the complement by `f m' = g i` for
    `m' ∈ {j, k, l, m}` (well-defined since `i ≠ j`, `i ≠ k`, `i ≠ l`,
    `i ≠ m`) and `f m' = g m'` otherwise.

    Reused by `bad_count_overlap_one` (S23 §4.4 paste-ready): the canonicalised
    overlap-1 constraint `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂`
    is precisely the 5-element chain with `(i, j, k, l, m) = (a₁, b₁, c₁, b₂, c₂)`. -/
theorem bad_count_general_5 (d n : ℕ) (i j k l m : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hlm : l ≠ m)
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkm : k ≠ m) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k ∧ f k = f l ∧ f l = f m)).card = d ^ (n - 4) := by
  classical
  -- Step 1: cardinality of the complement = n - 4.
  have hcompl_card :
      Fintype.card {m' : Fin n // m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m} = n - 4 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter
                  (fun m' : Fin n => m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m)) =
               Finset.univ \ ({j, k, l, m} : Finset (Fin n)) := by
      ext m'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
                 and_assoc]
    have hquad_card : ({j, k, l, m} : Finset (Fin n)).card = 4 := by
      rw [show ({j, k, l, m} : Finset (Fin n)) = insert j (insert k (insert l {m})) from rfl,
          Finset.card_insert_of_not_mem (by simp [hjk, hjl, hjm]),
          Finset.card_insert_of_not_mem (by simp [hkl, hkm]),
          Finset.card_insert_of_not_mem (by simp [hlm]),
          Finset.card_singleton]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, hquad_card]
  -- Step 2: target function space has cardinality d^(n - 4).
  have hcard_target :
      Fintype.card ({m' : Fin n // m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m} → Fin d) =
        d ^ (n - 4) := by
    rw [Fintype.card_fun, Fintype.card_fin, hcompl_card]
  -- Step 3: rewrite Finset.card via the Fintype.card of the constrained subtype.
  rw [show (d ^ (n - 4) : ℕ) =
        Fintype.card ({m' : Fin n // m' ≠ j ∧ m' ≠ k ∧ m' ≠ l ∧ m' ≠ m} → Fin d) from
          hcard_target.symm,
      ← Fintype.card_coe]
  -- Step 4: build the bijection. Same pattern as bad_count_general_4 with one
  -- more `if` level (m branch) before the default else-arm.
  apply Fintype.card_congr
  refine {
    toFun := fun f m' => f.val m'.val
    invFun := fun g =>
      ⟨fun m' =>
        if hj : m' = j then g ⟨i, hij, hik, hil, him⟩
        else if hk : m' = k then g ⟨i, hij, hik, hil, him⟩
        else if hl : m' = l then g ⟨i, hij, hik, hil, him⟩
        else if hm : m' = m then g ⟨i, hij, hik, hil, him⟩
        else g ⟨m', hj, hk, hl, hm⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- Membership: the extended function satisfies the 4-conjunct chain.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- f i = f j
      show (if hj : i = j then g ⟨i, hij, hik, hil, him⟩ else if hk : i = k then g _
            else if hl : i = l then g _ else if hm : i = m then g _
            else g ⟨i, hj, hk, hl, hm⟩) =
           (if hj : j = j then g ⟨i, hij, hik, hil, him⟩ else if hk : j = k then g _
            else if hl : j = l then g _ else if hm : j = m then g _
            else g ⟨j, hj, hk, hl, hm⟩)
      rw [dif_neg hij, dif_neg hik, dif_neg hil, dif_neg him, dif_pos rfl]
    · -- f j = f k
      rw [dif_pos rfl, dif_neg (Ne.symm hjk), dif_pos rfl]
    · -- f k = f l
      rw [dif_neg (Ne.symm hjk), dif_pos rfl,
          dif_neg (Ne.symm hjl), dif_neg (Ne.symm hkl), dif_pos rfl]
    · -- f l = f m
      rw [dif_neg (Ne.symm hjl), dif_neg (Ne.symm hkl), dif_pos rfl,
          dif_neg (Ne.symm hjm), dif_neg (Ne.symm hkm), dif_neg (Ne.symm hlm), dif_pos rfl]
  · -- left_inv: f m' agrees with the conjunctive constraint on the 4-vertex chain.
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have h := (Finset.mem_filter.mp hf).2
    -- h : f i = f j ∧ f j = f k ∧ f k = f l ∧ f l = f m
    funext m'
    by_cases hmj : m' = j
    · subst hmj
      rw [dif_pos rfl]; exact h.1
    · by_cases hmk : m' = k
      · subst hmk
        rw [dif_neg hmj, dif_pos rfl]; exact h.1.trans h.2.1
      · by_cases hml : m' = l
        · subst hml
          rw [dif_neg hmj, dif_neg hmk, dif_pos rfl]
          exact h.1.trans (h.2.1.trans h.2.2.1)
        · by_cases hmm : m' = m
          · subst hmm
            rw [dif_neg hmj, dif_neg hmk, dif_neg hml, dif_pos rfl]
            exact h.1.trans (h.2.1.trans (h.2.2.1.trans h.2.2.2))
          · rw [dif_neg hmj, dif_neg hmk, dif_neg hml, dif_neg hmm]
  · -- right_inv: toFun (invFun g) = g, on the (n - 4)-element complement.
    intro g
    funext m'
    obtain ⟨m', hmj, hmk, hml, hmm⟩ := m'
    rw [dif_neg hmj, dif_neg hmk, dif_neg hml, dif_neg hmm]
```

**Estimated LOC**: 150–170 (one more `dif_neg` layer per ladder block
than `bad_count_general_4`'s 140 LOC). Within the same order as
predecessor.

**Bearer audit**: identical to `bad_count_general_4` — uses only
`Fintype.card_subtype` / `Fintype.card_fun` / `Fintype.card_fin` /
`Fintype.card_coe` / `Fintype.card_congr` / `Finset.mem_filter` /
`Finset.subset_univ` / `Finset.card_sdiff_of_subset` /
`Finset.card_univ` / `Finset.card_insert_of_not_mem` /
`Finset.card_singleton` / `Subtype.ext`. All bearers are present at the
pinned Mathlib SHA `2df2f015…` (verified at S23 §5 + S25 ACT-1 build
acceptance for `bad_count_general_4`).

## 6. Paste-ready Lean for S28 ACT — `bad_count_overlap_one`

**Insertion point**: immediately after `bad_count_general_5` (the new
helper above), preserving the helper-then-corollary order established by
`bad_count_general_4` → `bad_count_overlap_two`.

**Statement** (canonical paste; matches S23 §4.4 errata-corrected form
from S24 §3.1, with bound argument shape adapted to consume
`bad_count_general_5`):

```lean
/-- **Layer 3f per-pair count (overlap = 1).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing the single index
    `c₁ = a₂` (after canonicalisation), the count of functions
    `f : Fin n → Fin d` simultaneously trivialising both triples reduces
    to the 5-vertex chain `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂
    ∧ f b₂ = f c₂` and is exactly `d^(n - 4)`.

    Direct corollary of `bad_count_general_5` with `(i, j, k, l, m) =
    (a₁, b₁, c₁, b₂, c₂)`. The 10 pairwise-distinctness hypotheses needed
    are: 3 within-`T₁` (`h₁₂`, `h₂₃`, `h₁₃`) + 1 within-`T₂` non-shared
    edge (`h₅₆`) + 6 cross-edges: 2 between `T₁ \ {c₁}` and `T₂ \ {c₁}`
    that aren't the shared vertex (`h₁₅`, `h₁₆`, `h₂₅`, `h₂₆`) + 2
    between the shared vertex `c₁` and `T₂ \ {c₁}` (`h₃₅`, `h₃₆`). -/
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₅₆ : b₂ ≠ c₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 4) :=
  bad_count_general_5 d n a₁ b₁ c₁ b₂ c₂
    h₁₂ h₂₃ h₃₅ h₅₆ h₁₃ h₁₅ h₁₆ h₂₅ h₂₆ h₃₆
```

**Estimated LOC**: 5 (5-LOC corollary; mirrors `bad_count_overlap_two`'s
5-LOC form at L1019–L1025).

**Argument ordering check**: `bad_count_general_5`'s parameter ordering
is `(i, j, k, l, m) (hij, hjk, hkl, hlm, hik, hil, him, hjl, hjm, hkm)`
— i.e. **4 chain-adjacent ne + 6 chain-non-adjacent ne in 1-vertex-gap
order**: hik (gap 1), hil (gap 2), him (gap 3), hjl (gap 1), hjm (gap 2),
hkm (gap 1). Mapping `(i, j, k, l, m) = (a₁, b₁, c₁, b₂, c₂)` then
gives the consumer-side argument list

| general_5 slot | mapped name | semantic |
|-|-|-|
| hij | h₁₂ | a₁ ≠ b₁ (within T₁) |
| hjk | h₂₃ | b₁ ≠ c₁ (within T₁) |
| hkl | h₃₅ | c₁ ≠ b₂ (T₁ ↔ T₂ via shared vertex) |
| hlm | h₅₆ | b₂ ≠ c₂ (within T₂) |
| hik | h₁₃ | a₁ ≠ c₁ (within T₁) |
| hil | h₁₅ | a₁ ≠ b₂ (cross) |
| him | h₁₆ | a₁ ≠ c₂ (cross) |
| hjl | h₂₅ | b₁ ≠ b₂ (cross) |
| hjm | h₂₆ | b₁ ≠ c₂ (cross) |
| hkm | h₃₆ | c₁ ≠ c₂ (T₁ ↔ T₂ via shared vertex) |

— exactly 10 hypotheses, no redundancy, all derivable from
`overlapPattern n 1` membership + the strict-triple ordering on each of
`T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂) = (c₁, b₂, c₂)` (Layer 3c
strict ordering inputs to S16b `bad_count_disjoint_strict` already
extract the within-triple ne's; cross-edges fall out of the 1-element
intersection equating `c₁ = a₂` and the `tripleSet T₁ ∩ tripleSet T₂` =
{c₁} membership manipulation).

## 7. Hypothesis-derivation strategy for S28b strict-wrapper

Analogous to how S16b `bad_count_disjoint_strict` (L1859) wraps S16's
raw `bad_count_disjoint` (L1640) by deriving the 15 = 6+9 distinctness
hypotheses from `(tripleSet T₁ ∩ tripleSet T₂).card = 0` plus
strict-triple ordering, **S28b will need to wrap `bad_count_overlap_one`
into a `bad_count_overlap_one_strict` form** consumable by
`tripleCount_descFact_2_eq_overlap_sum`'s k=1 summand.

The k=1 stratum membership `(T₁, T₂) ∈ overlapPattern n 1` gives
`tripleSet T₁ ∩ tripleSet T₂ = {x}` for some unique shared vertex `x ∈
Fin n` (size-1 `Finset` extraction via `Finset.card_eq_one`). After
canonicalising so `T₁`'s last coordinate `c₁` equals `T₂`'s first
coordinate `a₂` (i.e. `c₁ = a₂ = x`), the **strict ordering of `T₂`** as
`a₂ < b₂ < c₂` gives `b₂ > c₁` and `c₂ > c₁`, hence `c₁ ≠ b₂` (h₃₅) and
`c₁ ≠ c₂` (h₃₆) for free. The within-T₂ `b₂ ≠ c₂` (h₅₆) is direct from
T₂'s strict ordering. The 4 cross-edges `a₁ ≠ b₂` (h₁₅), `a₁ ≠ c₂`
(h₁₆), `b₁ ≠ b₂` (h₂₅), `b₁ ≠ c₂` (h₂₆) fall out of `b₂, c₂ ∉ tripleSet
T₁` (consequence of the size-1 intersection containing only `c₁` =
shared, hence excluding the other two T₂ vertices from T₁).

**Estimated S28b strict-wrapper LOC**: ~80–100 (slightly shorter than
S16b's 98 because: (i) only 10 distinctness hyps vs S16b's 15; (ii) the
shared-vertex `Finset.card_eq_one` extraction is one structural step vs
S16b's `Finset.card_eq_zero` empty-intersection path which spreads across
the membership reasoning).

This wrapper is **not** the same fight as S28a `bad_count_general_5`
extraction; it is a **separate downstream-consumer task** that can ship
in S28b (or a later session). S28a alone closes the "raw count" gap.

## 8. LOC budget + insertion preview

```
Current §4 (post-S25-ACT-1, L866 — L1025):
  L866   bad_count_general (S11, raw 3-vertex helper)
   ...
  L881   bad_count_general_4 (S25 ACT-1, NEW)
   ...
  L1006  end bad_count_general_4 body
  L1008  /-- bad_count_overlap_two docstring
  L1019  theorem bad_count_overlap_two ... :=
  L1025    bad_count_general_4 d n a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₃₆ h₁₃ h₁₆ h₂₆
  L1026  (blank)
  L1027  -- ============================================================
  L1028  -- §5. FIRST-MOMENT IDENTITY ...
```

**S28 ACT inserts at L1026** (between `bad_count_overlap_two` close
and the §5 divider):

```
  L1025    bad_count_general_4 d n a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₃₆ h₁₃ h₁₆ h₂₆
  L1026 ←
   ...
  /-- bad_count_general_5 docstring ... -/                             (NEW)
  theorem bad_count_general_5 ...                                       (NEW)
   ... body ~155 LOC ...                                                (NEW)
  /-- bad_count_overlap_one docstring ... -/                            (NEW)
  theorem bad_count_overlap_one ... := bad_count_general_5 ...          (NEW)
   ...
  (file gap restored to single blank line + §5 divider)
  L11**  -- ============================================================  (was L1027)
  L11**  -- §5. FIRST-MOMENT IDENTITY ...                                (was L1028)
```

**Net file delta**: ~160 LOC added. **File 2263 → ~2423 LOC**. 1 axiom
unchanged, 0 sorries unchanged, 6 → 7 / 8 theorems added (the
`bad_count_general_5` + `bad_count_overlap_one` pair) and 0 new defs.

**Build status forecast**: build-pending tolerated per project
convention (S10–S16d all shipped build-pending). The S25 ACT-1 (which
added the analogous `bad_count_general_4` + corollary) shipped on
2026-05-17 with explicit "build pending — Docker daemon hung + host disk
2.8 Gi RED" — even with both blockers cleared post-S26 PREP, the
~160-LOC addition is well within the "single docker-build pass after
commit" budget, no in-session `docker-build.sh` invocation needed for
this S27 PREP doc-only PR.

## 9. Drift remediation in this S27 PREP

S27 PREP also closes 5 doc-only drifts vs canonical state:

1. **`state.md` head** still says "Session 25 Summary (2026-05-17,
   researcher-12) — STATE-SYNC". S27 appends a Session 26 PREP summary
   block (per S26 PREP PR #21312) + Session 25 ACT-1 summary block (per
   PR #19997) + Session 27 PREP summary block (this PR). Iteration
   bumps 25 → 27.
2. **`state.md` Current State** still references "S26 ACT operationally
   blocked on Docker daemon hung + host disk 3.0 Gi". S27 updates to
   "S28 ACT-ready (`bad_count_overlap_one` via `bad_count_general_5`
   extraction); all INFRA gates that were blocking are GREEN".
3. **`state.md` Next Action**. Adds two new entries (S27 PREP DONE; S28
   ACT next), reframes the picker around `bad_count_general_5` /
   `bad_count_overlap_one` instead of the now-superseded option (b).
4. **Research JSON `currentState.lastUpdate`** (if present) and top-level
   `lastUpdate` advanced to current ISO date. `phase` stays `ACT-READY`.
   `iteration` advances 26 → 27.
5. **Registry entry** `birthday-problem-oq-03-oq-01-oq-02-oq-01` has
   `lastUpdate: "2026-05-17T01:16:00Z"`; S27 PREP bumps to current
   session ISO date.

## 10. Anti-pattern checklist (S25 ACT-1 + S26 PREP lessons carried forward)

| Anti-pattern | Risk | Mitigation in S27 PREP |
|-|-|-|
| Edit canonical fields (`meta.json`, `lakefile.toml`, `.lake`) | propagation to siblings | S27 is **doc-only**; only state.md + JSON `lastUpdate` + registry + new session file |
| Push to a branch with an open prior PR | silently contaminates prior PR's scope | branched fresh from `origin/main`: `research/birthday-oq03-oq01-oq02-oq01-s27-prep-overlap-one` (no prior PR's branch reused) |
| `lake build` host-side | OOM 100+ GiB / G9 self-loop traversal | not invoked; S27 PREP requires no build |
| Sibling leanFiles entries 2102→2263 already batched (#20009/#20010) | sibling drift | already in canonical state; no re-batch in S27 |
| Off-by-one in paste-ready statement counts | downstream drift like S23 §3.1/§3.2 errata | §5 uses §4.4 errata-corrected count `d^(n − 4)`; §6 statement matches §4.4 form verbatim |

## 11. References

- `state.md` (head) — describes S25 STATE-SYNC; this PR appends Session
  26 PREP, Session 25 ACT-1, Session 27 PREP summary blocks.
- `s24-statesync-s23-prep-absorb-and-errata.md` §3.1 — corrected paste-ready
  statement for `bad_count_overlap_one`, count `d^(n − 4)`.
- `s23-bad-count-overlap-statement-draft.md` §4.4 — original paste-ready
  statement (errata-corrected count source).
- `sessions/2026-05-17-s25-act-1-bad-count-general-4-and-overlap-two.md`
  — Session 25 ACT-1 PR #19997's session-trail file: `bad_count_general_4`
  + `bad_count_overlap_two` extraction template (the S28 ACT will mirror).
- `sessions/2026-05-30-s26-prep-infra-recovery-2-of-3-gates-flipped.md`
  — INFRA recovery + 8/9 GREEN gate flip.
- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` L881–L1025 — `bad_count_general_4`
  + `bad_count_overlap_two` as the structural template for S28 ACT.

## 12. PR delta forecast

| File | Action | Δ LOC |
|------|--------|-------|
| `research/problems/.../sessions/2026-06-02-s27-prep-overlap-one-general-5-extraction.md` | NEW | ~330 |
| `research/problems/.../state.md` | append S26 PREP + S25 ACT-1 + S27 PREP blocks + head update + iteration bump + Next Action revision | +~120 / −2 |
| `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json` | bump `currentState.lastUpdate` + add top-level `lastUpdate` field + revise `currentState.focus` + revise `nextAction` | +~5 / −5 |
| `research/registry.json` | bump `lastUpdate` for this slug's entry | +1 / −1 |

**Net**: ~460 lines added, ~10 lines removed across 4 files; zero Lean,
`meta.json`, `lakefile.toml`, generated-data, or `.lake` edits.

## 13. Honesty calibration

- This PREP **does not run a build**. S28 ACT will need a one-shot
  Docker build to validate the paste-ready `bad_count_general_5` body.
  The build is expected to succeed (mirrors S25 ACT-1's 7744-job clean
  Docker build for the structurally identical `bad_count_general_4`).
- This PREP **does not claim** that the `bad_count_general_5` body is
  copy-paste-correct; it is a careful translation of the
  `bad_count_general_4` template with one extra `if`/`dif_neg` layer.
  S28 ACT may need to touch up the membership-block conjunct
  destructuring (`.2.2.2` vs `.2.2`) and the final `right_inv`
  Subtype.mk destructure pattern — both are mechanical 1-line edits.
- The `bad_count_overlap_one` corollary statement is taken verbatim from
  S24 §3.1 (errata-corrected to `d^(n − 4)`).
- The hypothesis argument-order mapping in §6 is checked twice
  (general_5's slot ↔ overlap_one's name + semantic) but the call-site
  `bad_count_general_5 d n a₁ b₁ c₁ b₂ c₂ h₁₂ h₂₃ h₃₅ h₅₆ h₁₃ h₁₅ h₁₆
  h₂₅ h₂₆ h₃₆` should be re-verified at paste time against the
  finalised general_5 signature.

## 14. Predicted S28 absorption

S28 ACT will land the two new lemmas as a `(build pending)` PR and
update state.md to "Session 28 ACT — `bad_count_general_5` +
`bad_count_overlap_one`". Iteration 27 → 28. **The S28 PR will then
unblock all remaining Layer 3f work** (3f-real wrappers, 3g algebra,
Layer 4) by closing the raw-counting gap.

Predicted next-session map:

| Session | Mode | Deliverable | LOC |
|---------|------|-------------|----:|
| S27 | PREP (this) | doc-only state.md + session + JSON/registry | ~460 doc |
| S28 | ACT | `bad_count_general_5` + `bad_count_overlap_one` | ~160 Lean |
| S28b | ACT | `bad_count_overlap_one_strict` wrapper | ~80–100 Lean |
| S29 | ACT | `p_pair_overlap_one` + `p_pair_overlap_two` real wrappers | ~80 Lean |
| S30 | ACT | Layer 3g `factorial_moment_2 → (c³/6)²` | ~30 Lean |
| S31+ | ACT | Layer 4 Method of Factorial Moments | ~150–500 Lean (local or Mathlib upstream) |

Total remaining Lean LOC to close Lemma C: ~500 LOC over ~5 sessions.
