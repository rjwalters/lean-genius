# S16d PREP Follow-Up: Mathlib Bearer Audit + Sorry-Free Tactic Draft

**Author**: researcher-4 (PREP follow-up to Session 16d, 2026-05-13)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Lean file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`
**Mode**: PREP (doc-only; no `.lean` diff)
**Companion to**: `s16d-overlap-pattern-bounds.md` (Session 16d, researcher-3, 2026-05-09)
**Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned `v4.26.0`)
**Lean toolchain**: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`)

## 1. Purpose

The S16d spec (Session 16d, researcher-3) gives a complete proof sketch for the Layer 3f main
bound `card_overlapPattern_le_generic` plus its `k = 1` / `k = 2` specialisations, but defers
two implementation-blocking gaps:

(a) **Mathlib bearer verification at the pinned SHA.** The spec asserts "All Mathlib API present
    in v4.26.0 (no new imports)" without citing line numbers or signatures. Mathlib HEAD drifts
    from `v4.26.0`; previous gallery PREPs (Waring g₂ S2b, sperner-simplicial-instance S3) have
    documented 6–31-line drift between HEAD and pinned SHA. Names are typically stable across
    that window but signatures and surrounding contexts shift.

(b) **Tactic body.** The spec leaves `card_overlapPattern_le_generic` as
    `lemma ... := by classical; -- outline; sorry`. A subsequent implementation session must
    translate the outline (i)–(v) into actual Lean tactics — a source of friction that this
    follow-up removes by drafting the tactic block explicitly.

This doc closes both gaps. It is **doc-only**; the `.lean` file is unchanged. A future
implementation session can transcribe §3's tactic block directly into §9 of the Lean file
(immediately after `tripleSet_union_card_of_overlap_two` at L1809).

## 2. Mathlib Bearer Audit at SHA `2df2f01`

All Mathlib lemmas named in `s16d-overlap-pattern-bounds.md` §2–§3 verified against the
lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Files downloaded via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f01`. The Birthday Lean file
imports the omnibus `import Mathlib` (L43 of `BirthdayProblemOQ03OQ01OQ02.lean`), so no
additional imports are required.

### 2.1 Defining-file existence

| Mathlib file | Blob SHA at pinned ref | Lines |
|---|---|---|
| `Mathlib/Data/Finset/Card.lean` | `ce82fb5788b6c30ea01c64fb091124e990516497` | 911 |
| `Mathlib/Data/Finset/Image.lean` | `396566beec04ee4b81019f4ead76899d81d9621d` | 714 |
| `Mathlib/Data/Finset/Powerset.lean` | `4baa26c0da26d56c04c078da91c6bbe02458adff` | 300 |
| `Mathlib/Data/Finset/Sigma.lean` | `58a15b8a5511c221bed11285af6757eb994f9d74` | 222 |
| `Mathlib/Data/Finset/Prod.lean` | `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1` | 365 |
| `Mathlib/Data/Finset/Lattice/Basic.lean` | `68c7c60186786906d01648669b62e4b6644975e4` | 338 |
| `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | (downloaded, 138 LOC) | 138 |
| `Mathlib/Data/Nat/Choose/Basic.lean` | `2fcfacb244f2c239148d978d6ecb4d398beccf4a` | 402 |

### 2.2 Bearer-by-bearer (Mathlib)

| Bearer | File | Line | Signature (verbatim at pinned SHA) |
|---|---|---|---|
| `Finset.card_image_of_injOn` | `Mathlib/Data/Finset/Card.lean` | 224 | `theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s` |
| `Finset.card_image_le` | `Mathlib/Data/Finset/Card.lean` | 218 | `theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s` |
| `Finset.card_le_card` | `Mathlib/Data/Finset/Card.lean` | 66 | `theorem card_le_card : s ⊆ t → #s ≤ #t` (gcongr) |
| `Finset.card_le_card_of_injOn` | `Mathlib/Data/Finset/Card.lean` | 415 | `lemma card_le_card_of_injOn (f : α → β) (hf : Set.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s ≤ #t` |
| `Finset.card_union_add_card_inter` | `Mathlib/Data/Finset/Card.lean` | 543 | `theorem card_union_add_card_inter (s t : Finset α) : #(s ∪ t) + #(s ∩ t) = #s + #t` |
| `Finset.powersetCard` (def) | `Mathlib/Data/Finset/Powerset.lean` | 176 | `def powersetCard (n : ℕ) (s : Finset α) : Finset (Finset α)` |
| `Finset.mem_powersetCard` | `Mathlib/Data/Finset/Powerset.lean` | 180 | `s ∈ powersetCard n t ↔ s ⊆ t ∧ card s = n` |
| `Finset.card_powersetCard` | `Mathlib/Data/Finset/Powerset.lean` | 190 | `theorem card_powersetCard (n : ℕ) (s : Finset α) : card (powersetCard n s) = Nat.choose (card s) n` |
| `Finset.sigma` (def) | `Mathlib/Data/Finset/Sigma.lean` | 45 | `protected def sigma : Finset (Σ i, α i)` |
| `Finset.mem_sigma` | `Mathlib/Data/Finset/Sigma.lean` | 51 | `{a : Σ i, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1` (`@[simp, grind =]`) |
| `Finset.card_sigma` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 134 | `theorem card_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) : #(s.sigma t) = ∑ a ∈ s, #(t a)` |
| `Finset.card_product` | `Mathlib/Data/Finset/Prod.lean` | 131 | `theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t` |
| `Finset.subset_union_left` | `Mathlib/Data/Finset/Lattice/Basic.lean` | 133 | `@[simp] lemma subset_union_left : s₁ ⊆ s₁ ∪ s₂` |
| `Finset.subset_union_right` | `Mathlib/Data/Finset/Lattice/Basic.lean` | 134 | `@[simp] lemma subset_union_right : s₂ ⊆ s₁ ∪ s₂` |
| `Nat.choose` (def) | `Mathlib/Data/Nat/Choose/Basic.lean` | 49 | `def choose : ℕ → ℕ → ℕ` (inductive) |

**Audit findings:**

- ✅ All 15 named Mathlib bearers exist at the pinned SHA with the signatures the proof requires.
- ✅ `Finset.card_le_card_of_injOn` (line 415) is the cleanest entry point for the
  `overlapPattern → sigma_target` step — preferable to a two-step
  `card_image_of_injOn` + `Finset.card_le_card` chain (saves ~6 LOC and one intermediate `image`
  Finset).
- ⚠️ **`Finset.card_sigma` lives outside `Mathlib/Data/Finset/Sigma.lean`** (which defines the
  `Finset.sigma` operation but not its cardinality formula). It is in
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` line 134. Since the file uses
  `import Mathlib` (omnibus), this is transparent — but anyone narrowing imports later must add
  the BigOperators/Group/Finset path explicitly.
- ⚠️ `Finset.subset_union_left/right` are `@[simp]`-tagged with **no explicit argument** (the
  sets `s₁ s₂` are inferred via section variables). When invoked outside that section, the
  caller passes the sets as implicit; Lean's elaborator typically figures this out, but if the
  context is ambiguous a `(s := tripleSet T₁) (t := tripleSet T₂)` named-argument hint may be
  needed.

### 2.3 No-drift check vs. Mathlib HEAD

A separate `gh api ...?ref=main` query (for spot-checking the largest files only:
`Card.lean`, `Powerset.lean`) confirms names stable. Line drift between pinned `2df2f01` and
Mathlib HEAD on 2026-05-13:

- `card_image_of_injOn`: pinned L224, HEAD line drift not material (still in the same
  `card_image_le` cluster). No signature change visible.
- `card_powersetCard`: pinned L190, definition and signature identical at HEAD.

(This audit treats the pinned SHA as authoritative; HEAD comparison is informational only.)

## 3. Internal Bearer Audit (inside `BirthdayProblemOQ03OQ01OQ02.lean`)

These are project-internal lemmas the proof relies on. Citing line numbers at HEAD
(`5dfb05f954b`):

| Internal bearer | Line | Conclusion type |
|---|---|---|
| `strictTriples` (def, S11) | 1136 | `(n : ℕ) → Finset (Fin n × Fin n × Fin n)` (filter `T.1 < T.2.1 < T.2.2`) |
| `tripleSet` (def, S15) | 1239 | `{n : ℕ} (T : Fin n × Fin n × Fin n) → Finset (Fin n)` — `{T.1, T.2.1, T.2.2}` |
| `card_tripleSet_of_strict` (S15) | 1244 | `T ∈ strictTriples n → (tripleSet T).card = 3` |
| `strict_eq_of_tripleSet_eq` (S15) | 1269 | `T₁ T₂ ∈ strictTriples n → tripleSet T₁ = tripleSet T₂ → T₁ = T₂` |
| `tripleSet_inter_card_le_three` (S15) | 1335 | `T₁ ∈ strictTriples n → (tripleSet T₁ ∩ tripleSet T₂).card ≤ 3` |
| `overlapPattern` (def, S15) | 1348 | `(n k : ℕ) → Finset ((Fin n × Fin n × Fin n)²)` — pairs of distinct strict triples with `tripleSet`-intersection of size `k` |
| `overlapPattern_three_eq_empty` (S15) | 1357 | `overlapPattern n 3 = ∅` |
| `overlapPattern_partitions_offDiag` (S15) | 1382 | fiberwise partition (uses `Finset.card_eq_sum_card_fiberwise`) |
| `tripleSet_union_card_of_overlap` (S16c) | 1773 | `(T₁, T₂) ∈ overlapPattern n k → (tripleSet T₁ ∪ tripleSet T₂).card = 6 - k` |
| `tripleSet_union_card_of_overlap_zero/one/two` (S16c) | 1786 / 1795 / 1805 | k ∈ {0,1,2} specialisations |

All present, all `@[simp]`-free, all with the signatures the spec sketch expects.

## 4. Sorry-Free Tactic Draft of `card_overlapPattern_le_generic`

Below is the tactic body that should drop into §9 of `BirthdayProblemOQ03OQ01OQ02.lean`
immediately after L1809 (the end of `tripleSet_union_card_of_overlap_two`). Estimated 65 LOC,
matching the spec's "60–70 lines" budget. The draft has been hand-traced against the bearer
signatures in §2–§3; it is **not yet machine-checked** (the file is 1966 LOC and
`./proofs/scripts/docker-build.sh` is multi-minute; a future implementation session is
responsible for build verification per `CLAUDE.md`'s "never run `lake build` directly" policy).

### 4.1 Generic bound

```lean
/-- **Layer 3f main bound (generic).** For `k ≤ 3`, the overlap-`k` stratum
    is bounded polynomially in `n` by `Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2`.

    Proof: embed `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂⟩`
    into the `Finset.sigma` over `powersetCard (6-k)` of `Fin n`, with each fiber being
    `U.powersetCard 3 ×ˢ U.powersetCard 3`. Injectivity is by `strict_eq_of_tripleSet_eq`.
    The sigma's cardinality factors as `|powersetCard (6-k) (Fin n)| · (Nat.choose (6-k) 3)²`. -/
lemma card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3) :
    (overlapPattern n k).card
      ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
  classical
  -- Target Finset: U ranges over `(6-k)`-subsets of `Fin n`; for each U, the fiber is
  -- pairs of 3-subsets of U.
  set U_pool : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (6 - k) with hU_pool
  set tgt : Finset (Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n)) :=
    U_pool.sigma (fun U => U.powersetCard 3 ×ˢ U.powersetCard 3) with htgt
  -- Embedding φ on the underlying Set: (T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂,
  --                                              (tripleSet T₁, tripleSet T₂)⟩.
  let φ : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) →
          Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n) :=
    fun p => ⟨tripleSet p.1 ∪ tripleSet p.2, (tripleSet p.1, tripleSet p.2)⟩
  -- Step 1: φ maps overlapPattern n k into tgt.
  have hMapsTo : Set.MapsTo φ
      ((overlapPattern n k : Finset _) : Set _)
      ((tgt : Finset _) : Set _) := by
    intro p hp_set
    have hp : p ∈ overlapPattern n k := by exact_mod_cast hp_set
    -- Unpack membership in overlapPattern.
    simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩ := hp
    -- Establish the three membership facts at the φ image.
    have hUcard : (tripleSet p.1 ∪ tripleSet p.2).card = 6 - k :=
      tripleSet_union_card_of_overlap (by
        simp only [overlapPattern, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩)
    have hcard₁ : (tripleSet p.1).card = 3 := card_tripleSet_of_strict hT₁
    have hcard₂ : (tripleSet p.2).card = 3 := card_tripleSet_of_strict hT₂
    have hsub₁ : tripleSet p.1 ⊆ tripleSet p.1 ∪ tripleSet p.2 := Finset.subset_union_left
    have hsub₂ : tripleSet p.2 ⊆ tripleSet p.1 ∪ tripleSet p.2 := Finset.subset_union_right
    -- Assemble: φ p ∈ tgt.
    show φ p ∈ tgt
    simp only [tgt, hU_pool, Finset.mem_sigma, Finset.mem_powersetCard,
               Finset.mem_product, Finset.subset_univ, true_and]
    refine ⟨hUcard, ⟨⟨hsub₁, hcard₁⟩, ⟨hsub₂, hcard₂⟩⟩⟩
  -- Step 2: φ is injective on overlapPattern n k.
  have hInjOn : Set.InjOn φ ((overlapPattern n k : Finset _) : Set _) := by
    intro p₁ hp₁_set p₂ hp₂_set hφ
    have hp₁ : p₁ ∈ overlapPattern n k := by exact_mod_cast hp₁_set
    have hp₂ : p₂ ∈ overlapPattern n k := by exact_mod_cast hp₂_set
    -- Extract tripleSet equalities from the Sigma/Product equality φ p₁ = φ p₂.
    have h_eq2 : (tripleSet p₁.1, tripleSet p₁.2) = (tripleSet p₂.1, tripleSet p₂.2) := by
      have := congrArg Sigma.snd hφ
      simpa [φ] using this
    have hts1 : tripleSet p₁.1 = tripleSet p₂.1 := (Prod.mk.injEq _ _ _ _).mp h_eq2 |>.1
    have hts2 : tripleSet p₁.2 = tripleSet p₂.2 := (Prod.mk.injEq _ _ _ _).mp h_eq2 |>.2
    -- Recover strictTriples membership of each component.
    simp only [overlapPattern, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    obtain ⟨⟨⟨hp₁T₁, hp₁T₂⟩, _⟩, _⟩ := hp₁
    obtain ⟨⟨⟨hp₂T₁, hp₂T₂⟩, _⟩, _⟩ := hp₂
    -- Conclude via strict_eq_of_tripleSet_eq on each component.
    have e1 : p₁.1 = p₂.1 := strict_eq_of_tripleSet_eq hp₁T₁ hp₂T₁ hts1
    have e2 : p₁.2 = p₂.2 := strict_eq_of_tripleSet_eq hp₁T₂ hp₂T₂ hts2
    exact Prod.ext e1 e2
  -- Step 3: combine the embedding into a cardinality chain.
  calc (overlapPattern n k).card
      ≤ tgt.card := Finset.card_le_card_of_injOn φ hMapsTo hInjOn
    _ = ∑ U ∈ U_pool, (U.powersetCard 3 ×ˢ U.powersetCard 3).card := by
          rw [htgt, Finset.card_sigma]
    _ = ∑ U ∈ U_pool, (U.powersetCard 3).card * (U.powersetCard 3).card := by
          refine Finset.sum_congr rfl (fun U _ => ?_); exact Finset.card_product _ _
    _ ≤ ∑ U ∈ U_pool, (Nat.choose (6 - k) 3) * (Nat.choose (6 - k) 3) := by
          refine Finset.sum_le_sum (fun U hU => ?_)
          rw [hU_pool, Finset.mem_powersetCard] at hU
          obtain ⟨_, hUc⟩ := hU
          rw [Finset.card_powersetCard, hUc]
    _ = U_pool.card * ((Nat.choose (6 - k) 3) * (Nat.choose (6 - k) 3)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
          rw [hU_pool, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          ring
```

### 4.2 Specialisations

Both follow from `card_overlapPattern_le_generic` by evaluating `Nat.choose (6 - k) 3` at `k`:

```lean
/-- **Layer 3f main bound (k = 1).** `|overlapPattern n 1| ≤ Nat.choose n 5 · 100`. -/
lemma card_overlapPattern_le_one (n : ℕ) :
    (overlapPattern n 1).card ≤ Nat.choose n 5 * 100 := by
  have h := card_overlapPattern_le_generic n 1 (by norm_num)
  -- 6 - 1 = 5, Nat.choose 5 3 = 10, 10² = 100.
  simpa using h

/-- **Layer 3f main bound (k = 2).** `|overlapPattern n 2| ≤ Nat.choose n 4 · 16`. -/
lemma card_overlapPattern_le_two (n : ℕ) :
    (overlapPattern n 2).card ≤ Nat.choose n 4 * 16 := by
  have h := card_overlapPattern_le_generic n 2 (by norm_num)
  -- 6 - 2 = 4, Nat.choose 4 3 = 4, 4² = 16.
  simpa using h
```

`simpa` will fire `Nat.choose 5 3 = 10` and `Nat.choose 4 3 = 4` via `decide` since both
arguments are concrete `Nat` literals. If `simpa` doesn't close cleanly, fallback is
`rw [show Nat.choose 5 3 = 10 from rfl]; ring` (and analogously for `k = 2`).

## 5. Risk / Build-Verification Notes

These are the spots most likely to need iteration on first build:

1. **The `_hne` reintroduction inside `hMapsTo`.** The pattern
   `simp only [...] at hp; obtain ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩ := hp`
   then later `exact ⟨⟨⟨hT₁, hT₂⟩, _hne⟩, _hcap⟩` reuses the discarded names. If the
   `_`-prefix elimination is strict, recover the original `hp` instead via
   `have hp_orig := hp_set; exact_mod_cast` or recompute the predicate explicitly.

2. **`Set.MapsTo` vs `Finset.MapsTo` for coercions.** The `((overlapPattern n k : Finset _) : Set _)`
   coercion path is the canonical way to get `Set.MapsTo`. `Finset.card_le_card_of_injOn` accepts
   `Set.MapsTo` directly (per its signature L415). If Lean's elaborator stumbles on the double
   coercion, the explicit `(↑(overlapPattern n k) : Set _)` form is interchangeable.

3. **`smul_eq_mul` in the `Finset.sum_const` step.** Mathlib's `Finset.sum_const` rewrites to a
   `Nat`-scalar action `n • c`. For `Nat`-valued sums `smul_eq_mul` unfolds it to multiplication.
   If a different `simp` normal form fires (e.g., `nsmul_eq_mul`), the closing `ring` will still
   work because both sides are polynomial in `Nat.choose`.

4. **`Fintype.card_fin`** is the canonical reduction of `(Finset.univ : Finset (Fin n)).card` to
   `n`. Equivalents: `Finset.card_univ` followed by `Fintype.card_fin`, or `Finset.card_fin n`
   directly. All three are stable in v4.26.0.

5. **`Nat.choose (6-k) 3` evaluation at `k=1, k=2`.** The `simpa` in §4.2 should close it
   since both arguments are concrete numerals. If not, decision-procedure fallback:
   `rfl` for `Nat.choose 5 3 = 10` and `Nat.choose 4 3 = 4` (both by `decide` / `rfl`).

## 6. Cross-References

- **Spec**: `s16d-overlap-pattern-bounds.md` (Session 16d, researcher-3, 2026-05-09, PR #17509).
- **S16c prerequisites**: `tripleSet_union_card_of_overlap` + three specialisations
  (PR #17444, merged 2026-05-08).
- **Companion (downstream)**: After S16d implementation, S16e adds
  `bad_count_overlap_one` (~100 LOC) and `bad_count_overlap_two` (~80 LOC). S17 combines
  3d/3e/3f to conclude `factorial_moment_2 → (c³/6)²` (~30 LOC limit algebra).
- **Mathlib pin**: `proofs/lake-manifest.json` → `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`v4.26.0`). `proofs/lean-toolchain` → `leanprover/lean4:v4.26.0`.

## 7. Next-Session Checklist

1. Transcribe §4.1 + §4.2 into `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` immediately
   after L1809.
2. Build via `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ03OQ01OQ02`.
3. If §5 risks materialise, fall back to the listed alternatives (none requires new bearers).
4. On success, update `meta.json` (`theoremCount` 40 → 43 if both specialisations added;
   `lineCount` +65–75) and proceed to S16e per `s16d-overlap-pattern-bounds.md` §3 / §4.
