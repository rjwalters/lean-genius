# S16d: Polynomial Bounds on `|overlapPattern n k|` (Layer 3f main bounds)

**Author**: researcher-3, Session 16d (2026-05-09)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Lean file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`
**Mode**: ANALYSIS (no Lean changes; planning + Lean-ready stub)

This note specifies the precise lemma forms, the embedding-into-fibers
proof skeleton, and the Mathlib 4.26 API surface needed to close
S16d's two cardinality bounds:

- `card_overlapPattern_le_one : (overlapPattern n 1).card ≤ Nat.choose n 5 * 100`
- `card_overlapPattern_le_two : (overlapPattern n 2).card ≤ Nat.choose n 4 * 16`

These are the two polynomial bounds promised by S16c's docstrings:
"This is the cardinality input for the Layer 3f bound `|overlapPattern n
1| = O(n⁵)` / `O(n⁴)`." Asymptotically, `Nat.choose n j ≤ n^j / j!`,
so the bounds give `O(n⁵)` and `O(n⁴)` respectively (constants `100/120`
and `16/24`). This is exactly what roadmap §4c needs to drive
`nondisjoint_factorial_moment_2_tendsto_zero` (S16e).

---

## 1. Why these constants

For `(T₁, T₂) ∈ overlapPattern n k`, write `U := tripleSet T₁ ∪ tripleSet
T₂`. By S16c's `tripleSet_union_card_of_overlap_*`, `|U| = 6 - k`. The
key embedding map

```
φ : overlapPattern n k → ((Fin n).powersetCard (6 - k))
                          × Finset (Fin n) × Finset (Fin n)
φ (T₁, T₂) := (tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂)
```

has image in the slice

```
{ (U, S₁, S₂) | S₁, S₂ ∈ U.powersetCard 3 ∧ S₁ ∪ S₂ = U }
```

and by `strict_eq_of_tripleSet_eq` (S12), `φ` is **injective**: the
3-subsets `S₁`, `S₂` uniquely recover the strict triples `T₁`, `T₂`.
Hence

```
|overlapPattern n k| ≤ Σ_{U ∈ powersetCard (6-k)} |U.powersetCard 3|²
                     ≤ Nat.choose n (6 - k) · (Nat.choose (6 - k) 3)².
```

The constant evaluations: `Nat.choose 5 3 = 10`, so for `k = 1` the
constant is `10² = 100`. `Nat.choose 4 3 = 4`, so for `k = 2` the constant
is `4² = 16`.

(A tighter — but non-elementary — bound counts only pairs `(S₁, S₂)`
with `|S₁ ∩ S₂| = k`; for `k = 1` that is `30` rather than `100`. The
loose bound is sufficient for asymptotic vanishing and saves significant
Lean machinery; we ship the loose bound.)

---

## 2. Lean-ready Lemma Statements (for §9 of the .lean file, post-S16c)

```lean
/-- **Layer 3f main bound (k = 1).** The overlap-1 stratum is bounded
    polynomially in n by `Nat.choose n 5 · 100`. Asymptotically `O(n⁵)`.
    Combines with `bad_count_overlap_one` (S16e) to give the
    overlap-1 contribution `O(n⁵ / d⁵) = O(d^{-5/3})` at `n = ⌊c·d^{2/3}⌋`.
    -/
lemma card_overlapPattern_le_one (n : ℕ) :
    (overlapPattern n 1).card ≤ Nat.choose n 5 * 100 := by
  classical
  -- Step 1: φ(T₁, T₂) := (tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂)
  --         injects overlapPattern n 1 into a Σ-bundle.
  -- Step 2: bound the image cardinality by powersetCard (6-1) (Fin n)
  --         times (powersetCard 3 of any 5-elt set)².
  sorry

/-- **Layer 3f main bound (k = 2).** The overlap-2 stratum is bounded
    polynomially in n by `Nat.choose n 4 · 16`. Asymptotically `O(n⁴)`.
    Combines with `bad_count_overlap_two` (S16e) to give the overlap-2
    contribution `O(n⁴ / d⁴) = O(d^{-4/3})` at `n = ⌊c·d^{2/3}⌋`. -/
lemma card_overlapPattern_le_two (n : ℕ) :
    (overlapPattern n 2).card ≤ Nat.choose n 4 * 16 := by
  classical
  sorry
```

---

## 3. Common helper lemma (factor out of `card_overlapPattern_le_*`)

The argument is parametric in `k` for `k ≤ 3`. Factor a shared helper:

```lean
/-- **Generic Layer 3f bound.** For `k ≤ 3`, the overlap-`k` stratum is
    bounded by `Nat.choose n (6 - k) · (Nat.choose (6 - k) 3)²`. -/
lemma card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3) :
    (overlapPattern n k).card
      ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
  classical
  -- Outline:
  -- (i) Define the embedding target:
  --       target n k := ((Finset.univ : Finset (Fin n)).powersetCard (6 - k)) ×ˢ
  --                     <product of two powersetCard 3 over each U>
  --     Use Finset.sigma instead of ×ˢ if the dependent type is needed.
  -- (ii) Define φ : overlapPattern n k → target n k by
  --        φ (T₁, T₂) := ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂⟩.
  --      Use Finset.image (fun p => ...) to push overlapPattern through φ.
  -- (iii) Show φ-image is contained in target via tripleSet_union_card_of_overlap
  --       (S16c) for the U cardinality, and tripleSet T_i ⊆ U for the inclusion.
  -- (iv) Show φ is injOn via strict_eq_of_tripleSet_eq (S12): the strict triple
  --      is uniquely determined by its tripleSet.
  -- (v) Conclude:
  --     (overlapPattern n k).card
  --       = ((overlapPattern n k).image φ).card           -- by injOn
  --       ≤ (target n k).card                             -- by Finset.card_le_card
  --       ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3)²
  sorry

/-- **k = 1 specialisation.** `Nat.choose 5 3 = 10`, so the constant is `100`. -/
lemma card_overlapPattern_le_one (n : ℕ) :
    (overlapPattern n 1).card ≤ Nat.choose n 5 * 100 := by
  have h := card_overlapPattern_le_generic n 1 (by omega)
  -- 6 - 1 = 5; Nat.choose 5 3 = 10; 10² = 100; rewrite.
  simpa [show (6 : ℕ) - 1 = 5 from rfl, show Nat.choose 5 3 = 10 from rfl,
         show (10 : ℕ) ^ 2 = 100 from rfl] using h

/-- **k = 2 specialisation.** `Nat.choose 4 3 = 4`, so the constant is `16`. -/
lemma card_overlapPattern_le_two (n : ℕ) :
    (overlapPattern n 2).card ≤ Nat.choose n 4 * 16 := by
  have h := card_overlapPattern_le_generic n 2 (by omega)
  simpa [show (6 : ℕ) - 2 = 4 from rfl, show Nat.choose 4 3 = 4 from rfl,
         show (4 : ℕ) ^ 2 = 16 from rfl] using h
```

---

## 4. Detailed proof skeleton for `card_overlapPattern_le_generic`

### 4.1 Embedding target

Two natural choices:

(a) **Cartesian-product target** (simpler indexing, slightly looser):

    ```lean
    let target : Finset _ :=
      ((Finset.univ : Finset (Fin n)).powersetCard (6 - k)) ×ˢ
      ((Finset.univ : Finset (Fin n)).powersetCard 3) ×ˢ
      ((Finset.univ : Finset (Fin n)).powersetCard 3)
    ```

    Cardinality: `Nat.choose n (6 - k) * Nat.choose n 3 * Nat.choose n 3`.

    This is **too loose** (gives `O(n^{6-k}) · O(n^3) · O(n^3) = O(n^{12-k})`).

(b) **Sigma target** (correct, tight):

    ```lean
    let target : Finset _ :=
      ((Finset.univ : Finset (Fin n)).powersetCard (6 - k)).sigma fun U =>
        (U.powersetCard 3) ×ˢ (U.powersetCard 3)
    ```

    Cardinality:
    `∑ U ∈ powersetCard (6 - k), (Nat.choose (6 - k) 3)² = Nat.choose n (6 - k) · (Nat.choose (6 - k) 3)²`.

Use **(b)**.

### 4.2 Embedding map

```lean
def φ {n k : ℕ} : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) →
    Σ U : Finset (Fin n), Finset (Fin n) × Finset (Fin n) :=
  fun p => ⟨tripleSet p.1 ∪ tripleSet p.2, tripleSet p.1, tripleSet p.2⟩
```

(In practice the type should be the dependent sigma into `target`; use
`Finset.image` with the bare codomain `Finset (Fin n) × Finset (Fin n) × Finset (Fin n)`
if the sigma machinery is awkward.)

### 4.3 Containment (`φ-image ⊆ target`)

For `(T₁, T₂) ∈ overlapPattern n k`:

1. **U-card**: `(tripleSet T₁ ∪ tripleSet T₂).card = 6 - k` by
   `tripleSet_union_card_of_overlap` (S16c).
2. **U-membership**: `tripleSet T₁ ∪ tripleSet T₂ ∈ powersetCard (6 - k)`
   via `Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h_card⟩`.
3. **S₁-membership in `U.powersetCard 3`**: `tripleSet T₁ ⊆ tripleSet T₁ ∪ tripleSet T₂ = U`
   by `Finset.subset_union_left`; cardinality `3` by `card_tripleSet_of_strict`
   (note the `T₁ ∈ strictTriples n` hypothesis is unpacked from
   `(T₁, T₂) ∈ overlapPattern n k`).
4. **S₂-membership in `U.powersetCard 3`**: symmetric (via
   `Finset.subset_union_right`).

### 4.4 Injectivity (`φ` is `Set.InjOn`)

Suppose `φ (T₁, T₂) = φ (T₁', T₂')`. Then `tripleSet T₁ = tripleSet T₁'`
and `tripleSet T₂ = tripleSet T₂'`. By `strict_eq_of_tripleSet_eq`
(file L1269, applied with the strict-triple witnesses unpacked from
the overlapPattern membership), `T₁ = T₁'` and `T₂ = T₂'`.

### 4.5 Cardinality bound

```lean
calc (overlapPattern n k).card
    = ((overlapPattern n k).image φ).card := (Finset.card_image_of_injOn h_inj).symm
  _ ≤ target.card                          := Finset.card_le_card h_subset
  _ = Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2 := by
      -- target.card via Finset.card_sigma + Finset.card_product
      simp [Finset.card_sigma, Finset.card_product, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin]
      ring
```

---

## 5. Mathlib 4.26 API surface

All Mathlib names below are confirmed present in Mathlib `v4.26.0` (the
gallery pin) and used elsewhere in `BirthdayProblemOQ03OQ01OQ02.lean`
or its imports. No new imports required.

| Name | Purpose |
|---|---|
| `Finset.image` | push `overlapPattern` through `φ` |
| `Finset.card_image_of_injOn` | turn injectivity into card-equality |
| `Finset.card_le_card` | bound by enclosing target |
| `Finset.powersetCard` | the family of `j`-element subsets |
| `Finset.card_powersetCard` | `|powersetCard j s| = (s.card).choose j` |
| `Finset.mem_powersetCard` | `s ∈ t.powersetCard j ↔ s ⊆ t ∧ s.card = j` |
| `Finset.subset_union_left` / `_right` | `tripleSet Tᵢ ⊆ U` |
| `Finset.sigma` | dependent target construction |
| `Finset.card_sigma` | `|s.sigma t| = ∑ x ∈ s, (t x).card` |
| `Finset.product` (`×ˢ`) | pair `S₁ × S₂` |
| `Finset.card_product` | `|s ×ˢ t| = s.card * t.card` |
| `Finset.sum_const` | `∑ _ ∈ s, c = s.card * c` |
| `Nat.choose` arithmetic via `decide` / `rfl` | evaluate small `Nat.choose 5 3 = 10`, `Nat.choose 4 3 = 4` |
| `tripleSet_union_card_of_overlap` (S16c) | `|U| = 6 - k` |
| `card_tripleSet_of_strict` (S12) | `|tripleSet T| = 3` |
| `strict_eq_of_tripleSet_eq` (S12) | `φ` is injective |

---

## 6. Estimated lines

- `card_overlapPattern_le_generic`: 50–60 lines (the bulk: containment +
  injectivity + final calc).
- `card_overlapPattern_le_one` / `_two`: 5 lines each (specialisation
  via `simpa` with `Nat.choose 5 3 = 10`, `Nat.choose 4 3 = 4` rewrites).

**Total**: ≈ 60–70 lines added to §9 of `BirthdayProblemOQ03OQ01OQ02.lean`,
matching the roadmap §8a estimate of "60–80 lines via the union-card
embedding".

---

## 7. Cross-sectional check vs `bad_count_overlap_*` (S16e)

The S16e per-pair joint-coincidence counts will produce, for each pair
`(T₁, T₂) ∈ overlapPattern n k` with `n ≥ 6 - k`:

```
card { f | f trivialises T₁ ∧ f trivialises T₂ } = d^(n - (6 - k))
```

(generalising `bad_count_disjoint`'s `d^(n - 4)` for `k = 0`).

Combining with S16d:

- `k = 1`: contribution `≤ |overlapPattern n 1| · d^(n - 5) ≤ Nat.choose n 5 · 100 · d^(n - 5)`.
  Probability `≤ 100 · Nat.choose n 5 / d⁵ ≤ 100 · n⁵ / (5! · d⁵) ≤ (5/6) · n⁵/d⁵`.
- `k = 2`: contribution `≤ |overlapPattern n 2| · d^(n - 4) ≤ Nat.choose n 4 · 16 · d^(n - 4)`.
  Probability `≤ 16 · Nat.choose n 4 / d⁴ ≤ 16 · n⁴ / (4! · d⁴) = (2/3) · n⁴/d⁴`.

At `n = ⌊c · d^{2/3}⌋`:

- `k = 1`: `O(d^{10/3 - 5}) = O(d^{-5/3})` → 0.
- `k = 2`: `O(d^{8/3 - 4}) = O(d^{-4/3})` → 0.

Both vanish, matching the roadmap §4c plan and unblocking S17.

---

## 8. Risk assessment

- **Build risk**: `BirthdayProblemOQ03OQ01OQ02.lean` has accumulated
  S15, S16, S16b, S16c as build-pending. S16d would also be
  build-pending under current Docker contention. The lemma
  `card_overlapPattern_le_generic`'s proof uses only `Finset` /
  `Nat.choose` API that has been stable across Mathlib `v4.26.0`, so
  build-failure risk is low *assuming* prior S16/S16b/S16c builds are
  correct (i.e., the file is buildable from origin/main today).

- **Conflict risk**: No open PRs cite S16d (verified via
  `gh pr list --search "birthday-problem-oq-03-oq-01-oq-02-oq-01"
  --state open`). The three open PRs (#16777, #16837, #16873) are
  stale Sessions 7–8 work pre-dating the Layer 3 sub-decomposition.

- **Out-of-order risk**: S16d implementation depends only on S16c
  (just merged) and S12 helpers (`card_tripleSet_of_strict`,
  `strict_eq_of_tripleSet_eq`, both on origin/main). No dependency on
  pending S16/S16b PRs at the lemma level.

---

## 9. Recommendation for next session (S16d-implement)

A single follow-up session should land both lemmas (generic + the two
specialisations) as 60–70 added lines under §9 in
`BirthdayProblemOQ03OQ01OQ02.lean`, after `tripleSet_union_card_of_overlap_two`
(file L1809). State.md and meta.json updated to reflect S16d
completion. Build will be pending under contention; convention here is
to label "(build pending)" in the PR title, matching S15/S16/S16b/S16c.
