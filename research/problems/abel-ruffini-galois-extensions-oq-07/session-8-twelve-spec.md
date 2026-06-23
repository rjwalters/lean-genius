# Session 8 — `|G| = 12` Axiom-Free Specification

**Session**: S8 (researcher-1, 2026-05-08)
**Goal**: Provide a build-ready specification for proving
`burnside_p_squared_q_twelve : ∀ {G} [Group G] [Finite G]
   [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)]
   (hcard : Nat.card G = 12), IsSolvable G`
axiom-free, completing the `(a, b) = (2, 1)` shape of `burnside_pq_nontrivial`.
**Status**: spec only — Lean prototype deferred until `proofs/.lake` recursive
self-symlink is repaired (each Docker build = ~30–45 min Mathlib clone).

S7 (PR #17114) and S7.5 (PR #17155) discharged `|G| = p² · q` axiom-free for
all `(p, q)` *except* the exceptional `(p, q) = (2, 3), |G| = 12`. S8 closes
this final sub-case via element-counting on Sylow 3-subgroups.

---

## 1. Strategy Overview

For `|G| = 12 = 2² · 3`, Sylow's third theorem gives:

* `n_3 := Nat.card (Sylow 3 G)` satisfies `n_3 ≡ 1 [MOD 3]` and `n_3 ∣ 4`;
  hence `n_3 ∈ {1, 4}`.
* `n_2 := Nat.card (Sylow 2 G)` satisfies `n_2 ≡ 1 [MOD 2]` and `n_2 ∣ 3`;
  hence `n_2 ∈ {1, 3}`.

Goal: prove **at least one of `n_2, n_3`** equals `1`.

* `n_3 = 1`: Sylow 3-subgroup `Q` is normal, `|Q| = 3`, discharge via
  `burnside_pq_with_normal_qSylow` with `(a, b) = (2, 1)`.
* `n_3 = 4`: Element-counting forces `n_2 = 1`. The Sylow 2-subgroup `P` is
  then normal, `|P| = 4`, discharge via `burnside_pq_with_normal_pSylow`
  with `(a, b) = (2, 1)`.

The non-trivial case is `n_3 = 4 ⇒ n_2 = 1`; this is the heart of S8.

---

## 2. Element-Counting Argument (Mathematical Core)

When `n_3 = 4`:

1. **Pairwise trivial intersections.** Each Sylow 3-subgroup `Q_i` has
   `|Q_i| = 3` (prime). For `i ≠ j`, `Q_i ∩ Q_j` is a subgroup of `Q_i`,
   so `|Q_i ∩ Q_j| ∣ 3`. Since `Q_i ≠ Q_j` (distinct Sylows), `Q_i ∩ Q_j ⊊ Q_i`,
   forcing `|Q_i ∩ Q_j| = 1`, i.e. `Q_i ∩ Q_j = {e}`.

2. **Counting elements of order dividing 3.** The set
   `S := {g ∈ G | g^3 = 1}` equals `⋃_i Q_i` (in either direction):
   * `Q_i ⊆ S` since every element of a 3-element group has `g^3 = 1`.
   * Conversely, `g^3 = 1` ⇒ `⟨g⟩` has order `1` or `3` ⇒ `⟨g⟩` lies in some
     Sylow 3-subgroup.

   By inclusion–exclusion + pairwise trivial intersection:
   `|S| = |⋃_i Q_i| = 1 + ∑_i (|Q_i| − 1) = 1 + 4 · 2 = 9`.

3. **Slot count for non-3-power elements.** `|G \ S| = 12 − 9 = 3`. Every
   element of a Sylow 2-subgroup `P` has order in `{1, 2, 4}`, none of
   which gives `g^3 = 1` except `g = 1`. So `P \ {1} ⊆ G \ S`.

4. **Uniqueness of the Sylow 2-subgroup.** `|P \ {1}| = 3 = |G \ S|`,
   forcing `P \ {1} = G \ S`, i.e. `P = (G \ S) ∪ {1}`. The right-hand
   side depends only on `G`, not on the choice of `P`. Hence every Sylow
   2-subgroup equals this fixed set, so `Subsingleton (Sylow 2 G)` and
   `n_2 = 1`.

This argument is **specific to `|G| = 12`** because:

* `|G| − (number of order-3 elements)` exactly fits one Sylow 2-subgroup.
* For `|G| = 18 = 2 · 3²` the analogous count gives `9` order-3 elements
  out of `18`, leaving `9` slots for Sylow 2's of order `2`, which doesn't
  uniquely pin down a Sylow.

---

## 3. Mathlib API Inventory (verification needed when build available)

| Lemma | Mathlib location (best guess) | Statement |
|---|---|---|
| `Sylow.card_eq_multiplicity` | `Mathlib.GroupTheory.Sylow` | Used in S7/S7.5 — proven reliable. |
| `card_sylow_modEq_one` | `Mathlib.GroupTheory.Sylow` | Used in S7/S7.5 — proven reliable. |
| `Sylow.card_dvd_index` | `Mathlib.GroupTheory.Sylow` | Used in S7/S7.5 — proven reliable. |
| `Sylow.normal_of_subsingleton` | `Mathlib.GroupTheory.Sylow` | Used in S7/S7.5 — proven reliable. |
| `Subgroup.card_mul_index` | `Mathlib.Algebra.Group.Subgroup.Finite` | Used in S7/S7.5 — proven reliable. |
| `Nat.card_eq_one_iff_unique` | `Mathlib.Data.Nat.Card` | Used in S7/S7.5 — proven reliable. |
| `Subgroup.disjoint_def` | `Mathlib.Algebra.Group.Subgroup.Basic` | For trivial intersection. |
| `Sylow.toSubgroup` | `Mathlib.GroupTheory.Sylow` | Coercion `Sylow p G → Subgroup G`. |
| **NEW for S8:** | | |
| `Set.ncard_biUnion` / `Finset.card_biUnion` | `Mathlib.Data.Set.Card` | `|⋃ f| = Σ |f i|` when pairwise disjoint. |
| `Subgroup.IsCyclic.card_eq_orderOf` | `Mathlib.GroupTheory.OrderOfElement` | Order-3 elements characterization. |
| `Subgroup.card_eq_one_iff_eq_bot` | `Mathlib.Algebra.Group.Subgroup.Lattice` | `|H| = 1 ↔ H = ⊥`. |
| `IsPGroup.disjoint_or_eq` | `Mathlib.GroupTheory.PGroup` (uncertain) | Distinct Sylow subgroups of prime order intersect trivially. |
| `Set.ncard_eq_of_bijective` | `Mathlib.Data.Set.Card` | For pinning down |G \ S|. |

---

## 4. Lean 4 Skeleton — Helper Lemma: Sylow-3 Count Constraint

```lean
/-- **Sylow count constraint for |G| = 12**: `n ∣ 4`, `n ≡ 1 [MOD 3]`,
    `n ≥ 1` ⇒ `n = 1 ∨ n = 4`. Reusable utility. -/
private lemma sylow_count_dvd_four_modEq_one_three
    {n : ℕ} (hpos : 0 < n) (hdvd : n ∣ 4) (hmod : n ≡ 1 [MOD 3]) :
    n = 1 ∨ n = 4 := by
  have hn_le : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · left; rfl
  · -- n = 2: 2 ≢ 1 [MOD 3] (decidable on naturals)
    exact absurd hmod (by decide)
  · -- n = 3: 3 ∤ 4
    exact absurd hdvd (by decide)
  · right; rfl
```

---

## 5. Lean 4 Skeleton — Helper Lemma: Distinct Sylow 3-Subgroups Disjoint

```lean
/-- For two distinct Sylow `p`-subgroups of order `p` (prime), the underlying
    subgroups intersect trivially. -/
private lemma sylow_prime_distinct_inter_bot
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime]
    (P Q : Sylow p G)
    (hP : Nat.card (P : Subgroup G) = p) (hQ : Nat.card (Q : Subgroup G) = p)
    (hne : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  -- Use IsPGroup analysis: intersection of two distinct subgroups of prime
  -- order has order 1 (only possible proper subgroup of cyclic Z_p).
  --
  -- Key observation: P ⊓ Q ≤ P, and |P ⊓ Q| ∣ p (Lagrange).
  -- p prime + (P ⊓ Q ≤ P with |P| = p) ⇒ |P ⊓ Q| = 1 or |P ⊓ Q| = p = |P|.
  -- The latter forces P ⊓ Q = P = Q (since P ⊓ Q ≤ Q similarly), contradicting hne.
  --
  -- Mathlib API:
  --   * `Subgroup.card_inf_le_of_le_of_le` or similar
  --   * `Sylow.ext_of_subgroup_eq` (if Sylow p with same underlying group are equal)
  --   * `Subgroup.eq_bot_or_eq_top_of_card_le_prime` (uncertain name)
  sorry
```

---

## 6. Lean 4 Skeleton — Helper Lemma: Order-3 Element Count

```lean
/-- For `|G| = 12` with exactly 4 Sylow 3-subgroups (each of order 3),
    the set `{g : G | g^3 = 1}` has exactly 9 elements. -/
private lemma card_pow_three_eq_one_of_n3_four
    {G : Type*} [Group G] [Finite G]
    [hp : Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    Nat.card {g : G // g^3 = 1} = 9 := by
  -- Plan:
  -- 1. Show the 4 Sylow 3-subgroups Q_1, …, Q_4 are pairwise disjoint
  --    (via sylow_prime_distinct_inter_bot above).
  -- 2. Show {g : g^3 = 1} = ⋃ Q_i (set equality).
  --    (⊆): if g^3 = 1 then ⟨g⟩ has order ∣ 3, so |⟨g⟩| ∈ {1, 3}; the latter
  --         makes ⟨g⟩ a Sylow 3-subgroup, so g lies in it.
  --    (⊇): every g in a Sylow 3-subgroup has order ∣ 3 (Lagrange).
  -- 3. Inclusion-exclusion: |⋃ Q_i| = Σ |Q_i| - Σ |Q_i ∩ Q_j| + … = 4·3 - 6·1 + 4·1 - 1 = 9
  --    Or use `Set.ncard_biUnion_eq_sum_of_pairwiseDisjoint` with disjoint-but-share-{e}
  --    handled by partitioning Q_i \ {1} sets.
  --
  -- Cleaner approach: partition {g : g^3 = 1} = {1} ⊔ ⊔_i (Q_i \ {1}), where each
  -- Q_i \ {1} has 2 elements and they are pairwise disjoint (from disjointness of Q_i, Q_j).
  -- Then card = 1 + 4·2 = 9.
  sorry
```

---

## 7. Lean 4 Skeleton — Main Sub-case: `n_3 = 4 ⇒ n_2 = 1`

```lean
/-- For `|G| = 12` with `n_3 = 4`, the Sylow 2-subgroup is unique. -/
private lemma sylow_two_unique_when_n3_four
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    Subsingleton (Sylow 2 G) := by
  -- 1. card_pow_three_eq_one_of_n3_four: |{g | g^3 = 1}| = 9.
  -- 2. So |G \ {g | g^3 = 1}| = 12 - 9 = 3.
  -- 3. For any P : Sylow 2 G, |P| = 4 (Sylow.card_eq_multiplicity), and
  --    every g ∈ P has g^4 = 1; combined with g^3 = 1 ⇒ g = 1, so
  --    g ∈ P \ {1} ⇒ g^3 ≠ 1.
  -- 4. P \ {1} ⊆ G \ {g | g^3 = 1}; both have cardinality 3.
  -- 5. So P \ {1} = G \ {g | g^3 = 1}, fixing P uniquely.
  --
  -- Lean form: use `Subsingleton.intro` then `Sylow.ext` matching underlying
  -- subgroups via the set equality P = {1} ∪ (G \ {g | g^3 = 1}).
  sorry
```

---

## 8. Main Theorem Skeleton

```lean
theorem burnside_p_squared_q_twelve
    {G : Type*} [Group G] [Finite G]
    [hp : Fact (Nat.Prime 2)] [hq : Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) : IsSolvable G := by
  have hcard' : Nat.card G = 2 ^ 2 * 3 := by rw [hcard]; norm_num
  have hcard'' : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [hcard]; norm_num
  -- Sylow 3-subgroup Q, |Q| = 3, Q.index = 4.
  obtain ⟨Q⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hcop : Nat.Coprime (2 ^ 2) 3 := by decide
  have hQ_card : Nat.card (Q : Subgroup G) = 3 := by
    -- factorization computation as in burnside_p_squared_q_p_lt_q
    sorry
  have hQ_index : (Q : Subgroup G).index = 4 := by
    -- from card_mul_index
    sorry
  -- n_3 ∈ {1, 4}.
  have hn3_mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hn3_dvd : Nat.card (Sylow 3 G) ∣ 4 := hQ_index ▸ Sylow.card_dvd_index Q
  have hn3_pos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  rcases sylow_count_dvd_four_modEq_one_three hn3_pos hn3_dvd hn3_mod with hn3 | hn3
  · -- n_3 = 1: Q normal, discharge.
    haveI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn3).1
    haveI : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
    exact burnside_pq_with_normal_qSylow (a := 2) (b := 1) hcard''
      (Q : Subgroup G) hQ_card
  · -- n_3 = 4: derive n_2 = 1, then discharge.
    haveI : Subsingleton (Sylow 2 G) := sylow_two_unique_when_n3_four hcard hn3
    obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
    have hP_card : Nat.card (P : Subgroup G) = 2 ^ 2 := by
      sorry  -- factorization gives |P| = 4 = 2^2
    haveI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    exact burnside_pq_with_normal_pSylow (a := 2) (b := 1) hcard''
      (P : Subgroup G) hP_card
```

---

## 9. Estimated Lines

| Component | Lines |
|---|---|
| `sylow_count_dvd_four_modEq_one_three` | 12 |
| `sylow_prime_distinct_inter_bot` | 25 (uncertain — depends on Mathlib's `Sylow` API for "distinct ⇒ subgroups distinct") |
| `card_pow_three_eq_one_of_n3_four` | 60 (set/Finset cardinality reasoning is verbose in Lean) |
| `sylow_two_unique_when_n3_four` | 35 |
| `burnside_p_squared_q_twelve` (main) | 50 |
| **Total** | **~180** (the original ~70 estimate was optimistic) |

---

## 10. Risks and Alternatives

### Risk: `IsPGroup.disjoint_or_eq` style lemma may not exist in expected form

Mathlib may not expose "distinct Sylow p-subgroups of prime order have trivial
intersection" as a single lemma. Workarounds:

1. **Cardinality + Lagrange**: `|P ⊓ Q| ∣ |P| = p`, so `|P ⊓ Q| ∈ {1, p}`.
   The case `|P ⊓ Q| = p` ⇒ `P ⊓ Q = P` (full subgroup) ⇒ `P = Q`, contradicting
   distinctness. Requires `Subgroup.card_le_of_le` or similar.

2. **`Sylow.ext_of_eq_subgroup`**: if two Sylow p-subgroups have the same
   underlying subgroup, they are equal. Combined with (1), we get the result.

### Alternative path: `Subgroup.normalCore` + `Equiv.Perm (Fin 4)` solvability

Instead of element counting, use the action of `G` on `G/Q` (4 cosets):

* `G →* Equiv.Perm (G ⧸ Q)` with kernel `(Q : Subgroup G).normalCore`.
* `normalCore Q ≤ Q` so `|normalCore Q| ∣ 3`, hence `normalCore Q ∈ {⊥, Q}`.
* If `normalCore Q = Q`: `Q` is normal — done.
* If `normalCore Q = ⊥`: `G ↪ Equiv.Perm (G ⧸ Q) ≃ Equiv.Perm (Fin 4)`.
  Need `IsSolvable (Equiv.Perm (Fin 4))` from Mathlib (or build via
  `V_4 ⊴ A_4 ⊴ S_4` chain — `V_4` is the Klein 4-group, abelian).

This route is cleaner mathematically but requires:
* `Subgroup.normalCore` and its properties (probably in Mathlib).
* `IsSolvable (Equiv.Perm (Fin 4))` — may need explicit construction.
* `solvable_of_solvable_injective` (or similar) for "subgroup of solvable is solvable".

Mathlib does have `Equiv.Perm.not_solvable` for `Fin 5`; the positive direction
for `Fin n ≤ 4` is likely available but name verification needed.

---

## 11. Build Strategy for Next Iteration

1. Repair `proofs/.lake` symlink first (or run on a host where it's intact).
2. Implement `sylow_count_dvd_four_modEq_one_three` standalone — verify with
   `lake build Proofs.AbelRuffiniGaloisExtensionsOQ07` (~45 min cold cache).
3. Add `sylow_prime_distinct_inter_bot` — try `IsPGroup` API first, fall back
   to manual cardinality argument.
4. Add `card_pow_three_eq_one_of_n3_four` — most verbose; consider
   `Set.ncard_biUnion` route vs `Finset.card_biUnion` route.
5. Add `sylow_two_unique_when_n3_four` and main theorem.
6. Update `burnside_pq` dispatch to peel off the `(a, b) = (2, 1)` shape via:
   `burnside_p_squared_q_p_gt_q ∨ burnside_p_squared_q_p_lt_q ∨ burnside_p_squared_q_twelve`.
7. Narrow `burnside_pq_nontrivial` to `(2 ≤ a ∨ 2 ≤ b) ∧ ¬ ((a, b) = (2, 1) ∨ (a, b) = (1, 2))`
   (after S8 + symmetric S8' for `(1, 2)` shape).

---

## 12. Why `|G| = 12` Is the Last Holdout

Among `|G| = p² · q` for primes `p ≠ q`:

* `q < p`: always `n_p = 1` (S7).
* `p < q ≠ p + 1`: always `n_q = 1` (S7.5, since `q ∣ p + 1` forces `q = p + 1`).
* `p < q = p + 1`: both prime, both ≥ 2 ⇒ `p = 2, q = 3` (only consecutive primes).

So `(p, q, |G|) = (2, 3, 12)` is the *unique* exceptional triple where
Sylow's third theorem fails to immediately give a normal Sylow. The
element-counting argument exploits the fact that `|G| − 9 = 3 = |P| − 1`
exactly — a delicate count that does not generalize to other shapes.

This is also why **A₄** (the alternating group on 4 letters) is the
classical witness: `|A₄| = 12`, `n_3 = 4` (the 3-cycles partition into 4
Sylow 3-subgroups), and the unique Sylow 2-subgroup is the Klein 4-group
`V₄ = {e, (12)(34), (13)(24), (14)(23)}`, which is normal in A₄.
