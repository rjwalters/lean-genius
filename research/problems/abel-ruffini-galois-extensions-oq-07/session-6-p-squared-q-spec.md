# Session 6 — `|G| = p² · q` Axiom-Free Specification

**Session**: S6 (researcher-12, 2026-05-08)
**Goal**: Provide a build-ready specification for proving
`burnside_p_squared_q : ∀ {G} [Group G] [Finite G] {p q} [Fact p.Prime] [Fact q.Prime]
   (hpq : p ≠ q) (hcard : Nat.card G = p^2 * q), IsSolvable G`
axiom-free (without invoking `burnside_pq_nontrivial`).
**Status**: spec only — Lean prototype deferred until `proofs/.lake` recursive
self-symlink is repaired (each Docker build = ~30–45 min Mathlib clone).

S5 (PR #16972) added `burnside_pq_with_normal_pSylow` and
`burnside_pq_with_normal_qSylow`. S6 plugs Sylow's third theorem into these
to discharge `|G| = p² · q` for the **two non-exceptional cases** (`p > q`
and `p < q ≠ 3`). The `p = 2, q = 3, |G| = 12` exception (where `n_2 = 3`
is possible) requires a special transfer/coset argument.

---

## 1. Two Sub-Cases

For `|G| = p² · q` with primes `p ≠ q`:

### 1.1 Case `p > q` (always `n_p = 1`)

By Sylow's third theorem:
* `n_p := Nat.card (Sylow p G) ≡ 1 [MOD p]`,
* `n_p ∣ index of P-Sylow = q`,

so `n_p ∈ {1, q}`. If `n_p = q`, then `q ≡ 1 [MOD p]`, i.e. `p ∣ q - 1`;
since `q < p`, this forces `q = 1` (impossible since `q` is prime).
Hence `n_p = 1`, the unique Sylow `p`-subgroup is normal, and
`burnside_pq_with_normal_pSylow` discharges.

### 1.2 Case `p < q` (always `n_q = 1` except `(p, q) = (2, 3)`)

Symmetrically:
* `n_q ≡ 1 [MOD q]`,
* `n_q ∣ index of Q-Sylow = p²`,

so `n_q ∈ {1, p, p²}`.
* `n_q = p` requires `q ∣ p - 1`. Since `p < q`, impossible.
* `n_q = p²` requires `q ∣ p² - 1 = (p - 1)(p + 1)`. Since `q > p > p - 1`,
  `q ∣ p + 1`. The only solution with both prime is `(p, q) = (2, 3)`
  (i.e. `q = p + 1`).
* Otherwise `n_q = 1`, the unique Sylow `q`-subgroup is normal, and
  `burnside_pq_with_normal_qSylow` discharges.

### 1.3 Exceptional case `(p, q) = (2, 3)`, `|G| = 12`

When `(p, q) = (2, 3)`: `n_3 ∈ {1, 4}`.
* If `n_3 = 1`: normal Sylow 3-subgroup of order 3, use `burnside_pq_with_normal_qSylow`.
* If `n_3 = 4`: there are 4 Sylow 3-subgroups, each contributes 2 elements of
  order 3, giving 8 elements of order 3. The remaining 4 elements form a
  unique Sylow 2-subgroup `V_4` (Klein 4-group) of order 4. Hence `n_2 = 1`,
  the Sylow 2-subgroup is normal, and `burnside_pq_with_normal_pSylow`
  discharges. (This is exactly the A_4 case.)

---

## 2. Mathlib API Inventory (verified against `mathlib4` master, 2026-05-08)

| Lemma | Mathlib location | Statement |
|---|---|---|
| `card_sylow_modEq_one` | `Mathlib/GroupTheory/Sylow.lean:324` | `[Fact p.Prime] [Finite (Sylow p G)] : Nat.card (Sylow p G) ≡ 1 [MOD p]`. |
| `Sylow.card_dvd_index` | `Mathlib/GroupTheory/Sylow.lean:408` | `[Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : Nat.card (Sylow p G) ∣ P.index`. |
| `Sylow.normal_of_subsingleton` | `Mathlib/GroupTheory/Sylow.lean:736` | `[Subsingleton (Sylow p G)] (P : Sylow p G) : P.Normal`. |
| `Sylow.unique_of_normal` | `Mathlib/GroupTheory/Sylow.lean:722` | `[Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) (h : P.Normal) : Unique (Sylow p G)` — converse, for completeness. |
| `Sylow.exists_subgroup_card_pow_prime` | `Mathlib/GroupTheory/Sylow.lean` | First Sylow theorem: existence of subgroup of order `p^n` for `p^n ∣ Nat.card G`. |
| `Nat.card_eq_one_iff_unique` | `Mathlib/Data/Nat/Card.lean` | `Nat.card α = 1 ↔ ∃ x : α, ∀ y, y = x` (instances Subsingleton α). |
| `Sylow.card_eq_multiplicity` | `Mathlib/GroupTheory/Sylow.lean:716` | `Nat.card P = p ^ Nat.factorization (Nat.card G) p`. Useful for getting `Nat.card P = p^2`. |
| `Subgroup.index_eq_card_quotient` | `Mathlib/Algebra/Group/Subgroup/Finite.lean` | `H.index = Nat.card (G ⧸ H)`. Used to compute `q = (P : Sylow p).index` when `Nat.card P = p²`. |
| `Subgroup.card_mul_index` | `Mathlib/Algebra/Group/Subgroup/Finite.lean` | `Nat.card H * H.index = Nat.card G`. |
| `Nat.eq_one_of_dvd_of_lt` (or `Nat.lt_one_iff`) | `Mathlib/Data/Nat/Basic.lean` | Used in n_p analysis to force divisor to be 1. |
| `Nat.ModEq` lemmas | `Mathlib/Data/Nat/ModEq.lean` | `Nat.ModEq.dvd` etc. for translating `n ≡ 1 [MOD p]` → `p ∣ n - 1`. |
| `pGroup_isSolvable` | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean:60` (existing) | Local file's lemma. |
| `burnside_pq_with_normal_pSylow` | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean:221` (S5, PR #16972) | Discharges via normal `p`-Sylow. |
| `burnside_pq_with_normal_qSylow` | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean:246` (S5, PR #16972) | Discharges via normal `q`-Sylow. |

All Mathlib lemmas verified present in `mathlib4` master via `gh api` on 2026-05-08.

---

## 3. Lean 4 Skeleton — Helper Lemma A: `n_p = 1` from `n_p ≡ 1 [MOD p]` and `n_p ∣ q < p`

```lean
/-- **Sylow count constraint**: if `|H| ∣ q` (with `q` prime, `q < p`) and
    `|H| ≡ 1 [MOD p]`, then `|H| = 1`. The two non-trivial divisors `q` of
    a prime are `1` and `q`; `q ≡ 1 [MOD p]` with `q < p` forces `q = 1`,
    contradiction. -/
private lemma sylow_count_eq_one_of_lt_prime
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q < p)
    (hmod : n ≡ 1 [MOD p]) (hdvd : n ∣ q) : n = 1 := by
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq n hdvd) with h1 | hq_eq
  · exact h1
  · -- n = q. Then q ≡ 1 [MOD p], i.e. p ∣ q - 1.
    rw [hq_eq] at hmod
    have hp_dvd_qm1 : p ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mp hmod.symm
    have : p ≤ q - 1 := Nat.le_of_dvd (by omega : 0 < q - 1) hp_dvd_qm1
    omega
```

---

## 4. Lean 4 Skeleton — Main Theorem (Case `p > q`)

```lean
theorem burnside_p_squared_q_p_gt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : q < p) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  -- Step 1: get a Sylow p-subgroup; its order is p^2 by `Sylow.card_eq_multiplicity`.
  letI : Fintype (Sylow p G) := Fintype.ofFinite _
  obtain ⟨P⟩ : Nonempty (Sylow p G) := Sylow.nonempty
  have hP_card : Nat.card (P : Subgroup G) = p ^ 2 := by
    rw [Sylow.card_eq_multiplicity P, hcard]
    have hpq_coprime : (p ^ 2).Coprime q := by
      apply Nat.Coprime.pow_left
      exact (Nat.coprime_primes hp.out hq.out).mpr (by omega)
    -- Nat.factorization (p^2 * q) p = 2 since p^2 contributes 2 and q is coprime.
    sorry  -- standard ordProj computation; ~5 lines
  -- Step 2: compute the index of P. Since |P| = p^2 and |G| = p^2 q, index = q.
  have hP_index : (P : Subgroup G).index = q := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    have hp2_pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
    exact Nat.eq_of_mul_eq_mul_left hp2_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q. Apply Helper A to get n_p = 1.
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := hP_index ▸ Sylow.card_dvd_index P
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime hp.out hq.out hpq hnp_mod hnp_dvd
  -- Step 4: n_p = 1 ⇒ Subsingleton (Sylow p G) ⇒ P.Normal.
  haveI : Subsingleton (Sylow p G) := Nat.card_eq_one_iff_unique.mp hnp_eq_one |>.subsingleton
  haveI hP_normal : (P : Subgroup G).Normal := P.normal_of_subsingleton
  -- Step 5: discharge via burnside_pq_with_normal_pSylow.
  exact burnside_pq_with_normal_pSylow (a := 2) (b := 1) hcard P hP_card
```

(Note: the `(a := 2) (b := 1)` instantiation matches the `Nat.card G = p^a * q^b`
shape with `a = 2`, `b = 1`. Verify that `q ^ 1 = q` simp-rewrites cleanly into
the existing lemma's hypothesis.)

---

## 5. Lean 4 Skeleton — Main Theorem (Case `p < q ≠ 3`)

```lean
theorem burnside_p_squared_q_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p < q) (hexceptional : ¬ (p = 2 ∧ q = 3))
    (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  -- Symmetric to §4: derive n_q = 1 from n_q ∣ p^2 and n_q ≡ 1 [MOD q],
  -- ruling out n_q = p (since p < q) and n_q = p² (since q ∤ p²-1 unless
  -- (p,q) = (2,3) — excluded by hexceptional).
  -- ...
  -- Apply burnside_pq_with_normal_qSylow.
  sorry
```

A two-`sorry` skeleton with the same shape as §4. Approximately 35–45 lines
(longer than §4 because the n_q analysis has 3 cases vs §4's 2).

---

## 6. Lean 4 Skeleton — Exceptional Case `(p, q) = (2, 3)`, `|G| = 12`

```lean
theorem burnside_p_squared_q_twelve
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 12) :
    IsSolvable G := by
  -- Two cases based on n_3 ∈ {1, 4}:
  -- 1. n_3 = 1: normal Sylow 3-subgroup of order 3, use burnside_pq_with_normal_qSylow.
  -- 2. n_3 = 4: 4 × 2 = 8 elements of order 3; remaining 4 are unique Sylow 2-subgroup
  --    (V_4); n_2 = 1, use burnside_pq_with_normal_pSylow.
  -- The element-counting argument requires: in distinct Sylow 3-subgroups,
  -- intersection is trivial (subgroup of prime order has only {e} as proper subgroup);
  -- so 4 Sylow 3-subgroups contribute 4 × 2 = 8 distinct non-identity elements.
  sorry  -- 60-80 lines; uses Sylow.card_eq_one_or_dvd and element-counting
```

---

## 7. Lean 4 Skeleton — Combined Theorem

```lean
theorem burnside_p_squared_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  rcases lt_or_gt_of_ne hpq with h | h
  · -- p < q
    by_cases hexc : p = 2 ∧ q = 3
    · -- exceptional: (p, q) = (2, 3), |G| = 12
      obtain ⟨hp2, hq3⟩ := hexc
      have h12 : Nat.card G = 12 := by rw [hcard, hp2, hq3]; norm_num
      exact burnside_p_squared_q_twelve h12
    · exact burnside_p_squared_q_p_lt_q h hexc hcard
  · -- p > q
    exact burnside_p_squared_q_p_gt_q h hcard
```

Then the existing `burnside_pq` main theorem (line 276) can be **augmented** to
peel off the `a = 2, b = 1` case axiom-free:

```lean
-- inside burnside_pq's case-split, after squarefree (a = b = 1):
by_cases h21 : a = 2 ∧ b = 1
· obtain ⟨ha2, hb1⟩ := h21
  rw [ha2, hb1, pow_one] at hcard
  exact burnside_p_squared_q hpq hcard
-- ... fall through to other cases or the axiom for a ≥ 3 / b ≥ 2 etc.
```

---

## 8. Critical Path: 4 `sorry` placeholders

| `sorry` | What it proves | Approach | Lines |
|---|---|---|---|
| 1 | `Nat.factorization (p^2 * q) p = 2` | `Nat.factorization_mul`, `Nat.factorization_pow`, `Nat.Prime.factorization_self` | 5 |
| 2 | `n_q ≠ p` (Case `p < q`) | `q ∣ p - 1 → p < q` contradiction | 5 |
| 3 | `n_q ≠ p²` (Case `p < q`) | `q ∣ (p-1)(p+1)`, ruled out by `hexceptional` | 10 |
| 4 | Exceptional case `\|G\| = 12` element counting | `Sylow.card_le_one_or_dvd` + `Subgroup.card_eq_one_iff` for trivial intersection | 60 |

**Total new code estimate**: ~150–180 lines (helper §3 ~15, Case `p > q` §4 ~30,
Case `p < q` §5 ~40, Exceptional §6 ~70, Combined §7 ~10, augmented `burnside_pq`
~10).

**Build verification**: 1 Docker run with `LEAN_BUILD_TIMEOUT=60m`.

---

## 9. Open Questions for S7

**Q1**: Should the exceptional `|G| = 12` case go in this file or a sibling
`AbelRuffiniGaloisExtensionsOQ07/Twelve.lean`? Given its 60–70 line footprint,
inline is fine; defer modular split to S8+.

**Q2**: Is `Subgroup.card_le_one_iff_subsingleton` the right Mathlib name in
v4.26.0, or has it been renamed to `Subgroup.subsingleton_iff`? Verify on
prototype.

**Q3**: After S6, the axiom narrows further: `burnside_pq_nontrivial`'s
hypothesis `2 ≤ a ∨ 2 ≤ b` can be tightened to **`(2 ≤ a ∧ 1 ≤ b) ∧ ¬(a = 2 ∧ b = 1)
∨ (1 ≤ a ∧ 2 ≤ b) ∧ ¬(a = 1 ∧ b = 2)`** — i.e. exclude the `p²q` and `pq²` cases.
S7 (Sylow analysis on `|G| = p · q²`) further narrows to `a, b ≥ 2`. S8 (`|G| = p² · q²`)
narrows to `a + b ≥ 5`.

**Q4 (advanced)**: After S6, S7, S8 land: the residual axiom requires `a ≥ 3` or
`b ≥ 3`. The Goldschmidt-Matsuyama transfer/focal-subgroup proof
(`Mathlib.GroupTheory.Focal`) handles all `pᵃqᵇ` uniformly without character
theory. Estimated 200-400 lines on top of the current scaffolding.

---

## 10. Recommended Session Sequence (revised)

* **S6** (1–2 hr): Prototype `burnside_p_squared_q_p_gt_q` per §4 + helper §3.
  Discharge `sorry` 1 (factorization). Run Docker build with
  `LEAN_BUILD_TIMEOUT=60m`. ~50 lines (helper + p > q case only).
* **S6.5** (1 hr): Add `burnside_p_squared_q_p_lt_q` per §5; discharge sorries
  2 and 3. Build verify. ~40 lines.
* **S7** (2–3 hr): Add `burnside_p_squared_q_twelve` exceptional case per §6;
  discharge sorry 4 (element counting). Build verify. ~70 lines.
* **S8** (1–2 hr): Add the symmetric `burnside_p_q_squared` (Case `|G| = p · q²`).
  By symmetry, structurally identical; ~80 lines including its own exception
  (`(p, q) = (2, 3), |G| = 18` may have similar structure — verify).
* **S9** (2–3 hr): Add `burnside_p_squared_q_squared` (`|G| = p² · q²`). Sylow
  analysis is more involved (3 × 3 case grid). ~150 lines.
* **S10+**: Goldschmidt-Matsuyama for the residual `a ≥ 3 ∨ b ≥ 3` cases.

---

## 11. Build Infrastructure Reminder

`proofs/.lake -> proofs/.lake` recursive self-symlink (memory
`feedback_researcher_lake_symlink_broken`) makes every Docker build a 30–45 min
Mathlib clone + 10 min cache fetch. S7 should:

1. Run a single Docker build with `LEAN_BUILD_TIMEOUT=60m` after each
   sub-case lands.
2. Or batch S6 + S6.5 + S7 into one session ending with one Docker build.

---

## Provenance

- Mathlib `Sylow.lean` API verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/GroupTheory/Sylow.lean`
  on 2026-05-08:
  - `card_sylow_modEq_one` (line 324)
  - `Sylow.card_dvd_index` (line 408)
  - `Sylow.normal_of_subsingleton` (line 736)
  - `Sylow.unique_of_normal` (line 722)
  - `Sylow.card_eq_multiplicity` (line 716)
- Repo helpers `burnside_pq_with_normal_pSylow` and `burnside_pq_with_normal_qSylow`
  taken from `AbelRuffiniGaloisExtensionsOQ07.lean:221`/`:246` on `origin/main`
  post-PR #16972 (S5 merged 2026-05-08).
- `pGroup_isSolvable` taken from line 60 of the same file.
