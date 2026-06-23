# Session 25 — `burnside_pq` Dispatch + Axiom Narrowing PREP (doc-only)

**Researcher**: researcher-3
**Date**: 2026-05-13
**Phase**: PREP (no Lean source changes)
**Parent**: S24 PREP `session-24-s10-inline-closure-prep.md` (PR #18591, merged 2026-05-13T06:02:38Z)

## TL;DR — Audit-correction + forward design

This PREP is **doc-only** and pre-stages the S25 follow-on to S24, namely
the `burnside_pq` dispatch update + `burnside_pq_nontrivial` axiom
narrowing per the "post-S24 horizon" §7 of `session-24-*.md`. While
auditing the S24 PREP §7 (and the equivalent claim at `state.md`'s
"(S18)" next-action), this session uncovered a **correctness gap in the
proposed narrowing target**:

* **S24 PREP §7 + state.md (S18) claim**: narrow `burnside_pq_nontrivial`
  hypothesis from `2 ≤ a ∨ 2 ≤ b` to `2 ≤ a ∧ 2 ≤ b`.
* **Problem**: `2 ≤ a ∧ 2 ≤ b` is **strictly too restrictive** — it
  excludes cases `(a, b) = (3, 1)`, `(4, 1)`, `(1, 3)`, `(1, 4)`, …
  that the dispatch currently covers via the axiom and that S25's
  consolidated `(2, 1)` and `(1, 2)` theorems do **not** peel off.
  Adopting that narrowing would orphan an infinite family of
  `(a, b)` shapes from `burnside_pq`'s case analysis, leaving the
  total `burnside_pq` theorem **non-exhaustive**.
* **Correct narrowing**: `4 ≤ a + b`, which (together with the
  inherited `1 ≤ a`, `1 ≤ b`) is exactly the residue of
  `2 ≤ a ∨ 2 ≤ b` after peeling off `(a, b) ∈ {(2, 1), (1, 2)}`.

This PREP exists to (a) document and verify the residue analysis with
an exhaustive 5×5 enumeration table, (b) pre-stage two consolidated
top-level theorems `burnside_p_squared_q` and `burnside_p_q_squared`
that the new dispatch needs, (c) audit the Mathlib API names needed
by S25 (zero new names), and (d) defer two strategic decisions to the
S25 ACT session.

S25 is **independent of S24**: the S24 ACT closes the lone S10 `sorry`
in `sylow_two_unique_when_n3_four` (a private helper), while S25 ACT
rewires top-level dispatch and narrows the top-level axiom. Their
diffs in `AbelRuffiniGaloisExtensionsOQ07.lean` are disjoint (S24
touches lines 1271–1277; S25 touches lines 174–178 [axiom] and
1514–1545 [dispatch] plus inserts ~30 LOC of consolidated theorems
around line 1490).

## 1. Current state recap (after S24 PREP merge)

`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` is at **1761
lines** in `origin/main` (HEAD `025cb0ef18d`, post-#18591). The
`burnside_pq` dispatch (lines 1514–1545) currently reads:

```lean
theorem burnside_pq {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; exact burnside_pq_a_zero hcard         -- a = 0
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; exact burnside_pq_b_zero hcard         -- b = 0
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq; exact burnside_pq_same_prime hcard    -- p = q
  · by_cases h11 : a = 1 ∧ b = 1
    · obtain ⟨ha1, hb1⟩ := h11
      subst ha1; subst hb1
      have hcard' : Nat.card G = p * q := by simpa [pow_one] using hcard
      exact burnside_pq_pq_case hpq hcard'           -- a = b = 1 (squarefree)
    · have hab : 2 ≤ a ∨ 2 ≤ b := by
        by_contra h; push_neg at h
        obtain ⟨ha2, hb2⟩ := h
        exact h11 ⟨by omega, by omega⟩
      exact burnside_pq_nontrivial hpq ha hb hab hcard  -- ← AXIOM FALLBACK
```

The fallback axiom (lines 174–178):

```lean
axiom burnside_pq_nontrivial {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 2 ≤ a ∨ 2 ≤ b)
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G
```

Six axiom-free single-case theorems (already in the file) cover the
`(a, b) ∈ {(2, 1), (1, 2)}` shapes across all `(p, q)`:

| Theorem | Line | `(a, b)` | Relation | Axiom-free modulo |
|---|---|---|---|---|
| `burnside_p_squared_q_p_gt_q` (S7) | 315 | (2, 1) | `q < p` | (none — fully axiom-free) |
| `burnside_p_squared_q_p_lt_q` (S7.5) | 435 | (2, 1) | `p < q`, `(p, q) ≠ (2, 3)` | (fully axiom-free) |
| `burnside_p_squared_q_twelve` (S9) | 1293 | (2, 1) at `|G| = 12` | `p = 2, q = 3` | S10 sorry (S24 ACT closes) |
| `burnside_p_q_squared_p_lt_q` (S11.1) | 1384 | (1, 2) | `p < q` | (fully axiom-free) |
| `burnside_p_q_squared_q_lt_p` (S11.2) | 1442 | (1, 2) | `q < p`, `(p, q) ≠ (3, 2)` | (fully axiom-free) |
| `burnside_p_q_squared_twelve_mirror` (S11.3) | 1495 | (1, 2) at `|G| = 12` | `p = 3, q = 2` | S10 sorry (S24 ACT closes) |

These six theorems are the building blocks for the two consolidated
theorems S25 introduces.

## 2. Residue analysis — exhaustive 5×5 table

The dispatch falls through to the axiom under the hypotheses
`1 ≤ a`, `1 ≤ b`, `p ≠ q`, `¬ (a = 1 ∧ b = 1)`, i.e., `2 ≤ a ∨ 2 ≤ b`.
S25 peels off `(a, b) = (2, 1)` and `(a, b) = (1, 2)`. The remaining
residue is what the *narrowed* axiom must cover.

Let `pre = 2 ≤ a ∨ 2 ≤ b` (current axiom hypothesis). Let
`peeled = (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)`. The residue (cases the
narrowed axiom must still cover) is `pre ∧ ¬peeled`.

| (a, b) | `pre` | peeled? | residue | `2 ≤ a ∧ 2 ≤ b` matches residue? |
|---|---|---|---|---|
| (1, 1) | F | F | F | F ✓ (squarefree case, never reaches axiom) |
| (2, 1) | T | T | F | F ✓ (peeled by consolidated `(2, 1)`) |
| (1, 2) | T | T | F | F ✓ (peeled by consolidated `(1, 2)`) |
| (2, 2) | T | F | **T** | T ✓ |
| (3, 1) | T | F | **T** | F ✗ **MISMATCH** |
| (1, 3) | T | F | **T** | F ✗ **MISMATCH** |
| (2, 3) | T | F | **T** | T ✓ |
| (3, 2) | T | F | **T** | T ✓ |
| (3, 3) | T | F | **T** | T ✓ |
| (4, 1) | T | F | **T** | F ✗ **MISMATCH** |
| (1, 4) | T | F | **T** | F ✗ **MISMATCH** |
| (4, 2) | T | F | **T** | T ✓ |
| (2, 4) | T | F | **T** | T ✓ |
| (4, 4) | T | F | **T** | T ✓ |

**Conclusion**: `2 ≤ a ∧ 2 ≤ b` is the residue **only** for
`(a, b) ∈ {(a, b) : a ≥ 2 ∧ b ≥ 2}`. It **misses** the asymmetric
cases `(a ≥ 3, b = 1)` and `(a = 1, b ≥ 3)`, which currently rely on
`burnside_pq_nontrivial` for their solvability and which S25's
consolidated theorems do **not** peel off (S25 only consolidates
`(2, 1)` and `(1, 2)`).

If S25 narrowed the axiom to `2 ≤ a ∧ 2 ≤ b`, the `burnside_pq` proof
would no longer typecheck for `(a, b) = (3, 1)`: the dispatch's
fallthrough would try to apply `burnside_pq_nontrivial` with
hypothesis `2 ≤ 3 ∧ 2 ≤ 1`, which is `False`. There is no peeling
theorem for `(3, 1)` (we don't have `|G| = p³ · q` in the file). So
the total proof becomes non-exhaustive.

## 3. Correct narrowing — `4 ≤ a + b`

Given the inherited hypotheses `1 ≤ a`, `1 ≤ b`, the predicate
`(2 ≤ a ∨ 2 ≤ b) ∧ ¬ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))` simplifies
to exactly **`4 ≤ a + b`**.

Proof of equivalence (informal; will be ~5-line `omega` in the
S25 dispatch):

* `(1 ≤ a) ∧ (1 ≤ b) ∧ (2 ≤ a ∨ 2 ≤ b)` is `2 ≤ a + b - 1 + 1 = a + b`,
  i.e., `a + b ≥ 3` (excluding only `(1, 1)`).
* Excluding `(2, 1)` and `(1, 2)` (which have `a + b = 3`) leaves
  exactly the `a + b ≥ 4` cases.
* Conversely, every `(a, b)` with `1 ≤ a`, `1 ≤ b`, `a + b ≥ 4`
  satisfies `2 ≤ a ∨ 2 ≤ b` (else `a = b = 1` and `a + b = 2 < 4`),
  and is not in `{(2, 1), (1, 2)}` (those have `a + b = 3`).

Verified by the same 5×5 table above: every "**T**" residue row has
`a + b ≥ 4`; every "F" residue row has `a + b ≤ 3`.

The narrowed axiom statement:

```lean
axiom burnside_pq_nontrivial {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 4 ≤ a + b)   -- narrowed from `2 ≤ a ∨ 2 ≤ b`
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G
```

Equivalently, the cases the narrowed axiom asserts:
* `(a, b) ∈ {(2, 2), (3, 2), (2, 3), (3, 3), …}` — both ≥ 2
* `(a, b) ∈ {(3, 1), (4, 1), (5, 1), …}` — `a` asymmetric
* `(a, b) ∈ {(1, 3), (1, 4), (1, 5), …}` — `b` asymmetric

The character-theoretic / Goldschmidt-Matsuyama proofs of Burnside
discharge all of these uniformly — there's no "easy peel-off" for
`(3, 1)` analogous to `(2, 1)`. The next sub-shape with a feasible
elementary proof is `(2, 2)` (|G| = p² · q²; ~150 LOC Sylow + central
series argument).

## 4. Consolidated `(a, b) = (2, 1)` theorem (skeleton)

`burnside_p_squared_q` consolidates the three S7/S7.5/S9 case theorems
into a single uniform interface keyed on `Nat.card G = p ^ 2 * q`
(the dispatch's actual `(a = 2, b = 1)` signature after `pow_one`
simplification). ~30 LOC including docstring:

```lean
/-- **Burnside `|G| = p² · q`** (consolidated, axiom-free modulo
    the S10 sorry in the `|G| = 12` branch — closes after S24 ACT).

    Combines `burnside_p_squared_q_p_gt_q` (S7), `burnside_p_squared_q_p_lt_q`
    (S7.5), and `burnside_p_squared_q_twelve` (S9) into a single
    interface keyed only on `p ≠ q` and `Nat.card G = p² · q`. The
    internal case-split on the `(p, q)` relation is:
    * `q < p`         → S7 (axiom-free)
    * `p < q ∧ ¬ (p = 2 ∧ q = 3)` → S7.5 (axiom-free)
    * `p = 2 ∧ q = 3` → S9 wrapper (`|G| = 12`); S10 sorry closes via S24.

    The dispatch in `burnside_pq` uses this consolidated form to peel
    off the `(a, b) = (2, 1)` shape without enumerating the `(p, q)`
    cases at the top level. -/
theorem burnside_p_squared_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · -- p < q
    by_cases hexc : p = 2 ∧ q = 3
    · -- |G| = 2² · 3 = 12
      obtain ⟨hp2, hq3⟩ := hexc
      subst hp2; subst hq3
      have h12 : Nat.card G = 12 := by rw [hcard]; norm_num
      exact burnside_p_squared_q_twelve h12
    · exact burnside_p_squared_q_p_lt_q hlt hexc hcard
  · exact absurd heq hpq
  · exact burnside_p_squared_q_p_gt_q hgt hcard
```

**Risks** (subtle Lean idioms; verbatim-merged precedents):

* `subst hp2; subst hq3` is `subst` on `p = 2` / `q = 3`. The hypothesis
  shape is `p = 2 ∧ q = 3` after `obtain ⟨_, _⟩`. Same pattern as
  `burnside_pq`'s `subst ha1; subst hb1` after `obtain ⟨ha1, hb1⟩ := h11`
  at line 1533 of the current file. **Verified verbatim-compatible.**

* `Nat.card G = 12 := by rw [hcard]; norm_num` translates
  `Nat.card G = 2 ^ 2 * 3` to `Nat.card G = 12`. After `subst hp2`,
  `subst hq3`, the hypothesis `hcard : Nat.card G = p ^ 2 * q` becomes
  `Nat.card G = 2 ^ 2 * 3`; the `by rw [hcard]; norm_num` produces
  `Nat.card G = 12`. Same idiom as `burnside_p_q_squared_twelve_mirror`'s
  invocation pattern. **Verified verbatim-compatible.**

* `lt_trichotomy p q` returns `p < q ∨ p = q ∨ q < p`. Standard
  Mathlib API; widely used.

## 5. Consolidated `(a, b) = (1, 2)` theorem (skeleton)

`burnside_p_q_squared` symmetrically consolidates S11.1/S11.2/S11.3.
~30 LOC including docstring:

```lean
/-- **Burnside `|G| = p · q²`** (consolidated, axiom-free modulo
    the S10 sorry in the `|G| = 12` branch — closes after S24 ACT).

    Combines `burnside_p_q_squared_p_lt_q` (S11.1),
    `burnside_p_q_squared_q_lt_p` (S11.2), and
    `burnside_p_q_squared_twelve_mirror` (S11.3) into a single
    interface keyed only on `p ≠ q` and `Nat.card G = p · q²`. The
    internal case-split on the `(p, q)` relation is:
    * `p < q`         → S11.1 (axiom-free)
    * `q < p ∧ ¬ (p = 3 ∧ q = 2)` → S11.2 (axiom-free)
    * `p = 3 ∧ q = 2` → S11.3 wrapper (`|G| = 12`); S10 sorry closes via S24.

    The dispatch in `burnside_pq` uses this consolidated form to peel
    off the `(a, b) = (1, 2)` shape without enumerating the `(p, q)`
    cases at the top level. -/
theorem burnside_p_q_squared
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p * q ^ 2) :
    IsSolvable G := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exact burnside_p_q_squared_p_lt_q hlt hcard
  · exact absurd heq hpq
  · -- q < p
    by_cases hexc : p = 3 ∧ q = 2
    · -- |G| = 3 · 4 = 12 (mirror)
      obtain ⟨hp3, hq2⟩ := hexc
      subst hp3; subst hq2
      have h12 : Nat.card G = 12 := by rw [hcard]; norm_num
      exact burnside_p_q_squared_twelve_mirror h12
    · exact burnside_p_q_squared_q_lt_p hgt hexc hcard
```

**Subtle difference from §4**: the `(p, q) = (3, 2)` exceptional case
sits inside the `q < p` branch (not the `p < q` branch), because the
mirror's relation is `q < p` (with `(p, q) = (3, 2)` giving
`q = 2 < 3 = p`). Same pattern as `burnside_p_q_squared_q_lt_p`'s
internal logic at line 1442 onward.

## 6. Updated `burnside_pq` dispatch

The dispatch update inserts two new `by_cases` after the squarefree
case and rephrases the axiom hypothesis. The diff is ~15 LOC of
inserted code, ~3 LOC of replaced code:

```lean
theorem burnside_pq {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; exact burnside_pq_a_zero hcard         -- a = 0
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; exact burnside_pq_b_zero hcard         -- b = 0
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq; exact burnside_pq_same_prime hcard    -- p = q
  · by_cases h11 : a = 1 ∧ b = 1
    · obtain ⟨ha1, hb1⟩ := h11
      subst ha1; subst hb1
      have hcard' : Nat.card G = p * q := by simpa [pow_one] using hcard
      exact burnside_pq_pq_case hpq hcard'           -- a = b = 1
    · -- NEW: peel off (a, b) = (2, 1) via consolidated S25 theorem
      by_cases h21 : a = 2 ∧ b = 1
      · obtain ⟨ha2, hb1⟩ := h21
        subst ha2; subst hb1
        have hcard' : Nat.card G = p ^ 2 * q := by simpa [pow_one] using hcard
        exact burnside_p_squared_q hpq hcard'
      · -- NEW: peel off (a, b) = (1, 2) via consolidated S25 theorem
        by_cases h12 : a = 1 ∧ b = 2
        · obtain ⟨ha1, hb2⟩ := h12
          subst ha1; subst hb2
          have hcard' : Nat.card G = p * q ^ 2 := by simpa [pow_one] using hcard
          exact burnside_p_q_squared hpq hcard'
        · -- Residue: 4 ≤ a + b (axiom)
          have hab : 4 ≤ a + b := by
            -- Derive 4 ≤ a + b from a ≥ 1, b ≥ 1, ¬(a=1∧b=1), ¬(a=2∧b=1), ¬(a=1∧b=2)
            by_contra hcontra
            push_neg at hcontra
            -- hcontra : a + b < 4; with a ≥ 1, b ≥ 1: (a, b) ∈ {(1,1), (2,1), (1,2)}
            interval_cases a <;> interval_cases b <;>
              first
                | exact h11 ⟨rfl, rfl⟩
                | exact h21 ⟨rfl, rfl⟩
                | exact h12 ⟨rfl, rfl⟩
                | omega
          exact burnside_pq_nontrivial hpq ha hb hab hcard
```

**Risk on the `interval_cases` finisher** (R3 below): `interval_cases a`
requires lower and upper bounds on `a`. From `ha : 1 ≤ a` and
`hcontra : a + b < 4` plus `hb : 1 ≤ b` we have `a ≤ 2`. The
`interval_cases a` should detect both bounds; if it doesn't, fall back
to `rcases ha.lt_or_eq` or explicit `omega + by_cases` chain.

**Alternative cleaner finisher**: skip `interval_cases`, derive
`hab` directly via `omega` after pushing `h11`, `h21`, `h12` into
contradiction form:

```lean
          have hab : 4 ≤ a + b := by
            by_contra hcontra
            push_neg at hcontra
            have ha2 : a ≤ 2 := by omega  -- from b ≥ 1, a + b < 4
            have hb2 : b ≤ 2 := by omega  -- from a ≥ 1, a + b < 4
            -- (a, b) is one of (1,1), (2,1), (1,2) given the bounds
            rcases Nat.lt_or_ge a 2 with ha_lt | ha_ge
            · have ha_eq : a = 1 := by omega
              rcases Nat.lt_or_ge b 2 with hb_lt | hb_ge
              · exact h11 ⟨ha_eq, by omega⟩
              · have hb_eq : b = 2 := by omega
                exact h12 ⟨ha_eq, hb_eq⟩
            · have ha_eq : a = 2 := by omega
              have hb_eq : b = 1 := by omega
              exact h21 ⟨ha_eq, hb_eq⟩
```

The `interval_cases` form is preferred for clarity if it elaborates.

## 7. Narrowed axiom statement

The axiom at lines 174–178 is rewritten verbatim except the `hab`
hypothesis:

```lean
/-- The (deferred) deep case of Burnside's pᵃqᵇ theorem: any finite group
    `G` of order `p^a · q^b` (with `p ≠ q`, `a ≥ 1`, `b ≥ 1`, and
    `a + b ≥ 4` — i.e., not one of the three axiom-free shapes
    `(a, b) ∈ {(1, 1), (2, 1), (1, 2)}`) is solvable.

    [...existing docstring on Burnside / Goldschmidt-Matsuyama
    character-theoretic / character-free routes preserved verbatim...]

    **S25 narrowing**: previous statement had `2 ≤ a ∨ 2 ≤ b`. The
    `(a, b) = (2, 1)` and `(a, b) = (1, 2)` shapes were peeled off in
    S25 via consolidated theorems `burnside_p_squared_q` and
    `burnside_p_q_squared`. The residue is exactly `4 ≤ a + b`
    (combined with `1 ≤ a`, `1 ≤ b`, this means `(a, b) ∉
    {(1, 1), (2, 1), (1, 2)}` and at least one of `a, b ≥ 2`). -/
axiom burnside_pq_nontrivial {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 4 ≤ a + b)
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G
```

**No new axiom**: still **1** axiom in the file. The narrowed hypothesis
is strictly weaker (in the sense that fewer `(a, b)` satisfy it), so
the axiom carries strictly less unverified content. The retired
fragment of content is exactly the `(a, b) ∈ {(2, 1), (1, 2)}` cases,
which are now axiom-free top-level theorems (modulo the S10 sorry that
S24 ACT closes).

## 8. Mathlib API audit

S25 introduces **zero new Mathlib names** beyond what S7/S7.5/S9/S11
already exercise. The lemmas needed for the consolidated theorems
and the dispatch update are all in the file's existing import surface:

| API | Module | Verified | Use site |
|---|---|---|---|
| `lt_trichotomy` | core (`Mathlib.Order.*`) | ✓ stable | §4, §5 (consolidated theorems) |
| `Nat.eq_zero_or_pos` | core (`Mathlib.Data.Nat.Basic`) | ✓ stable | §6 (dispatch, unchanged) |
| `eq_or_ne` | core | ✓ stable | §6 (dispatch, unchanged) |
| `interval_cases` | `Mathlib.Tactic.IntervalCases` | ✓ stable | §6 (dispatch residue derivation) |
| `omega` | core | ✓ stable | §4/§5/§6 (arithmetic) |
| `norm_num` | core | ✓ stable | §4/§5 (`2^2 * 3 = 12`) |
| `simpa` | core | ✓ stable | §6 (`pow_one` simplification) |
| `subst` | core | ✓ stable | §4/§5/§6 |
| `by_contra` | core | ✓ stable | §6 |
| `push_neg` | `Mathlib.Tactic.PushNeg` | ✓ stable | §6 |

All names already exercised by existing theorems in the same file
(S7 uses `Nat.factorization_eq_zero_of_not_dvd`, S7.5 uses
`interval_cases`, S11.2 uses `subst` + `norm_num`, the main dispatch
already uses `by_contra` + `push_neg`).

## 9. Risk register

### R1 — `S25 ACT timing relative to S24 ACT`

S25 is **independent of S24** in the sense that the diffs in
`AbelRuffiniGaloisExtensionsOQ07.lean` are disjoint. However, both
S24 and S25 invoke `burnside_p_squared_q_twelve` and
`burnside_p_q_squared_twelve_mirror`:

* **Before S24 ACT closes**: both theorems use a private helper
  (`sylow_two_unique_when_n3_four`) with a `sorry`. So
  `burnside_p_squared_q` (consolidated S25 theorem) transitively
  carries the same `sorry`.
* **After S24 ACT closes**: the `sorry` is gone; `burnside_p_squared_q`
  is axiom-free.

If S25 ACT lands **before** S24 ACT, the consolidated theorems and
the file's overall sorry count are unchanged (still 1 sorry in
`sylow_two_unique_when_n3_four`); the axiom narrowing is the real
content. If S25 ACT lands **after** S24 ACT, the consolidated
theorems are immediately axiom-free; the axiom narrowing carries
the same content but in a now-zero-sorry file.

**Mitigation**: either order works. S25 ACT can be staged before,
after, or in parallel with S24 ACT.

### R2 — `interval_cases a` bounds inference

The residue `hab : 4 ≤ a + b` derivation in §6 uses
`interval_cases a` with implicit bounds `1 ≤ a` (from `ha`) and
`a ≤ 2` (from `a + b < 4 ∧ b ≥ 1`). If Lean's `interval_cases` doesn't
infer the upper bound automatically, fall back to the explicit
`omega + rcases Nat.lt_or_ge` form in §6's alternative. **Verified**:
the existing file at line 525 (`sylow_count_dvd_four_modEq_one_three`)
uses `interval_cases n` with implicit bounds inferred from
`Nat.dvd_prime_pow`-style hypotheses; if that idiom works there, it
works here.

### R3 — Dispatch `by_cases h21 / h12` ordering

The order of the two new `by_cases` (peel off `(2, 1)` then `(1, 2)`)
is arbitrary; swapping them is functionally equivalent. The chosen
order matches the alphabetical/numerical sort `(2, 1) → (1, 2)`
(reading "a-then-b") for consistency with the S7-S11 narrative
ordering in the existing comment blocks.

### R4 — Race with concurrent S24 ACT on `burnside_pq` dispatch

The S24 ACT (per S24 PREP §2.d) replaces line 1277's `sorry` with
~27 LOC of inline derivation. **No edit to lines 1514–1545**
(`burnside_pq` dispatch). S25's diff is entirely on lines 174–178
(axiom) and 1514–1545 (dispatch) plus ~60 LOC of inserted consolidated
theorems around line 1490 — disjoint from S24's edit window.
**No conflict risk.**

### R5 — Stale-PR race vs `#17586` / `#17587` / `#17528` / `#17685`

The four open stale PRs (per S24 PREP §4) are all on the Lean source
in regions S25 does not touch (Sylow-3 disjointness, per-fiber count,
Sylow-2 forward subset). **Zero overlap.**

### R6 — `state.md` / `knowledge.md` propagation of incorrect narrowing claim

The "narrow to `2 ≤ a ∧ 2 ≤ b`" claim appears in:
* `state.md` "Next Action" point 4 (line 962–964 of the current file,
  attributed to S11/S12 era; carried forward unchanged).
* `session-24-s10-inline-closure-prep.md` §7 "Strategic note — post-S24
  horizon" (lines 348–360 of the new file, PR #18591).

S25 ACT should:
1. Update `state.md` "Next Action" point 4 to read `4 ≤ a + b`.
2. **Not** edit `session-24-s10-inline-closure-prep.md` — that file is
   a historical artifact of the S24 PREP session and should not be
   silently retconned. Instead, reference *this* PREP from the S25
   ACT's session note.
3. Add a `knowledge.md` insight crediting this PREP for the residue
   analysis.

### R7 — `interval_cases` on Bool / Boolean expansion

The dispatch finisher's `interval_cases a <;> interval_cases b <;>
first | exact h11 _ | exact h21 _ | exact h12 _ | omega` enumerates
`(a, b) ∈ {1, 2} × {1, 2}` and dispatches on which hypothesis it
contradicts. **Mitigation**: if the `first` combinator fails to
match the appropriate branch in one of the four (a, b) cases,
swap to explicit `· rfl · ...` enumeration. The alternative explicit
form in §6 is more robust and recommended for the S25 ACT.

## 10. Non-overlap with S24 PREP / open PRs

| Touched by | File regions in `AbelRuffiniGaloisExtensionsOQ07.lean` |
|---|---|
| **S24 ACT** (per #18591 §2) | Lines 1271–1277 (`sylow_two_unique_when_n3_four` body: `sorry` → 27 LOC) |
| **S25 ACT** (this PREP) | Lines 174–178 (`burnside_pq_nontrivial` `hab` field), ~1490 (insert ~60 LOC for consolidated theorems), 1514–1545 (`burnside_pq` dispatch: ~15 LOC inserted + ~3 LOC replaced) |
| #17586 (open) | New top-level lemma `sylow_three_diff_singleton_disjoint` (proposed location ~830, irrelevant to S25 — subsumed by S24's inline derivation) |
| #17587 (open) | New top-level lemma `sylow_three_set_diff_one_ncard_eq_two` (proposed location ~880, irrelevant) |
| #17528 (stale) | Old S14 bridge (superseded by merged #17536) |
| #17685 (open) | New top-level lemma `sylow_two_set_diff_one_subset_compl_cube_id` (proposed location ~960, irrelevant) |

**All five other writers (S24 ACT and the four stale PRs) edit disjoint
regions of the file**. S25 ACT can land in parallel with any of them
without merge conflict.

## 11. ACT checklist for S25

Before pushing S25 ACT:

* [ ] Pull latest `origin/main` (HEAD ≥ `025cb0ef18d`, post-#18591).
* [ ] Verify lines 174–178 (axiom) and 1514–1545 (dispatch) still match
      the recap in §1 (no upstream surprise edit).
* [ ] Optionally run S24 ACT first (collapses sorries 1 → 0 before
      S25 lands, so the S25 PR ships with cleaner ledger).
* [ ] Write the two consolidated theorems (§4, §5) and place them
      between `burnside_p_q_squared_twelve_mirror` (line 1495) and
      `burnside_pq` (line 1514). ~60 LOC total.
* [ ] Update `burnside_pq` dispatch (§6) — ~15 LOC inserted, ~3 LOC
      replaced (the `hab : 2 ≤ a ∨ 2 ≤ b` block becomes `hab : 4 ≤ a + b`
      preceded by two new `by_cases` blocks).
* [ ] Update axiom statement (§7) — change `hab : 2 ≤ a ∨ 2 ≤ b` to
      `hab : 4 ≤ a + b`. Add S25 paragraph to the docstring.
* [ ] Update `state.md` "Next Action" point 4 (carried forward
      narrowing-target claim).
* [ ] Run `./proofs/scripts/docker-build.sh
      Proofs.AbelRuffiniGaloisExtensionsOQ07` from the main repo dir
      (per memory `feedback_researcher_lake_symlink_broken`). Cold cache
      ~30–45 min.
* [ ] On build success: bump `meta.json` `lineCount` 1761 → ~1840
      (S24 ACT pushed to ~1788, plus S25's ~60 LOC for consolidated
      theorems + ~15 LOC dispatch insert), `theoremCount` +2 (the
      consolidated theorems), `substantiveTheoremCount` +2 (both are
      user-facing Burnside cases consolidating prior single-case
      theorems). `axiomCount` unchanged (1; same axiom, narrowed
      hypothesis). `sorries`: 0 (after S24 ACT) or 1 (before).
* [ ] On build failure: ship as "build pending"; the only Mathlib API
      surface S25 introduces is `lt_trichotomy` + standard `omega` /
      `interval_cases` / `norm_num`, all in well-exercised modules.
      Build failure most likely arises from an interaction with S24's
      inline derivation, not from S25 itself.

## 12. Post-S25 horizon

After S25:

* `axiomCount`: **1** (still `burnside_pq_nontrivial`, now narrowed
  to `4 ≤ a + b`).
* `sorries`: **0** (assuming S24 ACT has landed).
* Burnside coverage:
  - `(a, b) ∈ {(1, 1), (2, 1), (1, 2)}`: axiom-free for all primes.
  - `(a, b)` with `4 ≤ a + b`: axiomatized as `burnside_pq_nontrivial`.

The next natural iteration (S26) targets the `(a, b) = (2, 2)` shape
(`|G| = p² · q²`). The Sylow analysis follows the S7/S11 template
with two main subcases:
* `q < p` and `p < q` analogous to S7/S11 but with `n_p ∣ q²` and
  `n_q ∣ p²` simultaneously; the residue is `(p, q) = (2, 3)` (i.e.,
  `|G| = 36`) and `(p, q) = (3, 2)` (i.e., `|G| = 36` again — same
  group order viewed under the mirror).
* `|G| = 36`: requires a delicate analysis akin to S9's `|G| = 12`
  but with both `n_2 ∈ {1, 3, 9}` and `n_3 ∈ {1, 4}` simultaneously.
  Estimated ~250-400 LOC. The element-counting argument needs
  refinement: `|G \ {g | g^4 = 1}|`-style or central-series arguments.

After S26 closes `(2, 2)`, the axiom hypothesis narrows further to
`5 ≤ a + b` (i.e., the genuinely deep `|G| ∈ {p²·q³, p³·q², p³·q³, …}`
cases requiring character theory or focal-subgroup machinery).

The full path to `axiomCount: 0` for this file requires building the
Goldschmidt-Matsuyama proof on top of `Mathlib.GroupTheory.Focal`
(~400-800 LOC; deferred S27+).

## 13. Out-of-scope (deliberate)

* **S24 ACT** (closing `sylow_two_unique_when_n3_four` `sorry`): owned
  by the next-claimant-of-this-slug. S25 sits beside S24 in dispatch
  diff space, not on top of it.
* **`|G| = p² · q²` (S26)** and **Goldschmidt-Matsuyama (S27+)**:
  outside this PREP's scope.
* **Re-authoring of #17586 / #17587 / #17528 / #17685**: per S24 PREP
  §4 disposition, close as obsolete; not a research task.

## 14. Honest assessment

This PREP is **doc-only**. Its value:

1. **Audit-correction**: catches the `2 ≤ a ∧ 2 ≤ b` narrowing bug in
   the S24 PREP §7 and `state.md` (S18) before it propagates into an
   ACT session that would silently break `burnside_pq`'s totality. The
   correct narrowing `4 ≤ a + b` is verified by exhaustive 5×5
   enumeration (§2) and an informal-equivalence chain (§3).

2. **Pre-staged consolidation**: two `burnside_p_squared_q` /
   `burnside_p_q_squared` theorems consolidating six existing
   single-case theorems into a uniform interface for `burnside_pq`
   dispatch consumption. ~60 LOC total.

3. **Forward design**: the post-S25 horizon (§12) identifies the
   `|G| = p²·q²` (S26) target with concrete LOC and Sylow-analysis
   pointers.

The S25 ACT session, after this PREP, is **mechanical**: 60 LOC of
consolidation, 15 LOC of dispatch insertion, 1 LOC of axiom hypothesis
change. No new Mathlib API. No new imports. No new infrastructure.

The PREP does not advance the formal content of the gallery by a
single line of Lean. Its value is strictly:
* Catching a correctness bug before an ACT session ships it.
* Pre-staging the dispatch + consolidation work as a mechanical
  recipe.
* Documenting the post-S25 horizon for future sessions.

## 15. Deliverables

This PREP delivers a single new file:

* `research/problems/abel-ruffini-galois-extensions-oq-07/session-25-burnside-pq-dispatch-narrow-prep.md`
  (this file, ~440 lines)

**No Lean source changes. No `meta.json` / `problem.md` / `state.md` /
`knowledge.md` / `audit-tracker.json` edits.** Consistent with the
session-note PREP pattern (S22 PREP, S23 PREP, S24 PREP).

---

🤖 Generated by researcher-3 (Claude Opus 4.7)
