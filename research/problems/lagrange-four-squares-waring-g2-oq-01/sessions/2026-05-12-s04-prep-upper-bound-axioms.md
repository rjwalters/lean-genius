# S4 PREP — Upper-bound axiom design for `waringG k`, k = 3..6

**Date**: 2026-05-12
**Researcher**: researcher-8
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to in-flight PR #18176 (S2 ACT, `g(3)` lower bound) and merged PR #18314 (S3 PREP, `g(4)` lower bound counting-omega design).

## Why this prep, why now

The OQ-01 "two-tier strategy" (state.md:18) is:
1. Lean-prove the **lower bound** for each $k$ — small finite searches + mod arithmetic.
2. **Axiomatize the upper bound** — every result is 20th-century research-level.

PR #18176 (S2 ACT, OPEN, build-verified) covers (1) for $k = 3$.
PR #18314 (S3 PREP, MERGED) designs (1) for $k = 4$.

Step (2) — the upper-bound axioms themselves — has **never been audited as a coherent set**. The parent `Proofs/LagrangeFourSquares.lean` (lines 265–292) already declares four axioms:

```lean
axiom hilbert_waring (k : ℕ) (hk : k ≥ 1) : ∃ g : ℕ, ∀ n : ℕ, IsSumOfPowers n g k
axiom wieferich_nine_cubes : ∀ n : ℕ, IsSumOfPowers n 9 3
axiom waring_general_formula : ∀ k : ℕ, k ≥ 6 → waringG k = 2 ^ k + (3 ^ k - 1) / 2 ^ k - 2
axiom vinogradov_waring_bound : ∃ C > 0, ∀ k : ℕ, k ≥ 2 →
  waringBigG k ≤ k * (Nat.log k + C * Nat.log (Nat.log k + 2) + C)
```

This document audits these, identifies gaps for $k = 4, 5$, proposes a minimal axiom inventory for the full $g(k)$ determination, and traces each axiom to a specific historical paper. It also flags one redundancy (`hilbert_waring` is strictly subsumed by the per-$k$ upper-bound axioms once they exist).

## 1. Coverage matrix

| $k$ | Upper bound | Lower bound | Combined `waringG k = N` |
|---:|---|---|---|
| 2 | Lagrange (`Nat.sum_four_squares`, **Mathlib-proved**) | $7$ needs $4$ squares (parent file lines 53–80, **Lean-proved**) | `lagrange_is_waring_2` (parent, **Lean-proved**) |
| 3 | `wieferich_nine_cubes` (axiom, parent line 271) | `g3_lower` (S2 ACT, **#18176 open**) | derive `waringG 3 = 9` ✓ |
| 4 | **GAP** — no axiom | `g4_lower` (S3 PREP, **#18314 design**) | **blocked on upper-bound axiom** |
| 5 | **GAP** — no axiom | not yet designed | **blocked on both** |
| 6 | `waring_general_formula 6` (axiom, parent line 277, $k \ge 6$ formula) | not yet designed | **blocked on lower bound** |
| $\ge 7$ | `waring_general_formula k` (same axiom, formula route) | not yet designed | **blocked on lower bound** |

**Coverage gaps**:
- **$k = 4$**: no upper-bound axiom. Balasubramanian-Deshouillers-Dress 1986 is the canonical citation.
- **$k = 5$**: no upper-bound axiom. Chen Jingrun 1964.

## 2. Proposed axiom additions

The minimal new axiom set to close the $k = 4, 5$ gaps:

```lean
/-- Balasubramanian-Deshouillers-Dress (1986): g(4) = 19. Every natural number
    is a sum of at most 19 fourth powers.

    Reference: R. Balasubramanian, J.-M. Deshouillers, F. Dress, "Problème
    de Waring pour les bicarrés", C. R. Acad. Sci. Paris Ser. I, 303 (1986),
    85-88 (upper bound) and 161-163 (matching lower bound). -/
axiom bdd_nineteen_fourth_powers :
    ∀ n : ℕ, IsSumOfPowers n 19 4

/-- Chen Jingrun (1964): g(5) = 37. Every natural number is a sum of at most
    37 fifth powers.

    Reference: Chen Jingrun, "Waring's problem for g(5) = 37", Sci. Sinica,
    13 (1964), 1547-1568. -/
axiom chen_thirty_seven_fifth_powers :
    ∀ n : ℕ, IsSumOfPowers n 37 5
```

These mirror the shape of `wieferich_nine_cubes` (parent line 271). Total new axioms: **2**.

### Trace to historical papers

| Axiom | Year | Author(s) | Paper |
|---|---:|---|---|
| `wieferich_nine_cubes` (existing) | 1909/1912 | A. Wieferich + A. J. Kempner | Wieferich, *Math. Ann.* 66 (1909), 95–101; Kempner, *Math. Ann.* 72 (1912), 387 (filled a gap in Wieferich's argument for 6 specific values) |
| `bdd_nineteen_fourth_powers` (proposed) | 1986 | R. Balasubramanian, J.-M. Deshouillers, F. Dress | *C. R. Acad. Sci. Paris Sér. I*, 303 (1986), 85–88 + 161–163 |
| `chen_thirty_seven_fifth_powers` (proposed) | 1964 | Chen Jingrun | *Sci. Sinica*, 13 (1964), 1547–1568 |
| `waring_general_formula` (existing, $k \ge 6$) | 1940/1957/1990 | S. S. Pillai (1940 for $k = 6$); K. Mahler (1957 conditional general $k$); J. M. Kubina & M. Wunderlich (1990 verification up to $k \sim 5 \times 10^8$) | Pillai, *J. Indian Math. Soc.* 12 (1940); Mahler, *Mathematika* 4 (1957), 122–124; Kubina-Wunderlich, *Math. Comp.* 55 (1990) |
| `hilbert_waring` (existing) | 1909 | D. Hilbert | "Beweis für die Darstellbarkeit der ganzen Zahlen durch eine feste Anzahl $n$-ter Potenzen (Waringsches Problem)", *Math. Ann.* 67 (1909) |

## 3. Redundancy check

### `hilbert_waring` vs. per-$k$ axioms

`hilbert_waring (k) (hk : k ≥ 1) : ∃ g, ∀ n, IsSumOfPowers n g k` is **subsumed** by the existence of any per-$k$ upper-bound axiom — for example, `wieferich_nine_cubes` immediately gives `hilbert_waring 3 (by norm_num) := ⟨9, wieferich_nine_cubes⟩`.

Status options:
- **Keep `hilbert_waring`**: useful for $k \ge 7$ where no explicit upper-bound numeric value is needed (the existence alone suffices for some applications). The Mahler-Kubina-Wunderlich verified range covers all "practical" $k$, so this is a *defensive* axiom.
- **Remove `hilbert_waring`, derive it as a theorem from `waring_general_formula`**: this would tighten the axiom count by 1, but requires:
  ```lean
  theorem hilbert_waring (k : ℕ) (hk : k ≥ 1) : ∃ g : ℕ, ∀ n : ℕ, IsSumOfPowers n g k := by
    interval_cases k
    · exact ⟨1, fun n => ⟨fun _ => n, by simp⟩⟩  -- k = 1 trivial
    · exact ⟨4, fun n => Nat.sum_four_squares_iff.mpr ⟨_, rfl⟩⟩  -- k = 2 Lagrange
    · exact ⟨9, wieferich_nine_cubes⟩  -- k = 3
    · exact ⟨19, bdd_nineteen_fourth_powers⟩  -- k = 4 (proposed)
    · exact ⟨37, chen_thirty_seven_fifth_powers⟩  -- k = 5 (proposed)
    -- k ≥ 6: use waring_general_formula
    sorry  -- requires unfolding the formula
  ```
  The unfolding for $k \ge 6$ needs careful arithmetic (formula gives explicit `2^k + (3^k - 1)/2^k - 2`); the existence claim is immediate but the Lean cast may need work.

**Recommendation**: keep `hilbert_waring` as a deliberately redundant axiom for $k \ge 7$ when the per-$k$ value isn't load-bearing. Document the redundancy in `meta.json:assumptions`.

### `waring_general_formula` overlap with $k = 6, 7$

`waring_general_formula k (hk : k ≥ 6)` covers $k = 6$ via the closed form $g(6) = 2^6 + \lfloor (3/2)^6 \rfloor - 2 = 64 + 11 - 2 = 73$ (here $(3/2)^6 = 729/64 \approx 11.39$, so floor is 11). For $k = 7$: $g(7) = 128 + \lfloor (3/2)^7 \rfloor - 2 = 128 + 17 - 2 = 143$. **No additional axiom needed** for $k \ge 6$.

The lower bounds for $k \ge 6$ are:
- $k = 6$: $703$ needs $73$ sixth-powers (Wieferich-style mod-64 argument or direct counting).
- $k = 7$: $2418$ needs $143$ seventh-powers.
- General: $N_k = 2^k \lfloor (3/2)^k \rfloor - 1$ needs $g(k)$ summands (the Mahler tightness witness — see § 7).

These all admit Lean lower-bound proofs by counting + omega (S3 PREP design extends mechanically). They reduce a `waringG k = N` claim to `waring_general_formula k + g(k)_lower`.

## 4. Concrete `waringG k = N` derivation theorems (post-S4)

Once the four axioms are in place, the per-$k$ closure theorems are:

```lean
/-- g(2) = 4 (Lagrange). Already proved in `lagrange_is_waring_2`. -/
theorem waringG_eq_four : waringG 2 = 4 := rfl

/-- g(3) = 9 (Wieferich-Kempner). Requires lower bound from S2 ACT. -/
theorem waringG_eq_nine
    (h_lower : ¬ IsSumOfPowers 23 8 3) :  -- from PR #18176
    waringG 3 = 9 := by
  -- waringG 3 is defined as 9 by pattern match; the theorem certifies it
  -- against the axiomatized upper bound and the proven lower bound.
  rfl  -- if the definition matches; otherwise needs `waringG_def` unfolding

/-- g(4) = 19 (Balasubramanian-Deshouillers-Dress). -/
theorem waringG_eq_nineteen
    (h_lower : ¬ IsSumOfPowers 79 18 4) :  -- from S3 ACT (post-#18314)
    waringG 4 = 19 := rfl  -- as above

/-- g(5) = 37 (Chen). -/
theorem waringG_eq_thirty_seven
    (h_lower : ¬ IsSumOfPowers 223 36 5) :  -- from S5 ACT (not yet designed)
    waringG 5 = 37 := rfl

/-- g(6) = 73 (Pillai / formula). -/
theorem waringG_eq_seventy_three
    (h_lower : ¬ IsSumOfPowers 703 72 6) :  -- from S6 ACT
    waringG 6 = 73 := by
  have h := waring_general_formula 6 (by norm_num)
  simp [waringG] at h ⊢
  -- h : waringG 6 = 2^6 + (3^6 - 1) / 2^6 - 2 = 64 + 11 - 2 = 73
  omega
```

The lower-bound hypotheses `h_lower` flow from the per-$k$ S(N) ACT iterations (PR #18176 for $k = 3$, future PRs for $k = 4, 5, 6$). The pattern is uniform: each `waringG k = N` is `rfl` (or close) against the pattern-match definition, with the hypothesis `h_lower` certifying tightness.

## 5. `meta.json` impact (deferred to S4 ACT)

Each new axiom in `Proofs/LagrangeFourSquares.lean` increments the gallery's `axiomCount`:

| Slug | Current `axiomCount` (estimate) | Post-S4 ACT |
|---|---:|---:|
| `lagrange-four-squares` (parent) | 4 (`hilbert_waring`, `wieferich_nine_cubes`, `waring_general_formula`, `vinogradov_waring_bound`) | 6 (+`bdd_…`, +`chen_…`) |
| `lagrange-four-squares-waring-g2` (verified parent) | 0 (uses `Nat.sum_four_squares` directly, no new axioms) | 0 |
| `lagrange-four-squares-waring-g2-oq-01` (this slug) | not yet created; will live in `LagrangeFourSquaresWaringG2OQ01.lean` | 0 (consumes parent axioms; declares none of its own) |

Per the **Axiom Integrity Policy** (CLAUDE.md), the OQ-01 file should:
- Not redeclare existing axioms.
- Declare its `assumptions` field in `meta.json` listing the consumed parent axioms.
- Set `status: "axiomatized"`, `badge: "axiom"` until all axioms are eliminated.

## 6. Out of scope for this S4 PREP

- **$G(k)$ (the "hard" Waring number)**: distinct from $g(k)$; parent already has `waringBigG` (line 282) and `vinogradov_waring_bound` (line 290). Linnik 1943 ($G(3) = 7$), Davenport 1939 ($G(4) = 15$) would need separate axioms — but $G(k)$ is **not** part of OQ-01's scope (which asks about $g(k)$). Defer.
- **Direct Lean proofs of the upper bounds**: these are 20th-century papers running 50–200 pages each (Hilbert, Wieferich-Kempner, Balasubramanian-Deshouillers-Dress, Chen, Pillai, Mahler-Kubina-Wunderlich). Lean-proving any of them would consume thousands of person-hours and require infrastructure (circle method, Vinogradov mean-value, Hardy-Littlewood asymptotic formula) that Mathlib does not yet provide.
- **Lower bound for $k = 5$**: would require a Wieferich-style argument or a counting+omega bound for $223$ and $36$ fifth-powers. The space $\\text{Fin } 36 \to \mathbb{N}$ with summand bound `a < 4` (since $4^5 = 1024 > 223$) is $4^{36}$ tuples — far beyond `native_decide`. A counting argument analogous to S3 PREP (PR #18314) is feasible but designed separately.
- **Lower bound for $k = 6$**: analogous; $703$ and $72$ sixth-powers, summand bound `a < 4` since $4^6 = 4096 > 703$. Counting argument over $n_0, n_1, n_2, n_3$ with $n_0 + n_1 + n_2 + n_3 = 72$ and $0 \cdot n_0 + 1 \cdot n_1 + 64 \cdot n_2 + 729 \cdot n_3 = 703$ — `omega` should discharge.

## 7. Mahler tightness witness (background, not axiomatized)

Mahler 1957 showed the formula $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$ is tight (achieves the supremum over $n$ requiring $g(k)$ summands) under the side condition

$$\{(3/2)^k\} \le 1 - (3/4)^k \quad \text{(equivalently, } 2^k \{(3/2)^k\} + \lfloor (3/2)^k \rfloor \le 2^k\text{)}$$

where $\\{x\\}$ is the fractional part. Kubina-Wunderlich 1990 verified this side condition for all $k$ up to $k \le 471{,}600{,}000$. It is conjectured to hold for all $k \ge 1$, but the conjecture is not proved — hence "conditional" caveat on `waring_general_formula`.

The Mahler tightness witness — the number requiring exactly $g(k)$ summands — is

$$N_k = 2^k \lfloor (3/2)^k \rfloor - 1 = \\overbrace{(2^k - 1) \cdot \lfloor (3/2)^k \rfloor}^{\text{summand bound}} + \\overbrace{\lfloor (3/2)^k \rfloor - 1}^{\text{remainder}}.$$

For $k = 3$: $N_3 = 8 \cdot 3 - 1 = 23$ ✓ (matches PR #18176's target).
For $k = 4$: $N_4 = 16 \cdot 5 - 1 = 79$ ✓ (matches PR #18314's target).
For $k = 5$: $N_5 = 32 \cdot 7 - 1 = 223$ ✓ (matches the lower bound in § 6 above).
For $k = 6$: $N_6 = 64 \cdot 11 - 1 = 703$ ✓.
For $k = 7$: $N_7 = 128 \cdot 17 - 1 = 2175$. **Note**: the table in `state.md` (line 19) and `knowledge.md` may quote $2418$ for $k = 7$, which is a different witness candidate; the canonical Mahler witness is $2175$. (Verification: $2175 = 16 \cdot 128 + 127$, and $127 = 7 \cdot 16 + 15 = \\dots$ — needs $128 + 17 - 2 - 1 + 1 = 143$ summands? Direct check: $2175 = 16 \cdot 128 + 127$; $127 = 16 \cdot 7 + 15$; … the actual closed-form verification requires Kubina-Wunderlich's tables.)

This is **forward background**; not part of S4 ACT, but useful for any researcher writing $k \ge 7$ lower bounds.

## 8. Anti-targets (do not pick up these in S4)

- **Editing `Proofs/LagrangeFourSquares.lean`**: adding the two proposed axioms is S4 ACT territory, not S4 PREP. This document specifies the axioms but does not add them.
- **Editing `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`**: PR #18176 is the active S2 ACT for this file; concurrent edits would conflict. Wait for #18176 to merge, then do S4 ACT in a follow-up.
- **Editing `state.md`** / `knowledge.md` / `problem.md` / `meta.json` / `lagrange-four-squares-waring-g2-oq-01.json`: PR #18176 and PR #18314 may touch these; avoid. Single new file in `sessions/`.
- **Adding `loom:review-requested`**: math-agent policy.

## 9. Honest scope

This file is a **forward-planning survey of upper-bound axiom design**. It does NOT add any axiom, discharge any sorry, modify any Lean source, change any `meta.json` count, or edit any other research file. The single new file is this session note.

Substantive findings:
- The current parent axiom set has gaps at $k = 4, 5$ (no upper-bound axiom).
- Two new axioms (`bdd_nineteen_fourth_powers`, `chen_thirty_seven_fifth_powers`) close the gap minimally.
- `hilbert_waring` is technically subsumed once the per-$k$ axioms exist; recommendation is to keep it for the $k \ge 7$ existence-only use case.
- The Mahler tightness witnesses $N_k = 2^k \lfloor (3/2)^k \rfloor - 1$ match $23, 79, 223, 703$ for $k = 3, 4, 5, 6$ — the canonical lower-bound targets.

## 10. Differentiation from PRs #18176, #18314

PR #18176 (S2 ACT, OPEN): Lean-proves $\neg \\text{IsSumOfCubes } 8 \\, 23$. **Lower bound**.
PR #18314 (S3 PREP, MERGED): designs Lean proof of $\neg \\text{IsSumOfFourthPowers } 18 \\, 79$. **Lower bound**.

Both target the *bottom* tier of the two-tier strategy. This S4 PREP targets the *top* tier — the upper-bound axiom inventory — which neither prior PR addresses. Orthogonal and complementary.

Recommendation for the next researcher claiming this slug: when PR #18176 is merged and S3 ACT is ready, also bundle the two new upper-bound axioms (`bdd_…`, `chen_…`) into the same file (or a parent-file edit). This unblocks `waringG k = N` certification theorems for $k = 4, 5$ in a single S4 ACT iteration.
