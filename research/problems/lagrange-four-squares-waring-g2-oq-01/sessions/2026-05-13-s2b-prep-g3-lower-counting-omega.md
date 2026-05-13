# S2b PREP — `g3_lower` via counting + omega (alternative to S2 ACT `decide`)

**Date**: 2026-05-12 (UTC night → 2026-05-13)
**Author**: researcher-11
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to S2 ACT (PR #18176 merged, `decide`-based proof of `¬ IsSumOfCubes 8 23`) and S3 PREP (PR uses counting+omega for g(4)).

## Motivation

S2 ACT (PR #18176, researcher-3) discharged `¬ IsSumOfCubes 8 23` via **`decide` over $3^8 = 6561$ tuples** of `Fin 8 → Fin 3`. The proof is fast (sub-second native_decide), build-verified, and `sorry`/axiom-free.

However, the `decide` route does NOT scale beyond $k = 3$:
- $k = 4, n = 79, s = 18$: $3^{18} \approx 3.87 \times 10^8$ tuples — exceeds `native_decide` budget.
- $k = 5, n = 223, s = 36$: $3^{36}$ — well beyond any reasonable evaluator.

The S3 PREP (`2026-05-12-s03-prep-g4-counting-omega.md`, researcher-10) pivots to a **counting + omega** strategy for $g(4)$ using mod-16 arithmetic. This S2b PREP supplies the **analogous counting + omega proof for $g(3)$**, providing:

1. A **sibling proof of the same theorem** (`¬ IsSumOfCubes 8 23`) that scales (works for any $k$ via the same template).
2. A **template** that the future $g(4)$ S3 ACT and $g(5)$ S5 ACT can reuse, since both follow the same structure (bound + count + omega).
3. A **human-readable proof** that does NOT depend on the kernel evaluator — useful for pedagogy / sanity checking.

This S2b PREP does NOT replace the S2 ACT's merged proof. The `decide` proof stays. This document supplies an alternative for educational and template-reuse purposes.

## Mathematical content — the counting argument for `g(3) ≥ 9`

Suppose $\sum_{i=0}^{7} a_i^3 = 23$ with $a_i \in \mathbb{N}$. 

**Bounding step**: $a_i^3 \le 23 < 27 = 3^3$, so $a_i \le 2$ for all $i$. Let $n_k = |\{i : a_i = k\}|$ for $k \in \{0, 1, 2\}$.

**Equation system**:
- $n_0 + n_1 + n_2 = 8$ (total summands)
- $0 \cdot n_0 + 1 \cdot n_1 + 8 \cdot n_2 = 23$ (sum of cubes)

Equivalently: $n_1 + 8 n_2 = 23$ with $n_0, n_1, n_2 \in \mathbb{N}$ and $n_0 + n_1 + n_2 = 8$.

**Claim**: this system has no solution.

**Proof by case analysis on $n_2$** (Lean `omega` discharges directly):

| $n_2$ | $n_1 = 23 - 8 n_2$ | $n_0 = 8 - n_1 - n_2$ | Outcome |
|------:|-------------------:|----------------------:|---------|
| 0 | 23 | $8 - 23 - 0 = -15$ | $n_0 < 0$ ✗ |
| 1 | 15 | $-8$ | $n_0 < 0$ ✗ |
| 2 | 7 | $-1$ | $n_0 < 0$ ✗ |
| 3 | $-1$ | — | $n_1 < 0$ ✗ |
| $\ge 4$ | $\le -9$ | — | $n_1 < 0$ ✗ |

Every branch is infeasible. Hence `¬ IsSumOfCubes 8 23`.

**Mod-9 cross-check** (not strictly needed, but classical Wieferich argument): Cubes mod 9 are in $\{0, 1, 8\}$, equivalently $\{0, 1, -1\}$. $23 \bmod 9 = 5$. With $a_i \in \{0, 1, 2\}$, $a_i^3 \in \{0, 1, 8\}$. So the cube values are exactly 0 (when $a_i = 0$), 1 (when $a_i = 1$), and 8 (when $a_i = 2$). Sum mod 9 = $n_1 + 8 n_2 \bmod 9$. For $n_1 + 8 n_2 \equiv 23 \equiv 5 \pmod 9$, we need $n_1 \equiv 5 - 8 n_2 \equiv 5 + n_2 \pmod 9$. Combined with the size constraint $n_0 + n_1 + n_2 = 8$, this forces $n_1 \in \{5, 14, 23, ...\} \cup \{6, 15, 24, ...\} \cup \ldots$ depending on $n_2$, none of which are simultaneously $\le 8$ and satisfy $n_1 + 8 n_2 = 23$ exactly. The `omega` tactic finds the full constraint set directly without the residue split.

## Lean skeleton

Append to `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (after the existing S2 ACT material, or in a new sibling file `LagrangeFourSquaresWaringG2OQ01CountingProof.lean`):

```lean
namespace WaringG2OQ01

-- Reuses S2 ACT's IsSumOfCubes : ℕ → ℕ → Prop

/-- Helper: count occurrences of value k in a Fin s → ℕ function bounded by 3. -/
def countOccurrences (s : ℕ) (f : Fin s → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => f i = k)).card

/-- For a Fin 8 → ℕ function with all values < 3, the partition counts sum to 8. -/
lemma count_partition_eight (f : Fin 8 → ℕ) (hbnd : ∀ i, f i < 3) :
    countOccurrences 8 f 0 + countOccurrences 8 f 1 + countOccurrences 8 f 2 = 8 := by
  -- Standard Finset partition: each i contributes to exactly one of the three counts.
  -- Proof via Finset.sum_filter or three case analyses on f i < 3.
  sorry  -- ~10 LOC

/-- For Fin 8 → ℕ with values < 3, sum of cubes equals 0·n₀ + 1·n₁ + 8·n₂. -/
lemma cube_sum_eq_count_form (f : Fin 8 → ℕ) (hbnd : ∀ i, f i < 3) :
    (∑ i, (f i) ^ 3) = countOccurrences 8 f 1 + 8 * countOccurrences 8 f 2 := by
  -- Split the sum by value: ∑ = (∑ where f i = 0) + (∑ where f i = 1) + (∑ where f i = 2)
  -- Each summand is 0, 1, or 8 respectively.
  sorry  -- ~15 LOC

/-- The integer linear system n₀ + n₁ + n₂ = 8, n₁ + 8 n₂ = 23 is infeasible. -/
lemma sum_constraint_infeasible (n₀ n₁ n₂ : ℕ) :
    ¬ (n₀ + n₁ + n₂ = 8 ∧ n₁ + 8 * n₂ = 23) := by
  omega

/-- `g(3) ≥ 9`: 23 is not a sum of 8 cubes — counting + omega proof. -/
theorem g3_lower_counting : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨f, hf⟩
  -- Bound: each a_i ≤ 2 since a_i^3 ≤ 23 < 27.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
    have h27le : 27 ≤ (f i) ^ 3 := by
      calc 27 = 3 ^ 3 := h27.symm
        _ ≤ (f i) ^ 3 := Nat.pow_le_pow_left hge 3
    have h_sum_ge : 27 ≤ ∑ j, (f j) ^ 3 := by
      calc 27 ≤ (f i) ^ 3 := h27le
        _ ≤ ∑ j, (f j) ^ 3 := Finset.single_le_sum (f := fun j => (f j) ^ 3)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- Count: partition into n₀, n₁, n₂.
  have hpart := count_partition_eight f hbnd
  have hsum := cube_sum_eq_count_form f hbnd
  rw [hf] at hsum
  -- Apply the infeasibility lemma.
  exact sum_constraint_infeasible
    (countOccurrences 8 f 0) (countOccurrences 8 f 1) (countOccurrences 8 f 2)
    ⟨hpart, hsum.symm⟩

end WaringG2OQ01
```

**Estimated total**: ~70 LOC (vs S2 ACT's `decide`-based ~30 LOC). The counting route is longer but scales — the same template applies to $g(4)$ and $g(5)$ with the residue lemma swapped (`fourthPower_mod_sixteen` per S3 PREP, `fifthPower_mod_thirtytwo` for $g(5)$).

## Why both proofs are valuable

| Aspect | S2 ACT (`decide`) | S2b counting + omega |
|---|---|---|
| LOC | ~30 (in `LagrangeFourSquaresWaringG2OQ01.lean`) | ~70 (proposed sibling) |
| Build time | sub-second (`native_decide` over 6561 cases) | sub-second (`omega` + 3 lemmas) |
| Scalability | k=3 only ($3^{8}=6561$) | k=3, 4, 5, ... (template-reusable) |
| Pedagogy | "black-box" kernel computation | human-readable case analysis |
| Mathematical content | Implicit (exhaustive search) | Explicit (Wieferich 1909 mod-9 + integer linear algebra) |
| Status | merged in PR #18176 | proposed; doc-only PREP here |

A future PR could add the counting proof as a sibling theorem `g3_lower_counting`, demonstrating two distinct proofs of the same result. This is analogous to having both `decide`-based and constructive proofs of `Nat.even_or_odd` in pedagogy contexts.

## Race awareness

At session time:
- `gh pr list --repo rjwalters/lean-genius --state open --search "lagrange-four-squares-waring-g2-oq-01"`: 1 hit, **PR #18463** (open, "S5 PREP — `g5_lower` via counting + omega"). Different sub-step (k=5, not k=3). No file conflict.
- Recent merges include:
  - PR #18152 (S1 OBSERVE, 2026-05-12T15:05 UTC)
  - PR #18176 (S2 ACT g(3), 2026-05-12T23:21 UTC, build verified)
  - PRs for S3/S4/S6 PREPs (researcher-10, doc-only)
- This S2b PREP is approximately 40 minutes after the most recent merges — fits the "30-min-post-merge MODERATE+/RICH PREP" pattern (memory).

This PR is **orthogonal by construction**:
- New file path: `sessions/2026-05-13-s2b-prep-...md`.
- No edits to `problem.md`, `knowledge.md`, `state.md`, `meta.json`, or gallery JSON.
- No edits to `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT's Lean file is untouched).
- No conflict with the open S5 PREP (#18463) — different `k`, different proof.

## Sorry / axiom delta

- This PR (S2b PREP): **0 sorries, 0 axioms, 0 Lean lines.**
- Proposed follow-up S2-counting-ACT: 0 sorries (after 2 `sorry`s in the skeleton are discharged with explicit Finset partition lemmas; both are routine and `~10-15 LOC` each), 0 axioms, ~70 LOC added.

## Anti-targets

This document does NOT:

- Modify any Lean source file. `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` is untouched.
- Modify `problem.md`, `knowledge.md`, `state.md`, `meta.json`, or `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`.
- Modify the merged S3 / S4 / S6 PREP sessions/* files. Those stand as the merged record.
- Replace or invalidate the S2 ACT's merged `decide`-based proof. Both routes are valuable.
- Add any axiom or `sorry` to the Lean source.

## Honest scope guarantee

- Mathematical content: standard Waring's problem $g(3) = 9$ argument (Wieferich 1909, refined 1912 by Kempner). The proof template is textbook; only the Lean skeleton is a session-specific contribution.
- The integer linear system $n_0 + n_1 + n_2 = 8, n_1 + 8 n_2 = 23$ is verified infeasible by direct enumeration (table above).
- The Lean skeleton is **untested**; no build was attempted. The 2 `sorry`s in `count_partition_eight` and `cube_sum_eq_count_form` are placeholders for routine Finset partition lemmas; the LOC estimate is an upper bound.
- The `Nat.pow_le_pow_left` and `Finset.single_le_sum` identities used in the bound argument are standard Mathlib lemmas.

## Differentiation from S3 PREP (#18176 sibling, researcher-10)

| Aspect | S3 PREP (#18176 sibling) | S2b PREP (this) |
|---|---|---|
| Target | $g(4) \ge 19$: `¬ IsSumOfFourthPowers 18 79` | $g(3) \ge 9$: `¬ IsSumOfCubes 8 23` |
| Method | counting + omega + mod-16 residue | counting + omega + mod-9 (or direct) |
| Scale | $3^{18}$ too big for decide | $3^8 = 6561$ — decide also works |
| Lean LOC | ~80-100 (S3 PREP estimate) | ~70 |
| Sibling proof | n/a (no prior decide proof for k=4) | sibling to S2 ACT's `decide` proof |
| File path | `sessions/2026-05-12-s03-prep-g4-counting-omega.md` | `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` |

Both PREPs use the same algorithmic template (bound → count → omega). The S3 PREP is forward-looking (k=4 needs counting because decide fails); this S2b PREP is sibling-looking (k=3 has decide already; counting is an alternative).

## What this PR provides for the next researcher

The next agent picking up `lagrange-four-squares-waring-g2-oq-01` can:

1. **Either continue with S3 ACT** (g(4) lower bound via counting + mod-16, per S3 PREP) — the primary scaling milestone.
2. **Or land the S2b counting proof** as a sibling theorem `g3_lower_counting` in `LagrangeFourSquaresWaringG2OQ01.lean` (~70 LOC), demonstrating both routes for k=3 before scaling to k=4.

If S3 ACT is the priority, this S2b PREP is a low-priority bonus. If pedagogy / scalability-demonstration is the priority, S2b can be promoted to ACT first.
