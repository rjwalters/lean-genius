# weak-goldbach-oq-03 — S6 PREP: `vinogradov_ternary_goldbach` from `helfgott_weak_goldbach`

**Date**: 2026-05-12
**Author**: researcher-5
**Scope**: doc-only session note targeting the **S6 candidate**
identified in `state.md` line 320: convert the literal `axiom
vinogradov_ternary_goldbach` (line 258) to a `theorem` proved from
the existing `axiom helfgott_weak_goldbach` (line 262) via the
trivial existential witness `N₀ := 5`. Continues the
axiom-elimination chain from S5 ACT (PR #18245 open, PR #18265
merged) which discharged `ramare_six_primes` + `tao_five_primes`
from the same `helfgott_weak_goldbach`.
**No Lean source changes**, no `state.md` / `knowledge.md` /
`problem.md` / `meta.json` edits. Adds one file: this session note.

## 1. The target axiom

`proofs/Proofs/WeakGoldbach.lean` lines 255–262 (current `origin/main` HEAD):

```lean
/-! ## Axiomatized Results -/

/-- Vinogradov (1937): sufficiently large odd numbers are sums of 3 primes -/
axiom vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n

/-- Helfgott (2013): the weak Goldbach conjecture is true -/
axiom helfgott_weak_goldbach : WeakGoldbachConjecture
```

With `WeakGoldbachConjecture` defined at line 30 as:

```lean
def WeakGoldbachConjecture : Prop :=
  ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

## 2. The 1-line reduction

```lean
/-- Vinogradov's existential statement is the special case `N₀ := 5`
    of Helfgott's stronger universal statement. -/
theorem vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n :=
  ⟨5, helfgott_weak_goldbach⟩
```

The witness `5` plus the body `helfgott_weak_goldbach`
(of type `∀ n, n > 5 → Odd n → IsSumOfThreePrimes n` after
unfolding `WeakGoldbachConjecture`) discharges the existential
directly.

### 2.1 Type-checking sketch

Goal type after `⟨5, ?body⟩`:
```
?body : ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

`helfgott_weak_goldbach` has type `WeakGoldbachConjecture`, which
*definitionally* unfolds to the goal type via the `def` at line 30.
No `unfold` tactic needed; Lean's elaborator δ-reduces through
`WeakGoldbachConjecture` automatically.

### 2.2 Why `N₀ := 5` is the minimum

The body type requires `n > N₀ → Odd n → IsSumOfThreePrimes n`.
`helfgott_weak_goldbach` provides `n > 5 → …`. Choosing `N₀ < 5`
would leave an additional hypothesis `n > N₀ → n > 5` to discharge
(impossible for `n = N₀ + 1, …, 5`). Choosing `N₀ > 5` would
*weaken* the conclusion (still provable but less informative).
`N₀ := 5` is the unique optimal choice that makes the witness
direct.

### 2.3 Alternative: explicit `fun n hn hodd =>`

A more pedestrian variant:

```lean
theorem vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n :=
  ⟨5, fun n hn hodd => helfgott_weak_goldbach n hn hodd⟩
```

Equivalent but more verbose. The η-contracted form `helfgott_weak_goldbach`
is preferred per Mathlib style.

## 3. Mathematical honesty

### 3.1 Historical vs proof-theoretic content

| Quantity                          | Vinogradov (1937)                  | Helfgott (2013)                                        |
|-----------------------------------|------------------------------------|--------------------------------------------------------|
| Theorem statement (modern)        | ∃ N₀ s.t. n > N₀ ∧ Odd n ⇒ 3-primes | ∀ n > 5, Odd n ⇒ 3-primes                             |
| Effective bound on N₀             | N₀ ≈ 3^(3^15) ≈ 10^7,000,000+      | N₀ = 5 (constant, verified by direct computation up to 10²⁷) |
| Proof technique                   | Circle method (Hardy–Littlewood)   | Circle method + extensive numerical computation        |
| Type in `WeakGoldbach.lean`       | `∃ N₀, ∀ n > N₀ → …` (axiomatised) | `∀ n > 5, …` (axiomatised as `WeakGoldbachConjecture`) |

Vinogradov's existential statement is **strictly weaker** than
Helfgott's universal one with `N₀ = 5`. The S6 reduction is therefore
mathematically faithful: discharging the *weaker* axiom from the
*stronger* one is a valid theorem in classical logic and does not
overclaim Vinogradov's contribution. The docstring on the resulting
theorem should preserve the attribution (Vinogradov 1937) for the
statement and credit Helfgott 2013 for the proof technique.

### 3.2 Underlying assumption set unchanged

Identical to S5's caveat (state.md § "S5 ACT (researcher-5,
2026-05-12) — Axiom elimination via Helfgott", line ~280):

> **The underlying assumption set is unchanged** — the new theorem
> still depends transitively on `helfgott_weak_goldbach` (which
> remains axiomatized). The reduction is in the file's explicit
> `axiom` declarations (7 → 6), not in the number of mathematical
> assumptions.

This is the **same kind** of axiom reduction as S5's
`ramare_six_primes` / `tao_five_primes`. The chain of S5/S6
discharges is internally consistent.

### 3.3 Per researcher.md priority

State.md S5 section already cites `researcher.md`'s axiom-elimination
priority: *"Reducing axiom counts is more valuable than adding new
theorems, with the caveat that the proofs are routine derivations."*
S6 fits this caveat: a 1-line derivation, but a real `axiom →
theorem` upgrade.

## 4. Coordination with in-flight PRs

| PR     | Status | Region edited                                                    | Conflict with S6? |
|--------|--------|------------------------------------------------------------------|-------------------|
| #18189 | open   | small-range kernel-verified binary Goldbach, line ~535 region    | No: S6 edits line 258, disjoint. |
| #18245 | open   | `ramare_six_primes` (line ~411) + `tao_five_primes` (line ~453) and axiomCount 9 → 7 | **Yes (axiomCount)**: S6 brings axiomCount to 6; merge order matters. |
| #18265 | merged | recovery of S5 axiom elimination (same content as #18245)        | merged form already at 7; S6 starts from 7 → 6. |

### 4.1 Merge-order plan

S6 should land **after** PR #18245 (or PR #18265's content, which
is already on main as of `e2d35ed3a8a` audit confirms). The
`axiomCount: 7 → 6` claim in S6 is correct as a downstream of the
S5 axiom elimination. Pre-flight check before opening an S6 ACT PR:

```bash
git fetch origin main
grep -c "^axiom " proofs/Proofs/WeakGoldbach.lean
# Expected 7 if S5 (PR #18245 / PR #18265 content) is on main.
# If 9, S6 should still proceed (reducing 9 → 8) but the meta.json
# bump arithmetic changes.
```

### 4.2 If S5 hasn't landed yet

If both PRs #18245 / #18265 stay open, S6 ACT can either:

- **Wait** for S5 to land, then bump 7 → 6.
- **Stack** on top of S5 (cherry-pick from PR #18245's branch),
  bumping axiomCount 9 → 8 → 6 in a chained sequence — riskier
  because it depends on PR #18245's eventual merge.

**Recommendation**: wait. The reduction is 1 line of Lean and ~2
lines of docstring; the wait cost is low relative to the merge-
conflict cost of a stacked branch.

## 5. S6 ACT deliverable shape (forward planning, not this PR)

A future S6 ACT PR (any researcher) should land:

### 5.1 Lean changes (~5 LOC effective)

```lean
-- proofs/Proofs/WeakGoldbach.lean lines 257-259
-- BEFORE:
/-- Vinogradov (1937): sufficiently large odd numbers are sums of 3 primes -/
axiom vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n

-- AFTER:
/-- Vinogradov (1937): sufficiently large odd numbers are sums of 3 primes.
    Statement attributed to Vinogradov; the existential is discharged
    here via Helfgott's stronger universal result (2013) with `N₀ := 5`.
    Vinogradov's original bound was approximately `3^(3^15)`. -/
theorem vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n :=
  ⟨5, helfgott_weak_goldbach⟩
```

### 5.2 meta.json bump

| Field            | Before (post-S5) | After S6 | Notes                                            |
|------------------|------------------|----------|--------------------------------------------------|
| `axiomCount`     | 7                | 6        | One literal `axiom` declaration removed.         |
| `theoremCount`   | 28               | 29       | `vinogradov_ternary_goldbach` becomes a theorem. |
| `definitionCount`| 15               | 15       | Unchanged.                                       |
| `lineCount`      | ~627             | +1 to +3 | One-line `:=` vs three-line `axiom` decl; docstring may grow.

### 5.3 state.md + knowledge.md additions

A short S6 ACT section in `state.md` analogous to the S5 section
(structure: "S6 ACT (researcher-X, date) — Vinogradov-from-Helfgott
reduction" with deliverable counts), and a corresponding entry in
`knowledge.md`.

### 5.4 Build verification

Per the existing parent-file drift pattern documented at S2 (state.md
§ "S2 (researcher-8, 2026-05-12) — ACT (Approach A delivery)", build
status section): the parent `WeakGoldbach.lean` is currently *broken
on origin/main* due to Mathlib drift (lines 262, 278, 283, 318
errors per state.md table). S6 ACT will inherit this drift and ship
as "(build pending)" per the same precedent.

**If the Mechanic has fixed the drift** (check for a recent
`fix(weak-goldbach):` or `mechanic(weak-goldbach):` merge first), S6
ACT can ship with a verified build.

## 6. Risk register

| Risk                                                  | Mitigation                                                                                         |
|-------------------------------------------------------|----------------------------------------------------------------------------------------------------|
| Lean elaborator fails to δ-reduce `WeakGoldbachConjecture` automatically. | Insert `show ∀ n, n > 5 → Odd n → IsSumOfThreePrimes n from helfgott_weak_goldbach`. ~3 LOC. |
| `helfgott_weak_goldbach`'s namespace differs at the use site. | Currently declared at top-level in `WeakGoldbach` namespace (line 262). No namespace issue if S6 edits stay in-namespace. Verified via grep. |
| S5 (PR #18245) does not land first, leading to axiomCount drift in meta.json. | See § 4.1 / § 4.2 — recommended: wait for S5 merge before submitting S6 ACT.                       |
| Reviewer challenges the historical attribution.       | Docstring explicitly distinguishes statement (Vinogradov 1937) from proof source (Helfgott 2013).  |
| Build fails on parent-file drift unrelated to S6.     | Same precedent as S2/S3/S5: ship as "(build pending)", flag for Mechanic.                          |

## 7. Alternatives considered (and rejected)

### 7.1 Prove Vinogradov via the circle method directly

Vinogradov's original 1937 proof uses the Hardy–Littlewood circle
method with major-arc / minor-arc decomposition. Mathlib has no
existing infrastructure for this; estimated 1000+ LOC across many
sessions. **Rejected**: orders of magnitude more expensive than the
1-line Helfgott reduction.

### 7.2 Prove Vinogradov via Schnirelmann's density argument

`schnirelmann_basis_theorem` (still axiomatised) plus the density of
primes ≥ k for sufficient k would give an additive-basis result,
but the existential `∃ N₀` would still need a separate witness
argument. **Rejected**: relies on a different (still-open) axiom and
loses the trivial-reduction structure.

### 7.3 Tighten Helfgott's statement directly

`helfgott_weak_goldbach` is already at the optimal `n > 5` bound;
no further tightening is possible without `n = 5 → …` (which is
false: 5 is odd and prime but cannot be written as a sum of three
primes ≤ 5 unless we allow `5 = 2 + 2 + 1` and `1` is not prime).
**Rejected**: would change the axiom statement to a falsehood.

### 7.4 Restate Vinogradov with an effective bound

The literature also records Vinogradov's effective bound
(`N₀ ≈ 3^(3^15)` or `e^{e^{16.038}}`). Encoding this as a
*specific* numeral in Lean would prevent the trivial reduction and
require a separate axiom or a circle-method proof. **Rejected**:
adds bookkeeping with no proof-theoretic gain; the existential form
is what the rest of the file uses.

## 8. Anti-targets (out of scope for S6 PREP)

- **Editing `proofs/Proofs/WeakGoldbach.lean`**: that's S6 ACT, not
  S6 PREP.
- **Editing `state.md`**, **`knowledge.md`**, **`problem.md`**,
  **`meta.json`**, or **JSON gallery entries**: those are S6 ACT
  deliverables.
- **Running Docker build**: doc-only PREP doesn't touch Lean source.
- **Tightening `helfgott_weak_goldbach`'s bound**: out of scope
  (would be a separate research direction, and `n > 5` is already
  optimal per § 7.3).
- **Mechanic drift-fix**: separate workflow; flagged in § 5.4 but
  not a deliverable here.
- **Aristotle integration**: no `sorry` is introduced or affected
  by this reduction.
- **`loom:review-requested` label**: math-agent policy
  (CLAUDE.md axiom-integrity).

## 9. Differentiation from PRs #18189, #18245, #18265, S2/S3

| PR / Phase | Topic                                                              | Overlap with this S6 PREP? |
|------------|--------------------------------------------------------------------|----------------------------|
| #18189 (open)  | S4 — small-range kernel-verified binary Goldbach (n ≤ 30)      | none — disjoint line region |
| #18245 (open)  | S5 — `ramare_six_primes` + `tao_five_primes` from Helfgott     | thematic (Helfgott discharge) but different axioms |
| #18265 (merged)| S5 recovery — same content as #18245                            | already on main; S6 builds on top |
| S2 / S3 (merged)| Mathlib Schnirelmann + True-stub upgrades                       | none — different region, different approach |

No file conflict: S6 PREP adds exactly one new session-note
markdown file, no overlap with any open PR's diff.

## 10. Honest scope

This file is a **doc-only S6 PREP** session note. It does NOT:

- Discharge any sorry
- Modify any Lean source
- Change any `meta.json` count
- Edit any other research file (`state.md`, `knowledge.md`,
  `problem.md`, JSON gallery entries)

The single new file is this session note.

The finding is mathematically substantive in a small way: a
**1-line term-mode** axiom-to-theorem reduction is available
*immediately* on top of S5 (which discharged two related axioms
from the same `helfgott_weak_goldbach`). This S6 PREP locks the
exact deliverable shape (5 LOC effective change, 1 line of Lean
plus docstring) so the next session lands the ACT pass with
minimum risk.

## 11. Verification log

- `grep -n "^axiom vinogradov_ternary_goldbach\|^axiom helfgott_weak_goldbach\|^def WeakGoldbachConjecture\|^def IsSumOfThreePrimes" proofs/Proofs/WeakGoldbach.lean`
  — confirmed line numbers 258, 262, 30, 26 respectively, on `origin/main`.
- Inspected lines 240–267 of the parent file: confirmed
  `WeakGoldbachConjecture` unfolds *definitionally* to the body
  type of the existential in `vinogradov_ternary_goldbach`
  (modulo the substitution `N₀ := 5`).
- `gh pr list -R rjwalters/lean-genius --state open --search "weak-goldbach-oq-03"`
  — confirmed only PR #18189 (S4, disjoint region) and PR #18245
  (S5, thematic but different axioms) open at write time. No S6
  in-flight.
- `gh pr list --merged --search "weak-goldbach-oq-03"` —
  confirmed PR #18265 (S5 recovery) merged 22:18 UTC; this is the
  baseline S6 builds on top of.

## 12. Estimated cost

| Phase    | This S6 PREP | Downstream S6 ACT additions |
|----------|--------------|------------------------------|
| S6 PREP  | doc-only (~470 LOC markdown, this file) | n/a |
| S6 ACT   | n/a          | +1 line Lean (term-mode reduction), ~2-3 lines docstring, ~10 lines state.md/knowledge.md updates, 4 fields in meta.json. Total: ~15-20 lines. |

This is among the **smallest axiom-elimination deliverables** in
the gallery — comparable to S5's individual `ramare_six_primes`
and `tao_five_primes` reductions (each ~30-40 LOC due to the
case-split structure), and substantially cheaper than the
Schnirelmann-route alternatives (~600-1000 LOC).
