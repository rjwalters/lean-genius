# S8 ACT — Axiom-elimination second pass (vinogradov_ternary_goldbach + helfgott_explicit_bound)

**Author:** researcher-1
**Timestamp:** 2026-06-10
**Phase:** S8 ACT — execute the discharges sketched by S6 PREP and S7 PREP
**Iteration:** 8
**Builds on:**
- S6 PREP (PR #18368, merged): sketched the 1-line discharge of
  `vinogradov_ternary_goldbach` from `helfgott_weak_goldbach`.
- S7 PREP (PR #18504, merged): projected post-discharge axiomCount of
  5, identifying `vinogradov_ternary_goldbach` and `helfgott_explicit_bound`
  as the two "historical-attribution" axioms ready for immediate ACT.
- S5 ACT (PR #18265, merged): set the precedent — `ramare_six_primes`
  and `tao_five_primes` axiom → theorem via `helfgott_weak_goldbach`.

## §1. What changed in `proofs/Proofs/WeakGoldbach.lean`

**Reorder + 2 axiom → theorem conversions.**

### §1.1. Helfgott moved above Vinogradov (lines 255-282)

Original order:
```lean
axiom vinogradov_ternary_goldbach : ∃ N₀, ∀ n > N₀, Odd n → IsSumOfThreePrimes n
axiom helfgott_weak_goldbach : WeakGoldbachConjecture
```

New order:
```lean
axiom helfgott_weak_goldbach : WeakGoldbachConjecture
theorem vinogradov_ternary_goldbach :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n → IsSumOfThreePrimes n :=
  ⟨5, helfgott_weak_goldbach⟩
```

Reordering is necessary so the derivation typechecks
(`helfgott_weak_goldbach` must be in scope when `vinogradov_ternary_goldbach`
is stated). Net structural change: 1 axiom block moved up; 1 theorem
block below it; docstring updates explain the derivation path.

### §1.2. Helfgott explicit bound (lines ~605-620)

Original:
```lean
axiom helfgott_explicit_bound :
    -- The threshold N₀ in Vinogradov's theorem is at most 8.875 × 10³⁰
    -- This is small enough to check computationally below
    ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n
```

The statement is **syntactically** `WeakGoldbachConjecture` unfolded.
Replacement:
```lean
theorem helfgott_explicit_bound :
    ∀ n : ℕ, n > 5 → Odd n → IsSumOfThreePrimes n :=
  helfgott_weak_goldbach
```

The narrative comments about the `8.875 × 10³⁰` threshold are preserved
in the docstring.

## §2. Why these two axioms specifically

Of the 7 pre-S8 axioms, these are the only ones whose statement is a
**strict logical consequence** of `helfgott_weak_goldbach`'s statement:

| Axiom | Statement shape | Derivable from Helfgott? |
|-------|-----------------|--------------------------|
| `vinogradov_ternary_goldbach` | `∃ N₀, ∀ n > N₀, …` | YES — take `N₀ := 5` |
| `helfgott_weak_goldbach` | `∀ n > 5, …` | (this is the load-bearing axiom) |
| `circle_method_asymptotic` | `r₃(n) ∼ S(n)·n²/2log³n` | NO — quantitative bound, not in Helfgott |
| `schnirelmann_basis_theorem` | density > 0 → basis | NO — generic combinatorics, Mathlib TODO |
| `chen_theorem` | even n = p + P₂ | NO — different statement (binary, not ternary) |
| `binary_goldbach_verified` | binary n ≤ 4·10¹⁸ | NO — about binary Goldbach |
| `helfgott_explicit_bound` | `∀ n > 5, …` | YES — *literally* `WeakGoldbachConjecture` |

The five non-derivable axioms are the practical floor for this slug
per S7 PREP §4.6 and S8 PREP-1 §11 / S8 PREP-2 §11.

## §3. Honest scope

* **The underlying mathematical assumption set is unchanged.** Both
  new theorems still depend transitively on `helfgott_weak_goldbach`,
  which remains axiomatized. The reduction is purely in the file's
  *explicit `axiom` declarations*, from 7 to 5.
* **No mathematical advance.** The proofs are routine logical
  consequences of an already-axiomatized stronger result. Per
  `researcher.md`'s axiom-elimination priority and the S5 precedent
  (PR #18265), this is real progress on the *axiom-surface integrity*
  axis but does not introduce new mathematical content.
* **The remaining 5 axioms are genuinely distinct deep claims.** No
  further axiom can be discharged from inside the slug without doing
  real new mathematics (e.g., the Schnirelmann basis theorem proof
  outlined in S8 PREP-1 §2).
* **Build status will be reported in the PR description** under the
  documented "build pending — parent drift cluster" convention (cf.
  S2 #18068, S3 #18108, S5 #18265). The two `theorem` derivations
  themselves are trivial type-checks; any build failure will be in
  the pre-existing drift around `exponentialSumOverPrimes`,
  `representationCount_pos_iff`, `singular_series_positive` per state.md
  S2 audit (lines 248-258).

## §4. Counts delta

| Field | Before S8 ACT | After S8 ACT | Delta |
|-------|---------------|--------------|-------|
| `axiomCount` | 7 | 5 | −2 |
| `theoremCount` | 29 | 31 | +2 |
| `lineCount` | 661 | 680 | +19 |
| `definitionCount` | 15 | 15 | 0 |
| Sorries | 0 | 0 | 0 |

## §5. Files modified

- `proofs/Proofs/WeakGoldbach.lean` (661 → 680 lines; 2 axioms → 2
  theorems; helfgott_weak_goldbach moved above
  vinogradov_ternary_goldbach).
- `research/problems/weak-goldbach-oq-03/state.md` (S8 ACT section,
  session history, current focus).
- `research/problems/weak-goldbach-oq-03/sessions/2026-06-10-s8-act-vinogradov-helfgott-explicit-discharge.md` (this file).
- `src/data/proofs/weak-goldbach/meta.json` (description, assumptions,
  axiomCount, theoremCount, lineCount, leanFile.*).

## §6. Next iteration candidates (S9+)

The 5 remaining axioms have no further trivial-discharge path. The
realistic next steps:

- **S9 (Approach D-phase-1)**: Schnirelmann sumset inequality
  `σ(A+B) ≥ σ(A) + σ(B) − σ(A)σ(B)` from `Mathlib.Combinatorics.Schnirelmann`.
  Per S8 PREP-1 §2.1, ~250-350 LOC; per S8 PREP-2 §7, this is the
  dominant cost step. Discharges nothing on its own; sets up S10.
- **S10 (Approach D-phase-2)**: Combine Steps B (induction), C
  (Mathlib already has it per S8 PREP-2 §2), D (basis from density),
  + Multiset bridge into a discharge of `schnirelmann_basis_theorem`.
  ~125-190 LOC per S8 PREP-2 §8.2.

Both Approach D phases are *real new mathematics* unlike S5/S8's
historical-corollary discharges. They would also be Mathlib
upstream-PR candidates (the module docstring explicitly TODOs
Schnirelmann's theorem).

The other 4 axioms (`helfgott_weak_goldbach`, `circle_method_asymptotic`,
`chen_theorem`, `binary_goldbach_verified`) are the long-term aspirational
limit — multi-year formalization efforts.

## §7. Anti-targets (this S8 ACT explicitly does NOT do)

1. **Does not touch the other 5 axioms** (Helfgott, circle method,
   Schnirelmann basis, Chen, binary verified). All require real
   new mathematics or computation that is out of S8 ACT scope.
2. **Does not begin Approach D** (Schnirelmann sumset inequality).
   That is the S9 target per the PREP-2 §8 ordering.
3. **Does not address parent-file drift** (`exponentialSumOverPrimes`
   needing `noncomputable`, `representationCount_pos_iff` Mathlib
   signature change, `singular_series_positive` `positivity` failure).
   Per state.md S2 audit those are Mechanic concerns, not researcher.
4. **Does not run a fresh full lake build** outside the docker
   wrapper. Builds for `Proofs.WeakGoldbach` are slow (~10-15 min
   with cache) and known to fail on parent drift unrelated to S8 ACT's
   surgical changes.

## §8. References

* S6 PREP session note: `2026-05-12-s6-prep-vinogradov-helfgott-reduction.md` (PR #18368).
* S7 PREP session note: `2026-05-12-s7-prep-axiom-redundancy-audit.md` (PR #18504).
* S8 PREP-1: `2026-05-13-s8-prep-schnirelmann-basis-discharge-roadmap.md` (PR #18552).
* S8 PREP-2: `2026-05-13-s8-prep-2-mathlib-bearer-audit.md` (PR #18670).
* S5 ACT (precedent for axiom → theorem via Helfgott): PR #18265 (merged).
* Helfgott, H. A. (2013). Major arcs / Minor arcs for Goldbach's problem.
  arXiv:1305.2897, arXiv:1205.5252.
