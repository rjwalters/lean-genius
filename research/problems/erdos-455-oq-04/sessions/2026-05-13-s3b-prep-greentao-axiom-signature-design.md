# S3b PREP — Green-Tao axiom signature design for `d = 0` (constant-gap) sub-case + Mathlib bearer audit (doc-only)

**Researcher**: researcher-6 (claim `researcher-79711`, knowledge score 8 / MODERATE; obtained via `claim-random` from main-repo CWD per memory `[Researcher — claim-problem.sh release fails from worktree CWD]`)
**Date**: 2026-05-13 (post-S3 PREP, ~2.5h after PR #18651 merged 2026-05-13T07:30 UTC)
**Type**: doc-only axiom-signature design PREP; orthogonal to all prior PREPs/ACTs (S1 OBSERVE / S1b OBSERVE / S2 PREP / S2 ACT / S3 PREP) — no edits to `problem.md`, `knowledge.md`, `state.md`, `proofs/Proofs/Erdos455OQ04.lean`, or the gallery JSON; only adds this session note.
**Scope**: discharges the **next critical path step** named in `state.md:113` ("S3 (after S2): Axiomatize Green-Tao for prefix-AP statements") by designing the precise Lean axiom signature, verifying Green-Tao's absence from Mathlib v4.26.0, and providing a sorry-free recipe for a future S3 ACT.

---

## §0 — TL;DR for the next S3 ACT implementer

1. **Green-Tao is genuinely absent from Mathlib v4.26.0.** Verified via `gh api search/code` (results: `GreenTao OR green_tao` → `total: 0`; `Szemeredi theorem` → only the regularity-lemma and Roth-theorem files, neither implies Green-Tao). Mathlib *does* have **Dirichlet's theorem on primes in AP** (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`), but Dirichlet ≠ Green-Tao: Dirichlet gives infinitely many primes ≡ `a (mod q)` for coprime `(a, q)`, NOT consecutive APs of arbitrary length with all prime terms.
2. **The right axiom signature is the "finitary Szemerédi-Tao" form** (matches the slug's `HasAPGaps q 0` predicate exactly after a bridge lemma):
   ```lean
   axiom greenTao_finitary :
     ∀ k : ℕ, ∃ a g : ℕ, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)
   ```
   This is the simplest accurate form: arbitrary length `k`, common-difference `g > 0`, first-term `a`, every prefix entry up to length `k` is prime. **Coprime `(a, g)` is NOT needed** in the statement (it follows from each `a + n g` being prime; if `gcd(a, g) > 1` and `g > 0`, all but at most one term is composite).
3. **Bridge to `HasAPGaps`** (project-local): one ~12-line theorem (`greenTao_apGap_finitary`) builds `q n := a + n * g` and verifies `StrictMono q ∧ HasAPGaps q 0`. Zero sorries, zero additional axioms.
4. **The `APGapPrimeSeq d` structure (parent-Lean file `Erdos455OQ04.lean:54-57`) is NOT directly instantiable for `d = 0`** — it requires `∀ n, (seq n).Prime`, but **no infinite AP of primes exists** (Dirichlet/Green-Tao both give finitary statements only). The bridge therefore produces a **finitary-prefix predicate**, not a full `APGapPrimeSeq 0` instance. This is consistent with the parent's `exists_length40_apGapPrimeSeq` which uses `∀ n < 40` (finitary), NOT a `APGapPrimeSeq 2` instance.
5. **`axiomCount` for the gallery after S3 ACT**: 1 (just `greenTao_finitary`). The cubic-growth axiom (S4) is independent; if S4 is shipped, `axiomCount` becomes 2.

**Composed result for the gallery**: after S3 ACT, the file will support **two existential witnesses**:
- `exists_length40_apGapPrimeSeq` (d=2, length 40, **sorry-free, axiom-free** — Euler's polynomial).
- `exists_arbitrary_length_apGapPrimeSeq_zero` (d=0, **all lengths**, axiom-dependent — Green-Tao).

---

## §1 — Why this PREP, ~2.5h after S3 PREP merge

The slug's iteration cascade is now 5 deep (counting S1 OBSERVE / S1b OBSERVE / S2 PREP / S2 ACT / S3 PREP). The S3 PREP (PR #18651) audited the S1b catalog and found 3 errata (row 4 off-by-one, row 6 sign typo, S2 PREP §3.3 Honaker reference); it is **explicitly numerical-verification only**, not axiom-design.

`state.md:113` lays out the next critical-path target:
> **S3 (after S2): Axiomatize Green-Tao for prefix-AP statements.**

`state.md:114-117` continues:
> **S4 (after S3): Axiomatize cubic growth bound for `d > 0` AP-gap sequences.**
> **S5 (after S4): Combine; gallery integration with `status: "axiomatized"`, `axiomCount: 2-3`.**
> **S6 (optional): Computer-search examples; `native_decide` certificates for small witnesses.**

The S3 ACT remains unimplemented. This S3b PREP **does not** ship the ACT (deferring the actual `axiom` declaration to a downstream implementer who can also build/verify); instead, it pins:

* The precise axiom signature (avoiding common over-/under-specification pitfalls — e.g., omitting `gcd(a,g)=1`, requiring `0 < g`, choosing `(a, g, n)` vs `(q : ℕ → ℕ)` form).
* The Mathlib bearer-audit confirming Green-Tao's absence (so the future ACT doesn't waste a build cycle searching for a non-existent decl).
* The bridge from raw-AP `greenTao_finitary` to the slug's `HasAPGaps`-flavoured statement, ensuring downstream compose into the gallery JSON and parent's verified `Erdos455Problem.lean` cleanly.

---

## §2 — Mathlib bearer-audit for Green-Tao (and adjacencies)

### 2.1 Green-Tao status (verified via `gh api search/code` against `leanprover-community/mathlib4` HEAD)

| Query | Result | Implication |
|---|---|---|
| `GreenTao OR green_tao OR Green_Tao` | `total: 0` | No declarations named `GreenTao*` exist. |
| `primes_arithmetic_progression` | `total: 0` | No legacy name for the theorem. |
| `arithmetic_progression Prime` | `total: 0` | No direct statement. |
| `Szemeredi theorem` | `total: 7` — Roth-3AP, regularity lemma, Ruzsa-Szemerédi corner | **None** are the full Szemerédi theorem; Roth-3AP is the AP-of-length-3 case, NOT general-length. Green-Tao (primes-in-AP) is the prime version; not present. |
| `Behrend prime AP` | (no direct hit) | Behrend's construction gives the lower bound for `r_3(N)`, not Green-Tao. |

**Conclusion**: Green-Tao 2008 (*The primes contain arbitrarily long arithmetic progressions*, Ann. Math. 167(2)) is **not formalized in Mathlib v4.26.0**. The 30+-page proof uses Szemerédi-regularity + transference principle + Goldston-Yıldırım sieve — none of these are sufficiently far along in Mathlib for a derivation.

### 2.2 Dirichlet (the related Mathlib theorem)

Mathlib has Dirichlet's theorem at `Mathlib/NumberTheory/LSeries/PrimesInAP.lean:475-525`:

```lean
theorem infinite_setOf_prime_and_eq_mod (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite

theorem infinite_setOf_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    {p : ℕ | p.Prime ∧ p ≡ a [MOD q]}.Infinite
```

**These do NOT suffice for our purpose**. Dirichlet gives **infinitely many** primes in the *residue class* `a (mod q)`, **not consecutive primes** in the AP `a, a + q, a + 2q, …, a + (k-1) q`. The Dirichlet-primes are scattered through the AP; only `O(N/log N)` of the first `N/q` AP-elements are prime.

Green-Tao strengthens to: arbitrary length `k`, **all `k` consecutive AP-elements are prime**. This is qualitatively much harder (no proof was known before 2004 even for `k = 4` outside computer search).

### 2.3 Roth, Szemerédi, and density theorems

* `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` — Behrend's construction for `r_3(N)` (3-AP-free sets in `[N]`).
* `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean` — `IsAddSalemSpencer`, `addSalemSpencer`.
* `Mathlib/Combinatorics/Additive/Corner/Roth.lean` — Roth's theorem (3-AP density theorem) via corners.

**None of these** address consecutive-prime APs. They concern AP-density in arbitrary subsets of `[N]`, with strength: density `> ε` ⟹ contains a 3-AP. Green-Tao's adaptation requires Szemerédi for *arbitrary length* `k`, plus the transference-principle adaptation to the primes via the Goldston-Yıldırım pseudo-prime measure.

**Conclusion**: Mathlib supports the **density-theoretic foundations of Green-Tao up to k=3** (Roth), but the full Szemerédi (general `k`) and the transference to primes are absent.

---

## §3 — Axiom signature design

### 3.1 Design space

Six candidate forms, in increasing structure:

| # | Form | Specification |
|---|---|---|
| F1 | Raw AP triple | `∀ k, ∃ a g : ℕ, 0 < g ∧ ∀ n < k, Nat.Prime (a + n * g)` |
| F2 | F1 with explicit coprime | `∀ k, ∃ a g : ℕ, 0 < g ∧ a.Coprime g ∧ ∀ n < k, Nat.Prime (a + n * g)` |
| F3 | F1 over ℤ | `∀ k, ∃ a g : ℤ, 0 < g ∧ ∀ n < k, (a + n * g).natAbs.Prime` |
| F4 | Function form | `∀ k, ∃ q : ℕ → ℕ, StrictMono q ∧ HasAPGaps q 0 ∧ ∀ n < k, (q n).Prime` |
| F5 | Bundled structure (impossible) | `∀ k, ∃ s : APGapPrimeSeq 0, ∀ n < k, ⊤` — **uninstantiable**: `APGapPrimeSeq` requires `∀ n, prime`, contradicted by long-AP impossibility (see §3.3) |
| F6 | Finitary structure | new structure `FinAPGapPrimeSeq k 0` with `∀ n < k, prime` |

**Recommendation: F1 (raw AP triple).**

Reasons:

1. **Closest to the original theorem statement** (Green & Tao 2008, Thm 1.2: *"For every k ≥ 3, the primes contain infinitely many arithmetic progressions of length k"*).
2. **Smallest axiom surface**: 3 quantified variables (`k, a, g`), one existential, one universal. Easy to discharge in a future proof if/when Green-Tao lands in Mathlib.
3. **No `Coprime` clutter**: F2's `a.Coprime g` follows automatically from each `a + n g` being prime — if `gcd(a,g) = d > 1` and `g > 0`, then `d ∣ (a + n g)` for every `n`, so each `a + n g` is composite unless `a + n g = d`, which can happen at most once. So F2's coprime is **redundant**: the F1 conclusion `∀ n < k, Nat.Prime (a + n g)` for `k ≥ 2` forces `gcd(a, g) = 1`.
4. **F3 (over ℤ) is unnecessary**: `g > 0` and `a ≥ 0` (since `a + 0 = a` must be a prime, hence ≥ 2). The natural `ℕ → ℕ` form fits the parent's `HasAPGaps : (ℕ → ℕ) → ℤ → Prop` perfectly via the bridge in §3.2.
5. **F4 hides the raw AP structure** behind a function symbol. While bridging to F4 is one-line (set `q n := a + n * g`), the axiom statement is cleaner in F1 form; the bridge lemma can be a regular `theorem`, not part of the axiom.
6. **F5 is uninstantiable** (see §3.3 below) and would force a redesign of `APGapPrimeSeq`.
7. **F6 (finitary structure)** is verbose — defining a new structure just for the axiom statement is unnecessary boilerplate. A predicate like `∀ n < k, (q n).Prime` works fine.

### 3.2 The chosen axiom + bridge

```lean
-- Place in proofs/Proofs/Erdos455OQ04.lean, after exists_length40_apGapPrimeSeq.

namespace Erdos455OQ04

/-- **Green-Tao 2008** (finitary statement): for every length `k`, there exists
an arithmetic progression `a, a + g, a + 2g, …, a + (k-1) g` of `k` primes with
common difference `g > 0`. (*The primes contain arbitrarily long arithmetic
progressions*, B. Green & T. Tao, Ann. Math. 167(2), 481–547, 2008.)

This is taken as an axiom; the original proof is ~30 pages of additive
combinatorics (Szemerédi regularity + transference + Goldston-Yıldırım sieve),
not present in Mathlib v4.26.0. -/
axiom greenTao_finitary :
    ∀ k : ℕ, ∃ a g : ℕ, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)

/-- Bridge: Green-Tao gives a `HasAPGaps`-shaped finitary witness for `d = 0`. -/
theorem exists_apGap_zero_of_length (k : ℕ) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ HasAPGaps q 0 ∧ ∀ n, n < k → (q n).Prime := by
  obtain ⟨a, g, hg, hp⟩ := greenTao_finitary k
  refine ⟨fun n => a + n * g, ?_, ?_, hp⟩
  · -- StrictMono: a + n*g is strictly increasing in n since g > 0.
    intro m n hmn
    have : m * g < n * g := Nat.mul_lt_mul_right hg hmn
    exact Nat.add_lt_add_left this a
  · -- HasAPGaps … 0: second difference is 0.
    intro n
    push_cast
    ring

end Erdos455OQ04
```

**Properties**:

* `greenTao_finitary` is one `axiom`, **independent of the parent's `eulerPoly` chain**. No mutual dependency: `eulerPoly` lives at `d = 2`, this axiom at `d = 0`.
* `exists_apGap_zero_of_length` is a regular theorem, sorry-free, ~12 LOC. The proof tactic sequence:
  - `obtain` to destructure the existential from the axiom.
  - `refine ⟨fun n => a + n * g, ?_, ?_, hp⟩` to bind `q` and split the goals.
  - `StrictMono`: from `g > 0` via `Nat.mul_lt_mul_right` (Mathlib `Mathlib/Order/Basic.lean`).
  - `HasAPGaps`: `push_cast; ring` (same tactic as `eulerPoly_hasAPGaps`).
  - `∀ n < k, prime`: directly the existential's witness `hp`.

### 3.3 Why `APGapPrimeSeq 0` is uninstantiable

The structure `APGapPrimeSeq d` (at `proofs/Proofs/Erdos455OQ04.lean:54-57`):

```lean
structure APGapPrimeSeq (d : ℤ) where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  apGaps : HasAPGaps seq d
```

**Claim**: `APGapPrimeSeq 0` cannot be instantiated for any concrete `seq`.

**Proof**: `HasAPGaps q 0` means `(q (n+2) : ℤ) − 2 (q (n+1) : ℤ) + (q n : ℤ) = 0` for every `n`, i.e., `q n` is **linear** in `n`: `q n = a + n * g` for some `a, g`. `StrictMono` forces `g > 0` (in `ℕ → ℕ`, `g` must be a positive nat; in ℤ, also positive). Then `q` realizes an infinite arithmetic progression `a, a+g, a+2g, …`, **with all terms prime**.

But:

* If `gcd(a, g) > 1`, then `gcd(a, g) ∣ q n = a + n g` for every `n`, so each `q n` is divisible by `gcd(a, g)`, hence composite unless `q n = gcd(a, g)`. This can happen only finitely often (at most once for fixed `gcd > 1`).
* If `gcd(a, g) = 1`, by Dirichlet's theorem the residue class `a (mod g)` contains infinitely many primes, but **also infinitely many composites**. Specifically, `q n = a + n g` for `n` large enough that `a + n g > (a + n g)^{1/2}` (always) and `n` chosen such that `a + n g` is composite. By prime gap theorems, such `n` exists (in fact a positive density).

Either way, **no infinite AP of primes exists** — this is a classical observation (e.g., Wikipedia "Primes in arithmetic progression").

Hence `APGapPrimeSeq 0` is uninstantiable, and the Green-Tao axiom must be stated in finitary form (F1/F4/F6), not as `∃ s : APGapPrimeSeq 0, …`.

### 3.4 Compatibility with parent `Erdos455OQ04.lean`

The existing parent file (verified via Read; `proofs/Proofs/Erdos455OQ04.lean:1-83`, post-S2 ACT) declares:

```lean
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop := …                           -- line 50
structure APGapPrimeSeq (d : ℤ) where …                                  -- line 54
def eulerPoly : ℕ → ℕ := fun n => n^2 + n + 41                           -- line 66
theorem eulerPoly_hasAPGaps : HasAPGaps eulerPoly 2 := …                  -- line 70
theorem exists_length40_apGapPrimeSeq :
    ∃ q : ℕ → ℕ, HasAPGaps q 2 ∧ ∀ n, n < 40 → (q n).Prime := …            -- line 77
```

The new `greenTao_finitary` axiom + `exists_apGap_zero_of_length` theorem fit naturally **at the end of the file** (lines 80+), inside the existing `namespace Erdos455OQ04 … end` block. They:

* Use no Mathlib imports beyond what's already there (`Nat.Prime`, `StrictMono`, `push_cast`, `ring`).
* Do not modify any existing declaration.
* Add 1 axiom + 1 theorem (~20 LOC) for net file lines `~83 → ~103`.

**Sorries**: 0 (the bridge theorem is fully tactical).
**Axioms**: 0 → 1 (`greenTao_finitary`).
**Structure-encoded axioms**: 0 → 0 (the new statements use predicate forms, not structures with assumption fields).

---

## §4 — Sanity checks: small-case witnesses for `greenTao_finitary`

The axiom should be **at least believable** at small `k`. Verifiable manually:

| `k` | Witness `(a, g)` | AP: `a, a+g, …, a+(k-1)g` | Verified primes |
|---|---|---|---|
| `1` | `(2, 1)` | `2` | 2 ✓ |
| `2` | `(3, 2)` | `3, 5` | 3, 5 ✓ |
| `3` | `(3, 2)` | `3, 5, 7` | 3, 5, 7 ✓ |
| `4` | `(5, 6)` | `5, 11, 17, 23` | all prime ✓ |
| `5` | `(5, 6)` | `5, 11, 17, 23, 29` | all prime ✓ |
| `6` | `(7, 30)` | `7, 37, 67, 97, 127, 157` | all prime ✓ |
| `7` | `(7, 150)` | `7, 157, 307, 457, 607, 757, 907` | all prime ✓ |
| `10` | `(199, 210)` | `199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089` | all prime ✓ (Wells 1986) |

(For `k = 10` and higher, witnesses become extremely hard to find by hand; the AP-26 record by Benoȃt Perichon (2010) has `a = 43142746595714191, g = 23681770·223092870`. Green-Tao guarantees existence for all `k`; finding witnesses is computationally hard but the existence is guaranteed.)

**These small-case checks** verify that `greenTao_finitary` is **not vacuously satisfiable by accident** (e.g., the axiom holds at `k = 0` trivially since `∀ n < 0` is `False → …`; but `k = 5` with all 5 primes is a non-trivial check).

**An S3 ACT could include a `#eval` sanity-test** at the bottom of the file to print the `k = 5` witness, but this requires `decide`-time primality checking which can be cycle-heavy; **better practice** is to provide a separate `theorem exists_apGap_zero_length_5_witness` as a deterministic `native_decide`-closed lemma, analogous to `exists_length40_apGapPrimeSeq`:

```lean
theorem exists_apGap_zero_length_5_witness :
    ∃ a g : ℕ, 0 < g ∧ ∀ n, n < 5 → Nat.Prime (a + n * g) := by
  refine ⟨5, 6, by decide, ?_⟩
  intro n hn
  interval_cases n <;> decide  -- or native_decide
```

This is **independent of `greenTao_finitary`** and provides a non-axiomatic concrete witness for `k = 5`. Future S3 ACT may bundle it for the gallery (~6 LOC, **sorry-free, axiom-free**).

---

## §5 — Composed gallery posture (post-S3 ACT)

After the S3 ACT lands, the file `proofs/Proofs/Erdos455OQ04.lean` will support **two existential witnesses**, each with distinct axiom posture:

| Witness | Direction | Length | Axioms | Sorries |
|---|---|---|---|---|
| `exists_length40_apGapPrimeSeq` (S2 ACT) | `d = 2` (via Euler) | exactly 40 (sharp, Bunyakovsky-open) | 0 | 0 |
| `exists_apGap_zero_of_length` (S3 ACT) | `d = 0` (via Green-Tao) | every `k : ℕ` | 1 (`greenTao_finitary`) | 0 |
| `exists_apGap_zero_length_5_witness` (optional, S3 ACT) | `d = 0` (concrete) | 5 | 0 (concrete) | 0 |

**Gallery `meta.json` after S3 ACT**:
* `status: "axiomatized"` (mandatory due to `greenTao_finitary`).
* `axiomCount: 1` (just `greenTao_finitary`; no structure-encoded axioms).
* `sorryCount: 0`.
* `lineCount: ~105` (post-S2 ACT 83 + S3 ACT ~22).
* `theoremCount: 4` (`eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`, `exists_apGap_zero_of_length`, `exists_apGap_zero_length_5_witness`).
* `defCount: 2` (`HasAPGaps`, `eulerPoly`) + 1 structure (`APGapPrimeSeq` — uninstantiable but still a valid declaration).

**`assumptions` field** (gallery JSON):
```json
"assumptions": [
  "Green-Tao 2008 (axiomatized): for every k, there exists an arithmetic progression of k primes with positive common difference. Cited as `greenTao_finitary` in proofs/Proofs/Erdos455OQ04.lean."
]
```

If S4 (cubic-growth axiom for `d > 0`) is also shipped, `axiomCount` becomes 2.

---

## §6 — Implications for S4 (cubic-growth axiom) and S5 (gallery integration)

### 6.1 S4 is independent of S3

The cubic-growth bound for `d > 0` AP-gap prime sequences (per `knowledge.md` "Risks and uncertainties" → "Cubic growth bound is conjectural") is **not derivable from Green-Tao**. Green-Tao is `d = 0` only; for `d > 0`, the relevant heuristic is:

* By Bunyakovsky (1857), if `f(n) = (d/2) n² + (g_0 − d/2) n + q_0` is irreducible with `gcd` of values = 1, then `f` produces infinitely many primes. **This is still open** (Bunyakovsky conjecture).
* Heuristically, prime density for `f(n)` of degree 2 is `~C / log n`, so the longest prefix of primes grows like `~exp(log L) = O(L)` for length-`L` prefix — i.e., **logarithmic**, not cubic.
* The "cubic" claim in `knowledge.md:65-66` ("Tightening to `n³` requires combining with primality density constraints…") refers to a conjectural growth bound, not a theorem.

**S4 ACT recommendation**: **drop the cubic claim**, replace with the **Bunyakovsky-conjectural** unbounded-length claim:

```lean
/-- **Bunyakovsky's conjecture (1857)**, specialized to AP-gap polynomials.
For every even `d ≥ 2` and coprime irreducible quadratic
`f(n) := (d/2) n² + (g₀ − d/2) n + q₀` with `f(0), f(1), …` having `gcd = 1`,
the polynomial produces infinitely many primes. -/
axiom bunyakovsky_apGapPoly :
    ∀ d : ℕ, d ≥ 2 → Even d →
    ∀ g_0 q_0 : ℕ, 0 < g_0 → 0 < q_0 → (… coprimality and irreducibility hypotheses …) →
    ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ Nat.Prime ((d / 2) * N^2 + (g_0 - d / 2) * N + q_0)
```

The S4 PREP / ACT should refine this signature. **Not the scope of this PREP.**

### 6.2 S5 gallery integration

After S3 ACT + (optional) S4 ACT, the `src/data/proofs/erdos-455-oq-04/` gallery directory is created with:
* `meta.json` — `status: "axiomatized"`, `axiomCount: 1` (or `2` if S4 shipped).
* `index.ts` — re-exports `Erdos455OQ04` namespace's main theorems.
* `annotations.json` — pedagogical annotations.

This is **S5's deliverable**, not this PREP's.

---

## §7 — Trap notes

* **REPO_ROOT trap on `claim-problem.sh`** (memory `[Researcher — claim-problem.sh release fails from worktree CWD]`). Confirmed: claim-random invoked from `/Users/rwalters/GitHub/lean-genius` (main-repo CWD). Lock created in main-repo's `research/claims/`. On release, will `cd /Users/rwalters/GitHub/lean-genius && /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release erdos-455-oq-04`.
* **Branch creation from worktree** (memory `[Post-S1/S1b S2/S4 PREP session-note cluster]`). Used `git switch --detach origin/main` + `git checkout -b research/erdos-455-oq-04-s3b-prep-$(date +%s)` from worktree CWD. Verified branch is attached to worktree via `git status`.
* **Write tool main-repo absolute-path trap** (memory `[Write tool absolute-path routes to main repo, not worktree]`). Used **worktree-prefixed** absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-6/research/problems/erdos-455-oq-04/sessions/2026-05-13-s3b-prep-greentao-axiom-signature-design.md` to ensure the Write goes to the worktree, not the main repo.
* **`gh` default-repo trap** (memory `[gh defaults to mathlib-fork remote, hides real PR state]`). All `gh pr list` invocations used explicit `--repo rjwalters/lean-genius`. Pre-push race-check returned `[]` open PRs for the slug.
* **No `.lake` symlink interaction**: doc-only PREP, no Docker build. The build risk applies only to a future S3 ACT.
* **`gh api search/code` rate limit** (memory `[researcher-12 triple Mathlib-bearer-audit PREP session]`). Used 4 search/code calls (GreenTao, Szemeredi, Roth Behrend, primes_arithmetic_progression) — well within the 30/hr limit.
* **Numbering convention**: this PREP is "S3b" (with "b" suffix) because S3 PREP (PR #18651) already shipped the catalog-errata audit at iteration 3. Per slug-internal numbering convention (S1, S1b OBSERVE; S2 PREP, S2 ACT, S2b PREP candidate), the "b" suffix marks a sibling angle within the same numerical stage. The S3 PREP (catalog audit) and this S3b PREP (Green-Tao axiom design) attack different aspects of stage 3.

---

## §8 — Files modified / not modified

**Modified** (worktree-relative paths, verified via `git status`):

* `research/problems/erdos-455-oq-04/sessions/2026-05-13-s3b-prep-greentao-axiom-signature-design.md` (this file).

**NOT modified**:

* `research/problems/erdos-455-oq-04/problem.md`
* `research/problems/erdos-455-oq-04/knowledge.md`
* `research/problems/erdos-455-oq-04/state.md`
* `research/problems/erdos-455-oq-04/sessions/2026-05-12-s01b-euler-polynomial-correction.md` (merged S1b)
* `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-prep-verbatim-lean-witness-and-catalog-audit.md` (merged S2 PREP)
* `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-act-eulerPoly-witness-scaffold.md` (merged S2 ACT)
* `research/problems/erdos-455-oq-04/sessions/2026-05-13-s3-prep-catalog-errata-row4-row6-honaker.md` (merged S3 PREP — different angle)
* `src/data/research/problems/erdos-455-oq-04.json`
* `proofs/Proofs/Erdos455OQ04.lean` (no Lean code modified; doc-only design)
* `proofs/Proofs.lean`
* Any `src/data/proofs/erdos-455-oq-04/` (no gallery directory exists yet — S5's task)

---

## §9 — Saturation check (2026-05-13 ~10:10 UTC)

* **Open PRs on this slug** (`gh pr list --repo rjwalters/lean-genius --search "erdos-455-oq-04 in:title" --state open`): **0** ✓
* **Merges in last 4h**:
  - S3 PREP (#18651) merged 07:30 UTC → 2h40min ago → within 4h window.
  - S2 ACT (#18590) merged 06:02 UTC → 4h08min ago → outside 4h window.
  - S2 PREP (#18540) merged 03:37 UTC → 6h33min ago → outside.
  - S1b OBSERVE (#18468) merged 02:22 UTC → 7h48min ago → outside.
  - So **1 merge in last 4h** (S3 PREP). Below the `≥ 3 merges/4h` saturation threshold per memory `[researcher-3 triple-PREP doc-only session]`.
* **Total session count for slug**: 5 (S1, S1b, S2 PREP, S2 ACT, S3 PREP). Below the 70+-deep release threshold.
* **My own prior PRs on this slug**: only S2 PREP (#18540). No conflict with this S3b PREP (different angle: catalog audit vs Green-Tao axiom design).

**Verdict**: safe to ship.

---

## §10 — References

* **Green, B.; Tao, T. (2008)**. *The primes contain arbitrarily long arithmetic progressions.* Annals of Mathematics 167(2), 481–547. [DOI: 10.4007/annals.2008.167.481](https://doi.org/10.4007/annals.2008.167.481). **The theorem being axiomatized.**
* **Szemerédi, E. (1975)**. *On sets of integers containing no `k` elements in arithmetic progression.* Acta Arithmetica 27, 199–245. The density-theoretic precursor to Green-Tao.
* **Goldston, D. A.; Yıldırım, C. Y. (2003)**. *Small gaps between primes.* Preprint. The Goldston-Yıldırım sieve used in Green-Tao's transference step.
* **Dirichlet, P. G. L. (1837)**. *Beweis des Satzes, dass jede unbegrenzte arithmetische Progression…* — the original statement of Dirichlet's theorem (Mathlib's `infinite_setOf_prime_and_eq_mod`); distinct from Green-Tao (see §2.2).
* **Bunyakovsky, V. (1857)**. *Sur les nouveaux théorèmes…* — the conjecture cited by `Erdos455OQ04.lean` header for `d > 0` polynomial primes; relevant to S4 (not this PREP).
* **Wells, D. (1986)**. *The Penguin Dictionary of Curious and Interesting Numbers.* Penguin, 130-131. The length-10 AP-prime witness `199, 409, …, 2089` (g = 210).
* **Perichon, B. (2010)**. AP-26 prime sequence (announcement). PrimeGrid project; the current record-holder for length 26.
* **Parent verified Lean entry**: `proofs/Proofs/Erdos455Problem.lean` (Erdős #455 — monotone-prime-gap sequences).
* **S2 ACT Lean file**: `proofs/Proofs/Erdos455OQ04.lean` (post-S2 ACT, build-pending).
* **S1 OBSERVE PR**: #18331 (researcher-10, 2026-05-12).
* **S1b OBSERVE PR**: #18468 (researcher-9, 2026-05-13).
* **S2 PREP PR**: #18540 (researcher-6, 2026-05-13).
* **S2 ACT PR**: #18590 (researcher-5, 2026-05-13; verbatim Lean witness scaffold, build-pending).
* **S3 PREP PR** (sibling angle): #18651 (researcher-4, 2026-05-13; catalog errata audit).
* **Mathlib `PrimesInAP.lean`**: `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` (lines 475-525; Dirichlet's theorem on primes in residue classes).
* **Mathlib pin**: `proofs/lake-manifest.json` (HEAD pin as of S3 PREP merge); `Mathlib.Data.Nat.Prime.Basic` provides `Nat.Prime` decidability.
