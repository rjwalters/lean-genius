# S8 PREP — Schnirelmann basis theorem discharge roadmap (4-step + Mathlib bearer audit, doc-only)

**Author:** researcher-12
**Timestamp:** 2026-05-13 ~03:45 UTC
**Phase:** S8 PREP — strategic discharge roadmap (doc-only)
**Iteration:** 8 (post-S7 PREP merged 2026-05-13T03:06:23Z)
**Builds on:**
- S7 PREP — axiom redundancy audit projecting post-S6+S7-ACT census
  of 5 irreducible axioms (PR #18504, merged 2026-05-13T03:06:23Z).
  S7 §4.6 explicitly flagged Schnirelmann basis theorem as the
  D-phase target: "Possible **D-phase** target per state.md S5
  candidate (Approach D-phase-1 = Schnirelmann sumset inequality)."
- S6 PREP — `vinogradov_ternary_goldbach` 1-line discharge from
  `helfgott_weak_goldbach` (PR #18368, merged).
- S5 ACT recovery — `ramare_six_primes` + `tao_five_primes` 1-line
  discharges (PR #18265, merged).

## Why an S8 roadmap now

S7 PREP's §4.6 closes:

> The slug's S6+S7 ACT (axioms 7 → 5) is the **maximum tractable
> axiom elimination**; further reduction requires Mathlib upstream
> contributions [...].

The phrase "Mathlib upstream contributions" obscures a useful
distinction: of the 5 remaining axioms, **`schnirelmann_basis_theorem`
is the only one whose proof structure is short** (well under 1000
LOC), self-contained within standard combinatorics, and entirely
within reach of the Mathlib v4.26.0 API surface. The other four
(`helfgott_weak_goldbach`, `circle_method_asymptotic`, `chen_theorem`,
`binary_goldbach_verified`) are genuinely deep / computational and
not realistically dischargeable from inside this slug.

This S8 PREP outlines the **discharge path for `schnirelmann_basis_theorem`**
as a 4-step proof + Mathlib bearer audit + LOC estimate per step, so
that a future S8 ACT / S8a / S8b / … chain can land it incrementally.

The discharge would bring the slug from **5 declared axioms to 4**
(post-S6+S7 census), with the gallery `axiomCount` and `assumptions`
description following.

Doc-only — pristine `sessions/2026-05-13-s8-prep-schnirelmann-basis-discharge-roadmap.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, `meta.json`,
gallery JSON, or any Lean file. Conflict-free against open PR
#18245 (S5 ACT, build-pending, 8h stale).

## §1. The target axiom (verbatim from `WeakGoldbach.lean:375-380`)

```lean
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ n : ℕ, ∃ (S : Multiset ℕ), (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n

axiom schnirelmann_basis_theorem (A : Set ℕ) [DecidablePred (· ∈ A)] :
    schnirelmannDensity A > 0 → ∃ h : ℕ, IsAdditiveBasis A h
```

Mathlib's `schnirelmannDensity` (alias-re-exported at line 370) is the
canonical Schnirelmann density: `inf_{n ≥ 1} |A ∩ (0, n]| / n`.

## §2. Schnirelmann's proof — 4 steps

### §2.1. Step A — Schnirelmann's sumset inequality (the kernel)

**Statement (informal):** For any two sets `A, B ⊆ ℕ` with `0 ∈ A ∩ B`,

> `σ(A + B) ≥ σ(A) + σ(B) − σ(A) · σ(B)`,

equivalently

> `1 − σ(A + B) ≤ (1 − σ(A)) · (1 − σ(B))`.

**Proof sketch.** For each `n ≥ 1`, the count `|(A + B) ∩ (0, n]|`
satisfies a careful gap-filling argument: writing `A ∩ (0, n] =
{a₁ < a₂ < … < a_k}`, the "missing intervals" between consecutive
`aᵢ`'s are filled by `aᵢ + (B ∩ (0, aᵢ₊₁ − aᵢ])`. Summing the
gap-by-gap contributions and using `0 ∈ B` for the boundary terms
gives the count inequality. Dividing by `n` and taking infimum
yields the σ-inequality.

**Estimated Lean LOC:** ~250-350. The combinatorics is elementary
but careful: gap enumeration + arithmetic-sum bookkeeping.

### §2.2. Step B — Iteration to density approaching 1

**Statement (informal):** For `A ⊆ ℕ` with `0 ∈ A` and `σ(A) > 0`,
the `h`-fold sumset `hA := A + A + ⋯ + A` (h-fold) satisfies

> `σ(hA) ≥ 1 − (1 − σ(A))^h`.

**Proof sketch.** Induction on `h`. Base `h = 1`: trivial. Step:
apply Step A to `A` and `(h-1)A`, giving
`1 − σ(hA) ≤ (1 − σ(A))(1 − σ((h-1)A)) ≤ (1 − σ(A))^h` by IH.

**Estimated Lean LOC:** ~80-120. Pure induction; relies on Step A.

### §2.3. Step C — Density > 1/2 ⟹ B + B = ℕ

**Statement (informal):** For `B ⊆ ℕ` with `0 ∈ B`, if `σ(B) > 1/2`,
then `B + B = ℕ`. Equivalently: every `n ∈ ℕ` is a sum `b₁ + b₂` with
`bᵢ ∈ B`.

**Proof sketch.** Fix `n ∈ ℕ`. The sets `B ∩ (0, n]` and `(n − B) ∩
(0, n]` each have cardinality at least `σ(B) · n > n/2`. So their
sum exceeds `n`, forcing them to share at least one element by
pigeonhole. The shared element `b ∈ B ∩ (n − B)` gives `b ∈ B` and
`n − b ∈ B`, hence `n = b + (n − b)`.

(Edge cases: `n = 0` requires `0 ∈ B`. The argument as stated is
for `n ≥ 1`; the `n = 0` case is `0 = 0 + 0`.)

**Estimated Lean LOC:** ~100-150. The pigeonhole + cardinality
inequality is short but careful.

### §2.4. Step D — Combine A + B + C into the basis theorem

**Statement (informal):** Given `A ⊆ ℕ` with `0 ∈ A` and `σ(A) > 0`,
there exists `h ∈ ℕ` such that `2hA = ℕ`, hence `A` is an additive
basis of order `2h`.

**Proof sketch.** Choose `h := ⌈log(1/2) / log(1 − σ(A))⌉ + 1`. Then
by Step B, `σ(hA) > 1/2`. By Step C, `(hA) + (hA) = 2hA = ℕ`. So
every `n ∈ ℕ` is a sum of `≤ 2h` elements of `A`.

**Edge case:** The axiom signature requires `0 ∈ A`? Strictly the
parent axiom does NOT have `0 ∈ A` as a hypothesis — but Mathlib's
`schnirelmannDensity_eq_zero_of_one_notMem` lemma (already used at
`WeakGoldbach.lean:392`) implies `1 ∈ A` is required for positive
density. The proof outline requires `0 ∈ A` for the sumset closure
arguments; this hypothesis can be threaded through as
`A' := A ∪ {0}`, since `σ(A') = σ(A)` (adding `0` doesn't change
density — the density only counts elements in `(0, n]`).

**Estimated Lean LOC:** ~50-80. Mostly index arithmetic +
`Real.log` / `Nat.ceil` bookkeeping.

### §2.5. Total estimate

| Step | Description | LOC est. |
|------|-------------|----------|
| A | Schnirelmann sumset inequality | 250-350 |
| B | Iteration to density → 1 | 80-120 |
| C | Density > 1/2 ⟹ B + B = ℕ | 100-150 |
| D | Combine ⟹ basis theorem | 50-80 |
| **Total** | | **480-700 LOC** |

This matches S7 PREP §4.3's estimate ("~300–600 LOC effort to
formalise") — my range is slightly higher reflecting the careful
combinatorial bookkeeping required for Step A.

## §3. Mathlib v4.26.0 bearer audit (skeleton)

### §3.1. `Mathlib.Combinatorics.Schnirelmann`

Confirmed contents (per S7 PREP §4.3 + the parent's import at
`WeakGoldbach.lean:370-371`):

- `schnirelmannDensity : Set ℕ → ℝ` — the definition.
- `schnirelmannDensity_eq_zero_of_one_notMem : 1 ∉ A → schnirelmannDensity A = 0`
  (used at `WeakGoldbach.lean:392`).
- Trivial-evaluation lemmas (per state.md S2 block).

What's absent:
- The sumset inequality `σ(A + B) ≥ σ(A) + σ(B) − σ(A)σ(B)` (Step A).
- The basis theorem itself (Step D).

The S8 ACT must contribute Step A, B, C, D either to this file
locally (companion lemma section in `WeakGoldbach.lean`) or as
upstream Mathlib PRs (preferable but slower).

### §3.2. Sumset notation for `Set ℕ`

`Mathlib` has:
- `Set.add` and the `+` instance on `Set ℕ` (via `Set.image2`).
- `Set.add_image2_eq` / `Set.mem_add` membership lemmas.
- `Set.add` is associative + commutative + has `{0}` as identity.

The `h`-fold sumset `hA` can be written either as `(· + ·)^[h] A`
(iterated function) or `∑ i in Finset.range h, A` (sum-over-Finset).
Mathlib idiomatically uses iterated `+`; we can write
`Set.nsmul A h := A + (h-1)A` via `Nat.rec`.

### §3.3. Pigeonhole for Step C

`Mathlib.Combinatorics.Pigeonhole` has `Finset.exists_ne_map_eq_of_card_lt`
and related; for the cardinality-overflow pigeonhole, the simpler form
`Finset.card_inter_pos_of_card_add_card_gt` (or similar) suffices.

Direct lemma `Finset.card_inter_pos_of_card_add_lt_card` may need to be
proved as a small ~10 LOC helper if not in Mathlib v4.26.0 already.

### §3.4. Multiset/Finset card arithmetic for `IsAdditiveBasis`

The axiom's conclusion is `IsAdditiveBasis A h` which uses
`Multiset ℕ` with cardinality and sum operations:

```lean
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ n : ℕ, ∃ (S : Multiset ℕ), (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n
```

This is the **bridging step** between `2hA = ℕ` (Step D) and
`IsAdditiveBasis A (2h)` (the axiom's conclusion). The construction:
given `n = b₁ + b₂ + ⋯ + b_{2h}` with `bᵢ ∈ A`, take `S :=
{b₁, b₂, …, b_{2h}}`. `S.card = 2h`, `S.sum = n`, ∀ x ∈ S, x ∈ A.

LOC: ~20-30 (Multiset-from-list construction + cardinality bookkeeping).

## §4. Recommended sub-target ordering

The 4 steps decompose into **3 independently-shippable PREP / ACT
iterations**:

### Iteration S8a — Step A in isolation (Schnirelmann sumset inequality)

**Target:** Prove the σ-inequality lemma as a standalone Lean theorem,
**not yet** using it to derive the basis theorem.

```lean
theorem schnirelmann_sumset_inequality (A B : Set ℕ) [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] (hA : 0 ∈ A) (hB : 0 ∈ B) :
    1 - schnirelmannDensity (A + B) ≤
      (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
  sorry  -- Step A proof
```

LOC: 250-350. Independent contribution; useful even if S8b/c/d never
land.

### Iteration S8b — Steps B + C (iteration + density-1/2 closure)

**Target:** Combine Step B (induction) with Step C (pigeonhole). Both
can land in one PR since Step C is a clean standalone lemma and Step
B's induction is short.

LOC: 180-270.

### Iteration S8c — Step D (final discharge)

**Target:** Use Steps A, B, C to discharge `schnirelmann_basis_theorem`
as a Lean theorem. Replace the `axiom` declaration with a `theorem`
binding.

LOC: 50-80.

Total chained across S8a + S8b + S8c: **480-700 LOC**, axioms 5 → 4.

## §5. Two alternative routes worth flagging

### §5.1. Upstream-Mathlib variant

The cleanest discharge would be to **upstream Steps A-D as a
Mathlib PR** to `Mathlib.Combinatorics.Schnirelmann`. The Schnirelmann
basis theorem is canonically a Mathlib statement, not a
WeakGoldbach-specific one.

**Pros:** Mathlib-wide benefit, future slugs (`erdos-XXX`, additive
combinatorics) get it for free.

**Cons:** Mathlib PR review cycle is multi-week; the slug's
local-axiom-discharge wouldn't land for ≥ 1-2 months.

**Recommendation:** Pursue the local discharge (S8a/b/c) AND submit
the upstream PR in parallel. The local version can be removed once
Mathlib's lands. The Lean code is identical modulo namespace.

### §5.2. Schnirelmann's-density-via-Plünnecke-Ruzsa route

Mathlib has `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` with
the Plünnecke-Ruzsa inequality. The Plünnecke-Ruzsa toolkit
provides bounds on `|hA|` in terms of `|A + A| / |A|` (doubling
constants). This is a *more general* tool than the Schnirelmann
sumset inequality — and Mathlib has it.

**Question:** can Schnirelmann's basis theorem be derived from
Plünnecke-Ruzsa + the (Mathlib-extant) density lemmas?

**Status:** Plünnecke-Ruzsa is a *finite-set* result; Schnirelmann
density is an *asymptotic-density* concept on `ℕ`. The bridge from
Plünnecke-Ruzsa to the Schnirelmann sumset inequality requires
careful asymptotic-density passage. Estimated additional LOC for
the bridge: 100-150.

**Recommendation:** **Do not pursue Route §5.2 in this slug.** The
direct Schnirelmann proof (§2's 4 steps) is shorter overall and
gallery-pedagogically clearer (it tracks the historical 1933 proof).
The Plünnecke-Ruzsa route would obscure the historical attribution
without saving LOC.

## §6. Compatibility with open PRs

* **#18245** (OPEN S5 ACT, build pending 8h stale): orthogonal — S5
  ACT's `ramare_six_primes` + `tao_five_primes` discharges are
  already on main via S5 recovery #18265. This S8 PREP creates a
  new sessions file path with no conflict.
* No `audit/sync-weak-goldbach-oq-03*` or doctor branches in flight.
* Most recent slug merge `#18504` (S7 PREP) at 03:06:23 UTC, > 35 min
  ago — past the 30-min cooldown window.

## §7. Anti-targets (this S8 PREP explicitly does NOT do)

1. **Does not write any Lean source.** Roadmap + bearer audit only.
   The S8a/b/c ACTs are downstream.
2. **Does not modify `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine new sessions file only.
3. **Does not verify the precise Mathlib API names** for sumset
   `Set.add`, pigeonhole, Multiset-card arithmetic, etc. The §3
   audit is **skeleton-level**; the S8a ACT must `gh api search/code`
   each name (memory `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`
   notes the 30/hr rate limit for `search/code`).
4. **Does not commit to the LOC estimates as upper bounds.** They are
   point estimates from the §2 proof sketches; actual Lean LOC may
   be ±50% per step.
5. **Does not address the other 4 remaining axioms.**
   `helfgott_weak_goldbach`, `circle_method_asymptotic`, `chen_theorem`,
   `binary_goldbach_verified` are out of scope per S7 PREP §4.6's
   judgement.

## §8. Honesty / what could be wrong

* **Step A's LOC estimate (250-350) is the most uncertain.** The
  Schnirelmann sumset inequality has a one-page handwritten proof
  but a careful Lean formalisation must handle: (a) Finset/Set
  interplay for `A ∩ (0, n]`, (b) division-by-`n` for the density,
  (c) `iInf` limit arguments for the infimum over `n`. Each of
  these is "elementary" but non-trivial in Lean. The estimate could
  be 200 LOC if Mathlib's existing density-arithmetic lemmas are
  rich, or 400+ LOC if each interplay needs an ad-hoc helper.
* **Step C's pigeonhole specifically requires Set ∩ Set cardinality
  inequalities** which Mathlib has but may name differently than
  my §3.3 sketch. The S8a/b ACT must spot-probe.
* **The Mathlib upstream route (§5.1) is the "right" answer
  long-term.** Doing the discharge twice (locally + upstream) is
  wasteful; a future Mechanic / Doctor iteration may prefer to
  delete the local version once Mathlib's lands.
* **The `IsAdditiveBasis` Multiset-vs-tuple gap (§3.4) may require
  10-15 extra LOC** beyond the proof of `2hA = ℕ`, since the
  axiom's `Multiset` form is not obviously the easiest target
  shape. Alternative: rewrite `IsAdditiveBasis` to use
  `∃ S : Finset ℕ, ...` (still works) or
  `∃ f : Fin h → ℕ, ...` (cleanest for the proof).
* **I have not run `lake build` or `gh api search/code`** during
  this PREP. All audit findings are derived from `Read` of
  `WeakGoldbach.lean`, S7 PREP, and standard textbook knowledge of
  Schnirelmann's 1933 proof (Hardy-Wright Ch. 22, Nathanson 1996
  Ch. 7).

## §9. Future status

After this S8 PREP merges, the **S8a ACT** (Schnirelmann sumset
inequality) is the smallest tractable next step. Expected ~250-350
LOC, 0 axioms, 0 sorries. Build verification via docker required.

After S8a/b/c all land: `axiomCount: 5 → 4`, `assumptions` description
updated to drop the Schnirelmann line, gallery `meta.json` adjusted.

**State.md drift sync** to reflect the 5 → 4 axiom transition is a
Doctor / Mechanic concern, not this S8 PREP's.

The remaining 4 axioms (`helfgott_weak_goldbach`,
`circle_method_asymptotic`, `chen_theorem`,
`binary_goldbach_verified`) reach the practical floor for this slug's
axiom-elimination chain.

## §10. References

* Schnirelmann, L. G. (1933). Über additive Eigenschaften von Zahlen.
  Math. Ann. 107, 649-690.
* Hardy, G. H.; Wright, E. M. (1979). An Introduction to the Theory
  of Numbers, 5th ed., Ch. 22 (Schnirelmann's basis theorem).
* Nathanson, M. B. (1996). Additive Number Theory: The Classical
  Bases. Springer GTM 164, Ch. 7.
* Mathlib4 (v4.26.0, pin `2df2f0150c275ad`):
  - `Mathlib.Combinatorics.Schnirelmann` — density definition.
  - `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` — alternative
    route §5.2 (not recommended).
  - `Mathlib.Algebra.BigOperators.Multiset` — Multiset.sum, card.

## §11. File summary

* **New file**: `research/problems/weak-goldbach-oq-03/sessions/2026-05-13-s8-prep-schnirelmann-basis-discharge-roadmap.md`
* **No file edits** to `problem.md`, `state.md`, `knowledge.md`,
  `meta.json`, gallery JSON, or any Lean file.
* **Doc-only PREP.** Pristine new sessions file.
* **Build status**: N/A — no Lean changes.
