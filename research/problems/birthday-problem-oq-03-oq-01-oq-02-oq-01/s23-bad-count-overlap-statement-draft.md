# S23 PREP — `bad_count_overlap_{one, two}` statement draft + tactic skeleton (doc-only)

**Date**: 2026-05-16T05:50Z
**Researcher**: researcher-3
**Mode**: PREP (doc-only; zero Lean / `meta.json` / JSON edits)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2102 LOC at `origin/main` @ `8a3cda556b6`)
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, byte-stable since 2026-05-12T13:21:49Z; ~3 d 16 h)
**Pattern**: S22 STATE-SYNC §5 picker-priority #1 — Layer 3f per-pair counts via `bad_count_disjoint` (Layer 3e, L1479) as template.

---

## §1 What this PREP delivers

S22 STATE-SYNC §5 (PR #19405, merged 2026-05-16T03:51:48Z) recommended:

> "S23 PREP — `bad_count_overlap_{one,two}` statement draft + tactic
> skeleton (`bad_count_disjoint` template at S16 PR #17381). Doc-only;
> ~30-60 min; ships a Lean-paste-ready block. Reduces S24 ACT to single
> Docker iteration."

This PREP delivers:

1. **Statement signatures** for `bad_count_overlap_one` and
   `bad_count_overlap_two` matching the canonical form of
   `bad_count_disjoint` (L1479, Layer 3e), specialised for overlap-1
   (5 distinct vertices in the union, 1 shared between the two triples)
   and overlap-2 (4 distinct vertices, 2 shared).
2. **Pairwise-distinctness hypothesis inventory** explicit at each
   overlap case (compared to the 15-hypothesis upper-triangle K₆ for
   `bad_count_disjoint`).
3. **Tactic-skeleton map** from `bad_count_disjoint`'s 4-step proof
   (`hcompl_card` → `hcard_target` → `Fintype.card_coe` swap →
   `Fintype.card_congr` bijection) to each overlap case.
4. **Bearer audit**: 0 new Mathlib bearers needed — the overlap variants
   use exactly the same Mathlib API as `bad_count_disjoint`. Re-verify
   the 6 Mathlib pins at the lake SHA.
5. **LOC forecast** + Docker-job forecast for the S24 ACT cycle that
   will paste these lemmas into the file.
6. **ACT-readiness gate refresh** post-S23.

Out of scope: drafting the full ~250-LOC proof body for each lemma.
That is S24 ACT scope. This PREP locks down the boundary (statement
+ skeleton) so S24 can paste-and-build in a single Docker iteration.

---

## §2 Why these two lemmas are needed

Per S16d-overlap-pattern-bounds.md §1, the `nondisjoint_factorial_moment_tendsto_zero`
(Layer 3 main bound for the non-disjoint contribution) decomposes:

```
nondisjoint_factorial_moment_2 d n
  = ∑_{(T₁, T₂) ∈ overlapPattern n 1} P(f trivialises T₁ ∧ f trivialises T₂)
  + ∑_{(T₁, T₂) ∈ overlapPattern n 2} P(f trivialises T₁ ∧ f trivialises T₂)
```

Each summand is a per-pair probability `(bad_count / d^n)`. The
*cardinality bounds* `card_overlapPattern_le_one` (≤ Nat.choose n 5 · 100)
and `card_overlapPattern_le_two` (≤ Nat.choose n 4 · 16) are already on
`origin/main` (S16d PR #18925). The *per-pair counts*
`bad_count_overlap_one` and `bad_count_overlap_two` are what is missing.

The per-pair counts, combined with the cardinality bounds, give the
expected polynomial asymptotic:

```
overlap-1 contribution ≤ Nat.choose n 5 · 100 · (d^(n-5) / d^n)
                       = 100 · Nat.choose n 5 · d^{-5}
                       = O(n⁵ / d⁵) → 0  at n = ⌊c · d^{2/3}⌋

overlap-2 contribution ≤ Nat.choose n 4 · 16 · (d^(n-4) / d^n)
                       = 16 · Nat.choose n 4 · d^{-4}
                       = O(n⁴ / d⁴) → 0  at n = ⌊c · d^{2/3}⌋
```

(Both contributions vanish polynomially faster than the disjoint
contribution which has Θ(d^{-2/3}) decay; this is the
"non-disjoint dominates the cube on the disjoint side" punchline of §4c
in lemma-c-roadmap.md.)

---

## §3 Statement signatures (Lean-paste-ready)

### §3.1 `bad_count_overlap_one`

**Setting**: triples `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` share
**exactly one** index. Without loss of generality (after the
canonicalisation handled by `overlapPattern`), the shared index is
`c₁ = a₂`. The union `T₁ ∪ T₂` has 5 distinct vertices:
`{a₁, b₁, c₁ = a₂, b₂, c₂}`. The 4 equality constraints
`f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂` collapse via the
shared `c₁ = a₂` into the single equivalence class
`{a₁, b₁, c₁ = a₂, b₂, c₂} ↦ k` for some `k ∈ Fin d`. The remaining
`n - 5` unconstrained inputs are free, giving `d^(n - 5)` configurations.

```lean
/-- **Layer 3f per-pair count (overlap = 1).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing exactly the index
    `c₁ = a₂`, the count of functions `f : Fin n → Fin d` simultaneously
    trivialising both triples is `d^(n - 5)`.

    Combined with `card_overlapPattern_le_one` (L?? on main), this gives
    the polynomial asymptotic `overlap-1 ≤ 100 · Nat.choose n 5 · d^{-5}`
    needed by `nondisjoint_factorial_moment_2_tendsto_zero` (S17). -/
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₅₆ : b₂ ≠ c₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 5) := by
  sorry  -- S24 ACT scope; see §4 below for tactic skeleton.
```

**Hypothesis count**: 10 pairwise-distinctness hypotheses (edges of the
complete graph K₅ on the 5 distinct vertices), vs. 15 for the K₆ of
`bad_count_disjoint`. The reduction is exactly the 5 edges incident on
the shared vertex `c₁ = a₂` (3 "would-be-cross" edges `c₁ ≠ a₂` and
`c₁ ≠ b₂`-mapped-via-shared / `c₁ ≠ c₂`-mapped-via-shared collapse —
note `h₃₅` and `h₃₆` are retained because the shared vertex `c₁ = a₂`
must still be distinct from `b₂` and `c₂`; what is dropped is `h₂₄`
(formerly `b₁ ≠ a₂`) which is subsumed by `h₂₃` (`b₁ ≠ c₁`) since
`c₁ = a₂`, and similarly for `h₃₄`).

### §3.2 `bad_count_overlap_two`

**Setting**: triples `T₁` and `T₂` share **exactly two** indices. By the
canonicalisation handled by `overlapPattern`, the shared indices are
`b₁ = a₂` and `c₁ = b₂`. The union `T₁ ∪ T₂` has 4 distinct vertices:
`{a₁, b₁ = a₂, c₁ = b₂, c₂}`. The 4 equality constraints
`f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂` collapse via the
two shared identifications into the single equivalence class
`{a₁, b₁ = a₂, c₁ = b₂, c₂} ↦ k` for some `k ∈ Fin d`. The remaining
`n - 4` unconstrained inputs give `d^(n - 4)` configurations.

```lean
/-- **Layer 3f per-pair count (overlap = 2).** Given two ordered triples
    `T₁ = (a₁, b₁, c₁)` and `T₂ = (a₂, b₂, c₂)` sharing the two indices
    `b₁ = a₂` and `c₁ = b₂`, the count of functions `f : Fin n → Fin d`
    simultaneously trivialising both triples is `d^(n - 4)`.

    Note: counter-intuitively, the count is `d^(n - 4)` and *not*
    `d^(n - 2)` as one might expect from "4 equality constraints,
    n - 2 free indices". The 4 constraints over the 4 distinct vertices
    collapse into a single 4-way equivalence class — only one
    independent equality survives once the 2 vertex identifications are
    applied. The remaining `n - 4` indices are unconstrained, giving
    `d^(n - 4)`. -/
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₃₆ : c₁ ≠ c₂) (h₁₆ : a₁ ≠ c₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 4) := by
  sorry  -- S24 ACT scope; see §4 below for tactic skeleton.
```

**Hypothesis count**: 6 pairwise-distinctness hypotheses (edges of the
complete graph K₄ on the 4 distinct vertices), vs. 15 for `bad_count_disjoint`.

**Note on the third constraint duplication**: the filter predicate
`f a₂ = f b₂ ∧ f b₂ = f c₂` becomes `f b₁ = f c₁ ∧ f c₁ = f c₂` after
the substitutions `a₂ = b₁`, `b₂ = c₁`, giving `f a₁ = f b₁ ∧ f b₁ = f c₁
∧ f b₁ = f c₁ ∧ f c₁ = f c₂` — note the third conjunct is *literally
the same* as the second (after substitution), hence redundant. The
canonical form for S24 ACT should drop the redundant conjunct:

```lean
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 4)
```

(This is just `bad_count_general` applied to the 4-vertex chain
`a₁ → b₁ → c₁ → c₂`; in fact `bad_count_overlap_two` reduces to
`bad_count_general` with a 4-element chain via the redundancy
elimination. If `bad_count_general` is already in the file, the
overlap-2 proof becomes a 1-line `exact bad_count_general d n a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₁₃ h₃₆ h₁₆ h₂₆.`)

Decision for S24 ACT: **check whether `bad_count_general` (lemma-c-roadmap.md
L258) is on `origin/main`** by grepping the file. If yes, overlap-2 is
a 1-LOC proof; if no, follow the `bad_count_disjoint` template fully.

---

## §4 Tactic-skeleton map (overlap-1 case; overlap-2 is simpler)

`bad_count_disjoint`'s proof (L1479–~L1697 in the file, ~220 LOC) follows
this 4-step structure:

| Step | What it does | overlap-0 ($T_1 \cap T_2 = \emptyset$, 6 vertices, n-4 free) | overlap-1 (5 vertices, n-5 free) | overlap-2 (4 vertices, n-4 free) |
|------|--------------|---------------------------------------------|----------------------------------|----------------------------------|
| 1 | `hcompl_card` (complement subtype cardinality = n − k) | `n − 4` (excludes b₁, c₁, b₂, c₂) | **`n − 5`** (excludes b₁, c₁, b₂, c₂, plus shared a₂=c₁) | `n − 4` (excludes b₁, c₁, c₂, plus shared a₂=b₁) |
| 2 | `hcard_target` (target function space card = d^(n−k)) | `d^(n − 4)` | **`d^(n − 5)`** | `d^(n − 4)` |
| 3 | `Fintype.card_coe` swap (rewrite Finset.card as Fintype.card) | identical | identical | identical |
| 4 | `Fintype.card_congr` bijection (3 obligations: toFun, invFun + membership + left/right_inv) | 4 equality conjuncts in filter predicate; invFun's `if-then-else` chain has 5 branches (b₁/c₁/b₂/c₂/other) | **3 equality conjuncts (one redundant after shared-vertex collapse); invFun's `if-then-else` chain has 5 branches**; care needed in mapping the shared vertex `c₁ = a₂` to a single equivalence class | **2 equality conjuncts; invFun's `if-then-else` chain has 4 branches**; or — if `bad_count_general` is on main — 1-LOC reduction |

### §4.1 Step-1 difference (overlap-1)

Replace `bad_count_disjoint`'s line 1491:

```lean
have hcompl_card :
    Fintype.card {m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} = n - 4
```

with the overlap-1 form (note `c₁` appears twice in the excluded set —
once as itself and once as the shared `a₂`):

```lean
have hcompl_card :
    Fintype.card {m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} = n - 5
```

Wait — that gives the wrong count. The complement-subtype counts the
*free* indices, which is `n − |T₁ ∪ T₂|` = `n − 5`. The excluded indices
are `{a₁, b₁, c₁ = a₂, b₂, c₂}` minus `a₁` (which is the *fixed point* of
the equivalence class). Actually re-reading the disjoint version: the
excluded set is `{b₁, c₁, b₂, c₂}` (the 4 vertices that the `invFun`
*sends to the equivalence class*; `a₁` and `a₂` map to themselves
because they are the representatives of each triple).

For overlap-1, the equivalence class is `{a₁, b₁, c₁ = a₂, b₂, c₂}` —
all 5 vertices in the same class. The *representative* is `a₁` (the
"start" of the chain). The 4 "downstream" vertices `{b₁, c₁, b₂, c₂}`
are mapped to `a₁`'s value. So the complement-subtype's excluded set
is `{b₁, c₁, b₂, c₂}` — same 4 indices as the disjoint case — but
because `c₁ = a₂` is a single index, the actual count of distinct
excluded indices is **4**, not 5. So:

```lean
have hcompl_card :
    Fintype.card {m : Fin n // m ≠ b₁ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂} = n - 4
```

— the *same* hypothesis as the disjoint case! Therefore `hcompl_card`
is structurally identical between overlap-0 and overlap-1. The
difference is in Step 2: the *target function space cardinality*.

**Correction to §3.1 above**: the count `d^(n − 5)` is wrong; the
correct count is **`d^(n − 4)`** (same as overlap-0). Wait — that
doesn't match the asymptotic in §2 which uses `d^{-5}` ... let me
reconsider.

### §4.2 Asymptotic reconciliation (caveat)

The asymptotic `O(n⁵ / d⁵)` in §2 came from the *combined* contribution
`(cardinality bound) × (per-pair probability)`:

* cardinality bound: `100 · Nat.choose n 5`
* per-pair probability: `bad_count_overlap_one / d^n`

If `bad_count_overlap_one = d^(n - 4)` (i.e. 4 equivalence relations),
then per-pair probability is `d^{-4}`, and the combined contribution is
`100 · Nat.choose n 5 · d^{-4} = O(n⁵ / d⁴)`. At `n = ⌊c · d^{2/3}⌋`
this is `O(d^{10/3} / d⁴) = O(d^{-2/3})` — same as disjoint, which
contradicts the "non-disjoint vanishes faster" claim.

If `bad_count_overlap_one = d^(n - 5)` (i.e. 5 equivalence relations),
per-pair probability is `d^{-5}`, combined `100 · Nat.choose n 5 · d^{-5}
= O(n⁵ / d⁵) → c⁵ · d^{-5/3}` at `n = ⌊c · d^{2/3}⌋` — strictly faster
than disjoint's `Θ(d^{-2/3})`. This matches §2.

**Resolution**: the count is **`d^(n - 5)`**, not `d^(n - 4)`. The 5
equivalence-class merger is the single equivalence relation `{a₁, b₁,
c₁ = a₂, b₂, c₂} ↦ k`. The complement-subtype excludes **all 5**
downstream indices (treating `a₁` as the representative and `b₁, c₁
= a₂, b₂, c₂` as the 4 downstream + ... wait, 4 distinct downstream
indices since `c₁ = a₂` is one index, not two). So the
complement-subtype excludes 4 indices, giving `n - 4`. But the target
function space — `complement → Fin d` — has cardinality `d^(n - 4)`,
not `d^(n - 5)`.

There's an inconsistency. Let me re-think.

### §4.3 Resolution (key insight for S24 ACT)

The disjoint case's filter predicate has **4 equality constraints**:

```
f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂
```

These constrain `{a₁, b₁, c₁}` to a single value `k₁` and `{a₂, b₂, c₂}`
to a single value `k₂` — TWO independent equivalence classes, giving
`d × d^(n - 6) = d^(n - 4)` configurations. The complement-subtype
excludes 4 indices `{b₁, c₁, b₂, c₂}` (the 4 "downstream" indices from
the 2 representatives `a₁, a₂`).

The overlap-1 case has the same 4 equality constraints (overlap-1
doesn't change the predicate, just the topology of the shared index).
With `c₁ = a₂`, the two equivalence classes `{a₁, b₁, c₁}` and `{a₂,
b₂, c₂} = {c₁, b₂, c₂}` are linked via `c₁`, merging into a SINGLE
class `{a₁, b₁, c₁, b₂, c₂}` of size 5. This gives **one** value `k`
for all 5 indices, so total `d × d^(n - 5) = d^(n - 4)` configurations.

Wait — so overlap-1 *also* has count `d^(n - 4)`? Let me recount.

Disjoint: 2 free choices (`k₁, k₂`) × `d^(n - 6)` for the unconstrained
n - 6 indices = `d^2 · d^(n - 6) = d^(n - 4)`. ✓
Overlap-1: 1 free choice (`k`) × `d^(n - 5)` for the unconstrained
n - 5 indices = `d · d^(n - 5) = d^(n - 4)`. ✓

So overlap-0 and overlap-1 BOTH give `d^(n - 4)` ?! That's suspicious.

Per-pair probability for overlap-0: `d^(n - 4) / d^n = d^{-4}`.
Per-pair probability for overlap-1: `d^(n - 4) / d^n = d^{-4}`.

Combined contributions:
* overlap-0 (disjoint, dominant): `Nat.choose n 6 · 30 · d^{-4}` ~
  `n^6 / 6! · 30 / d^4 = n^6 / (24 d^4)` → at `n = c·d^{2/3}` → `c^6 / 24 · d^{0}` =
  Θ(1) constant — that's the `λ²` term!
* overlap-1: `Nat.choose n 5 · 100 · d^{-4}` ~ `n^5 / 120 · 100 / d^4`
  → at `n = c·d^{2/3}` → `c^5 · 5/6 · d^{-2/3}` — Θ(d^{-2/3}), vanishes!
* overlap-2: `Nat.choose n 4 · 16 · d^{-3}` (since 4 vertices, 3 free
  choices, d^(n-3) count, probability `d^{-3}`) ~ `n^4 / 24 · 16 / d^3`
  → at `n = c·d^{2/3}` → `c^4 · 2/3 · d^{-1/3}` — Θ(d^{-1/3}), vanishes!

Hmm — that doesn't match §2's `O(d^{-5/3})` and `O(d^{-4/3})` either.
The polynomial-in-n parts vs polynomial-in-d parts give different rates.

Actually re-doing § 2's algebra cleanly:

Disjoint case (count `d^(n-4)`, prob `d^{-4}`):
* contribution = `Nat.choose n 3 · Nat.choose (n-3) 3 / 2 · d^{-4} · 36` (need both ordered triples but only count unordered)
* at `n = c · d^{2/3}`: `(c·d^{2/3})^6 / (3! · 3! · 2) · 36 / d^4`
  = `c^6 · d^4 / 72 · 36 / d^4 = c^6 / 2 = λ²` ✓

Overlap-1 (5 vertices, count `d^(n-4)`, prob `d^{-4}`):
* contribution = `100 · Nat.choose n 5 · d^{-4}` (from §2)
* at `n = c · d^{2/3}`: `100 · c^5 · d^{10/3} / 120 / d^4 = (5/6) c^5 · d^{-2/3}` → 0 ✓

OK so the count IS `d^(n - 4)` and the asymptotic correction is right:
the *cardinality* of overlap-1 (n⁵ not n⁶) is what makes it vanish,
not a different `d` power. §2's `d^{-5}` was a typo — should be `d^{-4}`.

**Conclusion for §3.1 statement**: the right count is **`d^(n - 4)`**,
not `d^(n - 5)`. The overlap-1 case has the same `d^(n - 4)` count as
overlap-0 (one equivalence class of 5 vs two classes of 3; in both
cases, total free dimensions = `n - 4`). What makes overlap-1 vanish
relative to overlap-0 is the smaller *cardinality* `Nat.choose n 5 ·
100` vs `Nat.choose n 3 · Nat.choose (n-3) 3 / 2 · 36` (n⁵ vs n⁶).

### §4.4 Revised §3.1 statement (paste-ready)

```lean
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₅₆ : b₂ ≠ c₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 4) := by
  sorry  -- proof body ~250 LOC, S24 ACT scope; mirrors bad_count_disjoint Steps 1-4.
```

This is structurally identical to `bad_count_disjoint` except:
* 5-conjunct filter predicate (vs 4 in disjoint) — encodes the shared
  vertex via the explicit chain.
* Wait — the disjoint predicate is `f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂` (4 conjuncts). The overlap-1 predicate becomes `... ∧ f c₁ = f b₂ ∧ ...` (since `a₂ = c₁`), which IS 4 conjuncts. Wait, let me re-count.

Original disjoint predicate (4 conjuncts):
1. `f a₁ = f b₁`
2. `f b₁ = f c₁`
3. `f a₂ = f b₂`
4. `f b₂ = f c₂`

Overlap-1 case (`a₂ = c₁` substituted into conjunct 3):
1. `f a₁ = f b₁`
2. `f b₁ = f c₁`
3. `f c₁ = f b₂`   ← was `f a₂ = f b₂`, now substituted
4. `f b₂ = f c₂`

Still 4 conjuncts! And these 4 chain together: `f a₁ = f b₁ = f c₁ = f b₂
= f c₂`, giving a single equivalence class of 5 indices. The
complement-subtype excludes 4 of those 5 (with `a₁` as the rep), giving
`n - 4` free. Count = `d · d^(n-5) = d^(n-4)`. ✓

Revised paste-ready statement for §3.1 (4-conjunct, count d^(n-4)):

```lean
theorem bad_count_overlap_one (d n : ℕ) (a₁ b₁ c₁ b₂ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₅₆ : b₂ ≠ c₂) (h₃₅ : c₁ ≠ b₂) (h₃₆ : c₁ ≠ c₂)
    (h₁₅ : a₁ ≠ b₂) (h₁₆ : a₁ ≠ c₂)
    (h₂₅ : b₁ ≠ b₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f b₂ ∧ f b₂ = f c₂)).card =
      d ^ (n - 4) := by
  sorry  -- proof body ~250 LOC, mirrors bad_count_disjoint Steps 1-4.
```

This is literally the same as `bad_count_disjoint` after the
substitution `a₂ ↦ c₁` (and dropping the 5 distinctness hypotheses
that involved the substituted `a₂` separately, since they collapse into
hypotheses already on `c₁`).

**Insight for S24 ACT**: `bad_count_overlap_one` should be a direct
corollary of `bad_count_disjoint` via the substitution; in fact, an
~5 LOC proof:

```lean
theorem bad_count_overlap_one ... :
    ... = d ^ (n - 4) :=
  bad_count_disjoint d n a₁ b₁ c₁ c₁ b₂ c₂
    h₁₂ h₂₃ h₁₃ h₅₆ ... -- need to thread the 15 hypotheses; some may need symm
```

Wait, `bad_count_disjoint` requires `a₁ ≠ a₂`, `a₁ ≠ b₂`, ..., specifically
needs `c₁ ≠ a₂` and `b₁ ≠ a₂` and `a₁ ≠ a₂`. With `a₂ = c₁`, we'd need
`c₁ ≠ c₁` (FALSE!) — so the direct substitution gives a degenerate case
that `bad_count_disjoint` cannot handle.

So `bad_count_overlap_one` is **NOT** a corollary of `bad_count_disjoint`
— the disjoint version explicitly requires the 2 triples to be disjoint,
which fails for overlap-1. It must be proven independently.

### §4.5 Revised §3.2 statement (overlap-2 paste-ready)

After substitution `a₂ = b₁`, `b₂ = c₁` into the 4-conjunct predicate:

1. `f a₁ = f b₁`
2. `f b₁ = f c₁`
3. `f b₁ = f c₁`   ← redundant, can drop
4. `f c₁ = f c₂`

So the canonical form has 3 conjuncts (after redundancy elimination):

```lean
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₃₆ : c₁ ≠ c₂) (h₁₆ : a₁ ≠ c₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 3) := by
  sorry  -- proof body ~150 LOC (simpler than disjoint), mirrors Steps 1-4.
```

Count = `d · d^(n - 4) = d^(n - 3)` (one equivalence class of 4 indices).

**Asymptotic check (§2 revisit)**:
* overlap-2 contribution = `Nat.choose n 4 · 16 · d^{-3}` (per-pair prob is `d^{n-3}/d^n = d^{-3}`)
* at `n = c · d^{2/3}`: `c^4 · d^{8/3} / 24 · 16 / d^3 = (2/3) c^4 · d^{-1/3}` → 0 ✓

§2's `O(d^{-4})` per-pair-prob and `O(d^{-4/3})` combined was wrong;
correct is `d^{-3}` and `d^{-1/3}`.

---

## §5 Bearer audit (no new bearers vs. `bad_count_disjoint`)

Per S22 §3, the 8 Mathlib bearers required by the existing Layer 3a–3f
infrastructure are byte-stable at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
The overlap-1 and overlap-2 lemmas use a **strict subset** of these
bearers (no new Mathlib API):

| Bearer (lemma) | Path | Used by overlap-1? | Used by overlap-2? | S22 SHA |
|----------------|------|--------------------|--------------------|---------|
| `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` | ✓ Step 1 | ✓ Step 1 | byte-stable |
| `Finset.card_sdiff_of_subset` | `Mathlib/Data/Finset/Card.lean:569` | ✓ Step 1 | ✓ Step 1 | byte-stable |
| `Fintype.card_fun` | `Mathlib/Data/Fintype/Card.lean` | ✓ Step 2 | ✓ Step 2 | byte-stable |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | ✓ Step 2 | ✓ Step 2 | byte-stable |
| `Fintype.card_coe` | `Mathlib/Data/Fintype/Subtype.lean` | ✓ Step 3 | ✓ Step 3 | byte-stable |
| `Fintype.card_congr` | `Mathlib/Logic/Equiv/Defs.lean` | ✓ Step 4 | ✓ Step 4 | byte-stable |

All 6 are part of S22 §3's audit (verified ~75min ago); the lake SHA
has not advanced. **0 new Mathlib bearer pins needed for S24 ACT.**

Spot-check at this PREP's authoring time: `proofs/lake-manifest.json`
Mathlib `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `inputRev: v4.26.0`
— unchanged since S22 STATE-SYNC merged.

---

## §6 LOC + Docker forecast for S24 ACT

* `bad_count_overlap_one`: ~250 LOC (close to `bad_count_disjoint`'s 220
  LOC, slightly larger due to the more complex Step 4 invFun branches
  handling the 4-conjunct chain).
* `bad_count_overlap_two`: ~150 LOC (smaller — 4-vertex chain has 3
  conjuncts in canonical form, 4 invFun branches).
* Combined: **~400 LOC** new Lean code in §9 of the file (after
  `card_overlapPattern_le_two` at the current tail).

**Docker forecast**:
* First Docker iteration (Iter 1): 7743 jobs (file's current count + the
  ~400 new lines). Risk: medium. Mitigations:
  1. Paste both lemmas together but check Lean elaboration locally first
     if possible (worktree-side `lake build` no-go per project policy).
  2. If `bad_count_disjoint`'s tactic pattern transfers cleanly,
     expected 0 errors. If not, surface error class similar to S17's
     37-error v4.26.0 bug — but the file already builds clean at 7743
     jobs (PR #19247), so the new code is the only error source.
* Docker availability gate: **at this PREP's authoring time,
  `/dev/disk3s5  884Gi / 926Gi  100%`** (host disk full per S22 §7-style
  infra warning). S24 ACT must wait until disk clears, OR pivot to a
  doc-only S23b PREP if Docker availability persists as a blocker.

---

## §7 ACT-readiness gate (S24)

Compared to S22 §4's 7/8-GREEN gate:

| Gate | S22 verdict | S23 verdict | Notes |
|---|---|---|---|
| File builds on lake SHA | ✅ GREEN | ✅ GREEN | PR #19247 commit msg verifies 7743 jobs clean |
| 0 sorries | ✅ GREEN | ✅ GREEN | unchanged |
| 1 axiom (Lemma C only) | ✅ GREEN | ✅ GREEN | unchanged |
| Bearer audit current | ✅ GREEN | ✅ GREEN | §5 above; 0 new bearers |
| Layer 3a–3f infrastructure in place | ✅ GREEN | ✅ GREEN | unchanged |
| `bad_count_disjoint` template available | ✅ GREEN | ✅ GREEN | L1479 unchanged |
| Next-ACT skeleton drafted | ⚠ partial | **✅ GREEN** | §3 + §4 above pin statements + tactic map |
| Other agents not in flight on slug | ✅ GREEN | ✅ GREEN | re-verified at PR-creation time |
| Docker availability (NEW) | n/a | **⚠ RED** | host disk 100% full; doc-only iterations unaffected; S24 ACT must wait |

**Net change**: gate 7 (`Next-ACT skeleton drafted`) flips ⚠ → ✅;
gate 9 (NEW, Docker availability) is ⚠ RED. S24 ACT readiness is
**operationally blocked** by infrastructure only — all mathematical
prerequisites are in place.

---

## §8 What this PREP does NOT do

* Does not edit `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` or any
  Lean file. Zero Lean changes.
* Does not edit `state.md`, `meta.json`, or any JSON tracker.
* Does not invoke Docker.
* Does not draft the full ~250 LOC proof body for either lemma — that
  is S24 ACT scope.
* Does not pre-empt the S22 STATE-SYNC's picker-priority ordering — it
  refines #1 (statement draft) from "⚠ partial" to "✅ GREEN".

The deliberate decision to NOT edit state.md or JSON is to keep this
PREP strictly conflict-free with any concurrent PR (e.g. a Mechanic /
Doctor sweep) on this slug. The next S24 ACT PR or a separate STATE-SYNC
catch-up can absorb the iteration bump.

---

## §9 Acceptance criteria

- [x] `git diff origin/main --stat` shows exactly **1 file** added:
      `s23-bad-count-overlap-statement-draft.md` (this file, ~430 LOC).
- [x] No Lean files modified; no `axiom` / `theorem` / sorry count
      changes.
- [x] No state.md or JSON tracker edits (defer to S24 ACT or follow-up
      STATE-SYNC).
- [x] All 6 cited Mathlib bearers reaffirmed at byte-stable SHA against
      lake `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- [x] Paste-ready Lean statement signatures locked for
      `bad_count_overlap_one` (10 hypotheses, 4-conjunct chain,
      `d^(n - 4)`) and `bad_count_overlap_two` (6 hypotheses, 3-conjunct
      chain, `d^(n - 3)`). The asymptotic-reconciliation in §4.3 / §4.5
      corrects the §2 forecast (`d^{-4}` and `d^{-3}` per-pair probs,
      not `d^{-5}` and `d^{-4}`).
- [x] Conflict-free with any concurrent PR on the slug (verified
      `gh pr list --search "birthday-problem-oq-03 in:title" --state open`
      returned empty at this PR's authoring time).

---

## §10 References

* `s22-build-blocker-resolved-state-sync.md` (S22 STATE-SYNC, this slug,
  PR #19405, merged 2026-05-16T03:51:48Z) — direct predecessor; §5
  picker-priority #1 motivates this PREP.
* `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean:1479` (`bad_count_disjoint`,
  S16 PR #17381) — proof-template source.
* `s16d-overlap-pattern-bounds.md` (S16d PREP) — Layer 3f cardinality
  bounds (`card_overlapPattern_le_one/two`).
* `lemma-c-roadmap.md` §4c, §lemma-c-layer-3 — overlap-pattern partition
  and per-pair-count infrastructure plan.
* PR #19247 (mechanic Lean fix, 9-cluster repair, 7743 Docker jobs
  clean) — current `origin/main` baseline for this slug.
* Memory: `feedback_researcher_postship_pivot_lands_on_slug_whose_juststatesync_conditional_pivot_recommendation_needs_prestaging`
  — adjacent pattern; here the pivot is mathematical-prerequisite
  pre-staging rather than companion-file pre-staging, but structurally
  the same "ready the alternative one step before the trigger" recipe.
