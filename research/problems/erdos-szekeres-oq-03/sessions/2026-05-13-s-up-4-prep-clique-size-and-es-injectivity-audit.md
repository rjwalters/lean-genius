# Session — S-up-4 PREP: clique-size arithmetic + ES injectivity-hypothesis audit

**Date**: 2026-05-13
**Researcher**: researcher-6
**Phase**: PREP for S-up-4 (the stepping-up theorem proper; see S7 OBSERVE §3.4
of `2026-05-12-s7-observe-erdos-hajnal-stepping-up-lean-design.md`)
**Type**: Doc-only audit — resolves two unresolved Risk-4.x items in S7 OBSERVE
ahead of any Lean commitment. No `state.md` / `knowledge.md` / `problem.md` /
Lean / JSON edits.

## Rationale

S7 OBSERVE (PR #18303, merged 2026-05-12) and S-up-1 PREP (PR #18529, merged
2026-05-13 04:08Z) leave **two arithmetic / API mismatches** unresolved that
S-up-4 will hit immediately when stating `stepUp.stepping_up_lower_bound`:

1. **Clique-size formula.** S7 OBSERVE Risk 4.2 flags that the standard
   "`(2s−1)`-clique" formula yields a δ-walk of length `2s − 2`, but sequence
   Erdős–Szekeres requires `(s−1)² + 1` elements to extract a
   monotone-of-length-`s` subsequence. The inequality `2s − 2 ≥ (s − 1)² + 1`
   reduces to `(s − 2)² ≤ 0`, which **holds iff `s = 2`**. So the
   "stated tight version `(s−1)² + 2`" mentioned in Risk 4.2 is mandatory for
   `s ≥ 3`, not an optional cosmetic upgrade.

2. **Injective-hypothesis gap.** Both the in-repo `erdos_szekeres_existence`
   (`proofs/Proofs/ErdosSzekeres.lean:141-145`) and Mathlib's archive
   `Theorems100.erdos_szekeres` (`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:139`)
   require `Injective f`. The δ-walk `(d_1, …, d_{m})` of a clique
   `T₀ : Finset (Fin (2^N))` is **not** necessarily injective —
   `d_j = δ(i_j, i_{j+1})` can repeat values. So no off-the-shelf ES variant
   applies directly to the δ-walk; S-up-4 needs an explicit injectivity-aware
   adapter.

This session pins each gap to concrete file:line / Lean source and proposes a
resolution that S-up-4 can paste verbatim. All Mathlib citations verified via
GitHub Contents API read-throughs against `leanprover-community/mathlib4`
master HEAD.

Also orthogonal-by-construction to:

* **PR #18174 (S5b OPEN)** — edits `RamseyHypergraph.lean` lines 584-654
  (`sInf` characterisation helpers) plus `state.md` plus the slug JSON. No
  file overlap.
* **PR #18529 (S-up-1 PREP MERGED 1.5 h ago)** — disjoint file path
  (`2026-05-13-s-up-1-prep-mathlib-api-audit.md`). The §2 drop-in signatures
  for `stepUp.bit / .delta / .deltaWalk / .deltaImage_card` are unchanged
  by this audit.
* **PR #18303 (S7 OBSERVE MERGED)** — the parent design audit this session
  augments. Disjoint file path.

The single new file is the present session record. No edits to
`state.md`, `knowledge.md`, `problem.md`, `RamseyHypergraph.lean`,
`ErdosSzekeres.lean`, or `src/data/research/problems/erdos-szekeres-oq-03.json`.

---

## 1. Gap 1 — the clique-size arithmetic

### 1.1 What S7 OBSERVE Risk 4.2 said

> §1.3 step 1 uses sequence Erdős–Szekeres to extract a monotone subsequence.
> Standard expositions use `2s − 1` as the clique size, but sequence ES
> actually needs `(s−1)² + 1` elements for a monotone subsequence of length
> `s`. The numbers happen to coincide for `s = 2` and `s = 3` and diverge for
> `s ≥ 4`. […]
> **For Lean, the right move is:** state `stepping_up_lower_bound` with the
> **tight** clique size `(s−1)² + 2` (i.e. `(s−1)² + 1` elements in the
> δ-walk plus one vertex), and derive `2s − 1` as a corollary under
> `s ≤ …` or via an explicit `s = 2, 3` case check.

The "happens to coincide for `s = 2` and `s = 3`" claim is **wrong**. Let me
work the arithmetic in detail.

### 1.2 The exact arithmetic

The §1.3 proof outline:

* `T₀ : Finset (Fin (2^N))` is a monochromatic `(M)`-clique under `χ'`.
* δ-walk of `T₀` is `(d_1, …, d_{M-1}) ∈ (Fin N)^{M-1}`.
* Apply sequence ES to extract a **monotone subsequence of length `s`** from
  this δ-walk. The output indices `J = {j_1 < … < j_s}` correspond to a
  sub-clique `T₁ ⊆ T₀` of size `s + 1` whose induced δ-walk is monotone
  (by Lemma A.2 of S7 OBSERVE).
* The image of `T₁`'s monotone δ-walk is a `s`-subset of `Fin N`. Every
  `(k−1)`-subset of this `s`-subset is `χ`-monochromatic in the same colour
  (by Lemma A.2 + Case M of §1.2). Hence `χ` admits a monochromatic
  `s`-clique, contradicting the hypothesis.

So the **required** ES side-condition is:

```
δ-walk length M − 1 ≥ (s − 1)² + 1   ⟺   M ≥ (s − 1)² + 2.
```

### 1.3 Comparison with the "standard" `(2s − 1)`-clique

| `s` | Required `M = (s−1)² + 2` | Standard `2s − 1` | Standard − Required |
|-----|---|---|---|
| 2 | 3 | 3 | 0 |
| 3 | 6 | 5 | **−1** |
| 4 | 11 | 7 | **−4** |
| 5 | 18 | 9 | **−9** |
| 6 | 27 | 11 | **−16** |
| 7 | 38 | 13 | **−25** |

So `2s − 1` is sufficient **only at `s = 2`** (where both equal 3). At every
`s ≥ 3` the standard formula is **too small** — i.e. the proof via "extract
monotone-of-length-`s` from δ-walk" does not work with a `(2s − 1)`-clique
for `s ≥ 3`.

S7 OBSERVE Risk 4.2's parenthetical "coincide for `s = 2` and `s = 3`" is
arithmetic noise: at `s = 3`, Required = 6, Standard = 5 — they do not
coincide. (Possibly the author was thinking of `2s` vs `(s−1)² + 2`:
2·3 = 6 = (3−1)² + 2. But `2s` is not the standard formula.)

### 1.4 Where the standard `(2s − 1)` actually comes from

The Erdős–Hajnal 1972 paper and downstream references (Graham–Rothschild–
Spencer 1990, Conlon–Fox–Sudakov 2010) typically state the stepping-up lemma
roughly as:

> `R_{k−1}(s, s) > N`  ⟹  `R_k(2s − 1, 2s − 1) > 2^N`

(or `R_k(2(s − 1), 2(s − 1))`, depending on the reference). The `(2s − 1)`
clique size is *the conclusion*, not a hypothesis about ES extraction. The
fact that the *proof* in those references doesn't use the ES extraction
described in S7 OBSERVE §1.3 means **the textbook proof uses different
combinatorial machinery** — typically a *recursive* application of the
`(k−1)`-Ramsey hypothesis on the link coloring (similar to S6 ACT-D's
infrastructure) rather than a single ES extraction.

For the Lean formalization, S7 OBSERVE has *committed* to the ES extraction
path (§1.3 step 1, §2.7, S-up-4 size estimate "100–150 lines pure
assembly"). Under that commitment, the clique size **must** be at least
`(s − 1)² + 2`.

### 1.5 Recommendation

State the Lean theorem with the **tight** clique size `(s − 1)² + 2`:

```lean
theorem stepUp.stepping_up_lower_bound
    (k N s : ℕ) (hk : 3 ≤ k) (hs : k ≤ s) (hN : k - 1 ≤ N)
    (χ : Finset (Fin N) → Bool)
    (hχ : ∀ S : Finset (Fin N), S.card = s →
            ¬ IsMonochromatic χ (k - 1) S true ∧
            ¬ IsMonochromatic χ (k - 1) S false) :
    ∃ χ' : Finset (Fin (2 ^ N)) → Bool,
      ∀ T : Finset (Fin (2 ^ N)), T.card = (s - 1) ^ 2 + 2 →
        ¬ IsMonochromatic χ' k T true ∧ ¬ IsMonochromatic χ' k T false
```

Do **not** add a corollary specialising to `(2s − 1)` — for `s ≥ 3` the
tight formula is *larger*, so a `(2s − 1)`-clique would not even reach the
threshold, and the corollary "no `(2s − 1)`-monochromatic clique" does not
follow from "no `((s−1)² + 2)`-monochromatic clique" in general (it would
require `(2s − 1) ≥ (s − 1)² + 2`, false for `s ≥ 3`).

If matching the textbook Ramsey number is important for downstream
applications (S-up-5 tower iteration, S-up-6 Wiedijk #73 discharge), state
two **separate** lemmas:

1. The ES-based theorem above, with clique size `(s − 1)² + 2`.
2. The textbook lemma with clique size `2s − 1`, marked `axiom` for now
   (S-up-3.5 sub-OQ), pending the recursive link-coloring proof that
   Erdős–Hajnal actually use.

The ES-based bound implies `R_k((s−1)² + 2, (s−1)² + 2) > 2^N`, which is
**weaker** than the textbook `R_k(2s − 1, 2s − 1) > 2^N` only at the cost
of a quadratic-vs-linear blow-up in the clique-size argument of the
recursion. Iterated `k − 2` times, both produce `R_k(c · s², c · s²) ≥
tower_{k−2}(N)`-style bounds up to constants in `c`.

### 1.6 Down-stream impact on S-up-5

S-up-5 (tower iteration) plugs the stepping-up bound into

```
R_k(M_k, M_k) > 2^{R_{k−1}(M_{k−1}, M_{k−1})}
```

with the recursion `M_k = M(M_{k−1})` where `M` is the clique-size function.
The textbook uses `M(s) = 2s − 1`, giving linear iteration:
`M_k ≈ 2^{k−2} s`. The ES tight form gives `M(s) = (s−1)² + 2`, quadratic
iteration: `M_k ≈ s^{2^{k−2}}`. **At the level of the tower bound, both
yield `R_k(s, s) ≥ tower_{k−2}(c · s^{a_k})` for some constants `c, a_k > 0`;
the constants degrade, but the qualitative tower-shape is preserved.**

So for the qualitative OQ-03c statement ("`R_k(s, s)` grows like a tower in
`k` for fixed `s`"), the ES tight form is sufficient. Only quantitative
optimisations (e.g. matching Conlon–Fox–Sudakov 2010's improved constants)
need the textbook formula.

---

## 2. Gap 2 — the ES injectivity hypothesis

### 2.1 What the two ES theorems require

#### In-repo (`proofs/Proofs/ErdosSzekeres.lean:141-145`)

```lean
theorem erdos_szekeres_existence {α : Type*} [LinearOrder α] {n : ℕ}
    (f : Sequence α n) (hf : Injective f) (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1)
    (hn : n ≥ (r - 1) * (s - 1) + 1) :
    (∃ sub : IncreasingSubseq f r, True) ∨ (∃ sub : DecreasingSubseq f s, True)
```

backed by `erdos_szekeres_existence_axiom` (`ErdosSzekeres.lean:136`).

`IncreasingSubseq` / `DecreasingSubseq` (`ErdosSzekeres.lean:69-84`) use
`StrictMono` / `StrictAnti` on the value-side, i.e. strict monotonicity.

#### Mathlib archive (`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:139`)

```lean
theorem erdos_szekeres {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α)
    (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t
```

(`StrictMonoOn` / `StrictAntiOn`, again strict.)

Both demand `Injective f`. Both produce strictly monotone witnesses.

### 2.2 Why the δ-walk is not injective

The δ-walk `(d_1, …, d_{M-1})` of a clique `T₀ = {i_1 < … < i_M} ⊆ Fin (2^N)`
is `d_j = δ(i_j, i_{j+1}) : Fin N`. Repeated values are common:

**Concrete example.** Take `N = 3`, `T₀ = {0, 1, 5, 4, 6} ⊂ Fin (2³)`,
sorted as `{0, 1, 4, 5, 6}`:

* `i_1 = 0 = 000₂`, `i_2 = 1 = 001₂` ⟹ first differing bit (little-endian) =
  bit 0 ⟹ `d_1 = 0`.
* `i_2 = 1 = 001₂`, `i_3 = 4 = 100₂` ⟹ first differing bit = bit 0 ⟹ `d_2 = 0`.
* `i_3 = 4 = 100₂`, `i_4 = 5 = 101₂` ⟹ first differing bit = bit 0 ⟹ `d_3 = 0`.
* `i_4 = 5 = 101₂`, `i_5 = 6 = 110₂` ⟹ first differing bit = bit 0 ⟹ `d_4 = 0`.

So δ-walk `(d_1, d_2, d_3, d_4) = (0, 0, 0, 0)` — **constant**, hence not
injective. Plugging this into `erdos_szekeres_existence` with `hf : Injective`
fails at type-check.

This degeneracy is actually *systematic*: whenever the clique `T₀` consists of
"consecutive odd / even" runs in `Fin (2^N)`, the δ-walk repeats. So the
phenomenon is not an edge case — it is the typical situation for the
constructions S-up-3 will examine.

### 2.3 Three resolution strategies

#### Strategy A — Inject via the index

Replace the δ-walk `d : Fin (M − 1) → Fin N` with the *paired* sequence
`d̃ : Fin (M − 1) → Fin N × Fin (M − 1)` defined by `d̃ j = (d j, j)`,
ordered lex-with-second. The paired sequence is trivially injective (second
coordinate uniquely identifies `j`). Then any monotone sub-sequence of `d̃`
projects to a *weakly monotone* sub-sequence of `d`.

**Lean shape.**

```lean
-- step 0: pair δ-walk with index
def stepUp.pairedWalk (N k : ℕ) (T : Finset (Fin (2^N))) (hT : T.card = k) :
    Fin (k - 1) → Fin N ×ₗ Fin (k - 1) :=
  fun j => (stepUp.deltaWalk N k T hT j, j)

-- step 1: pairedWalk is injective (second coord is the identity)
lemma stepUp.pairedWalk_injective {N k : ℕ} (T : Finset (Fin (2^N)))
    (hT : T.card = k) : Function.Injective (stepUp.pairedWalk N k T hT) := by
  intro j₁ j₂ hj
  exact congr_arg Prod.snd hj
```

Then apply `erdos_szekeres_existence` to `pairedWalk` with `r = s = s_target`.

**Pros.** Cleanly off-the-shelf; uses existing in-repo ES axiom unchanged.

**Cons.** The output is a `StrictMono`-on-the-paired sequence, which is a
*weak* monotonicity on the projection. Lemma A.2 of S7 OBSERVE was stated
for *strict* monotonicity of the δ-walk; weakening it to weakly monotone
δ-walks changes the proof. Specifically, weakly monotone δ-walks can have
`d_j = d_{j+1}`, which falls under Case N of S7 OBSERVE §1.2 (because the
"non-monotone triple" detection includes `d_j ≤ d_{j+1} ≤ d_{j+2}` with
equality), so the structural claim of §2.6
(`stepUp.monochromatic_clique_walks_are_monotone`) is no longer obviously
correct.

**Verdict.** Need to re-derive A.2 + §2.6 for weakly monotone walks. About
30–50 extra lines.

#### Strategy B — Restrict to monochromatic cliques' walks-are-strict

Prove a separate lemma: **monochromatic cliques have strictly monotone
δ-walks**. The intuition: if `χ'(T)` is constant on every `k`-subset of `T₀`,
then by Case N of §1.2 there are no "valleys" or "peaks" in `T₀`'s δ-walk,
which (combined with Lemma A.1) forces strict monotonicity.

**Lean shape.**

```lean
lemma stepUp.monochromatic_clique_walk_strict
    {N k s : ℕ} (hk : 3 ≤ k) (hs : k ≤ s)
    (χ : Finset (Fin N) → Bool)
    (T₀ : Finset (Fin (2^N))) (hT₀ : T₀.card = M) (c : Bool)
    (hMono : IsMonochromatic (stepUp.lift N k χ) k T₀ c) :
    Function.Injective (stepUp.deltaWalk N M T₀ hT₀) ∧
    (StrictMono (stepUp.deltaWalk N M T₀ hT₀) ∨
     StrictAnti (stepUp.deltaWalk N M T₀ hT₀))
```

(Or just the `Injective` part, and let ES from there.)

**Pros.** Avoids modifying the ES axiom; the structural content of
"monochromatic ⟹ strict walk" is exactly what Case N of S7 OBSERVE §1.2 is
designed to enforce.

**Cons.** Proving `stepUp.monochromatic_clique_walk_strict` *is* the hard
part of S-up-3 (it's essentially the contrapositive of §2.6's structural
claim, restricted to a slightly stronger conclusion). This couples S-up-4 to
S-up-3 — S-up-4 cannot proceed until S-up-3 has fully landed §2.6 in a form
that yields injectivity.

**Verdict.** Architecturally correct but creates an unavoidable
S-up-3 → S-up-4 dependency.

#### Strategy C — Add a non-injective ES variant as a separate axiom

State a weaker ES axiom (no `Injective f` hypothesis) returning weakly
monotone subsequences. The standard ES *with weak monotonicity* is true:
any sequence of length `(r − 1)(s − 1) + 1` has either a *weakly* increasing
subsequence of length `r` or a *weakly* decreasing subsequence of length `s`
(no distinctness required). The proof is the same pigeonhole on
`(longest weakly-inc-ending-at-i, longest weakly-dec-ending-at-i)` pairs.

**Lean shape (in `Proofs/ErdosSzekeres.lean`, extending existing API).**

```lean
structure WeaklyIncreasingSubseq {α : Type*} [Preorder α] {n : ℕ}
    (f : Sequence α n) (k : ℕ) where
  positions : Fin k → Fin n
  strictMono_positions : StrictMono positions
  monotone_values : Monotone (f ∘ positions)

structure WeaklyDecreasingSubseq {α : Type*} [Preorder α] {n : ℕ}
    (f : Sequence α n) (k : ℕ) where
  positions : Fin k → Fin n
  strictMono_positions : StrictMono positions
  antitone_values : Antitone (f ∘ positions)

axiom erdos_szekeres_existence_weak {α : Type*} [LinearOrder α] {n : ℕ}
    (f : Sequence α n) (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1)
    (hn : n ≥ (r - 1) * (s - 1) + 1) :
    (∃ sub : WeaklyIncreasingSubseq f r, True) ∨
    (∃ sub : WeaklyDecreasingSubseq f s, True)
```

Note: **no `hf : Injective f`** in the weak version.

**Pros.** Cleanly matches the δ-walk situation. The proof of
`erdos_szekeres_existence_weak` is structurally identical to
`erdos_szekeres_existence_axiom` — both go through the
`(max-weakly-inc, max-weakly-dec)` pigeonhole pair, with `Monotone` replacing
`StrictMono`.

**Cons.** Adds a *new* axiom to `ErdosSzekeres.lean`, increasing the axiom
count from 2 (`erdos_szekeres_existence_axiom`, `erdos_szekeres_tight_axiom`)
to 3 — directly conflicting with the "Axiom Elimination Priority" rule in
`.lean/roles/researcher.md`. The honest path is then to *prove* the new
axiom from the existing one via Strategy A's index-pairing trick:
`erdos_szekeres_existence_weak` is a corollary of
`erdos_szekeres_existence` applied to the paired sequence
`f̃ j = (f j, j)`.

**Verdict.** Best long-term API but requires the bridging lemma to keep the
axiom count flat.

### 2.4 Recommendation

**Combine Strategy A + Strategy C with the bridging lemma.** The S-up-4 file
should:

1. Define `WeaklyIncreasingSubseq` / `WeaklyDecreasingSubseq` in a new
   utility section of `ErdosSzekeres.lean` (or in a fresh
   `ErdosSzekeresWeak.lean`).
2. Prove `erdos_szekeres_existence_weak` from `erdos_szekeres_existence` via
   the lex-paired sequence trick (~30 LOC, no new axioms).
3. Apply `erdos_szekeres_existence_weak` to the δ-walk in S-up-4. Output:
   weakly monotone δ-walk of length `s` extracted from a δ-walk of length
   `M − 1 ≥ (s − 1)² + 1` (where `M = (s − 1)² + 2`).
4. Re-derive Lemma A.2 of S7 OBSERVE for *weakly* monotone δ-walks. The
   proof is essentially the same — Lemma A.1's three-case analysis already
   handles `δ(i, j) = δ(j, k)`, returning `δ(i, k) > δ(i, j)`. Weakly
   monotone walks where `d_j = d_{j+1}` correspond to `δ(i_j, i_{j+1}) =
   δ(i_{j+1}, i_{j+2})` triggering Lemma A.1's third case, which gives
   `δ(i_j, i_{j+2}) > δ(i_j, i_{j+1})`. So in the "sub-clique" `T₁ =
   {i_{j_1}, i_{j_1+1}, i_{j_2+1}, …, i_{j_s+1}}` the induced δ-walk
   computed via consecutive δ's is *strictly* increasing (each `δ(i, k) >
   δ(i, j) = δ(j, k)` strictly), not weakly.

Crucially: **weakly monotone δ-walks under Lemma A.1 produce strictly
monotone induced δ-walks on sub-chains**. So Strategy A's "weak ES output"
is *upgraded* to "strict monotonicity on the sub-chain" by Lemma A.1's third
case — no separate proof of strict monotonicity is needed downstream.

This is the cleanest path: the user-facing structural lemma A.2 keeps its
strict-monotonicity conclusion, only the *intermediate* ES extraction goes
through the weak variant.

---

## 3. Pre-flight Mathlib citation grid (delta over S-up-1 PREP §1)

The S-up-1 PREP §1 already pinned 8 Mathlib citations for the S-up-1 file
(`stepUp.bit / .delta / .deltaWalk / .deltaImage_card`). This audit adds the
**S-up-4 specific** citations needed for the stepping-up theorem itself.

| # | Citation | Verdict | Verified file:line | Notes |
|---|---|---|---|---|
| 1 | `Nat.find_spec` | **VERIFIED** | `Mathlib/Data/Nat/Find.lean:74` | `protected theorem find_spec : p (Nat.find H)`. Used in Strategy A to extract the witness. |
| 2 | `Nat.find_min` | **VERIFIED** | `Mathlib/Data/Nat/Find.lean` (via doc-comment line 67) | Companion of `find_spec`. |
| 3 | `Nat.eq_of_testBit_eq` | **VERIFIED (core, not Mathlib)** | `lean4/src/Init/Data/Nat/Bitwise/Lemmas.lean:189` | The S-up-1 PREP §2.3 cites this without location. It is in **Lean core**, not Mathlib; signature `{x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y`. No Mathlib import needed beyond what `Nat.testBit` already pulls. |
| 4 | `Nat.zero_of_testBit_eq_false` | **VERIFIED** | `Mathlib/Data/Nat/Bitwise.lean:156` | Companion of (3). Used by (3) internally. |
| 5 | `Nat.lt_of_testBit` | **VERIFIED** | `Mathlib/Data/Nat/Bitwise.lean:192` | "If `n` has bit 0 at `i`, `m` has bit 1 at `i`, and they agree above `i`, then `n < m`." This is the structural inequality powering Lemma A.1's three-case proof — pin it for S-up-2 PREP. |
| 6 | `Nat.testBit_eq_false_of_lt` | **VERIFIED** | `Mathlib/Data/Nat/Bitwise.lean:161` | Already cited by S-up-1 PREP §1 row 2. Re-confirmed in this audit (line unchanged). |
| 7 | `Nat.exists_most_significant_bit` | **VERIFIED** | `Mathlib/Data/Nat/Bitwise.lean:178` | Bonus citation: useful for Strategy B's "monochromatic-cliques-have-strict-walks" route. |
| 8 | `StrictMono.injective` | **VERIFIED** | `Mathlib/Order/Monotone/Basic.lean:402` | `(hf : StrictMono f) : Injective f`. Standard. S-up-1 PREP §1 row 8 cited this without line. |
| 9 | `Monotone.injective` (counterexample expected) | **PHANTOM — replace** | n/a | There is no `Monotone.injective`; `Monotone` does not imply `Injective` (constant functions are monotone but not injective). The S-up-4 author should not search for this. Use `StrictMono` instead. |
| 10 | `IncreasingSubseq` / `DecreasingSubseq` | **IN-REPO** | `proofs/Proofs/ErdosSzekeres.lean:69, 78` | Already defined; `positions : Fin k → Fin n` + strict-monotone witnesses. |
| 11 | `erdos_szekeres_existence` | **IN-REPO (axiom-backed)** | `proofs/Proofs/ErdosSzekeres.lean:141-145` | Signature as quoted in §2.1; backed by `erdos_szekeres_existence_axiom` at line 136. |
| 12 | `Theorems100.erdos_szekeres` (Mathlib archive) | **VERIFIED but DO NOT USE** | `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:139` | Out-of-Mathlib-library archive; importing this from a research file pulls a 200-LOC archive file with no other purpose. Stick with the in-repo version. |
| 13 | `Sequence` type alias | **IN-REPO** | `proofs/Proofs/ErdosSzekeres.lean:66` | `abbrev Sequence (α : Type*) (n : ℕ) := Fin n → α`. |

### 3.1 Phantom to watch out for

The S-up-4 author **must not** invoke `Monotone.injective` (row 9): it
doesn't exist, and constructing it via `intro x y h` then trying to derive
`f x = f y → x = y` from `Monotone f` fails immediately (constant functions
are the counterexample). The only valid injectivity-preserving order
property is `StrictMono`.

---

## 4. Recommended S-up-4 file structure

Combining §1.5 (clique-size tight form) and §2.4 (weak-ES bridging),
S-up-4's `proofs/Proofs/RamseyHypergraphStepUpFour.lean` should contain
(in order):

1. **Imports.** `Mathlib`, plus the in-repo S-up-1 / S-up-2 / S-up-3 files
   once they exist.

2. **Weak-ES bridging (~30 LOC).** Defines `WeaklyIncreasingSubseq` /
   `WeaklyDecreasingSubseq`, proves `erdos_szekeres_existence_weak` from
   `erdos_szekeres_existence` via lex-paired sequence (Strategy A).

3. **The stepping-up theorem (~80 LOC, pure assembly).**

   ```lean
   theorem stepUp.stepping_up_lower_bound
       (k N s : ℕ) (hk : 3 ≤ k) (hs : k ≤ s) (hN : k - 1 ≤ N)
       (χ : Finset (Fin N) → Bool)
       (hχ : ∀ S : Finset (Fin N), S.card = s →
               ¬ IsMonochromatic χ (k - 1) S true ∧
               ¬ IsMonochromatic χ (k - 1) S false) :
       ∃ χ' : Finset (Fin (2 ^ N)) → Bool,
         ∀ T : Finset (Fin (2 ^ N)), T.card = (s - 1) ^ 2 + 2 →
           ¬ IsMonochromatic χ' k T true ∧ ¬ IsMonochromatic χ' k T false := by
     use stepUp.lift N k χ
     intro T hTcard
     -- Reductio: assume monochromatic-true (color-false symmetric via χ.swap).
     refine ⟨?_, ?_⟩ <;> intro hcMono
     -- Step 1: extract a sub-clique T₁ ⊆ T of size s+1 with strictly monotone δ-walk.
     obtain ⟨T₁, hT₁sub, hT₁card, hT₁mono⟩ :=
       stepUp.monochromatic_clique_extract_monotone_subclique
         (s := s) (k := k) (hk := hk) (hs := hs) χ T (by omega) hcMono
     -- Step 2: the image of T₁'s δ-walk is a s-subset of Fin N, χ-monochromatic.
     have hImageMono :
         IsMonochromatic χ (k - 1) (stepUp.deltaImage N (s + 1) T₁ hT₁card) _ :=
       stepUp.monochromatic_clique_implies_image_mono ...
     -- Step 3: contradict hχ.
     exact (hχ _ (stepUp.deltaImage_card ...)).1 hImageMono
   ```

   (Sketch — exact tactic structure depends on S-up-3's choice of
   `monochromatic_clique_extract_monotone_subclique` signature.)

4. **`(2s − 1)` corollary, if desired.** Only valid for `s = 2`:

   ```lean
   theorem stepUp.stepping_up_lower_bound_classical (k N : ℕ) (hk : 3 ≤ k)
       (hN : k - 1 ≤ N) (χ : Finset (Fin N) → Bool)
       (hχ : ∀ S : Finset (Fin N), S.card = 2 →
               ¬ IsMonochromatic χ (k - 1) S true ∧
               ¬ IsMonochromatic χ (k - 1) S false) :
       ∃ χ' : Finset (Fin (2 ^ N)) → Bool,
         ∀ T : Finset (Fin (2 ^ N)), T.card = 3 →
           ¬ IsMonochromatic χ' k T true ∧ ¬ IsMonochromatic χ' k T false :=
     stepping_up_lower_bound k N 2 hk (by omega) hN χ hχ
   ```

   The `(s − 1)² + 2 = 3 = 2·2 − 1` arithmetic at `s = 2` makes this trivial.
   For `s ≥ 3`, no such corollary exists — see §1.3 table.

---

## 5. Risk register delta over S7 OBSERVE §4 and S-up-1 PREP §3

| Risk | Pre-audit rating | Post-audit rating | Reason |
|---|---|---|---|
| 4.2 `(2s − 1)` vs tight clique size | High | **High** (sharpened) | Standard formula is sufficient only at `s = 2`; tight version `(s − 1)² + 2` is mandatory for `s ≥ 3`. S-up-4 must use tight. |
| **NEW** — ES injectivity hypothesis | (un-flagged) | **High** | δ-walk is not injective; existing ES variants do not apply. Resolution: Strategy A bridging lemma (~30 LOC, no new axiom). |
| **NEW** — Lemma A.1 third-case upgrade | (un-flagged) | **Medium** | The third-case `δ(i, j) = δ(j, k) ⟹ δ(i, k) > δ(i, j)` is what *upgrades* weak monotonicity (from ES) to strict monotonicity (in Lemma A.2). Must be proved cleanly in S-up-2; without it Strategy A leaks. |
| **NEW** — `Monotone.injective` phantom | (un-flagged) | **Low** | Easy mistake; flagged in §3.1. |
| 4.5 Tower function elaboration | Medium-Low | **Medium-Low** (unchanged) | S-up-1 PREP §3 already downgraded this. |
| 4.6 `Theorems100.erdos_szekeres` naming | None | **None** (unchanged) | S-up-1 PREP §1 row 4 already pinned in-repo path. |

---

## 6. Sequencing impact

S7 OBSERVE §5 / S-up-1 PREP §4 ordering: S-up-1 → S-up-2 → S-up-3 → S-up-4 →
S-up-5. **This audit does not change the order.** It does:

* **Add a sub-step to S-up-4** — the weak-ES bridging (§2.4 Strategy A). +30
  LOC over S7 OBSERVE's "100–150 LOC pure assembly" estimate. New estimate:
  **130–180 LOC**.
* **Sharpen the precondition** — S-up-2 must prove Lemma A.1 case 3 strictly
  (i.e. `δ(i, k) > δ(i, j)` strictly, not just `≥`), so that the Strategy A
  weak-ES output upgrades to strict on the sub-chain. This is *implicit* in
  S7 OBSERVE §2.2 (Lemma A.1) but worth pinning so S-up-2 does not weaken
  the conclusion.
* **Pin the tight clique size in S-up-3 too** — S-up-3's structural claim
  `stepUp.monochromatic_clique_walks_are_monotone` takes a clique of size
  `2s − 1` per S7 OBSERVE §2.6. **Replace with `(s − 1)² + 2`** in the
  statement signature, with the rest of the proof unchanged (S-up-3's proof
  body never uses the specific `2s − 1` formula — it just propagates "clique
  is monochromatic ⟹ δ-walk has no non-monotone triples").

---

## 7. Build / verification status

* **No Lean compiled.** The worktree shares `proofs/.lake` with the main
  repo's known self-referential symlink (per memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`); a clean Mathlib
  clone takes ~10 min and is doctor-territory.
* **All Mathlib citations verified via GitHub Contents API** read-throughs
  of `leanprover-community/mathlib4` and `leanprover/lean4` master HEAD as
  of the audit timestamp. File:line citations in §3 are reproducible via:

  ```bash
  gh api repos/leanprover-community/mathlib4/contents/Mathlib/Order/Monotone/Basic.lean \
    --jq '.content' | base64 -d | grep -n "StrictMono.injective"
  # → 402:theorem StrictMono.injective (hf : StrictMono f) : Injective f :=
  ```

* **No build attempt is required for this PR** — it is doc-only.

---

## 8. What this session does *not* do

* No Lean source modifications (`RamseyHypergraph.lean`, `ErdosSzekeres.lean`
  untouched).
* No new Lean files (the §4 file structure is *proposed* in this audit, not
  *committed*).
* No `state.md` / `knowledge.md` / `problem.md` / `<slug>.json` edits
  (S-up-4 hasn't started; this is a PREP).
* No commitment to a Strategy (A / B / C); §2.4 recommends combining A + C,
  but the implementer may choose differently.
* No build attempt (worktree's `proofs/.lake` symlink is the loop documented
  in `feedback_researcher_lake_symlink_loop_and_wipe.md`).
* No conflict with PR #18174 (S5b OPEN): orthogonal file path; S5b edits
  `RamseyHypergraph.lean` line 584-654 + state.md + JSON, this audit edits a
  fresh `sessions/` file only.

## 9. What this session deliberately produces

* A **clique-size arithmetic resolution** (§1): tight formula
  `(s − 1)² + 2`, with a `s = 2…7` table showing the standard `(2s − 1)`
  formula is insufficient for `s ≥ 3` under the ES-based proof path.
* A **non-injective ES gap analysis** (§2): three resolution strategies
  (A index-pairing, B monochromatic-implies-strict, C separate weak axiom)
  with a recommendation (A + bridging C, ~30 LOC, no new axiom).
* A **citation grid** (§3) cross-validating 13 Mathlib / lean4-core / in-repo
  identifiers for S-up-4, with one phantom-name flag (`Monotone.injective`,
  row 9) and one core-vs-Mathlib pin (`Nat.eq_of_testBit_eq`, row 3).
* A **drop-in S-up-4 file structure** (§4) with imports, theorem signature,
  proof sketch, and an `s = 2` corollary recovering the classical
  `(2s − 1)` form.
* A **risk register delta** (§5) listing three NEW risks (ES injectivity,
  Lemma A.1 case-3 strictness, `Monotone.injective` phantom) and one
  sharpened risk (4.2).
* A **sequencing impact** statement (§6): S-up-4 estimate +30 LOC over S7
  OBSERVE; S-up-3 statement needs clique-size sharpening too.

---

## 10. References (delta over S7 OBSERVE §9 + S-up-1 PREP §8)

* `Mathlib/Data/Nat/Find.lean` — `Nat.find`, `Nat.find_spec` (line 74),
  `Nat.find_min`.
* `Mathlib/Data/Nat/Bitwise.lean` — `Nat.testBit_eq_false_of_lt` (line 161),
  `Nat.zero_of_testBit_eq_false` (line 156), `Nat.lt_of_testBit` (line 192),
  `Nat.exists_most_significant_bit` (line 178).
* `lean4/src/Init/Data/Nat/Bitwise/Lemmas.lean` — `Nat.eq_of_testBit_eq`
  (line 189). **Lean core, not Mathlib.**
* `Mathlib/Order/Monotone/Basic.lean:402` — `StrictMono.injective`.
* `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:139` —
  Mathlib's `Theorems100.erdos_szekeres` (cross-referenced, not imported).
* `proofs/Proofs/ErdosSzekeres.lean:66, 69, 78, 136, 141-145` — in-repo
  `Sequence`, `IncreasingSubseq`, `DecreasingSubseq`,
  `erdos_szekeres_existence_axiom`, `erdos_szekeres_existence`.

## 11. Sign-off

Session writes one new file
(`research/problems/erdos-szekeres-oq-03/sessions/2026-05-13-s-up-4-prep-clique-size-and-es-injectivity-audit.md`).
No other files modified. Build status: N/A (doc-only).

The next researcher picking up S-up-4 should:

1. Read §1.5 for the *tight* theorem signature (clique size
   `(s − 1)² + 2`, not `2s − 1`).
2. Read §2.4 for the Strategy A weak-ES bridging lemma (~30 LOC, no new
   axiom).
3. Cross-reference §3 row 3 — `Nat.eq_of_testBit_eq` is in **Lean core**, not
   Mathlib; no extra Mathlib import needed.
4. Avoid the §3.1 phantom: do not invoke `Monotone.injective`.

S-up-3's structural-claim signature (S7 OBSERVE §2.6) should also be
sharpened to clique size `(s − 1)² + 2` per §6.
