# Session 7 — S7 OBSERVE: Erdős–Hajnal Stepping-Up Lean Design Audit

**Date**: 2026-05-12
**Researcher**: researcher-1
**Phase**: OBSERVE (orientation for OQ-03c, the harder half)
**Type**: Doc-only design audit; no Lean changes, no `state.md` / `knowledge.md` / json edits.

## Rationale

S5b (PR #18174) and S6 ACT-D (PR #18249) both extend `RamseyHypergraph.lean`
for OQ-03a (existence). Both touch the same lines (`584 → 654` and
`584 → 658` respectively), so a third Lean PR would conflict.
`knowledge.md`'s 10-line treatment of OQ-03c (the Erdős–Hajnal stepping-up
lower bound) is the only meaningfully orthogonal angle remaining in this
slug.

This session writes a **Lean design audit** for OQ-03c — entirely in
a new session file — that:

1. Decomposes the Erdős–Hajnal stepping-up construction into Lean-amenable
   primitives.
2. Maps each primitive to candidate Mathlib API (path + identifier; not
   verified-buildable but cross-checked against typical naming).
3. Proposes a sub-OQ decomposition for OQ-03c so future researchers can
   peel off independently formalizable lemmas.
4. Identifies the trickiest combinatorial step (parity fix-up for the
   non-monotone case) and proposes a *cleaner structural alternative*
   that may reduce Lean overhead.

This is **doc-only**: no `state.md`, no `knowledge.md`, no Lean, no
`src/data/research/problems/<slug>.json`. The single new file is this
session record.

---

## 1. The Erdős–Hajnal 1972 stepping-up construction

### 1.1 Statement (the lemma we want to formalize)

> **Lemma (Erdős–Hajnal 1972).** Let `k ≥ 3` and `N ≥ k - 1`. If there
> exists a `(k − 1)`-coloring `χ : [N]^{(k−1)} → Bool` with no
> monochromatic `s`-clique, then there exists a `k`-coloring
> `χ' : [2^N]^{(k)} → Bool` with no monochromatic `(2s − 1)`-clique.

In terms of Ramsey numbers (the contrapositive packaging used in
`knowledge.md`):

> If `R_{k−1}(s, s) > N` then `R_k(2s − 1, 2s − 1) > 2^N`.

Iterated, this gives the tower lower bound
`R_k(s, s) ≥ tower_{k − 2}(c_k · s²)` for `k ≥ 4` and (with the same
construction at `k = 3`) `R_3(s, s) ≥ 2^{c · s}`.

### 1.2 The construction

**Input.** `χ : Finset (Fin N) → Bool`, treated as a coloring of
`(univ : Finset (Fin N)).powersetCard (k - 1)`.

**Output.** `χ' : Finset (Fin (2^N)) → Bool`, treated as a coloring of
`(univ : Finset (Fin (2^N))).powersetCard k`.

**Bit-encoding.** Each `i : Fin (2^N)` corresponds to a binary string
`b(i) : Fin N → Bool` (its base-2 representation, padded to length `N`).
For distinct `i ≠ j : Fin (2^N)`, define
```
δ(i, j) := Nat.find ⟨t, b(i) t ≠ b(j) t⟩
```
the **first differing bit-index**. Equivalently, `δ(i, j)` is the index
of the most-significant differing bit (depending on whether we use
big-endian or little-endian; the rest of this doc fixes **little-endian**
so that `δ(i, j) < δ(j, k) → i < j ⟺ j < k` — see Lemma A.1 below).

**Coloring rule.** For a `k`-subset `T = {i_1 < i_2 < ... < i_k}` of
`Fin (2^N)`, define the **δ-vector**
```
d_j := δ(i_j, i_{j+1}),  j = 1, ..., k-1.
```
Let `D(T) := {d_1, ..., d_{k-1}}` as a `Finset (Fin N)`. We define
`χ'(T)` by cases:

- **Case M (monotone).** If the sequence `(d_1, d_2, ..., d_{k-1})`
  is strictly increasing or strictly decreasing, then
  `|D(T)| = k - 1` and we set
  ```
  χ'(T) := χ(D(T)).
  ```

- **Case N (non-monotone).** Otherwise, let `j*` be the smallest index
  `j ∈ {1, ..., k-2}` such that `(d_j, d_{j+1}, d_{j+2})` is *not*
  monotone (so either `d_j > d_{j+1} < d_{j+2}` — a "valley" at `j+1` —
  or `d_j < d_{j+1} > d_{j+2}` — a "peak" at `j+1`). Set
  ```
  χ'(T) := (parity j*) XOR (peak vs valley at j+1).
  ```

  Concretely (one common normalization):
  - `χ'(T) := true` if `j*` is even and `j+1` is a peak, OR `j*` is odd
    and `j+1` is a valley;
  - `χ'(T) := false` otherwise.

The exact normalization of Case N varies between expositions
(Erdős–Hajnal 1972; Graham–Rothschild–Spencer 1990; Conlon–Fox–Sudakov
2010). What matters for the proof is two structural properties:

- **Property M.** If `T = {i_1 < ... < i_k}` lies in a `(2s-1)`-clique
  `T₀` of `χ'` *all* of whose δ-vectors are monotone, then `χ'(T)`
  is determined by `χ` applied to a `(k-1)`-subset of `Fin N`.
- **Property N.** If any δ-triple in `T₀`'s δ-walk is non-monotone,
  then Case-N colorings alternate fast enough that no `(2s-1)`-clique
  can be monochromatic on those triples alone.

### 1.3 The witness extraction (the proof that `χ'` has no `(2s-1)`-clique)

Suppose `T₀ = {i_1 < ... < i_{2s-1}} ⊆ Fin (2^N)` is monochromatic
under `χ'`. Consider its **δ-walk** `(d_1, ..., d_{2s-2})` where
`d_j = δ(i_j, i_{j+1})`.

**Step 1.** Apply the *sequence* Erdős–Szekeres theorem to
`(d_1, ..., d_{2s-2})`: a sequence of length `(s-1)(s-1)+1 = s² - 2s + 2`
has a monotone subsequence of length `s`. Since `2s - 2 ≥ s² - 2s + 2`
fails for `s ≥ 4`, we need the *full sequence Erdős–Szekeres*
`(s-1)(s-1) + 1`; choosing `2s - 2 ≥ (s-1)² + 1` requires `s ≥ ...`.

> **NOTE on the exact length.** The standard exposition uses
> `R_k(2s-1, 2s-1) > 2^N` (so the clique has `2s - 1` elements and the
> δ-walk has `2s - 2` steps). The argument actually only needs the
> δ-walk to be long enough that *some* monotone-of-length-`s`
> subsequence exists, which is `s² - 2s + 2` by sequence ES. So the
> tight statement is "`R_k(s² - 2s + 3, …) > 2^N`," and the `2s - 1`
> figure is a clean simplification under `s ≥ 2`. **For Lean we should
> formalize the tight version and derive the simplified one as a
> corollary.**

**Step 2.** Let `J = {j_1 < ... < j_s} ⊆ {1, ..., 2s-2}` be the index
set of a monotone-of-length-`s` δ-subsequence. The corresponding
`(s+1)`-element vertex-subset `T₁ := {i_{j_1}, i_{j_1 + 1}, i_{j_2 + 1},
..., i_{j_s + 1}} ⊆ T₀` has the property that *every* `k`-tuple
`(i_{a_1} < ... < i_{a_k}) ⊆ T₁` has a strictly monotone δ-sub-vector
(by the **Lemma A.2** transitivity property below). Hence every such
`k`-tuple falls in **Case M**, and the corresponding `χ'`-value equals
`χ` applied to the corresponding `(k-1)`-subset of `D(T_1)`.

**Step 3.** The collection of `(k-1)`-subsets of `D(T_1)` thus inherits
a *monochromatic* coloring under `χ`. Since `|D(T_1)| = s`, this gives
a monochromatic `s`-clique under `χ`, contradicting the hypothesis.
**QED.**

The "fix-up" in Case N is purely defensive — it ensures Step 1's
monotone-subsequence extraction is enough to conclude, without
having to worry about the non-monotone triples *also* being
monochromatic.

---

## 2. Lean primitives needed

### 2.1 The bit-encoding `b : Fin (2^N) → Fin N → Bool`

The function `b(i) t` is "the `t`-th bit of `i`." Two well-supported
Mathlib idioms:

**Option (a).** `Nat.testBit i t : Bool` (in `Mathlib.Data.Nat.Bitwise.Basic`,
historically `Mathlib.Data.Nat.Bits`). Pros: clean per-bit access; full
ext API (`Nat.testBit_ext`). Cons: indexed by `ℕ` not `Fin N`, so the
"padded-to-N" constraint is implicit (use `i < 2^N → testBit i t = false
∀ t ≥ N`, which is `Nat.testBit_lt_two_pow`).

**Option (b).** `Nat.digits 2 i : List ℕ` (in `Mathlib.Data.Nat.Digits`).
Pros: explicit padding via `List.replicate (N - digits.length) 0 ++
digits`. Cons: list-vs-vector mismatch is awkward for indexing.

**Recommendation.** **Option (a)** — `Nat.testBit` is the canonical
choice in current Mathlib (the bitwise file is now better-developed than
the digits file). Encode `b : Fin (2^N) → Fin N → Bool` as
```lean
def stepUp.bit (N : ℕ) (i : Fin (2^N)) (t : Fin N) : Bool :=
  Nat.testBit i.val t.val
```

### 2.2 The first-differing-index `δ : Fin (2^N) → Fin (2^N) → Fin N` (partial)

We want `δ(i, j) := Nat.find ⟨t, bit N i t ≠ bit N j t⟩` for `i ≠ j`.

**Mathlib hooks.**
- `Nat.find` (in `Mathlib.Data.Nat.Find`) requires the existence witness.
- For `i ≠ j : Fin (2^N)`, `i.val ≠ j.val` gives the existence witness:
  `Nat.xor i.val j.val ≠ 0`, and the bit at the position of the lowest
  set bit of `Nat.xor i.val j.val` differs. The function
  `Nat.log2 (Nat.xor i.val j.val) : ℕ` (or its dual `Nat.lowestBit`)
  identifies this position — but Mathlib's `Nat.log2` is for the
  *highest* set bit, which corresponds to the **most-significant**
  differing bit. For Lean we should pick **lowest** for "first" to
  match the sequence-monotonicity property (see Lemma A.1).
- `Nat.findGreatest` (`Mathlib.Data.Nat.FindGreatest`) for highest;
  `Nat.find` + `Nat.lt_two_pow` for lowest with a custom decidable
  instance.

**Recommendation.** Define
```lean
def stepUp.delta (N : ℕ) (i j : Fin (2^N)) (h : i ≠ j) : Fin N :=
  ⟨Nat.find (stepUp.differs_exists N i j h), stepUp.delta_lt N i j h⟩
```
where `differs_exists` packages the existence of a differing bit and
`delta_lt` bounds it by `N`. The argument that `δ(i,j) < N` uses
`Nat.testBit_lt_two_pow : i.val < 2^N → ∀ t ≥ N, Nat.testBit i.val t =
false`, which forces the difference to occur strictly below `N`.

### 2.3 The δ-walk of a `k`-subset

Given a `Finset (Fin (2^N))` of cardinality `k`, we extract its sorted
list and compute consecutive δ's.

**Mathlib hooks.**
- `Finset.sort (· ≤ ·) T : List (Fin (2^N))` gives the sorted list.
  - Pro: well-tested API in `Mathlib.Data.Finset.Sort`.
  - Con: indexed by `ℕ`, not `Fin (T.card - 1)`.
- `Finset.orderIsoOfFin T h : Fin (T.card) ≃o T` (where `h : T.card = n`)
  in `Mathlib.Order.SuccPred.LinearLocallyFinite` (subject to drift
  across Mathlib versions). Pro: `Fin (T.card)`-indexed; perfect for
  recording the δ-walk as `Fin (k-1) → Fin N`.

**Recommendation.** Use `Finset.orderIsoOfFin` to define
```lean
def stepUp.deltaWalk (N k : ℕ) (T : Finset (Fin (2^N))) (hT : T.card = k) :
    Fin (k - 1) → Fin N :=
  fun j => stepUp.delta N
    ((Finset.orderIsoOfFin T hT) ⟨j.val, by omega⟩)
    ((Finset.orderIsoOfFin T hT) ⟨j.val + 1, by omega⟩)
    (by
      apply (Finset.orderIsoOfFin T hT).injective.ne
      simp [Fin.mk_lt_mk]; omega)
```
The `k - 1 = 0` edge case (i.e. `k ≤ 1`) is handled trivially since
`Fin 0` is empty.

### 2.4 Detecting monotone δ-walks

We want `Strict.isMono : Fin (k - 1) → Fin N → Prop`, plus
decidability.

**Mathlib hooks.**
- `StrictMono`, `StrictAnti` (`Mathlib.Order.Monotone.Basic`).
- `Monotone.decidable_of_finite` (not a stock name; the standard
  decidable instance is `decidableLE` lifted through `Finset.univ`).

**Recommendation.** Define
```lean
def stepUp.isMonotoneWalk (N k : ℕ) (w : Fin (k - 1) → Fin N) : Bool :=
  decide (StrictMono w) || decide (StrictAnti w)
```
with the decidability supplied by `Fintype.decidableForall_fintype`.

### 2.5 Translating the δ-walk to a coloring input

In **Case M**, the δ-walk has `k - 1` strictly monotone entries, so its
*image* is a `Finset (Fin N)` of size exactly `k - 1`. We feed that to
`χ`.

**Mathlib hooks.**
- `Finset.image f s` for the image set.
- `Finset.card_image_of_injOn` for the cardinality control.

**Recommendation.** Define
```lean
def stepUp.deltaImage (N k : ℕ) (T : Finset (Fin (2^N))) (hT : T.card = k) :
    Finset (Fin N) :=
  Finset.image (stepUp.deltaWalk N k T hT) Finset.univ
```
The size claim
```lean
theorem stepUp.deltaImage_card (N k : ℕ) (T : Finset (Fin (2^N)))
    (hT : T.card = k) (hMono : stepUp.isMonotoneWalk N k (deltaWalk T hT)) :
    (stepUp.deltaImage N k T hT).card = k - 1
```
follows from injectivity of strictly-monotone functions on `Fin (k - 1)`.

### 2.6 The Case-N parity fix-up — *the painful part*

Each rendering of the Case-N rule in the literature is slightly
different. The combinatorial requirement is:

> If `T_0` is a `(2s-1)`-clique in `χ'` and *some* `k`-tuple of `T_0`
> falls in Case N, then `T_0` is not monochromatic.

The cleanest way to package this in Lean is to **decompose Case N into
its sole structural use**: the contrapositive

> If `T_0` is monochromatic in `χ'`, then *every* `k`-tuple of `T_0`
> falls in Case M.

If we can prove the contrapositive directly (without committing to a
specific Case-N rule), the rule itself becomes a black box used only
inside one helper lemma. The structural claim is:

**Structural Claim (clean Case-N abstraction).** There exists a
function `chiN : (k-tuple of (Fin (2^N))) × (Case-N input data) → Bool`
such that for any monochromatic `(2s-1)`-clique `T_0` of `χ'`, the
δ-walk of `T_0` has no non-monotone triple.

This is *exactly* what the proof in §1.3 step 2 invokes — and it lets
us push the messy parity computation into a single lemma that takes
the *output* (no non-monotone triples) as a hypothesis, never
constructively unfolding the parity inside the main inductive
argument.

**Lean shape.**
```lean
theorem stepUp.monochromatic_clique_walks_are_monotone
    (N k s : ℕ) (hk : 3 ≤ k) (hs : k ≤ s)
    (χ : Finset (Fin N) → Bool)
    (T₀ : Finset (Fin (2^N))) (hT₀ : T₀.card = 2*s - 1)
    (hMono : IsMonochromatic (stepUp.lift N k χ) k T₀ c) :
    ∃ (T₁ : Finset (Fin (2^N))) (hT₁ : T₁ ⊆ T₀) (hT₁card : T₁.card = s + 1),
      ∀ (T : Finset (Fin (2^N))) (hT : T ⊆ T₁), T.card = k →
        stepUp.isMonotoneWalk N k (stepUp.deltaWalk N k T (by aesop)) = true
```
The proof internally uses Case-N (to derive non-monotone triples =
non-monochromatic), then runs sequence Erdős–Szekeres on the δ-walk to
extract `T₁`. **The parity fix-up is wholly inside this lemma.**

### 2.7 The sequence Erdős–Szekeres input

For Step 1 of §1.3, we need: given a sequence
`w : Fin (k - 1) → Fin N` (the δ-walk of `T_0`, length `2s - 2`), there
is a monotone subsequence of length `s`.

This is **`erdos_szekeres_existence`** in `Proofs/ErdosSzekeres.lean`,
or its Mathlib analogue `Theorems100.erdos_szekeres` (in
`Mathlib.Combinatorics.ErdosSzekeres` for Wiedijk #73). Both express
the result as "every sequence of length `(r-1)(s-1)+1` has a
non-decreasing subsequence of length `r` or a non-increasing
subsequence of length `s`."

**Recommendation.** Re-use the existing `erdos_szekeres_existence`
theorem from `Proofs/ErdosSzekeres.lean` — this gives us an
*in-repo* dependency rather than a Mathlib-version-pinning concern.
With `r = s = s`, length `(s-1)² + 1` suffices. Convert
`2s - 2 ≥ (s-1)² + 1` to a Lean `Nat` arithmetic side-condition
`s ≥ ...` (true for `s ≥ 3`; check the small cases separately).

---

## 3. Sub-OQ decomposition for OQ-03c

The full OQ-03c statement
`R_k(s, s) ≥ tower_{k-2}(c'_k · s²)` factors into the following
*independently formalizable* sub-OQs. Each is a candidate for its own
research session.

### S-up-1: bit-encoding and δ-function infrastructure

**Goal.** Define `stepUp.bit`, `stepUp.delta`, `stepUp.deltaWalk`,
`stepUp.deltaImage` and their basic API:

- `bit_lt_two_pow_iff_zero_above`: `b(i) t = false ∀ t ≥ N`
  (cleanup lemma for `i < 2^N`).
- `delta_lt_N`: `δ(i, j) < N`.
- `delta_symm`: `δ(i, j) = δ(j, i)`.
- `bit_below_delta_eq`: `t < δ(i, j) → b(i) t = b(j) t`.
- `bit_at_delta_ne`: `b(i) (δ(i, j)) ≠ b(j) (δ(i, j))`.
- `deltaWalk_card_eq_pred_of_card`: `T.card = k → (deltaWalk).card =
  k - 1`.

**Size estimate.** 200–300 lines. Pure `Fin` + `Nat.testBit` arithmetic.
No combinatorial content. Aristotle-companion candidate.

### S-up-2: order-comparison via the δ-function (Lemma A.1)

**Goal.** State and prove

> **Lemma A.1 (δ-order).** For `i < j` and `j < k` in `Fin (2^N)`:
> - If `δ(i, j) < δ(j, k)`, then `b(i)(δ(j,k)) = b(j)(δ(j,k)) = ¬b(k)(δ(j,k))`,
>   so `δ(i, k) = δ(j, k)`.
> - If `δ(i, j) > δ(j, k)`, then `b(i)(δ(i,j)) = ¬b(j)(δ(i,j)) = ¬b(k)(δ(i,j))`,
>   so `δ(i, k) = δ(i, j)`.
> - If `δ(i, j) = δ(j, k)`, then `δ(i, k) > δ(i, j)`.

This lemma is the **combinatorial heart** of the stepping-up
argument — it says that the δ-function, restricted to a monotone-δ-walk
chain, behaves like a strict total order on bit-positions. From it
follows:

> **Corollary (Lemma A.2 — transitivity for monotone-δ chains).** If
> `T = {i_1 < ... < i_k}` has a δ-walk `(d_1, ..., d_{k-1})` that is
> strictly monotone, then for any sub-chain `i_{j_1} < ... < i_{j_l}`,
> the induced δ-walk `(δ(i_{j_1}, i_{j_2}), ..., δ(i_{j_{l-1}},
> i_{j_l}))` is *also* strictly monotone in the same direction, and
> its image equals `{d_{j_1}, ..., d_{j_{l-1}}}`.

**Size estimate.** 150–250 lines. Modular: 5–6 small lemmas.

### S-up-3: the lift `stepUp.lift : (Finset (Fin N) → Bool) → (Finset (Fin (2^N)) → Bool)`

**Goal.** Define `stepUp.lift N k χ : Finset (Fin (2^N)) → Bool` per
the rule of §1.2, prove its `IsMonochromatic`-compatibility, and prove
the structural claim of §2.6.

**Sub-lemma split.**

- `stepUp.lift_case_M`: under monotone δ-walk, `χ'(T) = χ(D(T))`.
- `stepUp.lift_case_N`: under non-monotone δ-walk (specifically: some
  δ-triple is non-monotone), `χ'(T) = (parity, peak/valley)` —
  packaged but unfolded only inside §2.6's structural claim.
- `stepUp.monochromatic_clique_walks_are_monotone` (the structural
  claim itself, see §2.6).

**Size estimate.** 400–600 lines. The Case-N proof is the hard part.
Aristotle is unlikely to help with the parity fix-up; this is the
session that *must* be researcher-driven.

### S-up-4: stepping-up theorem proper

**Goal.** State and prove the lemma of §1.1.

```lean
theorem stepUp.stepping_up_lower_bound
    (k N s : ℕ) (hk : 3 ≤ k) (hs : k ≤ s) (hN : k - 1 ≤ N)
    (χ : Finset (Fin N) → Bool)
    (hχ : ∀ S : Finset (Fin N), S.card = s → ¬ IsMonochromatic χ (k-1) S true ∧
                                                  ¬ IsMonochromatic χ (k-1) S false) :
    ∃ χ' : Finset (Fin (2^N)) → Bool,
      ∀ T : Finset (Fin (2^N)), T.card = 2*s - 1 →
        ¬ IsMonochromatic χ' k T true ∧ ¬ IsMonochromatic χ' k T false
```

Proof: instantiate `χ' := stepUp.lift N k χ`; assume a monochromatic
`(2s-1)`-clique `T_0`; apply `monochromatic_clique_walks_are_monotone`
to extract `T_1`; observe that `(deltaImage T_1)` is a `s`-subset of
`Fin N` whose every `(k-1)`-subset is `χ`-monochromatic in the same
color; conclude the contradictory `s`-clique in `χ`.

**Size estimate.** 100–150 lines. Pure assembly.

### S-up-5: the tower iteration → `R_k(s, s) ≥ tower_{k-2}(s²)`

**Goal.** Iterate `stepping_up_lower_bound` from the `R_3(s, s) ≥ 2^{cs}`
base to the general `R_k`.

**Pre-requisite.** A `k = 3` base case `R_3(s, s) ≥ 2^{c · s}`. This
*does not* come from stepping-up (since stepping-up needs `k - 1 ≥ 2`,
i.e. `k ≥ 3`); it comes from a **separate probabilistic argument**
(Erdős 1947 random-graph). So in fact OQ-03c's full statement
requires *two* independent lower-bound sources:

- **The `k = 2` base.** `R_2(s, s) ≥ 2^{s/2}` via random graph (Erdős
  1947). This is the lower-bound half of `erdos_szekeres_tight_axiom`
  (see `knowledge.md` §Insights), and it would be a great
  Aristotle target if formalized via the second-moment method on a
  random `[N]^{(2)} → Bool` coloring.

- **The `k = 3` base.** `R_3(s, s) ≥ 2^{c · s}` from stepping-up
  applied to the `k = 2` random-graph base.

For `k ≥ 4`, the tower iterates.

**Size estimate.** 80–120 lines. Trivial induction once S-up-4 is in
place. *However* the `k = 2` base is its own large undertaking
(possibly a new sub-OQ in its own right).

### S-up-6 (optional): Wiedijk #73 discharge

**Goal.** Use the `k = 2` lower bound (random graph) of S-up-5 to
discharge `erdos_szekeres_tight_axiom` in
`Proofs/ErdosSzekeres.lean`. This was raised in `knowledge.md` and
`problem.md` and is the only **gallery-impact** sub-OQ.

**Size estimate.** 50–80 lines (assuming the `k = 2` random-graph
lower bound is already formalized).

---

## 4. Risk register and Lean-design pitfalls

### 4.1 `Nat.testBit` indexing direction

The construction relies on **little-endian** indexing: bit 0 is the
least significant. Lean's `Nat.testBit` is little-endian
(`Nat.testBit n 0 = n.bodd`), so the natural definition aligns with
Mathlib. **The δ-order Lemma A.1 is stated for little-endian; if a
researcher accidentally uses big-endian (via `Nat.size n` minus
testBit-index), the *direction* of the order reverses and the entire
construction's monotonicity claims flip sign.** Add an axiom-style
comment in the file header pinning the convention.

### 4.2 The `2*s - 1` vs `s² - 2s + 3` discrepancy

§1.3 step 1 uses sequence Erdős–Szekeres to extract a monotone
subsequence. Standard expositions use `2s - 1` as the clique size, but
sequence ES actually needs `(s-1)² + 1` elements for a monotone
subsequence of length `s`. The numbers happen to coincide for `s = 2`
and `s = 3` and diverge for `s ≥ 4`.

**For Lean, the right move is:** state `stepping_up_lower_bound` with
the **tight** clique size `(s-1)² + 2` (i.e. `(s-1)² + 1` elements in
the δ-walk plus one vertex), and derive `2s - 1` as a corollary
under `s ≤ ...` or via an explicit `s = 2, 3` case check. The tight
version is shorter to prove than the loose version.

### 4.3 `Fin (2^N)` blowup at small `N`

`Fin (2^0) = Fin 1`. `Fin (2^1) = Fin 2`. The construction is vacuous
or trivial in these cases. **`stepping_up_lower_bound` should require
`N ≥ k - 1`** (else the input coloring has no support and the
conclusion is vacuous).

### 4.4 Aristotle suitability

Per `research/SORRY-CLASSIFICATION.md`, Aristotle proves theorem-sorries
but skips definition-sorries. The Case-N parity fix-up in S-up-3 is
the worst-case profile for Aristotle: heavy case analysis on `Bool`,
parity arithmetic on `j*`, and three-way splits per δ-triple. **S-up-3
is researcher-driven.** S-up-1, S-up-2, S-up-4 are good Aristotle
candidates (clean arithmetic + structure transport).

### 4.5 Tower function

`tower_n(x) := Nat.iterate (2 ^ ·) n x` is the obvious choice. Mathlib
has `Nat.iterate`; no new definitions needed. The only concern is the
`Nat.iterate (2^·)` non-tail-recursive elaboration, which can be slow
at `n = 4, 5` if Lean kernel-reduces it eagerly. **Recommendation:**
mark the tower function `@[irreducible]` and prove rewrite lemmas
`tower_succ : tower (n+1) x = 2 ^ tower n x` and
`tower_zero : tower 0 x = x` for use in inductions.

### 4.6 Naming collision with existing `Theorems100.erdos_szekeres`

If Mathlib's `Theorems100.erdos_szekeres` is in scope, the new
`stepUp.*` namespace should be clearly separated. Recommend
`RamseyK.StepUp.*` to land cleanly under the existing
`RamseyHypergraph.lean` namespace.

---

## 5. Sequencing recommendation

The natural session order is:

1. **S-up-1** (bit-encoding API) — 200 LOC, Aristotle-friendly.
2. **S-up-2** (δ-order Lemma A.1) — 150 LOC, partly Aristotle-friendly.
3. **S-up-3** (lift + structural claim) — 400 LOC, researcher-driven.
4. **S-up-4** (stepping-up lemma proper) — 100 LOC, Aristotle-friendly.
5. **S-up-5** (tower iteration) — 80 LOC, contingent on `k = 2` base.

The `k = 2` random-graph base (which discharges `erdos_szekeres_tight_axiom`)
is itself a sub-OQ — perhaps **a new seeker slug** `erdos-szekeres-tight-axiom-via-random-graph`
or similar, since it has independent significance (Wiedijk discharge of
the only remaining axiom in `ErdosSzekeres.lean`).

---

## 6. Pre-flight Mathlib API citations

Cited from Mathlib's standard naming conventions. **Not verified
buildable in this session** (worktree shares the broken `proofs/.lake`
symlink per memory `feedback_researcher_lake_symlink_broken.md`); a
follow-up S2 session should re-verify via `docker-build.sh` before
committing to these names.

| Primitive | Likely Mathlib path | Identifier |
|---|---|---|
| Per-bit access of `Nat` | `Mathlib.Data.Nat.Bitwise.Basic` | `Nat.testBit` |
| Bit-zero above bound | `Mathlib.Data.Nat.Bitwise.Lemmas` | `Nat.testBit_lt_two_pow` |
| Existence of differing bit | derived | `Nat.find` + custom helper |
| `Fin n ≃o T` for `T : Finset α` of card `n` | `Mathlib.Data.Finset.Sort` | `Finset.orderIsoOfFin` |
| Sequence Erdős–Szekeres | `Proofs/ErdosSzekeres.lean` (in-repo) | `erdos_szekeres_existence` |
| `StrictMono` decidability on `Fin n` | `Mathlib.Order.Monotone.Basic` + `Fintype.decidableForall_fintype` | (derived) |
| Image of a function on a `Finset` | `Mathlib.Data.Finset.Image` | `Finset.image` |
| Cardinality of image under injection | `Mathlib.Data.Finset.Image` | `Finset.card_image_of_injective` |
| `Nat.iterate` (for tower) | `Mathlib.Logic.Function.Iterate` | `Nat.iterate` |

---

## 7. What this session does *not* do

- No new Lean declarations.
- No changes to `state.md` or `knowledge.md` or `src/data/research/problems/erdos-szekeres-oq-03.json`.
- No `RamseyHypergraph.lean` edits (orthogonal to PR #18249 / PR #18174).
- No build attempt (worktree shares broken `proofs/.lake` symlink).
- No commitment to a specific Case-N fix-up rule (deferred to S-up-3).

## 8. What this session deliberately produces

- A **session-local design audit** (this file), pristinely conflict-free
  against in-flight Lean PRs.
- A **sub-OQ decomposition** for OQ-03c into 5 independently
  formalizable sessions plus an optional Wiedijk-#73 discharge.
- A **risk register** for the trickiest Lean-design pitfalls,
  particularly indexing direction and the loose-vs-tight clique-size
  formula.
- A **Mathlib API citation table** for the bit-encoding and δ-walk
  primitives, to be re-verified in S-up-1.

---

## 9. References

- F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc.
  (2) 30 (1930), 264–286. *[OQ-03a, the original existence proof.]*
- P. Erdős, R. Rado, *A partition calculus in set theory*, Bull. AMS 62
  (1956), 427–489. *[OQ-03b, the tower upper bound.]*
- P. Erdős, A. Hajnal, *On Ramsey like theorems. Problems and results.*,
  Combinatorics (Oxford 1972), 123–140. *[OQ-03c, the stepping-up
  construction. The original reference for §1.2's coloring rule.]*
- R. Graham, B. Rothschild, J. Spencer, *Ramsey Theory* (2nd ed.,
  Wiley 1990), Ch. 4. *[Modern textbook exposition of the stepping-up
  construction with explicit Case-N parity rules.]*
- D. Conlon, J. Fox, B. Sudakov, *Hypergraph Ramsey numbers*, J. AMS 23
  (2010), 247–266. *[Modern improvement of OQ-03b's upper bound;
  contains a re-exposition of OQ-03c.]*

## 10. Sign-off

Session writes one new file
(`research/problems/erdos-szekeres-oq-03/sessions/2026-05-12-s7-observe-erdos-hajnal-stepping-up-lean-design.md`).
No other files modified. Build status: N/A (doc-only).

The next researcher picking up OQ-03c should claim the slug, read this
file, and start with **S-up-1** (bit-encoding API) — the most
self-contained sub-task with the least dependence on the
in-flight S6 ACT-D / S5b structure.
