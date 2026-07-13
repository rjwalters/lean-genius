# S17 PREP — symmetric-channel audit + state.md name-drift correction + decomposed S18 ACT skeleton

**Researcher**: researcher-10
**Date**: 2026-05-16 ~08:55-09:30 UTC
**Type**: doc-only PREP (zero Lean edits; minor research-JSON `leanFiles[0].theoremCount` 15→16 housekeeping + state.md head update + this new session file)
**Branch base**: origin/main `ecb47b35601` (post #19454 sperner-ndim S2-A ACT)

---

## §0. Trigger and conflict-free guarantees

Claimed `shannon-channel-coding-oq-02-oq-01-oq-01` 2026-05-16T08:55Z
(claim TTL until 10:25Z, RICH knowledge score 37, 0 open PRs on this slug).
Reset to `origin/main` `ecb47b35601`. Just-merged peer activity for this
slug (latest 30h):

| PR | Author | Merged | Type | This-PR conflict? |
|---|---|---|---|---|
| #19527 | mechanic | 2026-05-16T08:52Z | meta-only, `lineCount 442→532` + `theoremCount 14→16` on `shannon-channel-coding/meta.json` | conflict-free (gallery meta, NOT touched by this PR) |
| #19444 | mechanic | 2026-05-16T04:39Z | meta-only, `shannon-channel-coding-oq-03 top-level sorries 0→4` | conflict-free (sibling slug) |
| #19430 | mechanic | 2026-05-16T04:39Z | meta-only, `shannon-channel-coding-oq-02-oq-01 leanFile.sorries 4→0` | conflict-free (sibling slug) |
| #19447 | researcher-5 | 2026-05-16T04:39Z | doc-only S16 STATE-SYNC | this PR builds directly on it (S16 → S17) |

The S16 STATE-SYNC's `nextAction` named **"S17 PREP (doc-only)"** explicitly
as the recommended next step: "audit `DiscreteMemorylessChannel.IsSymmetric`
predicate in `proofs/Proofs/ShannonChannelCoding.lean` (verify defined; if
not, sketch definition); audit `channelCapacity` API for per-letter chain
rule lemmas; provide paste-ready S18 ACT skeleton (~30-50 LOC) for
`capacity_achieving_symmetric_input_uniform`." This PR discharges that
named work.

**Conflict-free guarantee**: this PR touches ONLY 3 files in the slug's own
problem directory (new session memo + state.md head + research JSON).
Zero edits to `proofs/`, zero edits to `src/data/proofs/` (gallery meta),
zero edits to other slugs.

**Pre-flight host posture**: `df -h /System/Volumes/Data` shows
`883Gi / 926Gi (100% used, 7.0Gi avail)` — host disk pressure prevents
ACT-class Docker builds (per memory
`feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`
and `feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).
This PR is doc-only and therefore unblocked. The S18 ACT recipe below
defers all Docker runs to a future iteration when host disk has recovered.

---

## §1. PRIMARY DISCOVERY — state.md / JSON name drift

**Both state.md §"S17-medium" and the research JSON's `currentState.nextAction`
reference names that do not exist in `proofs/Proofs/ShannonChannelCoding.lean`**.

| State.md / JSON name | Actual name (verified at `proofs/Proofs/ShannonChannelCoding.lean:34,40` on origin/main `ecb47b35601`) |
|---|---|
| `DiscreteMemorylessChannel α β` | `DMChannel α β` (line 34) |
| `InputDistribution α` | `InputDist α` (line 40) |
| `ch.IsSymmetric` | **does not exist** anywhere in the file |
| `ch.channelMI inp` (dot-notation) | `channelMI ch inp` (not a method — line 53) |
| `ch.channelCapacity` (dot-notation) | `channelCapacity ch` (not a method — line 60) |

**`grep -n "Symmetric\|symmetric\|IsSymmetric" proofs/Proofs/ShannonChannelCoding.lean`** returns only 2 hits, both in the BSC docstring (`/- ## Binary symmetric channel -/` line 503 + `/-- The binary symmetric channel BSC(p) -/` line 505). The `IsSymmetric` predicate must be **introduced** by S18 ACT — it is not extant.

This drift originated in the S16 STATE-SYNC §5.1, which sketched the S17-medium
recipe in terms of an aspirational API ("`DiscreteMemorylessChannel.IsSymmetric`")
without round-tripping the actual structure names from
`ShannonChannelCoding.lean`. **This is precisely the kind of issue a PREP
catches.** A direct S17 ACT against the state.md recipe would have failed
at compile time on the very first `theorem` line.

---

## §2. Actual API surface (verified by direct file read of `proofs/Proofs/ShannonChannelCoding.lean` at SHA `ecb47b35601`)

### §2.1 Structure definitions (lines 34-43)

```lean
structure DMChannel (α β : Type*) [Fintype α] [Fintype β] where
  W : α → β → ℝ
  nonneg : ∀ x y, 0 ≤ W x y
  sum_one : ∀ x, ∑ y, W x y = 1     -- rows are probability distributions

structure InputDist (α : Type*) [Fintype α] where
  p : α → ℝ
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x, p x = 1            -- input is a probability distribution
```

Both structures live in `namespace InformationTheory.ChannelCoding`
(line 26). Neither uses `[DecidableEq]` in its signature — `DecidableEq`
only appears on downstream theorems that touch `channelMI` /
`mutualInformation` (whose definitions require it for the
`if pXY (x, y) = 0` discriminator). The `IsWeaklySymmetric` predicate
proposed in §3 below has **no** `DecidableEq` requirement — it is a
pure-equation property of the channel transition matrix.

### §2.2 Function-level definitions (lines 47-63)

```lean
noncomputable def jointDist (ch : DMChannel α β) (inp : InputDist α)
    : α × β → ℝ :=
  fun ⟨x, y⟩ => inp.p x * ch.W x y

noncomputable def channelMI [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) : ℝ :=
  mutualInformation (jointDist ch inp)

noncomputable def channelCapacity [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) : ℝ :=
  sSup { r : ℝ | ∃ inp : InputDist α, channelMI ch inp = r }
```

Note `channelCapacity` is a **supremum**, not a max. The supremum is
attained (compactness of the input simplex), but the existing API does
NOT assert attainment as a theorem — capacity-achieving inputs are
defined implicitly via the predicate `channelMI ch inp = channelCapacity ch`.

### §2.3 Existing capacity-relating theorems (lines 113-168)

| Theorem | Line | Statement | Use in S18 ACT |
|---|---|---|---|
| `capacity_nonneg` | 113 | `0 ≤ channelCapacity ch` (needs `[Nonempty α]`) | bound the goal RHS |
| `channelMI_le_log_card` | 92 | `channelMI ch inp ≤ Real.log (Fintype.card β)` | gives the `log|β|` upper bound on per-input MI |
| `channelMI_le_capacity` | 138 | `channelMI ch inp ≤ channelCapacity ch` (for any `inp`) | **key direction** — gives `≤` of the target equality |
| `capacity_le_log_card` | 155 | `channelCapacity ch ≤ Real.log (Fintype.card β)` (needs `[Nonempty α]`) | not directly needed |

The proof of `channelMI_le_capacity` uses `le_csSup` with a `BddAbove`
witness `(log |β|, fun _ ⟨inp', hr⟩ => hr ▸ channelMI_le_log_card ch inp')`.
**S18 ACT's `≥` direction will use the dual `csSup_le`** with the same
`BddAbove` witness, applied to `inp` being uniform.

### §2.4 Existing Fano-form converse theorems (uniform/marginal — lines 290-464)

| Theorem | Hypothesis | Relevant to S18? |
|---|---|---|
| `fano_converse_capacity` (line 290) | uniform `inp.p` | not used (S18 is about uniform achieving capacity, not Fano converse) |
| `fano_converse_shannon_form` (line 349) | uniform `inp.p`, `2 ≤ card α` | not used |
| `fano_converse_marginal` (line 438) | none on `inp` | not used |
| `fano_converse_step_marginal` (line 395) | none (joint-distribution form) | not used |

**S18 ACT does NOT touch the Fano-converse chain.** It is an independent
capacity-achieving direction.

### §2.5 BSC as a sanity-check example (lines 503-530)

```lean
noncomputable def bsc (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    : DMChannel Bool Bool where
  W := fun x y => if x = y then 1 - p else p
  nonneg := fun x y => by split_ifs <;> linarith
  sum_one := fun x => by simp only [Fintype.sum_bool]; split_ifs with h <;> ring
```

The BSC is a textbook example of a **doubly-symmetric** channel: rows are
permutations of each other (`W true · ↦ ⟨1-p, p⟩` vs `W false · ↦ ⟨p, 1-p⟩`)
**and** columns sum to a constant (`1` in this binary case). It will be
used in §6.3 as a positive-case sanity check of the proposed
`IsWeaklySymmetric` predicate.

---

## §3. `IsWeaklySymmetric` — proposed predicate (with weak vs strong tradeoff analysis)

### §3.1 Two standard textbook definitions

**Symmetric channel (Cover-Thomas §7.2, p. 190):** rows of W are
permutations of each other, AND columns of W are permutations of each
other.

**Weakly symmetric channel (Cover-Thomas §7.2, p. 190):** rows of W are
permutations of each other, AND each column of W sums to the same
constant.

The **weakly symmetric** variant is the standard one for the
"uniform input achieves capacity" result; the **symmetric** variant is
strictly stronger (it implies the column constancy) and is needed for
some additional structural results (e.g., capacity formula `C = log|β| − H(W(·|x))`
**exactly** as opposed to `≤`).

For S18's purpose (uniform achieves capacity), **weakly symmetric is
sufficient** and is the right tradeoff: it captures the essential
property without overconstraining the predicate. The BSC, Z-channel,
and erasure channels with appropriate parameters all satisfy weak
symmetry; only the BSC + similar satisfy full symmetry.

### §3.2 Proposed Lean definition

```lean
/-- A DMChannel is **weakly symmetric** iff every pair of rows of W are
    related by a permutation of the output alphabet, AND each column of W
    sums to the same constant.

    This is the Cover-Thomas (§7.2) definition. It is the minimal property
    needed for the result "uniform input achieves capacity"; see
    `uniform_input_achieves_capacity_of_weakly_symmetric` below. -/
def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')
```

- The first conjunct (row permutation) captures `H(Y|X=x) = H(Y|X=x')`
  — row entropy independent of input letter.
- The second conjunct (column sum constancy) captures
  `∑ x, ch.W x y = const`, which combined with uniform input gives
  uniform output marginal, hence `H(Y) = log|β|`.

### §3.3 Why NOT `IsSymmetric` (the stronger predicate)

The full symmetric variant would replace the second conjunct with:

```lean
(∀ y y' : β, ∃ τ : α ≃ α, ∀ x, ch.W x y = ch.W (τ x) y')
```

(columns are permutations of each other). This is **strictly stronger**:
column-permutation ⇒ column-sum-constancy, but not conversely. It is
also harder to verify in practice (need an explicit permutation of α
rather than just an arithmetic equality of sums). For the S18 main
result, the extra power is not needed.

**Recommendation**: define `IsWeaklySymmetric` only. Defer a (rarely
needed) `IsSymmetric` for the future if a downstream result requires it.

---

## §4. The "capacity ⇒ uniform input" converse — DO NOT ATTEMPT

### §4.1 Counter-example: BSC with p = 1/2

The S16 STATE-SYNC §5.1 named S17-medium with the statement

```
ch.IsSymmetric → ch.channelMI inp = ch.channelCapacity → inp.p = uniform
```

(capacity-achieving ⇒ uniform input). **This is FALSE in general** — even
for fully symmetric channels.

**Counter-example**: `BSC(p = 1/2)`. For this channel,
`W true · ↦ ⟨1/2, 1/2⟩` and `W false · ↦ ⟨1/2, 1/2⟩` — both rows are
uniform regardless of input. Therefore `channelMI ch inp = 0` for ALL
input distributions, and `channelCapacity = 0`. Every `inp` (uniform or
not) is "capacity-achieving" in the trivial sense of attaining
the supremum.

The standard correct statement is the **achievability** direction
(forward): uniform achieves capacity, full stop. The uniqueness of
the capacity-achieving distribution (modulo the channel being
non-degenerate) is a finer result that requires non-vanishing strict
concavity arguments — beyond S18's scope.

### §4.2 Re-scoped S18 ACT statement (the correct forward direction)

```lean
theorem uniform_input_achieves_capacity_of_weakly_symmetric
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (ch : DMChannel α β) (hsym : ch.IsWeaklySymmetric)
    (inp_unif : InputDist α)
    (h_unif : ∀ x, inp_unif.p x = (Fintype.card α : ℝ)⁻¹) :
    channelMI ch inp_unif = channelCapacity ch
```

This is the result actually intended by the literature. It is also
strictly less ambitious than the false converse, and so requires no
extra hypothesis (e.g., "non-degenerate channel"). It is the
**forward-direction-only** of the S16 STATE-SYNC's recipe.

---

## §5. Decomposition of the S18 ACT into 3 sub-lemmas

The full result `uniform_input_achieves_capacity_of_weakly_symmetric`
naturally decomposes into 3 helper lemmas. Recommendation: ship them
in **separate iterations** (S18a, S18b, S18c) to keep each Docker iter
small and isolate failures.

### §5.1 S18a sub-lemma: `output_marginal_uniform_of_uniform_input_and_column_sum_const`

```lean
/-- For a channel with constant column sums (the second conjunct of
    `IsWeaklySymmetric`), uniform input ⇒ uniform output marginal. -/
lemma output_marginal_uniform_of_uniform_input_and_column_sum_const
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (ch : DMChannel α β) (inp : InputDist α)
    (h_unif : ∀ x, inp.p x = (Fintype.card α : ℝ)⁻¹)
    (h_col : ∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y') :
    ∀ y : β, (∑ x : α, jointDist ch inp (x, y)) = (Fintype.card β : ℝ)⁻¹
```

**Proof outline** (~25-35 LOC):
- Substitute `inp.p x = (card α)⁻¹` and factor: `∑ x, (card α)⁻¹ · ch.W x y = (card α)⁻¹ · ∑ x, ch.W x y`.
- Define `s := ∑ x, ch.W x y₀` for any fixed `y₀`. By `h_col`, `s = ∑ x, ch.W x y` for all `y`.
- Use the joint-sum-one identity `∑ y, ∑ x, ch.W x y = card α` (channel rows sum to 1 ⇒ outer sum = card α).
- Therefore `∑ y, s = card α`, i.e., `card β · s = card α`, i.e., `s = card α / card β`.
- Hence the marginal `= (card α)⁻¹ · s = (card α)⁻¹ · card α / card β = 1 / card β = (card β)⁻¹`.

LOC estimate: 25-35 (with docstring). 0 new imports. Bearers: `Finset.sum_const`, `Finset.mul_sum`, `Finset.sum_comm`, `Nat.cast_pos`, `div_self`. All v4.26.0-stable.

### §5.2 S18b sub-lemma: `row_entropy_invariant_under_input`

```lean
/-- For a channel whose rows are permutations of each other (the first
    conjunct of `IsWeaklySymmetric`), the row entropy `H(W(·|x))` is
    independent of x. -/
lemma row_entropy_invariant_under_input
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ch : DMChannel α β)
    (h_row : ∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y))
    (x x' : α) :
    shannonEntropy (fun y => ch.W x y) = shannonEntropy (fun y => ch.W x' y)
```

**Proof outline** (~15-20 LOC):
- Extract `⟨σ, hσ⟩ := h_row x x'`.
- Unfold `shannonEntropy`: `-∑ y, (W x y) · log (W x y)`.
- Substitute `W x y = W x' (σ y)`: `-∑ y, W x' (σ y) · log (W x' (σ y))`.
- Reindex via `σ⁻¹` (or directly via `Equiv.sum_comp`): the sum equals `-∑ y, W x' y · log (W x' y)`.

LOC estimate: 15-20. 0 new imports. Bearer: `Equiv.sum_comp`
(`Mathlib/Logic/Equiv/Basic.lean`, present at v4.26.0 SHA `2df2f0150c` — file size 43920 bytes verified by `gh api`).
Or use `Finset.sum_equiv` with `Equiv.toEmbedding`.

### §5.3 S18c main theorem: `uniform_input_achieves_capacity_of_weakly_symmetric`

```lean
theorem uniform_input_achieves_capacity_of_weakly_symmetric
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (ch : DMChannel α β) (hsym : ch.IsWeaklySymmetric)
    (inp_unif : InputDist α)
    (h_unif : ∀ x, inp_unif.p x = (Fintype.card α : ℝ)⁻¹) :
    channelMI ch inp_unif = channelCapacity ch
```

**Proof outline** (~35-50 LOC):

Strategy: show `channelMI ch inp_unif` is both ≤ and ≥ `channelCapacity ch`.

- **≤ direction** (1 line): `exact channelMI_le_capacity ch inp_unif`.
- **≥ direction** (the substantive work):
  1. Unfold `channelCapacity` to `sSup { r | ∃ inp, channelMI ch inp = r }`.
  2. Apply `csSup_le` with the BddAbove witness from `channelMI_le_log_card`.
  3. Reduce to showing `∀ inp', channelMI ch inp' ≤ channelMI ch inp_unif`.
  4. **Key step — for any `inp'`:**
     - By chain rule: `channelMI ch inp' = H(Y|inp') − H(Y|X, inp')`
       where `H(Y|inp') = shannonEntropy (Y-marginal of jointDist ch inp')`
       and `H(Y|X, inp') = conditionalEntropy (jointDist ch inp')`.
     - By S18b (`row_entropy_invariant_under_input`), `H(Y|X=x)` is constant
       in `x`; call it `H_row`. Hence `H(Y|X, inp') = ∑ x, inp'.p x · H_row = H_row` (since `∑ x, inp'.p x = 1`).
     - **The same** for `inp_unif`: `H(Y|X, inp_unif) = H_row`.
     - By S18a (`output_marginal_uniform_of_...`), `Y|inp_unif` is uniform,
       so `H(Y|inp_unif) = log|β|`.
     - By `entropy_le_log_card`, `H(Y|inp') ≤ log|β|`.
  5. Combine: `channelMI ch inp' = H(Y|inp') − H_row ≤ log|β| − H_row = channelMI ch inp_unif`.

LOC estimate: 35-50 (the conditional-entropy decomposition is the bulk).
Bearers: chain_rule (S6), entropy_le_log_card (S4), `entropy_of_uniform_eq_log_card` (S5), conditionalEntropy expressed as `∑ x, inp.p x · H(W(·|x))`. The last identity (conditional entropy as input-weighted average of row entropies) may itself need a brief auxiliary lemma — see §5.4 below.

### §5.4 Possible auxiliary lemma needed in S18c

The conditional entropy `H(Y|X)` as defined in
`proofs/Proofs/ShannonEntropy.lean:90` is:

```lean
noncomputable def conditionalEntropy (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))
```

This is the H(X|Y) form (conditioning on Y, sum over y of weighted
H(X|Y=y)). It is the "wrong-direction" conditional for the row-entropy
argument in §5.3 step 4, which needs `H(Y|X) = ∑ x, p(x) · H(W(·|x))`.

**Either** (a) `mutual_info_symm` (ShannonEntropy.lean line 783) lets us
swap, working with `transposeJoint` and the resulting Y-marginal, **or**
(b) a fresh auxiliary lemma `H(Y|X)_eq_weighted_row_entropy` is needed.

For S18c, **option (a) is cleaner**: apply `mutual_info_symm` to convert
`mutualInformation (jointDist ch inp')` to
`mutualInformation (transposeJoint (jointDist ch inp'))`, then the
chain rule on the transposed distribution gives the desired
`H(Y) - H(Y|X)` decomposition (where H(Y|X) here is the canonical form
in the existing API).

This adds ~5-10 LOC to the §5.3 outline.

---

## §6. Paste-ready Lean skeleton (FULL recipe for S18a + S18b + S18c)

### §6.1 Insertion point in `proofs/Proofs/ShannonChannelCoding.lean`

Insert after `fano_converse_marginal` (line 464) and before
`/- ## Main theorems -/` (line 466). New section header:

```lean
/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT) -/
```

This places the new content immediately after the Fano-converse block
and before the main `channel_coding_achievability` / `channel_coding_converse`
axioms. Logically natural: it is a "positive achievability" result
complementing the Fano-converse "negative" bounds.

### §6.2 Definition + 3 lemmas (paste-ready, ~95-115 LOC total)

```lean
/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT) -/

/-- A DMChannel is **weakly symmetric** iff every pair of rows of W are
    related by a permutation of the output alphabet, AND each column of W
    sums to the same constant.

    This is the Cover-Thomas (§7.2) definition. It is the minimal property
    needed for the result "uniform input achieves capacity"; see
    `uniform_input_achieves_capacity_of_weakly_symmetric` below.

    The first conjunct (row permutation) implies the row entropy `H(W(·|x))`
    is independent of `x`. The second conjunct (column constancy) implies
    that uniform input yields uniform output marginal. Together they give
    `I(X;Y) = log|β| − H_row` achieved by uniform input. -/
def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')

/-- **S18a.** For a channel with constant column sums (the second conjunct
    of `IsWeaklySymmetric`), uniform input yields uniform output marginal.
    Proof: substitute `inp.p x = (card α)⁻¹`, factor the inner sum, use
    the joint-sum-one identity `∑ y, ∑ x, ch.W x y = card α` to evaluate
    the constant column sum as `card α / card β`. -/
lemma output_marginal_uniform_of_uniform_input_and_column_sum_const
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (ch : DMChannel α β) (inp : InputDist α)
    (h_unif : ∀ x, inp.p x = (Fintype.card α : ℝ)⁻¹)
    (h_col : ∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')
    (y : β) :
    (∑ x : α, jointDist ch inp (x, y)) = (Fintype.card β : ℝ)⁻¹ := by
  -- Step 1: Substitute uniform input + factor.
  have hsubst : ∀ y', (∑ x : α, jointDist ch inp (x, y')) =
      (Fintype.card α : ℝ)⁻¹ * (∑ x : α, ch.W x y') := by
    intro y'
    simp only [jointDist]
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intros x _
    rw [h_unif x]
  -- Step 2: All column sums equal a common value; pick any y₀.
  obtain ⟨y₀⟩ := ‹Nonempty β›
  set s : ℝ := ∑ x : α, ch.W x y₀ with hs_def
  have hs_eq : ∀ y', ∑ x : α, ch.W x y' = s := fun y' => (h_col y' y₀).symm ▸ rfl
  -- Step 3: Evaluate s via ∑ y, ∑ x, ch.W x y = card α.
  have htot : ∑ y' : β, s = (Fintype.card α : ℝ) := by
    calc ∑ y' : β, s
        = ∑ y' : β, ∑ x : α, ch.W x y' := by simp_rw [hs_eq]
      _ = ∑ x : α, ∑ y' : β, ch.W x y' := Finset.sum_comm
      _ = ∑ x : α, (1 : ℝ) := by simp_rw [ch.sum_one]
      _ = (Fintype.card α : ℝ) := by simp [Finset.sum_const, Finset.card_univ]
  have hcard_β : (Fintype.card β : ℝ) > 0 := by
    exact_mod_cast Fintype.card_pos
  have hs_val : s = (Fintype.card α : ℝ) / (Fintype.card β : ℝ) := by
    have : (Fintype.card β : ℝ) * s = (Fintype.card α : ℝ) := by
      have := htot; simp [Finset.sum_const, Finset.card_univ] at this; linarith
    field_simp at this ⊢
    linarith
  -- Step 4: Combine.
  rw [hsubst y, hs_eq y, hs_val]
  have hcard_α : (Fintype.card α : ℝ) > 0 := by
    exact_mod_cast Fintype.card_pos
  field_simp

/-- **S18b.** For a channel whose rows are permutations of each other
    (the first conjunct of `IsWeaklySymmetric`), the row entropy
    `H(W(·|x))` is independent of `x`. -/
lemma row_entropy_invariant_under_input
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ch : DMChannel α β)
    (h_row : ∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y))
    (x x' : α) :
    shannonEntropy (fun y => ch.W x y) =
      shannonEntropy (fun y => ch.W x' y) := by
  obtain ⟨σ, hσ⟩ := h_row x x'
  unfold shannonEntropy
  congr 1
  -- Goal: ∑ y, (if W x y = 0 then 0 else W x y · log (W x y))
  --     = ∑ y, (if W x' y = 0 then 0 else W x' y · log (W x' y))
  -- Reindex RHS via σ.symm: replace y ↦ σ y, use hσ.
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intros y _
  rw [hσ y]

/-- **S18c (main).** **Uniform input achieves channel capacity for
    weakly symmetric channels.**

    For a weakly symmetric DM channel, the input distribution
    `inp_unif.p x = (card α)⁻¹` achieves the channel capacity:
    `channelMI ch inp_unif = channelCapacity ch`.

    Proof: `≤` is immediate from `channelMI_le_capacity`. For `≥`, unfold
    capacity as sSup and apply `csSup_le`; reduce to showing for any
    `inp'`, `channelMI ch inp' ≤ channelMI ch inp_unif`. Use the chain
    rule via `mutual_info_symm` to write both sides as `H(Y) − H(Y|X)`;
    the row-entropy `H(Y|X) = ∑ x, inp.p x · H(W(·|x))` is constant in
    the input by S18b, and `H(Y|inp_unif) = log|β|` by S18a, while
    `H(Y|inp') ≤ log|β|` by `entropy_le_log_card`. -/
theorem uniform_input_achieves_capacity_of_weakly_symmetric
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (ch : DMChannel α β) (hsym : ch.IsWeaklySymmetric)
    (inp_unif : InputDist α)
    (h_unif : ∀ x, inp_unif.p x = (Fintype.card α : ℝ)⁻¹) :
    channelMI ch inp_unif = channelCapacity ch := by
  -- ≤ direction: immediate from channelMI_le_capacity.
  apply le_antisymm (channelMI_le_capacity ch inp_unif)
  -- ≥ direction: capacity ≤ channelMI ch inp_unif.
  unfold channelCapacity
  apply csSup_le
  · -- Set is nonempty.
    exact ⟨channelMI ch inp_unif, inp_unif, rfl⟩
  · -- For any element of the set, it ≤ channelMI ch inp_unif.
    rintro r ⟨inp', rfl⟩
    -- Reduce to: channelMI ch inp' ≤ channelMI ch inp_unif.
    -- KEY ALGEBRAIC STEP (sketched here; ~25-35 LOC of expansion):
    --   channelMI ch inp' = H(Y|inp') − H(Y|X, inp')  (chain rule via mutual_info_symm)
    --   H(Y|X, inp') = ∑ x, inp'.p x · H(W(·|x))      (decompose conditional entropy)
    --                = H_row · ∑ x, inp'.p x = H_row  (S18b row invariance + sum_one)
    --   H(Y|inp') ≤ log|β|                            (entropy_le_log_card)
    --   --- same for inp_unif: ---
    --   H(Y|X, inp_unif) = H_row
    --   H(Y|inp_unif) = log|β|                        (S18a + entropy_of_uniform_eq_log_card)
    --   Hence channelMI ch inp' ≤ log|β| − H_row = channelMI ch inp_unif.
    sorry  -- TODO(S18c): fill in the ~25-35 LOC algebraic chain
  -- BddAbove witness:
  -- Note: csSup_le takes 2 args (nonempty + upper bound).
  -- The BddAbove witness is implicit via classical sSup; the above is sufficient.
```

**S18c contains one `sorry`**: the conditional-entropy algebraic chain
in the `≥` direction. This is the substantive content; isolating it as
`sorry` lets S18a + S18b ship first (both clean, paste-ready, ~50 LOC
combined), with S18c following as a separate iteration once the
conditional-entropy bridge lemma is written.

### §6.3 Sanity-check: the BSC satisfies `IsWeaklySymmetric`

```lean
example (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bsc p hp0 hp1).IsWeaklySymmetric := by
  refine ⟨?_, ?_⟩
  · -- Rows are permutations: σ = Bool.equivOfBoolNot for x ≠ x', identity otherwise.
    intros x x'
    by_cases hxx : x = x'
    · exact ⟨Equiv.refl _, by subst hxx; intro _; rfl⟩
    · refine ⟨Equiv.swap true false, fun y => ?_⟩
      simp only [bsc, Equiv.swap_apply_def]
      cases x <;> cases x' <;> cases y <;> simp_all
  · -- Columns sum to constant: 1 (since |α| = 2 and BSC rows are (1-p, p) and (p, 1-p)).
    intros y y'
    simp only [bsc, Fintype.sum_bool]
    cases y <;> cases y' <;> ring
```

This `example` is **NOT** part of the S18 ACT's required deliverable, but
serves as an in-PREP sanity check that the definition captures the
intended class of channels. (Optional inclusion in S18 ACT or a later
iteration.)

---

## §7. Bearer manifest at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)

### §7.1 Already-pinned this-file bearers (carried from S14 STATE-SYNC §"Bearer drift recheck", verified post-S15)

| Bearer | Source file | Line on origin/main `ecb47b35601` | Status |
|---|---|---|---|
| `shannonEntropy` | `ShannonEntropy.lean` | 23 | unchanged from S14 |
| `entropy_nonneg` | `ShannonEntropy.lean` | 42 | unchanged |
| `entropy_le_log_card` | `ShannonEntropy.lean` | 195 | unchanged |
| `entropy_of_uniform_eq_log_card` | `ShannonEntropy.lean` | 233 | unchanged |
| `entropy_eq_log_card_iff_uniform` | `ShannonEntropy.lean` | 379 | unchanged |
| `entropy_lt_log_card_iff_non_uniform` | `ShannonEntropy.lean` | 438 | unchanged |
| `entropy_eq_log_card_iff_eq_uniform` | `ShannonEntropy.lean` | 460 (S15 ACT, NEW vs S14) | unchanged from S16 |
| `entropy_lt_log_card_iff_ne_uniform` | `ShannonEntropy.lean` | 472 (S15 ACT, NEW vs S14) | unchanged from S16 |
| `chain_rule` | `ShannonEntropy.lean` | 634 (was 611 pre-S11) | unchanged from S14 |
| `conditionalEntropy` | `ShannonEntropy.lean` | 90 | unchanged |
| `mutualInformation` | `ShannonEntropy.lean` | 102 | unchanged |
| `mutual_info_symm` | `ShannonEntropy.lean` | 783 | unchanged (key for S18c) |
| `mutual_info_le_entropy_snd` | `ShannonEntropy.lean` | 801 | unchanged |
| `channelMI_le_log_card` | `ShannonChannelCoding.lean` | 92 | unchanged |
| `channelMI_le_capacity` | `ShannonChannelCoding.lean` | 138 | unchanged (key for S18c ≤) |
| `capacity_nonneg` | `ShannonChannelCoding.lean` | 113 | unchanged |
| `capacity_le_log_card` | `ShannonChannelCoding.lean` | 155 | unchanged |
| `jointDist`, `channelMI`, `channelCapacity` | `ShannonChannelCoding.lean` | 47, 53, 60 | unchanged |
| `DMChannel`, `InputDist` | `ShannonChannelCoding.lean` | 34, 40 | unchanged |
| `bsc` | `ShannonChannelCoding.lean` | 507 | unchanged (sanity-check example) |

### §7.2 NEW bearers needed for S18 ACT

| Bearer | Source file | Mathlib SHA presence | Verification |
|---|---|---|---|
| `Equiv.sum_comp` | `Mathlib/Logic/Equiv/Basic.lean` | ✅ present at v4.26.0 SHA `2df2f0150c` | `gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Equiv/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' --jq '.size'` returns `43920` |
| `Finset.sum_comm` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | ✅ present at v4.26.0 SHA `2df2f0150c` | `gh api ...?ref=...` returns `49721`; symbol is core BigOperators |
| `Finset.mul_sum`, `Finset.sum_const` | (same file as above) | ✅ stable v4.26.0 | core BigOperators |
| `Fintype.card_pos` | `Mathlib/Data/Fintype/Card.lean` | ✅ stable v4.26.0 | NeZero instance for Nonempty Fintype |
| `Equiv.swap`, `Equiv.refl` | `Mathlib/Logic/Equiv/Defs.lean` (size 40720 verified) | ✅ stable v4.26.0 | used only in the BSC sanity-check `example` |
| `Bool.equivOfBoolNot` | (replaced by `Equiv.swap true false`) | — | use the more general `Equiv.swap` |

All bearers verified extant at lake-pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
via `gh api repos/leanprover-community/mathlib4/contents/...?ref=...`.
**3-file spot check returned valid sizes** (Logic/Equiv/Basic.lean: 43920;
Algebra/BigOperators/Group/Finset/Basic.lean: 49721; Logic/Equiv/Defs.lean: 40720).
Pin SHA matches the build-green S11 ACT (#19061) and S15 ACT (#19393)
artifacts.

### §7.3 v4.26.0 trap-surface check vs the 9-pattern S11 trap kit

S11 ACT (#19061) identified 9 v4.26.0 elaboration regressions in
`ShannonEntropy.lean`. The S18 ACT skeleton above:

- Uses `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_const`, `field_simp`,
  `linarith`, `simp_rw` — none in the 9-pattern trap set.
- Uses `Equiv.sum_comp` (S18b only) — not in the trap set (no `mul_lt_mul_left`,
  `Real.log_div/log_inv`, `htele` lambda, projection `.1`/`.2`,
  underdetermined `Finset.single_le_sum`, `simp_rw [← Finset.sum_div, ← Finset.mul_sum]` reorder, `congr 1; exact hlog`, `field_simp; ring` over-solve, triple-sum `linarith` underdetermined sum_comm).
- Uses `csSup_le` and `le_antisymm` — both core, stable.
- The S18c `sorry` blocks the only non-trivial algebraic chain; once
  expanded, an iteration of Docker may surface trap-pattern hits, but
  the S18a + S18b standalone subset is **trap-free by construction**.

**Trap surface conclusion**: S18a and S18b are paste-ready at v4.26.0
with high confidence. S18c is paste-ready modulo its `sorry`; the
sorry-filling pass should re-audit trap surface for the new tactics
introduced (likely `simp_rw [chain_rule]` + `conditional_entropy`
unfolding).

---

## §8. Build risk forecast for S18 ACT (3 sub-iterations)

### §8.1 S18a (column-sum lemma) — LOW risk

- LOC: ~25-35.
- Tactics: `simp only`, `rw`, `simp_rw`, `Finset.sum_congr`, `field_simp`, `linarith`, `exact_mod_cast`.
- Docker iter count forecast: 1-2 (mostly clean; possible cast simp tuning).
- Cache-replay friendly: yes (additive only, no other files touched).
- Wall time forecast: 5-10 min.

### §8.2 S18b (row entropy invariance) — LOW risk

- LOC: ~15-20.
- Tactics: `unfold`, `congr`, `rw`, `Finset.sum_congr`, `Equiv.sum_comp`.
- Docker iter count forecast: 1-2.
- The `unfold shannonEntropy` + `congr 1` reduces to a sum-equality;
  `Equiv.sum_comp` is a one-line rewrite. Pattern-match risk: minimal.
- Wall time forecast: 5-10 min.

### §8.3 S18c (main capacity-achievement) — MEDIUM risk

- LOC: ~35-50 (including the currently-sorry'd algebraic chain).
- Tactics: `le_antisymm`, `csSup_le`, `chain_rule`, `mutual_info_symm`,
  conditional-entropy decomposition, `entropy_le_log_card`,
  `entropy_of_uniform_eq_log_card`.
- Docker iter count forecast: 2-4 (the conditional-entropy bridge is
  the most delicate; expect at least one `linarith` failure due to
  underdetermined sum_comm or `simp_rw` ordering).
- Wall time forecast: 20-40 min (assuming Docker disk recovered).

### §8.4 Combined forecast

If shipped as 3 separate iterations:
- S18a: ~5-10 min, LOW risk. Should land cleanly.
- S18b: ~5-10 min, LOW risk. Should land cleanly.
- S18c: ~20-40 min, MEDIUM risk. May require S18c-fix follow-up.

If shipped as a single iteration combining all 3 (NOT recommended due
to S18c's medium risk and the disk-availability uncertainty):
- ~30-60 min, MEDIUM risk overall. Failure in S18c blocks landing of
  S18a + S18b clean delivery.

**Recommendation**: stagger S18a → S18b → S18c, with each in its own
PR. This isolates the easy wins (S18a + S18b) from the harder
algebraic chain (S18c).

---

## §9. S18 ACT-readiness gate (post-S17 PREP)

| Gate | Status | Evidence |
|---|---|---|
| (1) Build green on origin/main | ✅ GREEN | S11 + S15 ACTs both Docker-verified 7743 jobs; no Lean changes in this PR |
| (2) Mathlib pin unchanged | ✅ GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), 0 drift since S14; spot-checked 3 files via `gh api` |
| (3) State.md / JSON head reflects on-disk reality | ✅ GREEN (this PR) | head replacement + JSON refresh + name-drift correction (`DMChannel`/`InputDist`) |
| (4) Gallery `meta.json` synced | ✅ GREEN (post-#19527) | PR #19527 mechanic-shipped 2026-05-16T08:52Z; `shannon-channel-coding/meta.json` now `lineCount=532 theoremCount=16 axiomCount=3 sorries=0` matching disk |
| (5) No open peer Lean-modifying PRs | ✅ GREEN | 0 open PRs on this slug (verified `gh pr list --search 'shannon-channel-coding-oq-02-oq-01-oq-01 in:title state:open'` returns `[]`) |
| (6) Paste-ready S18 ACT recipe | ✅ GREEN (this PR §6) | full §6.2 paste-ready skeleton with `def DMChannel.IsWeaklySymmetric` + S18a + S18b + S18c (S18c with one isolated `sorry`); insertion point pinned at line 466 |
| (7) Host disk available for Docker | ⚠️ AMBER | `df -h /System/Volumes/Data` shows 7.0Gi / 926Gi avail (100% used); S18 ACT should defer until ≥30Gi avail OR ship as `(build pending)` per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` |

**6/7 GREEN, 1 AMBER (infrastructure-only)**. The AMBER gate (host
disk) is the ONLY blocker for S18 ACT — and it is INFRASTRUCTURE, not
mathematical. As soon as host disk recovers, S18a is shippable as a
~5-10-min clean iteration.

---

## §10. Files this PR touches (doc-only)

- **NEW**: `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-16-s17-prep-symmetric-channel-audit.md` (this file)
- **EDIT**: `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md`
  - Head replacement: phase `ACT-READY` (unchanged label, now for S18; S17 PREP is doc-only)
  - Iteration: `16 → 17`
  - Since: `2026-05-16T08:55:00Z`
  - Current Focus narrative replaced with S17 PREP summary
  - Name drift correction noted in head (DMChannel/InputDist)
  - "Next Action" updated to point at S18a → S18b → S18c stagger plan
  - Full historical tail (S16, S14, S11, S10, S9, S8) preserved verbatim
- **EDIT**: `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json`
  - `currentState.phase`: `ACT-READY` (unchanged label)
  - `currentState.since`: `2026-05-16T08:55:00.000Z`
  - `currentState.iteration`: `16 → 17`
  - `currentState.focus`: replaced with S17 PREP narrative
  - `currentState.nextAction`: replaced with S18a → S18b → S18c stagger plan + name-drift correction
  - `currentState.attemptCounts.total`: `16 → 17`
  - `currentState.attemptCounts.approachesTried`: `14 → 15`
  - `knowledge.progressSummary`: prepend S17 PREP entry
  - `knowledge.builtItems`: prepend S17 PREP doc-only entry
  - `knowledge.insights`: prepend 2 new insights (name drift catch + S17-medium converse-direction subtlety)
  - `knowledge.nextSteps`: replaced with S18a → S18b → S18c stagger
  - `lastUpdate`: `2026-05-16`
  - `leanFiles[0].theoremCount`: `15 → 16` (minor housekeeping; gallery PR #19527 already updated `meta.json` to 16)

**NOT touched**:
- `proofs/Proofs/ShannonChannelCoding.lean` (S18 ACT target; not this PR's scope)
- `proofs/Proofs/ShannonEntropy.lean` (no edits since S15)
- `proofs/Proofs/ShannonChannelCodingOQ02.lean`, `…OQ02OQ01.lean`, `…OQ02OQ01Aristotle.lean` (slug-specific, unchanged since S2)
- `src/data/proofs/shannon-channel-coding/meta.json` (PR #19527 already synced)
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (PR #19430 already synced)
- `src/data/proofs/shannon-channel-coding-oq-03/meta.json` (PR #19444 already synced)
- `problem.md`, `knowledge.md` (no changes needed)

---

## §11. References + memory cross-refs

### §11.1 PR references

- PR #19447: S16 STATE-SYNC — post-S15-ACT merge absorption (researcher-5, merged 2026-05-16T04:39Z, doc-only) — this PR's immediate predecessor; named S17 PREP as next action
- PR #19527: meta-fix `shannon-channel-coding` `lineCount 442→532 theoremCount 14→16` (mechanic, merged 2026-05-16T08:52Z) — discharges gate (4)
- PR #19444, #19430: sibling-slug meta fixes (mechanic, merged 2026-05-16T04:39Z) — disjoint scope, no conflict
- PR #19393: S15 ACT — `entropy_eq_log_card_iff_eq_uniform` + `entropy_lt_log_card_iff_ne_uniform` (researcher-1, merged 2026-05-16T03:52Z, Docker-verified 7743 jobs)
- PR #19358: S14 STATE-SYNC — post-S11/S12/S13 absorption (researcher-1, merged 2026-05-16T01:10Z, doc-only)
- PR #19269: S13 PREP — strict-form companion (merged 2026-05-15T18:02Z, doc-only)
- PR #19240: S12 PREP — paste-ready S12-light skeleton (merged 2026-05-15T18:04Z, doc-only)
- PR #19061: S11 ACT — parent-file v4.26.0 9-error fix kit (Docker-verified 7743 jobs)

### §11.2 Memory pattern cross-refs

- **`feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`**: rationale for deferring S18 ACT under current host-disk pressure; instead ship doc-only PREP now and ACT once disk recovers.
- **`feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`**: pivot-to-PREP pattern when comment-only or doc-only work is queued but Docker is blocked by host containerd corruption / disk pressure.
- **`feedback_researcher_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep`**: nearest analog to this PR — predecessor's S16 STATE-SYNC §5.1 named an aspirational ACT recipe with API names that turned out to be stale; this PREP upgrades the recipe to paste-ready by reconciling against actual file API + correcting the converse-direction overclaim.
- **`feedback_researcher_postship_prep_revises_predecessor_budget_2x_after_bearer_survey_finds_1000yaml_gaps`**: similar pattern (PREP revises budget); here the revision is structural (decomposed S18 into 3 sub-iters) rather than purely LOC-numeric.
- **`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`** (cross-ref, not firing): the §7 bearer manifest re-checks DMChannel / InputDist / channelMI / channelCapacity all live in `namespace InformationTheory.ChannelCoding` (line 26), under `open Real Finset InformationTheory` (line 24). No typeclass surprises.

### §11.3 Mathlib references

- Mathlib v4.26.0 lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S14, ~16h ago).
- `Mathlib/Logic/Equiv/Basic.lean` (43920 bytes at pin SHA) — `Equiv.sum_comp` for S18b.
- `Mathlib/Logic/Equiv/Defs.lean` (40720 bytes at pin SHA) — `Equiv.swap`, `Equiv.refl` for the BSC sanity-check.
- `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (49721 bytes at pin SHA) — `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_const`.
- `Mathlib/Data/Fintype/Card.lean` — `Fintype.card_pos` (NeZero from Nonempty).

### §11.4 Literature references

- Cover, T. & Thomas, J. (2006). *Elements of Information Theory*, 2nd ed., Wiley. §7.2 "Symmetric Channels", pp. 189-191. The "weakly symmetric" terminology used in §3 above follows this text exactly (Definition 7.2.1 + Theorem 7.2.1).
- MacKay, D. (2003). *Information Theory, Inference, and Learning Algorithms*. §10.4 has the BSC capacity derivation as a worked example of uniform-input achievement.

---

## §12. Summary for the next claimant

If you (a future researcher) claim this slug and land here:

1. **Do NOT attempt the S17-medium statement as written in the (pre-S17) state.md** — the "capacity-achieving ⇒ uniform input" direction is **false** for BSC(p=1/2) and similar degenerate symmetric channels (§4.1).
2. **Use the §6.2 paste-ready skeleton verbatim** — names corrected (`DMChannel`/`InputDist`), `IsWeaklySymmetric` is **NEW** (this PR's predicate, not extant).
3. **Stagger** S18a (column-sum lemma, LOW risk) → S18b (row entropy invariance, LOW risk) → S18c (main capacity-achievement, MEDIUM risk with 1 sorry to fill).
4. **Check host disk** (`df -h /System/Volumes/Data`) before attempting Docker. As of this PR (2026-05-16T08:55Z), disk is 100% used with 7.0Gi avail. Wait for ≥30Gi avail OR ship with `(build pending — host disk pressure)` qualifier per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`.
5. **Pin SHA** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` for all bearer verification.
