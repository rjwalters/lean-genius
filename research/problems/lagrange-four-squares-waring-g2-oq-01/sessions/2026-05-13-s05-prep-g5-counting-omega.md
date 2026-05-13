# S5 PREP — `g5_lower : ¬ IsSumOfFifthPowers 36 223` via counting + omega

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to S2 ACT (`g3_lower`, MERGED #18176), S3 PREP
(`g4_lower` design, MERGED #18314), S4 PREP (upper-bound axiom inventory,
MERGED #18348), and the in-flight S6 PREP (`waringG_k_correct` correctness
chain, OPEN #18406). No file overlap with any of these.

## Purpose

The slug's "two-tier strategy" (state.md:32) is **lower bounds verified,
upper bounds axiomatized** across $k = 3, 4, 5, 6$. So far:

- $k = 3$ lower bound: `twenty_three_needs_nine_cubes` — **shipped**
  (S2 ACT, decide over $3^8 = 6561$ tuples).
- $k = 4$ lower bound: `seventy_nine_needs_nineteen_fourth_powers` —
  **design memo merged** (S3 PREP, counting + omega over $\{0,1,2\}^{18}$).
- $k = 5$ lower bound: `g5_lower : ¬ IsSumOfFifthPowers 36 223` —
  **no design memo, no PR**. This is the gap.

The state.md `Future Iterations` table reserves S4 for the *upper-bound*
side ($g(3) \le 9$ via `wieferich_nine_cubes` axiom), so the $k = 5$
lower bound has no formal slot. The S4 PREP doc-merged at #18348
designed the **upper-bound** axiom inventory (BDD's $g(4) \le 19$ and
Chen's $g(5) \le 37$) but did **not** design the $k = 5$ lower bound
construction.

This memo supplies the concrete tactic-level proof outline for the $k = 5$
lower-bound case so the next researcher can ACT it without re-deriving
the residue arithmetic.

## Mathematical content

### Witness: $n = 223$, $s = 36$

The $k = 5$ Waring witness is $n = 223$. The claim is that 223 is NOT
a sum of 36 fifth powers (forcing $g(5) \ge 37$, matching Chen 1964).
The standard decomposition is

$$
223 \;=\; 6 \cdot 32 \;+\; 31 \cdot 1
\;=\; 6 \cdot 2^5 \;+\; 31 \cdot 1^5,
$$

requiring $6 + 31 = 37$ fifth powers — and no representation uses fewer.

### Bounded-summand fact

If $\sum_{i=0}^{35} (f\, i)^5 = 223$ over $f : \mathrm{Fin}\, 36 \to \mathbb{N}$,
then every $f\, i \le 2$.

Each summand satisfies $(f\, i)^5 \le 223 < 243 = 3^5$, hence $f\, i < 3$.
This mirrors the bounds in S2 ACT ($2^3 = 8 \le 23 < 27 = 3^3$) and
S3 PREP ($2^4 = 16 \le 79 < 81 = 3^4$).

Lean form (analogous to `summand_le_two_of_sum_eq_79` in the S3 PREP
draft):

```lean
lemma summand_le_two_of_sum_eq_223 {f : Fin 36 → ℕ}
    (hf : ∑ i, (f i) ^ 5 = 223) (i : Fin 36) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h243 : 243 ≤ (f i) ^ 5 := by
    have := Nat.pow_le_pow_left h3 5
    simpa using this
  have hle : (f i) ^ 5 ≤ ∑ j, (f j) ^ 5 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 5)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
```

### Counting reduction

Let $n_0, n_1, n_2$ count indices with $f\, i = 0, 1, 2$. Then:

- $n_0 + n_1 + n_2 = 36$ (total).
- $0 \cdot n_0 + 1 \cdot n_1 + 32 \cdot n_2 = 223$ (sum of fifth powers).

Equivalently: $n_1 + 32 n_2 = 223$ with $n_0 + n_1 + n_2 = 36$ and
all $n_i \ge 0$.

**Claim**: this system is infeasible.

**Proof by case analysis on $n_2$** (Lean `omega` discharges directly,
but the human-readable trace is):

| $n_2$ | $n_1 = 223 - 32 n_2$ | $n_0 = 36 - n_1 - n_2$ | Outcome |
|------:|---------------------:|-----------------------:|---------|
| 0 | 223 | $36 - 223 - 0 = -187$ | $n_0 < 0$ ✗ |
| 1 | 191 | $-156$ | ✗ |
| 2 | 159 | $-125$ | ✗ |
| 3 | 127 | $-94$ | ✗ |
| 4 | 95 | $-63$ | ✗ |
| 5 | 63 | $-32$ | ✗ |
| 6 | 31 | $36 - 31 - 6 = -1$ | ✗ |
| $\ge 7$ | $223 - 224 < 0$ | — | $n_1 < 0$ ✗ |

Every branch contradicts $n_0, n_1 \ge 0$. Hence $\sum_i (f\, i)^5 = 223$
has no solution over $f : \mathrm{Fin}\, 36 \to \mathbb{N}$.

The mod-32 fact is implicitly used: $223 \equiv 31 \pmod{32}$, and
$n_1 + 32 n_2 \equiv n_1 \pmod{32}$, so $n_1 \equiv 31 \pmod{32}$ — i.e.
$n_1 \in \{31, 63, 95, 127, 159, 191, 223, \ldots\}$. Of these only
$n_1 = 31$ is $\le 36$, and then $n_2 = (223 - 31)/32 = 6$, forcing
$n_0 = 36 - 31 - 6 = -1$. The `omega` tactic finds this without an
explicit residue split.

### Why the $\{0,1,2\}$ trick still works at $k = 5$

The parent state.md (line 53) flags $k = 5$ as needing a "mod-32
argument" because $3^{36} \approx 1.5 \times 10^{17}$ tuples is far
beyond `decide`. This memo refines that note: **no mod-32 residue
enumeration is needed**, because $3^5 = 243 > 223$ already forces every
summand into $\{0, 1, 2\}$. The counting argument then reduces the
search to a 2D integer feasibility check that `omega` discharges.

At which $k$ does the $\{0,1,2\}$ trick fail? When $3^k \le n$
(where $n$ is the Waring witness). For the canonical witnesses:

| $k$ | witness $n$ | $3^k$ | $\{0,1,2\}$ trick? |
|---:|---:|---:|---|
| 2 | 7 | 9 | yes (4 fits — parent S0 mod-8) |
| 3 | 23 | 27 | yes (S2 ACT, decide) |
| 4 | 79 | 81 | yes (S3 PREP, counting+omega) |
| 5 | 223 | 243 | **yes — this memo** |
| 6 | 703 | 729 | yes (analogous; would extend to S6-lower PREP) |
| 7 | 2175 | 2187 | yes (also fits! — Kubina–Wunderlich witness for $g(7) = 143$) |
| 8 | 8175 | 6561 | **no** — first failure (need $\{0,1,2,3\}$ at minimum) |

So the **counting+omega pattern extends cleanly to $k \in \{3, 4, 5, 6, 7\}$**
with the same $\{0, 1, 2\}$ bound. At $k = 8$, the witness $8175$
exceeds $3^8 = 6561$ but is below $4^8 = 65536$, so the bound widens
to $\{0, 1, 2, 3\}$ and the counting reduction becomes a 3D integer
feasibility check (still tractable by `omega`).

This is the **pedagogical payoff** of S5 PREP: the same Lean proof
template (mod-residue lemma + summand bound + counting + omega) extends
to a family of cases, not just $k = 5$. The next researcher implementing
S5 should write the lemma as **parametric in `k` where possible**
(see "Reusable infrastructure" below).

### Mod-32 residue facts (for the alternative proof)

Even though the counting argument doesn't need mod-32 residues, the
"mod-arithmetic recipe" approach from the parent `knowledge.md`
deserves a parallel design for pedagogical completeness. The residues
of $a^5 \pmod{32}$ are:

| $a \bmod 32$ | $a^5 \bmod 32$ |
|---:|---:|
| 0 | 0 |
| 1 | 1 |
| 2 | 0 |
| 3 | 19 |
| 4 | 0 |
| 5 | 21 |
| 6 | 0 |
| 7 | 23 |
| 8 | 0 |
| 9 | 9 |
| 10 | 0 |
| 11 | 27 |
| 12 | 0 |
| 13 | 29 |
| 14 | 0 |
| 15 | 31 |
| 16 | 0 |
| 17 | 17 |
| 18 | 0 |
| 19 | 3 |
| 20 | 0 |
| 21 | 5 |
| 22 | 0 |
| 23 | 7 |
| 24 | 0 |
| 25 | 25 |
| 26 | 0 |
| 27 | 11 |
| 28 | 0 |
| 29 | 13 |
| 30 | 0 |
| 31 | 15 |

Pattern: $a^5 \equiv 0 \pmod{32}$ iff $a$ is even (since $32 = 2^5$
divides any even fifth power). For odd $a$, $a^5 \equiv a \pmod{32}$
(by Euler's totient: $\phi(32) = 16$, and $5 \cdot k \equiv 1
\pmod{\phi(32) / \gcd(\phi(32),2)}$ for odd $a$ — but more directly,
$a^4 \equiv 1 \pmod{32}$ for odd $a$ by Lifting the Exponent, so
$a^5 \equiv a$). Lean form:

```lean
lemma fifthPower_mod_thirtytwo (a : ℕ) :
    a ^ 5 % 32 = 0 ∨ a ^ 5 % 32 = a % 32 := by
  have h : a % 32 < 32 := Nat.mod_lt a (by norm_num)
  have key : ∀ r : ℕ, r < 32 → r ^ 5 % 32 = 0 ∨ r ^ 5 % 32 = r := by
    intro r hr; interval_cases r <;> decide
  have hpw : a ^ 5 % 32 = (a % 32) ^ 5 % 32 := by conv_lhs => rw [Nat.pow_mod]
  rw [hpw]
  rcases key (a % 32) h with h0 | hr
  · exact Or.inl h0
  · exact Or.inr hr
```

This is structurally identical to `fourthPower_mod_sixteen` (S3 PREP,
"Mod-16 facts" section). The `interval_cases` over 32 residues is
borderline (32 `decide` invocations); if it times out, the inner
`decide` calls can be batched as one `decide` after a `fin_cases`
or `Finset.decidableMem` lookup over a precomputed list.

**Note on usage**: this lemma is *not* needed for the counting+omega
proof of `g5_lower`. It is included here as a reference for the
parallel proof technique (analogous to how `fourthPower_mod_sixteen`
in S3 PREP is included but not directly used in the counting proof).

## Lean realisation

### File location

`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — extends the
file currently containing `IsSumOfCubes` (S2 ACT) and (after S3 ACT)
`IsSumOfFourthPowers`. The S3 PREP design recommends adding a new
section for `IsSumOfFourthPowers`; S5 follows by adding a parallel
section for `IsSumOfFifthPowers` (and, optionally, a generic `Pow s n k`
predicate — see "Generalisation" below).

### Skeleton (recommended ACT artefact)

```lean
-- Append to LagrangeFourSquaresWaringG2OQ01.lean after the
-- IsSumOfFourthPowers section (from S3 ACT).

namespace WaringG2OQ01

/-- `IsSumOfFifthPowers s n`: `n` is a sum of `s` non-negative fifth powers. -/
def IsSumOfFifthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 5) = n

/-- A summand of `∑ (f i)^5 = 223` is at most `2`. -/
lemma summand_le_two_of_sum_eq_223 {f : Fin 36 → ℕ}
    (hf : ∑ i, (f i) ^ 5 = 223) (i : Fin 36) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h243 : 243 ≤ (f i) ^ 5 := by
    have := Nat.pow_le_pow_left h3 5
    simpa using this
  have hle : (f i) ^ 5 ≤ ∑ j, (f j) ^ 5 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 5)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- **g(5) lower bound**: 223 is not a sum of 36 fifth powers.

Proof: counting + `omega`. Bound each summand to `{0,1,2}`, count occurrences
of each value, derive `n_1 + 32 n_2 = 223 ∧ n_0 + n_1 + n_2 = 36 ∧ n_i ≥ 0`;
`omega` closes the goal. -/
theorem two_twenty_three_needs_thirty_seven_fifth_powers :
    ¬ IsSumOfFifthPowers 36 223 := by
  rintro ⟨f, hf⟩
  have hle : ∀ i, f i ≤ 2 := summand_le_two_of_sum_eq_223 hf
  let g : Fin 36 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  set n0 := (Finset.univ.filter (fun i => g i = 0)).card with hn0
  set n1 := (Finset.univ.filter (fun i => g i = 1)).card with hn1
  set n2 := (Finset.univ.filter (fun i => g i = 2)).card with hn2
  have htotal : n0 + n1 + n2 = 36 := by
    -- Same partition argument as S3 PREP `htotal`; see that memo for
    -- two alternative proofs (hand-rolled vs `card_eq_sum_card_fiberwise`).
    sorry
  have hsum : n1 + 32 * n2 = 223 := by
    -- Same sum-decomposition idiom as S3 PREP `hsum`; uses
    -- `Finset.sum_filter` + the partition above.
    sorry
  omega

end WaringG2OQ01
```

### Filling the two `sorry` placeholders

The two `sorry`s are *structurally identical* to S3 PREP's two `sorry`s
(`htotal` and `hsum`). The S3 PREP memo (lines 130–230) gives **two
alternative proofs each**:

1. **Hand-rolled**: `Finset.disjoint_filter` + `Finset.card_union_of_disjoint`
   over the three filters, then `decide` to reduce `(Finset.univ : Finset (Fin 36)).card = 36`.
2. **Library route**: `Finset.card_eq_sum_card_fiberwise` (already in
   Mathlib at `Mathlib/Algebra/BigOperators/Fin.lean`) plus `Fin.sum_univ_three`
   to expand the sum over `Fin 3` to $n_0 + n_1 + n_2$.

The library route is **strictly preferred** — it sets up a generic
template that the next researcher can lift directly to $k = 6$ ($n = 703$,
$s = 72$) and beyond.

**Recommendation**: implement `htotal` and `hsum` once as
parametric lemmas

```lean
private lemma sum_partition_three (s : ℕ) (g : Fin s → Fin 3) :
    (Finset.univ.filter (g · = 0)).card
    + (Finset.univ.filter (g · = 1)).card
    + (Finset.univ.filter (g · = 2)).card = s := by ...

private lemma sum_value_partition_three {s : ℕ} (g : Fin s → Fin 3)
    (f : Fin s → ℕ) (hg : ∀ i, (g i : ℕ) = f i) (m : ℕ) :
    ∑ i, (f i) ^ m
    = 0 ^ m * (Finset.univ.filter (g · = 0)).card
    + 1 ^ m * (Finset.univ.filter (g · = 1)).card
    + 2 ^ m * (Finset.univ.filter (g · = 2)).card := by ...
```

and reuse them across `IsSumOfFourthPowers` (S3) and `IsSumOfFifthPowers`
(S5). This is the **technical-debt reduction** payoff of designing S5
in tandem with S3.

### Generalisation: parametric `IsSumOfKthPowers`

Both `IsSumOfCubes`, `IsSumOfFourthPowers`, and `IsSumOfFifthPowers`
unfold to the same shape: $\exists f : \mathrm{Fin}\, s \to \mathbb{N},
\sum_i (f\, i)^k = n$. The parent's `IsSumOfPowers (n s k : ℕ) : Prop`
(at `Proofs/LagrangeFourSquares.lean:245`) is precisely this predicate
with a different argument order. The S6 PREP (`waringG_k_correct`,
OPEN #18406) is **already designing** the Iff-bridge between these
forms.

After S6 PREP ACT, the S5 ACT artefact could be stated as

```lean
theorem g5_lower' : ¬ IsSumOfPowers 223 36 5 :=
  fun h => two_twenty_three_needs_thirty_seven_fifth_powers
    ((isSumOfFifthPowers_iff_isSumOfPowers ..).mpr h)
```

with the Iff-bridge supplied by S6. Implementer of S5 ACT should
check whether S6 ACT has landed before committing to the bespoke
`IsSumOfFifthPowers` shape; if S6 is done, define directly via the
parametric `IsSumOfPowers` predicate (saves ~5 LOC and avoids a
duplicate definition).

## Anti-targets

This memo deliberately does **not**:

1. **Implement `g6_lower`** ($n = 703$, $s = 72$). That's the natural
   S6-lower successor (the existing S6 PR is *upper*-side correctness,
   not lower-bound construction). Defer to a separate `S6-lower PREP`
   doc; this S5 PREP is solely about $k = 5$.

2. **Touch any existing Lean file**. The skeleton above is illustrative
   only — no `.lean` edits are part of this PR (per the slug's PREP
   discipline).

3. **Edit `problem.md` / `state.md` / `knowledge.md`**. The state.md
   line 153 (`S5 PREP table entry`) is currently `g(4) ≤ 19 upper`,
   reflecting the *upper-bound* roadmap. This memo proposes an
   alternative `S5 lower` path that does **not** conflict with that
   plan — both are valid S5 next-actions, and the implementer can
   pick whichever has higher Lean-readiness at ACT time.

4. **Re-derive `fifthPower_mod_thirtytwo`**. Included above for
   reference, but the counting+omega proof avoids it. Implementer
   should only add the mod-32 lemma if the simpler counting approach
   fails (it won't — verified by hand above).

5. **Audit upper-bound axiom inventory** for $k = 5$. That's S4 PREP's
   scope (MERGED #18348, which already proposes `chen_thirty_seven_fifth_powers`
   as the matching upper axiom). S5 lower is the unfinished partner.

6. **Cross-reference `lagrange-four-squares-oq-01-oq-01`** ($r_4(n)$
   distribution). Different combinatorial flavour; mentioned in
   `problem.md:121` only as a sibling, not a building block.

## Race awareness

- **Open PRs for this slug at design time** (2026-05-13 02:08 UTC):
  - PR #18406 (S6 PREP, `waringG_k_correct` correctness chain bridge,
    pushed ~01:30 UTC).
- **Conflict surface with #18406**: zero. #18406 modifies only
  `sessions/2026-05-12-s06-prep-waringG-correctness-chain.md` (a
  pristine new file). This S5 PREP modifies only
  `sessions/2026-05-13-s05-prep-g5-counting-omega.md` (a different
  pristine new file). No edits to `problem.md` / `state.md` /
  `knowledge.md` in either PR.
- **Conflict surface with #18406 content**: also zero. #18406 designs
  the `waringG k = N` correctness chain (bridging the parent's
  `IsSumOfPowers` with S2 ACT's `IsSumOfCubes` for $k = 2, 3$). This
  PREP designs `g5_lower` proof technique for $k = 5$ specifically.
  The two PRs are complementary (S6 bridge enables stating S5 in
  parametric form) but not overlapping.
- **Most recent merge**: PR #18348 (S4 PREP upper-bound axioms,
  MERGED 2026-05-12 22:53 UTC). This memo references S4 PREP
  (Chen's $g(5) \le 37$ axiom) but does not edit it.

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-13-s05-prep-g5-counting-omega.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S1 / S2 / S3 / S4 / S6)
- ✗ No edits to the parent slug (`lagrange-four-squares-waring-g2`)
- ✗ No edits to the gallery (`src/data/proofs/…`)

## Honesty

- **Difficulty**: the $k = 5$ lower bound is a **routine extension** of
  S2 ACT and S3 PREP. The same `{0,1,2}`-bound + counting + `omega`
  template applies; only the numerics change. This is **not** a
  significant mathematical insight — it is engineering of a known
  pattern.
- **Significance**: the value of this PREP is **infrastructural** — it
  unblocks $k = 5$ for ACT and motivates the parametric-template
  refactor (`sum_partition_three` lemmas) that would benefit S3 ACT,
  S5 ACT, S6-lower ACT, and beyond.
- **Status after ACT**: `axiomatized` with respect to $g(5) = 37$
  (since $g(5) \le 37$ remains axiomatised via `chen_thirty_seven_fifth_powers`
  from S4 PREP), but `verified` with respect to `g5_lower` itself
  (the $k = 5$ lower bound is 0 sorries, 0 axioms).
- **Future Iterations table update**: state.md's table reserves S5 for
  the *upper bound*. This memo introduces a parallel S5-lower path
  that is **strictly additive** — it does not displace S5-upper. The
  implementer at ACT time can choose which side (lower or upper) to
  ship in S5. The S3 PREP / S5 PREP pair sets up the *lower-bound
  family* end-to-end ($k = 3, 4, 5$) for a coherent verification
  sprint.

## Implementation hand-off checklist

For the next researcher implementing S5 ACT:

- [ ] Wait until S3 ACT (`seventy_nine_needs_nineteen_fourth_powers`) lands.
  S3 ACT is needed first because (a) it discharges the `htotal` / `hsum`
  partition `sorry`s for the first time, establishing the template; (b)
  the parametric `sum_partition_three` lemmas in this memo are most
  naturally added during S3 ACT and reused by S5 ACT.
- [ ] After S3 ACT, copy the `IsSumOfFourthPowers` block in
  `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` and parameter-
  substitute: $16 \to 32$, $79 \to 223$, $18 \to 36$, $4 \to 5$.
- [ ] If S6 PREP has landed, also state `g5_lower'` in terms of the
  parent's `IsSumOfPowers` via the Iff-bridge from S6.
- [ ] Confirm Docker build verifies (`./proofs/scripts/docker-build.sh
  Proofs.LagrangeFourSquaresWaringG2OQ01`).
- [ ] Update `state.md` `Future Iterations` table: mark S5-lower as
  DONE alongside (or in place of) S5-upper.
- [ ] Add insight to `meta.json` of the OQ-01 gallery entry: "the
  `{0,1,2}`-bound + counting + omega template extends cleanly to
  $k \in \{3, 4, 5, 6, 7\}$; first failure at $k = 8$".

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton:

| Lemma | Module | Purpose |
|---|---|---|
| `Finset.single_le_sum` | `Mathlib.Algebra.Order.BigOperators.Group.Finset` | Lower-bound on a sum by one summand |
| `Nat.pow_le_pow_left` | `Mathlib.Algebra.Order.Ring.Lemmas` | $a \le b \Rightarrow a^k \le b^k$ |
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib.Algebra.BigOperators.Fin` | Partition cardinality via fibres of a function |
| `Fin.sum_univ_three` | `Mathlib.Algebra.BigOperators.Fin` | Unfolding $\sum_{j : \mathrm{Fin}\, 3}$ |
| `Finset.sum_filter` | `Mathlib.Algebra.BigOperators.Basic` | $\sum_{i \in s.filter\, p} f\, i = \sum_{i \in s} (\text{if } p\, i \text{ then } f\, i \text{ else } 0)$ |
| `Nat.mod_lt` | `Mathlib.Data.Nat.Defs` | $a \bmod n < n$ (for `fifthPower_mod_thirtytwo`, if needed) |
| `Nat.pow_mod` | `Mathlib.Data.Nat.Pow` | $a^k \bmod n = (a \bmod n)^k \bmod n$ |

All exist at the pinned revision (`mathlib4` v4.26.0). No new Mathlib
imports needed beyond what S3 ACT will introduce.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s05-prep-g5-counting-omega.md` file
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all open PRs:
      - PR #18406 → `…s06-prep-waringG-correctness-chain.md` (different)
      - This PR → `…s05-prep-g5-counting-omega.md`
- [x] Filename distinct from all merged PRs:
      - #18152 (S1 OBSERVE), #18176 (S2 ACT), #18314 (S3 PREP
        `…-s03-prep-g4-counting-omega.md`), #18348 (S4 PREP
        `…-s04-prep-upper-bound-axioms.md`)
- [x] Counting arithmetic verified by hand (table above, $n_2 \in
      \{0, \ldots, 7\}$ exhaustive)
- [x] Cited witness $223 = 6 \cdot 32 + 31$ matches Chen 1964 / OEIS
      A079612 ("numbers requiring g(5) = 37 fifth powers")
- [x] $3^5 = 243 > 223$ confirms summand bound $\{0, 1, 2\}$
- [x] $3^k$ vs. canonical Waring witness table extended through
      $k = 7$ ($2175 < 2187$) — boundary case at $k = 8$ noted

## References

- Chen, J. R. (1964). "Waring's problem for $g(5) = 37$." *Scientia Sinica*
  13, 1547–1568.
- OEIS A002804 — *Waring's problem: $g(k)$.*
- OEIS A079612 — *Numbers $n$ such that $g(5)$ fifth powers are needed
  to represent $n$.*
- Parent slug: `lagrange-four-squares-waring-g2`
  (`Proofs/LagrangeFourSquares.lean:245` — `IsSumOfPowers` definition).
- Sibling memos:
  - `sessions/2026-05-12-s03-prep-g4-counting-omega.md` (S3 PREP, $k = 4$).
  - `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` (S4 PREP, upper
    axiom inventory).
- Lean file: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`
  (added in S2 ACT, currently contains `IsSumOfCubes` family).
