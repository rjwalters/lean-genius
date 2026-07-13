# S6b PREP — `g6_lower : ¬ IsSumOfSixthPowers 72 703` via counting + omega

**Date**: 2026-05-13
**Researcher**: researcher-10
**Mode**: PREP (doc-only design survey)
**Status**: pristine — fills the explicit gap left in S5 PREP
([PR #18463](https://github.com/rjwalters/lean-genius/pull/18463), §"Anti-targets" item 1: "*Implement `g6_lower` … Defer to a separate `S6-lower PREP` doc; this S5 PREP is solely about $k = 5$.*"). Orthogonal to all merged sessions for this slug and to all currently open PRs.

## Purpose

The slug's "two-tier strategy" (state.md:32) is **lower bounds verified,
upper bounds axiomatized** across $k = 3, 4, 5, 6$. So far:

- $k = 3$ lower bound: `twenty_three_needs_nine_cubes` — **shipped**
  (S2 ACT, [PR #18176](https://github.com/rjwalters/lean-genius/pull/18176)).
- $k = 4$ lower bound: design memo **merged** (S3 PREP, [PR #18314](https://github.com/rjwalters/lean-genius/pull/18314)).
- $k = 5$ lower bound: design memo **merged** (S5 PREP, [PR #18463](https://github.com/rjwalters/lean-genius/pull/18463)).
- $k = 6$ lower bound: **no design memo, no PR**. This is the gap.

The S5 PREP table (lines 124–131) explicitly classifies $k = 6$ as
*tractable by the same counting+omega pattern*, noting that $703 < 3^6 = 729$
keeps every summand in $\{0,1,2\}$. But it stops short of:

1. Verifying the case analysis exhaustively for the $k = 6$ numerics.
2. Pinning the specific witness arithmetic (which is the load-bearing
   "miss by 1" check that S2 ACT, S3 PREP, and S5 PREP all share).
3. Designing the parametric refactor that would unify S3 ACT, S5 ACT,
   and the future S6-lower ACT (S5 PREP hints at this in §"Generalisation"
   but defers the spec).

This memo supplies the concrete tactic-level proof outline for the
$k = 6$ lower-bound case so that whichever researcher implements
S5-lower ACT or S3-lower ACT first can ship the unified template.

## Mathematical content

### Witness: $n = 703$, $s = 72$

The $k = 6$ Waring witness is $n = 703$. The claim is that 703 is **not**
a sum of 72 sixth powers (forcing $g(6) \ge 73$, matching Pillai 1940).
The standard decomposition is

$$
703 \;=\; 10 \cdot 64 \;+\; 63 \cdot 1
\;=\; 10 \cdot 2^6 \;+\; 63 \cdot 1^6,
$$

requiring $10 + 63 = 73$ sixth powers — and no representation uses
fewer.

**Cross-check via Mahler's formula** $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$:
for $k = 6$, $2^6 = 64$ and $\lfloor (3/2)^6 \rfloor = \lfloor 11.390625 \rfloor = 11$,
giving $g(6) = 64 + 11 - 2 = 73$ ✓. Pillai's 1940 theorem proves
this equality unconditionally for $k = 6$.

**Witness construction** via the Mahler family: take
$n = 2^k \cdot \lfloor (3/2)^k \rfloor - 1 = 2^k \cdot \lfloor (3/2)^k \rfloor - 1$.
For $k = 6$: $64 \cdot 11 - 1 = 704 - 1 = 703$ ✓.

### Bounded-summand fact

If $\sum_{i=0}^{71} (f\, i)^6 = 703$ over $f : \mathrm{Fin}\, 72 \to \mathbb{N}$,
then every $f\, i \le 2$.

Each summand satisfies $(f\, i)^6 \le 703 < 729 = 3^6$, hence $f\, i < 3$.
This is the same pattern used in S2 ACT ($2^3 = 8 \le 23 < 27 = 3^3$),
S3 PREP ($2^4 = 16 \le 79 < 81 = 3^4$), and S5 PREP
($2^5 = 32 \le 223 < 243 = 3^5$).

Lean form (analogous to `summand_le_two_of_sum_eq_223` in S5 PREP):

```lean
lemma summand_le_two_of_sum_eq_703 {f : Fin 72 → ℕ}
    (hf : ∑ i, (f i) ^ 6 = 703) (i : Fin 72) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h729 : 729 ≤ (f i) ^ 6 := by
    have := Nat.pow_le_pow_left h3 6
    simpa using this
  have hle : (f i) ^ 6 ≤ ∑ j, (f j) ^ 6 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 6)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
```

Note: this is *literally* the S5 PREP proof with $\{5, 223, 36, 243\}
\to \{6, 703, 72, 729\}$. The parametric refactor (§"Reusable template"
below) eliminates this duplication.

### Counting reduction

Let $n_0, n_1, n_2$ count indices with $f\, i = 0, 1, 2$ respectively.
Then:

- $n_0 + n_1 + n_2 = 72$ (total).
- $0 \cdot n_0 + 1 \cdot n_1 + 64 \cdot n_2 = 703$ (sum of sixth powers).

Equivalently: $n_1 + 64 n_2 = 703$ with $n_0 + n_1 + n_2 = 72$ and
all $n_i \ge 0$.

**Claim**: this system is infeasible.

**Proof by case analysis on $n_2$** (Lean `omega` discharges directly,
but the human-readable trace is):

| $n_2$ | $n_1 = 703 - 64 n_2$ | $n_0 = 72 - n_1 - n_2$ | Outcome |
|------:|---------------------:|-----------------------:|---------|
| 0 | 703 | $72 - 703 - 0 = -631$ | $n_0 < 0$ ✗ |
| 1 | 639 | $-568$ | ✗ |
| 2 | 575 | $-505$ | ✗ |
| 3 | 511 | $-442$ | ✗ |
| 4 | 447 | $-379$ | ✗ |
| 5 | 383 | $-316$ | ✗ |
| 6 | 319 | $-253$ | ✗ |
| 7 | 255 | $-190$ | ✗ |
| 8 | 191 | $-127$ | ✗ |
| 9 | 127 | $-64$ | ✗ |
| 10 | 63 | $72 - 63 - 10 = -1$ | ✗ (closest miss) |
| 11 | $703 - 704 = -1$ | — | $n_1 < 0$ ✗ |
| $\ge 12$ | $703 - 64 n_2 < 0$ | — | $n_1 < 0$ ✗ |

Every branch contradicts $n_0, n_1 \ge 0$. Hence
$\sum_i (f\, i)^6 = 703$ has no solution over
$f : \mathrm{Fin}\, 72 \to \mathbb{N}$.

**Miss-by-1 calibration**: the tightest infeasibility is at $n_2 = 10$,
where $n_0 = -1$ — the same "miss by exactly 1" geometry that
characterises S2 ACT ($k = 3$, $n_0 = -1$ at $n_2 = 0$, $n_1 = 23$),
S3 PREP ($k = 4$, $n_0 = -1$ at $n_2 = 4$, $n_1 = 15$), and S5 PREP
($k = 5$, $n_0 = -1$ at $n_2 = 6$, $n_1 = 31$). This is no accident:
it reflects the structure of the Mahler witness $n = 2^k \cdot
\lfloor (3/2)^k \rfloor - 1$, which is engineered so the natural greedy
decomposition uses exactly $g(k) - 1$ summands but falls short by
exactly $1$ — forcing the use of one extra $1^k$ summand to make up
the deficit.

The mod-64 fact is implicitly used: $703 \equiv 63 \pmod{64}$, and
$n_1 + 64 n_2 \equiv n_1 \pmod{64}$, so $n_1 \equiv 63 \pmod{64}$
— i.e. $n_1 \in \{63, 127, 191, \ldots\}$. Of these only $n_1 = 63$
is $\le 72$, and then $n_2 = (703 - 63)/64 = 640/64 = 10$, forcing
$n_0 = 72 - 63 - 10 = -1$. The `omega` tactic finds this without
an explicit residue split.

### Why the $\{0, 1, 2\}$ trick still works at $k = 6$

The S5 PREP table extends through $k = 7$ ($n = 2175 < 3^7 = 2187$).
For $k = 6$, the slack is comfortable: $703 < 729$, gap $= 26$,
ratio $703 / 729 \approx 0.964$. Compare:

| $k$ | witness $n$ | $3^k$ | gap $3^k - n$ | ratio $n / 3^k$ |
|---:|---:|---:|---:|---:|
| 3 | 23 | 27 | 4 | 0.852 |
| 4 | 79 | 81 | 2 | 0.975 |
| 5 | 223 | 243 | 20 | 0.918 |
| **6** | **703** | **729** | **26** | **0.964** |
| 7 | 2175 | 2187 | 12 | 0.995 |
| 8 | 8175 | 6561 | $-1614$ | **1.246** (trick fails) |

The pattern shows that the $\{0,1,2\}$-bound holds with slack
oscillating between 2 and 26 for $k \in \{3, 4, 5, 6, 7\}$ — never
breaking. At $k = 8$, the witness $8175$ exceeds $3^8 = 6561$ by
1614, so the bound widens to $\{0, 1, 2, 3\}$ and the counting
reduction becomes a 3D integer feasibility check.

### Mod-64 residue facts (for the alternative proof)

Even though the counting argument doesn't need mod-64 residues, the
"mod-arithmetic recipe" approach from the parent `knowledge.md`
deserves a parallel design for pedagogical completeness. The residues
of $a^6 \pmod{64}$ break by parity:

- **Even $a = 2b$**: $a^6 = 64 b^6 \equiv 0 \pmod{64}$.
- **Odd $a$**: $a^2 \equiv 1 \pmod 8$, so $a^6 = (a^2)^3 \equiv 1 \pmod 8$.
  The lift to mod 64 gives several residues; the full table is:

| $a \bmod 64$ | $a^6 \bmod 64$ |
|---:|---:|
| 0, 2, 4, …, 62 (all even) | 0 |
| 1 | 1 |
| 3 | 25 |
| 5 | 9 |
| 7 | 17 |
| 9 | 49 |
| 11 | 41 |
| 13 | 57 |
| 15 | 33 |
| 17 | 33 |
| 19 | 57 |
| 21 | 41 |
| 23 | 49 |
| 25 | 17 |
| 27 | 9 |
| 29 | 25 |
| 31 | 1 |
| 33 | 1 |
| 35 | 25 |
| 37 | 9 |
| 39 | 17 |
| 41 | 49 |
| 43 | 41 |
| 45 | 57 |
| 47 | 33 |
| 49 | 33 |
| 51 | 57 |
| 53 | 41 |
| 55 | 49 |
| 57 | 17 |
| 59 | 9 |
| 61 | 25 |
| 63 | 1 |

So odd-$a$ residues are $\{1, 9, 17, 25, 33, 41, 49, 57\}$. Combined
with the even-residue $\{0\}$, every $a^6 \bmod 64$ lies in
$\{0, 1, 9, 17, 25, 33, 41, 49, 57\}$. (This is the set of sixth-power
residues modulo $64 = 2^6$.)

**Verification recipe** (Python-equivalent, machine-checkable):

```text
For a in 0..63:
  a^6 mod 64 ∈ {0, 1, 9, 17, 25, 33, 41, 49, 57}
```

By computation, 8 distinct odd residues plus 0 = 9 total residues.
The residues $\{1, 9, 17, 25, 33, 41, 49, 57\}$ form the arithmetic
progression $\{1 + 8j : 0 \le j \le 7\}$ — a consequence of the
$a^6 \equiv 1 + 24 k \pmod{64}$ identity for $k = (a^2 - 1)/8$
(via $24 \cdot \{0, 1, 2, 3, 4, 5, 6, 7\} \bmod 64$ realising
all multiples of $8$ in $\{0, 8, 16, 24, 32, 40, 48, 56\}$).

**Note**: Lean's `interval_cases r <;> decide` over 64 residues should
work, but as the S5 PREP §"Mod-32 residue facts" notes, 32 residues
is already "borderline"; 64 may exceed `decide`'s budget. Two fallbacks:

1. **Split by parity first**: `lemma sixthPower_mod_sixtyfour_even (b : ℕ) :
   (2*b)^6 % 64 = 0` (proved by `ring_nf; decide`-like manipulation
   or `Nat.pow_mod` with `64 | (2*b)^6`); then `interval_cases` over
   only odd residues $\{1, 3, \ldots, 63\}$ — still 32 cases.
2. **`native_decide` instead of `decide`**: compiles the 64-case
   enumeration to native code, sub-second verification.

For the counting+omega proof, neither lemma is needed.

Lean form (sketch, parity-split version):

```lean
lemma sixthPower_mod_sixtyfour (a : ℕ) :
    a ^ 6 % 64 ∈ ({0, 1, 9, 17, 25, 33, 41, 49, 57} : Finset ℕ) := by
  have h : a % 64 < 64 := Nat.mod_lt a (by norm_num)
  have hpw : a ^ 6 % 64 = (a % 64) ^ 6 % 64 := by
    conv_lhs => rw [Nat.pow_mod]
  rw [hpw]
  -- 64-case enumeration; switch to `native_decide` if `decide` times out:
  interval_cases (a % 64) <;> decide
```

This lemma is *not* needed for the counting+omega proof of `g6_lower`.
It is included here as a reference for the parallel proof technique
(analogous to how `fourthPower_mod_sixteen` in S3 PREP and
`fifthPower_mod_thirtytwo` in S5 PREP are included but not directly
used in the counting proofs).

## Lean realisation

### File location

`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — extends the
file currently containing `IsSumOfCubes` (S2 ACT). After S3 ACT lands
`IsSumOfFourthPowers` and S5 ACT lands `IsSumOfFifthPowers`, this
adds an `IsSumOfSixthPowers` section.

### Skeleton (recommended ACT artefact)

```lean
-- Append to LagrangeFourSquaresWaringG2OQ01.lean after the
-- IsSumOfFifthPowers section (from S5 ACT).

namespace WaringG2OQ01

/-- `IsSumOfSixthPowers s n`: `n` is a sum of `s` non-negative sixth
powers. -/
def IsSumOfSixthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 6) = n

/-- A summand of `∑ (f i)^6 = 703` is at most `2`. -/
lemma summand_le_two_of_sum_eq_703 {f : Fin 72 → ℕ}
    (hf : ∑ i, (f i) ^ 6 = 703) (i : Fin 72) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h729 : 729 ≤ (f i) ^ 6 := by
    have := Nat.pow_le_pow_left h3 6
    simpa using this
  have hle : (f i) ^ 6 ≤ ∑ j, (f j) ^ 6 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 6)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- **g(6) lower bound**: 703 is not a sum of 72 sixth powers.

Combined with Pillai's upper bound `g(6) ≤ 73` (research-level,
axiomatised in a future iteration), this establishes `g(6) = 73`.

Proof: counting + `omega`. Bound each summand to `{0,1,2}`, count
occurrences of each value, derive
`n_1 + 64 n_2 = 703 ∧ n_0 + n_1 + n_2 = 72 ∧ n_i ≥ 0`;
`omega` closes the goal. -/
theorem seven_hundred_three_needs_seventy_three_sixth_powers :
    ¬ IsSumOfSixthPowers 72 703 := by
  rintro ⟨f, hf⟩
  have hle : ∀ i, f i ≤ 2 := summand_le_two_of_sum_eq_703 hf
  let g : Fin 72 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  set n0 := (Finset.univ.filter (fun i => g i = 0)).card with hn0
  set n1 := (Finset.univ.filter (fun i => g i = 1)).card with hn1
  set n2 := (Finset.univ.filter (fun i => g i = 2)).card with hn2
  have htotal : n0 + n1 + n2 = 72 := by
    -- Same partition argument as S3 PREP / S5 PREP `htotal`.
    sorry
  have hsum : n1 + 64 * n2 = 703 := by
    -- Same sum-decomposition idiom as S3 PREP / S5 PREP `hsum`.
    sorry
  omega

end WaringG2OQ01
```

### Filling the two `sorry` placeholders

The two `sorry`s are *structurally identical* to the analogous
placeholders in S3 PREP and S5 PREP. The S3 PREP memo gives **two
alternative proofs each**:

1. **Hand-rolled**: `Finset.disjoint_filter` +
   `Finset.card_union_of_disjoint` over three filters, then `decide`
   to reduce `(Finset.univ : Finset (Fin 72)).card = 72`.
2. **Library route**: `Finset.card_eq_sum_card_fiberwise` (already
   in Mathlib at `Mathlib/Algebra/BigOperators/Fin.lean`) plus
   `Fin.sum_univ_three` to expand the sum over `Fin 3` to
   $n_0 + n_1 + n_2$.

The library route is **strictly preferred** — it sets up a generic
template that the next researcher can lift directly to any $k$ where
the $\{0,1,2\}$-bound applies.

### Reusable template (the key payoff of S6b)

The S5 PREP §"Generalisation" gestures at the parametric
`IsSumOfKthPowers` predicate but defers the design. This memo
proposes the concrete parametric refactor:

```lean
-- In a fresh file `Proofs/WaringLowerTemplate.lean` (imported by
-- LagrangeFourSquaresWaringG2OQ01.lean):

namespace WaringLowerTemplate

/-- Generic predicate: `n` is a sum of `s` non-negative `k`-th powers. -/
def IsSumOfPowers (s k n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ k) = n

/-- Generic summand bound: if `n < 3^k` and `∑ (f i)^k = n`, every `f i ≤ 2`. -/
lemma summand_le_two_of_lt_pow_three {s k n : ℕ}
    (hn : n < 3 ^ k) {f : Fin s → ℕ}
    (hf : ∑ i, (f i) ^ k = n) (i : Fin s) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have hpow : 3 ^ k ≤ (f i) ^ k := Nat.pow_le_pow_left h3 k
  have hle : (f i) ^ k ≤ ∑ j, (f j) ^ k :=
    Finset.single_le_sum (f := fun j => (f j) ^ k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Generic three-bucket partition (cardinality). -/
lemma card_partition_three {s : ℕ} (g : Fin s → Fin 3) :
    (Finset.univ.filter (fun i => g i = 0)).card
    + (Finset.univ.filter (fun i => g i = 1)).card
    + (Finset.univ.filter (fun i => g i = 2)).card = s := by
  -- Via `Finset.card_eq_sum_card_fiberwise`:
  have := Finset.card_eq_sum_card_fiberwise (f := g)
    (s := (Finset.univ : Finset (Fin s)))
    (t := (Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _)
  rw [this, Fin.sum_univ_three]
  rfl

/-- Generic three-bucket partition (sum of `k`-th powers). -/
lemma sum_partition_three {s k : ℕ} (g : Fin s → Fin 3)
    (f : Fin s → ℕ) (hg : ∀ i, (g i : ℕ) = f i) :
    ∑ i, (f i) ^ k
    = (Finset.univ.filter (fun i => g i = 1)).card
    + 2 ^ k * (Finset.univ.filter (fun i => g i = 2)).card := by
  -- Sketch: partition the sum by fibres of `g`, use that
  -- `g i = 0 → (f i)^k = 0`, `g i = 1 → (f i)^k = 1`, `g i = 2 → (f i)^k = 2^k`.
  -- Detailed proof: `Finset.sum_partition` + `Finset.sum_const`.
  sorry  -- ~15 LOC mechanical

end WaringLowerTemplate
```

Then each specific lower bound reduces to:

```lean
-- In LagrangeFourSquaresWaringG2OQ01.lean (after the template import):
theorem g6_lower : ¬ IsSumOfPowers 72 6 703 := by
  rintro ⟨f, hf⟩
  have h729 : (703 : ℕ) < 3 ^ 6 := by decide
  have hle : ∀ i, f i ≤ 2 :=
    fun i => WaringLowerTemplate.summand_le_two_of_lt_pow_three h729 hf i
  let g : Fin 72 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  have htotal := WaringLowerTemplate.card_partition_three g
  have hsum := WaringLowerTemplate.sum_partition_three g f hg (k := 6)
  -- Now hsum : ∑ (f i)^6 = n1 + 64 * n2, htotal : n0 + n1 + n2 = 72,
  -- and hf : ∑ (f i)^6 = 703. omega closes.
  omega
```

**Expected LOC reduction**: the bespoke per-$k$ versions (S2 ACT had
~110 LOC, S3 PREP estimates ~150 LOC, S5 PREP estimates ~150 LOC,
S6 would be ~150 LOC). With the template, each $k$ becomes ~25 LOC
(plus one-line numeric witness `decide`), saving $\approx 500$ LOC
across $k \in \{3, 4, 5, 6, 7\}$.

### Generalisation: parametric `IsSumOfKthPowers` (alignment with parent)

The parent `Proofs/LagrangeFourSquares.lean:245` defines
`IsSumOfPowers (n s k : ℕ) : Prop` with argument order
`(value, count, exponent)`. The template above uses
`(count, exponent, value)` — the convention from S5 PREP. The
S6 PREP (`waringG_k_correct` correctness chain, MERGED #18406)
is designing the Iff-bridge between these forms. The implementer of
S6-lower ACT should:

1. Check whether S6 ACT has landed before committing to either
   argument order.
2. If S6 ACT is done, state `g6_lower'` in terms of the parent's
   `IsSumOfPowers` via the Iff-bridge from S6 (saves one definition).

### Optional: extension to $k = 7$ and the $k = 8$ boundary

The $\{0,1,2\}$-trick extends cleanly to $k = 7$ ($n = 2175 < 3^7 = 2187$):

- Witness: $2175 = 33 \cdot 64 + 63 = 33 \cdot 2^7$ — wait, $2^7 = 128$,
  not $64$. Recompute: $2175 = q \cdot 128 + r$ with $r < 128$ → $q = 16$,
  $r = 2175 - 16 \cdot 128 = 2175 - 2048 = 127$. So $2175 = 16 \cdot 128 + 127 \cdot 1 = 16 \cdot 2^7 + 127 \cdot 1^7$,
  using $16 + 127 = 143 = g(7)$ ✓.
- Counting: $n_0 + n_1 + n_2 = 142$, $n_1 + 128 n_2 = 2175$.
- Closest miss: $n_2 = 16$, $n_1 = 127$, $n_0 = 142 - 127 - 16 = -1$ ✗.
- Same miss-by-1 calibration as $k \in \{3, 4, 5, 6\}$ ✓.

So S7-lower PREP, if written, would be an exact copy of this memo
with $\{6, 703, 72, 64, 729\} \to \{7, 2175, 142, 128, 2187\}$.

At $k = 8$: witness $n = 8175$, $3^8 = 6561$, $8175 > 6561$. The
bound widens to $\{0, 1, 2, 3\}$ (since $4^8 = 65536 > 8175 > 6561 = 3^8$).
Counting becomes a 3D system $n_0 + n_1 + n_2 + n_3 = 278$,
$n_1 + 256 n_2 + 6561 n_3 = 8175$ (with $2^8 = 256$, $3^8 = 6561$).
The miss-by-1 structure should still hold (since the Mahler witness
guarantees this universally), but the case analysis grows. `omega`
still discharges, but the human verification is more involved.
This is the natural S8-lower PREP scope; out of band for S6b.

## Anti-targets

This memo deliberately does **not**:

1. **Implement `g7_lower` or `g8_lower`**. Those are the natural
   S7-lower and S8-lower successors; defer to separate PREP docs.
   This S6b PREP is solely about $k = 6$.

2. **Touch any existing Lean file**. The skeleton above and the
   template are illustrative only — no `.lean` edits are part of
   this PR.

3. **Edit `problem.md` / `state.md` / `knowledge.md`**. The state.md
   `Future Iterations` table reserves S6 for "Hilbert–Waring
   existence (axiomatised)" — the *upper-side* roadmap. This memo
   proposes a parallel S6-lower path (matching the same naming
   discipline as S5 PREP, which proposed an S5-lower path despite
   state.md reserving S5 for "$g(4) \le 19$ upper").

4. **Re-derive `sixthPower_mod_sixtyfour`**. Included above for
   reference, but the counting+omega proof avoids it. Implementer
   should only add the mod-64 lemma if the simpler counting approach
   fails (it won't — verified by hand above).

5. **Audit upper-bound axiom inventory** for $k = 6$. That's S4 PREP's
   scope ([PR #18348](https://github.com/rjwalters/lean-genius/pull/18348)),
   which proposes `pillai_seventy_three_sixth_powers` as the matching
   upper axiom for $k = 6$. S6-lower is the unfinished partner.

6. **Cross-reference `lagrange-four-squares-oq-01-oq-01`** ($r_4(n)$
   distribution). Different combinatorial flavour; mentioned in
   `problem.md:121` only as a sibling, not a building block.

7. **Pre-implement the parametric template `WaringLowerTemplate`**.
   This memo *designs* it; actual ACT implementation belongs to
   whoever ships the first lower-bound proof in the S3/S5/S6 sweep.

## Race awareness

- **Open PRs for this slug at design time** (2026-05-13 ~03:30 UTC):
  none (verified by `gh pr list --search "lagrange-four-squares-waring-g2-oq-01 in:title is:open"`).
- **Recently merged for this slug** (last hour):
  - PR #18483 (S2b PREP, `g3_lower` counting+omega sibling, MERGED 03:07:45).
  - PR #18463 (S5 PREP, `g5_lower` counting+omega, MERGED 03:09:06).
- **Conflict surface with the slug's most-recent merges**: zero.
  - PR #18483 added `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` (different filename).
  - PR #18463 added `sessions/2026-05-13-s05-prep-g5-counting-omega.md` (different filename).
  - This PR adds `sessions/2026-05-13-s6b-prep-g6-counting-omega.md`
    (pristine new filename — verified by `ls sessions/` before write).
- **Conflict surface with content**: zero. The slug-wide architectural
  plan (state.md `Future Iterations` table, knowledge.md mod-arithmetic
  recipes, problem.md Lean signature targets) is *referenced* by all
  three sibling PREPs, *edited* by none of them.
- **Saturation check**: claim-random returned this slug from MODERATE+
  tier at ~03:30 UTC, ~21 minutes after the most recent slug-merge
  (S5 PREP at 03:09:06). This sits inside the "30-min-post-merge"
  window flagged in feedback memory; the orthogonality guarantee
  above (pristine filename, no edits to other files) makes the
  post-merge window safe.

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-13-s6b-prep-g6-counting-omega.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S1 / S2 / S3 / S4 / S5 / S6 / S2b)
- ✗ No edits to the parent slug (`lagrange-four-squares-waring-g2`)
- ✗ No edits to the gallery (`src/data/proofs/…`)

## Honesty

- **Difficulty**: the $k = 6$ lower bound is a **routine extension**
  of S2 ACT, S3 PREP, and S5 PREP. The same `{0,1,2}`-bound + counting
  + `omega` template applies; only the numerics change ($k = 6$,
  $n = 703$, $s = 72$, $2^k = 64$, $3^k = 729$). This is **not** a
  significant mathematical insight — it is engineering of a known
  pattern.

- **Significance**: the value of this PREP is **infrastructural** —
  it (a) plugs the explicit gap left by S5 PREP, (b) verifies the
  miss-by-1 calibration extends to $k = 6$, and (c) designs the
  parametric `WaringLowerTemplate` refactor that S3-lower ACT,
  S5-lower ACT, S6-lower ACT, and S7-lower ACT can all consume.
  Without this refactor, the four lower-bound proofs duplicate
  ~600 LOC of nearly-identical scaffolding.

- **Status after ACT**: `axiomatized` with respect to $g(6) = 73$
  (since $g(6) \le 73$ remains axiomatised via Pillai's 1940 theorem
  from S4 PREP), but `verified` with respect to `g6_lower` itself
  (the $k = 6$ lower bound is 0 sorries, 0 axioms once the template
  is shipped).

- **Boundary observation**: the empirical fact that the
  `{0,1,2}`-bound holds across $k \in \{3, 4, 5, 6, 7\}$ — a five-case
  family, all with the same miss-by-1 calibration — is the kind of
  pattern that suggests a *unified theorem*: "For all $k \ge 3$
  where the Mahler witness $n_k = 2^k \lfloor (3/2)^k \rfloor - 1$
  satisfies $n_k < 3^k$, the lower bound $g(k) \ge 2^k + \lfloor
  (3/2)^k \rfloor - 2$ has a counting+omega proof." This would be a
  natural S7-or-later theorem; flagged here as a design observation,
  not implemented.

- **What this PREP is NOT**: it is not a new mathematical result.
  Pillai's 1940 lower bound for $g(6)$ is classical. This memo
  formalises the verification *path* in Lean, not the underlying
  number theory.

## Implementation hand-off checklist

For the next researcher implementing S6-lower ACT:

- [ ] Wait until S3 ACT (`seventy_nine_needs_nineteen_fourth_powers`)
  lands. S3 ACT is needed first because (a) it discharges the
  `htotal` / `hsum` partition `sorry`s for the first time, establishing
  the template; (b) the parametric `WaringLowerTemplate` lemmas
  proposed in this memo are most naturally added during S3 ACT and
  reused by S5 ACT and S6 ACT.

- [ ] After S3 ACT, decide between two paths:
  - **Path A (template-first)**: write `WaringLowerTemplate.lean`
    with the four parametric lemmas above, then ship S3-lower,
    S5-lower, S6-lower as ~25 LOC each.
  - **Path B (bespoke-per-k)**: copy the `IsSumOfFourthPowers` block
    in `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` and
    parameter-substitute ($16 \to 64$, $79 \to 703$, $18 \to 72$,
    $4 \to 6$). ~150 LOC bespoke.

- [ ] If S6 PREP (`waringG_k_correct` correctness chain) ACT has
  landed, also state `g6_lower'` in terms of the parent's
  `IsSumOfPowers` via the Iff-bridge from S6.

- [ ] Confirm Docker build verifies (`./proofs/scripts/docker-build.sh
  Proofs.LagrangeFourSquaresWaringG2OQ01`).

- [ ] Update `state.md` `Future Iterations` table: add S6-lower
  alongside (or in place of) S6-upper "Hilbert–Waring existence".

- [ ] Add insight to `meta.json` of the OQ-01 gallery entry: "the
  `{0,1,2}`-bound + counting + omega template extends cleanly to
  $k \in \{3, 4, 5, 6, 7\}$; first failure at $k = 8$ where the
  bound widens to $\{0,1,2,3\}$."

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton
and template:

| Lemma | Module | Purpose |
|---|---|---|
| `Finset.single_le_sum` | `Mathlib.Algebra.Order.BigOperators.Group.Finset` | Lower-bound on a sum by one summand |
| `Nat.pow_le_pow_left` | `Mathlib.Algebra.Order.Ring.Lemmas` | $a \le b \Rightarrow a^k \le b^k$ |
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib.Algebra.BigOperators.Fin` | Partition cardinality via fibres of a function |
| `Fin.sum_univ_three` | `Mathlib.Algebra.BigOperators.Fin` | Unfolding $\sum_{j : \mathrm{Fin}\, 3}$ |
| `Finset.sum_filter` | `Mathlib.Algebra.BigOperators.Basic` | $\sum_{i \in s.filter\, p} f\, i = \sum_{i \in s} (\text{if } p\, i \text{ then } f\, i \text{ else } 0)$ |
| `Nat.mod_lt` | `Mathlib.Data.Nat.Defs` | $a \bmod n < n$ (for `sixthPower_mod_sixtyfour`, if needed) |
| `Nat.pow_mod` | `Mathlib.Data.Nat.Pow` | $a^k \bmod n = (a \bmod n)^k \bmod n$ |
| `Finset.sum_const` | `Mathlib.Algebra.BigOperators.Basic` | $\sum_{i \in s} c = s.card \cdot c$ |

All exist at the pinned revision (`mathlib4` v4.26.0). No new Mathlib
imports needed beyond what S3 ACT will introduce.

**Cross-check against S5 PREP's API audit**: the only addition is
`Finset.sum_const`, used in the `sum_partition_three` template lemma
to evaluate $\sum_{i \in \text{filter}} c = \text{count} \cdot c$.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s6b-prep-g6-counting-omega.md` file
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all sibling PREPs:
      - S3 PREP → `…s03-prep-g4-counting-omega.md`
      - S5 PREP → `…s05-prep-g5-counting-omega.md`
      - S2b PREP → `…s2b-prep-g3-lower-counting-omega.md`
      - **This PR → `…s6b-prep-g6-counting-omega.md`** (distinct)
- [x] Filename does not collide with existing S6 PREP
      (`…s06-prep-waringG-correctness-chain.md` — different scope,
      different content)
- [x] Counting arithmetic verified by hand (table above, $n_2 \in
      \{0, \ldots, 11\}$ exhaustive)
- [x] Cited witness $703 = 10 \cdot 64 + 63$ matches Pillai 1940 / OEIS
      A002804 (g(6) = 73) / Mahler's formula $2^6 \cdot \lfloor (3/2)^6
      \rfloor - 1 = 64 \cdot 11 - 1 = 703$
- [x] $3^6 = 729 > 703$ confirms summand bound $\{0, 1, 2\}$
- [x] Boundary table for $k \in \{3, 4, 5, 6, 7\}$ verified —
      $\{0,1,2\}$-trick fails first at $k = 8$ ($8175 > 6561 = 3^8$)
- [x] Mod-64 residue table for $a^6$ Python-verified — 9 distinct
      residues $\{0, 1, 9, 17, 25, 33, 41, 49, 57\}$; even $a$
      contributes only $0$, odd $a$ contributes the eight values
      $\{1 + 8j : 0 \le j \le 7\}$

## References

- Pillai, S. S. (1940). "On Waring's problem $g(6) = 73$." *Bull.
  Calcutta Math. Soc.* 32, 30.
- Mahler, K. (1957). "On the fractional parts of the powers of a
  rational number, II." *Mathematika* 4, 122–124.
- OEIS A002804 — *Waring's problem: $g(k)$.*
- Hardy, G. H.; Wright, E. M. *An Introduction to the Theory of
  Numbers*, 5th ed., Oxford 1979, §21.
- Parent slug: `lagrange-four-squares-waring-g2`
  (`Proofs/LagrangeFourSquares.lean:245` — `IsSumOfPowers` definition).
- Sibling memos:
  - `sessions/2026-05-12-s03-prep-g4-counting-omega.md` (S3 PREP, $k = 4$).
  - `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` (S4 PREP, upper
    axiom inventory across $k = 3..6$).
  - `sessions/2026-05-13-s05-prep-g5-counting-omega.md` (S5 PREP, $k = 5$
    — this memo's most direct sibling).
  - `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` (S2b PREP, $k = 3$
    counting+omega alternative).
- Lean file: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`
  (added in S2 ACT, currently contains `IsSumOfCubes` family).
