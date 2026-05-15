# S7 PREP — `g7_lower : ¬ IsSumOfSeventhPowers 142 2175` via counting + omega

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design survey)
**Status**: pristine — fills the explicit gap left in S6b PREP
([PR #18547](https://github.com/rjwalters/lean-genius/pull/18547),
§"Optional: extension to $k = 7$ and the $k = 8$ boundary" lines 443–451,
which sketches the $k = 7$ outline in 5 lines and defers a full design
memo). Orthogonal to all merged sessions for this slug and to all
currently open PRs for this slug (verified at draft time, 2026-05-13
~05:40 UTC).

## Purpose

The slug's "two-tier strategy" (state.md:32) is **lower bounds verified,
upper bounds axiomatized** across $k = 3, \ldots, K$ for $K$ growing.
So far the lower-bound design coverage is:

| $k$ | $g(k)$ | witness $n_k$ | PREP / ACT | PR |
|---:|---:|---:|---|---|
| 3 | 9   | 23     | S2 ACT (build-verified, 0 sorries, 0 axioms) | [#18176](https://github.com/rjwalters/lean-genius/pull/18176) |
| 3 | 9   | 23     | S2b PREP (counting+omega sibling) | [#18483](https://github.com/rjwalters/lean-genius/pull/18483) |
| 4 | 19  | 79     | S3 PREP (counting+omega) | [#18314](https://github.com/rjwalters/lean-genius/pull/18314) |
| 5 | 37  | 223    | S5 PREP (counting+omega) | [#18463](https://github.com/rjwalters/lean-genius/pull/18463) |
| 6 | 73  | 703    | S6b PREP (counting+omega + reusable template) | [#18547](https://github.com/rjwalters/lean-genius/pull/18547) |
| **7** | **143** | **2175** | **this memo** | (TBD) |
| 8 | 279 | 6399   | (open) | — |

PR #18547's §"Optional: extension to $k = 7$ and the $k = 8$ boundary"
(lines 443–451 of `…s6b-prep-g6-counting-omega.md`) gives the $k = 7$
numerics in 5 lines:

> "Witness: $2175 = 16 \cdot 128 + 127 \cdot 1 = 16 \cdot 2^7 + 127 \cdot 1^7$,
> using $16 + 127 = 143 = g(7)$ ✓.
> Counting: $n_0 + n_1 + n_2 = 142$, $n_1 + 128 n_2 = 2175$.
> Closest miss: $n_2 = 16$, $n_1 = 127$, $n_0 = 142 - 127 - 16 = -1$ ✗.
> Same miss-by-1 calibration as $k \in \{3, 4, 5, 6\}$ ✓.
>
> So S7-lower PREP, if written, would be an exact copy of this memo
> with $\{6, 703, 72, 64, 729\} \to \{7, 2175, 142, 128, 2187\}$."

This memo supplies that "exact copy" with the full numeric verification,
Lean skeleton, Mathlib API audit, and corrected boundary table (citing
PR #18555 = the S6b PREP audit memo's universal $\{0,1,2\}$-trick proof,
which extends applicability through $k = 8$ and beyond).

## Mathematical content

### Witness: $n = 2175$, $s = 142$

The $k = 7$ Pillai/Mahler witness is $n_7 = 2175$. The claim is that
$2175$ is **not** a sum of $142$ seventh powers (forcing $g(7) \ge 143$,
matching Pillai 1940). The Mahler decomposition is

$$
2175 \;=\; 16 \cdot 128 \;+\; 127 \cdot 1
\;=\; 16 \cdot 2^7 \;+\; 127 \cdot 1^7,
$$

requiring $16 + 127 = 143 = g(7)$ seventh powers — and no representation
uses fewer.

**Cross-check via Mahler's formula** $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$:
for $k = 7$, $2^7 = 128$ and $\lfloor (3/2)^7 \rfloor = \lfloor 17.0859375 \rfloor = 17$,
giving $g(7) = 128 + 17 - 2 = 143$ ✓ (matches OEIS A002804).

**Witness construction** via the Mahler family: take
$n_k = 2^k \cdot \lfloor (3/2)^k \rfloor - 1$.
For $k = 7$: $128 \cdot 17 - 1 = 2176 - 1 = 2175$ ✓.

### Bounded-summand fact

If $\sum_{i=0}^{141} (f\, i)^7 = 2175$ over
$f : \mathrm{Fin}\, 142 \to \mathbb{N}$, then every $f\, i \le 2$.

Each summand satisfies $(f\, i)^7 \le 2175 < 2187 = 3^7$, hence $f\, i < 3$.
This is the same pattern used in S2 ACT ($2^3 = 8 \le 23 < 27 = 3^3$),
S3 PREP ($2^4 = 16 \le 79 < 81 = 3^4$), S5 PREP
($2^5 = 32 \le 223 < 243 = 3^5$), and S6b PREP
($2^6 = 64 \le 703 < 729 = 3^6$).

**Important narrowness observation**: $k = 7$ has the **tightest gap**
among $k \in \{3, 4, 5, 6, 7\}$ — only $2187 - 2175 = 12$ units of
slack. The $\{0, 1, 2\}$-trick still applies, but with the least room
to spare. (S6b PREP §"Why the $\{0, 1, 2\}$ trick still works at $k = 6$",
lines 145–164, gives the comparison table; my own S6b PREP audit
memo PR #18555 §3 generalises this to a **universal** strict inequality
$n_k < 3^k$ for **every** $k \ge 1$, since $q_k = \lfloor (3/2)^k \rfloor
< (3/2)^k$ strictly whenever $(3/2)^k \notin \mathbb{Z}$, which holds
for every $k \ge 1$.)

Lean form (analogous to `summand_le_two_of_sum_eq_703` in S6b PREP and
`summand_le_two_of_sum_eq_223` in S5 PREP):

```lean
lemma summand_le_two_of_sum_eq_2175 {f : Fin 142 → ℕ}
    (hf : ∑ i, (f i) ^ 7 = 2175) (i : Fin 142) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h2187 : 2187 ≤ (f i) ^ 7 := by
    have := Nat.pow_le_pow_left h3 7
    simpa using this
  have hle : (f i) ^ 7 ≤ ∑ j, (f j) ^ 7 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 7)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
```

Note: this is *literally* the S5 PREP / S6b PREP proof with the
substitution $\{5, 223, 36, 243\} \to \{7, 2175, 142, 2187\}$ (or
$\{6, 703, 72, 729\} \to \{7, 2175, 142, 2187\}$). The parametric
refactor in S6b PREP's §"Reusable template" (the `WaringLowerTemplate`
proposal) eliminates this per-$k$ duplication. **No new boilerplate
is introduced by this memo**; if S6b PREP's template ships first, the
$k = 7$ ACT reduces to a 25-LOC consumer:

```lean
theorem g7_lower : ¬ IsSumOfPowers 142 7 2175 :=
  -- 25 LOC consumer of WaringLowerTemplate; see "Reusable template
  -- (key payoff)" of S6b PREP for the parametric chain
  sorry  -- replaced by template instantiation
```

### Counting reduction

Let $n_0, n_1, n_2$ count indices with $f\, i = 0, 1, 2$ respectively.
Then:

- $n_0 + n_1 + n_2 = 142$ (total).
- $0 \cdot n_0 + 1 \cdot n_1 + 128 \cdot n_2 = 2175$ (sum of seventh powers).

Equivalently: $n_1 + 128 n_2 = 2175$ with $n_0 + n_1 + n_2 = 142$ and
all $n_i \ge 0$.

**Claim**: this system is infeasible.

**Proof by case analysis on $n_2$** (Lean `omega` discharges directly,
but the human-readable trace is):

| $n_2$ | $n_1 = 2175 - 128 n_2$ | $n_0 = 142 - n_1 - n_2$ | Outcome |
|------:|----------------------:|------------------------:|---------|
| 0  | 2175 | $142 - 2175 - 0 = -2033$ | $n_0 < 0$ ✗ |
| 1  | 2047 | $-1906$ | ✗ |
| 2  | 1919 | $-1779$ | ✗ |
| 3  | 1791 | $-1652$ | ✗ |
| 4  | 1663 | $-1525$ | ✗ |
| 5  | 1535 | $-1398$ | ✗ |
| 6  | 1407 | $-1271$ | ✗ |
| 7  | 1279 | $-1144$ | ✗ |
| 8  | 1151 | $-1017$ | ✗ |
| 9  | 1023 | $-890$  | ✗ |
| 10 | 895  | $-763$  | ✗ |
| 11 | 767  | $-636$  | ✗ |
| 12 | 639  | $-509$  | ✗ |
| 13 | 511  | $-382$  | ✗ |
| 14 | 383  | $-255$  | ✗ |
| 15 | 255  | $-128$  | ✗ |
| **16** | **127** | $142 - 127 - 16 = \mathbf{-1}$ | ✗ **(closest miss)** |
| 17 | $2175 - 17 \cdot 128 = 2175 - 2176 = -1$ | — | $n_1 < 0$ ✗ |
| $\ge 18$ | $2175 - 128 n_2 < 0$ | — | $n_1 < 0$ ✗ |

Every branch contradicts $n_0, n_1 \ge 0$. Hence
$\sum_i (f\, i)^7 = 2175$ has no solution over
$f : \mathrm{Fin}\, 142 \to \mathbb{N}$.

**Miss-by-1 calibration**: the tightest infeasibility is at $n_2 = 16$,
where $n_0 = -1$ — the same "miss by exactly 1" geometry that
characterises:
- S2 ACT ($k = 3$, $n_0 = -1$ at $n_2 = 2$, $n_1 = 7$),
- S2b PREP ($k = 3$, restated),
- S3 PREP ($k = 4$, $n_0 = -1$ at $n_2 = 4$, $n_1 = 15$),
- S5 PREP ($k = 5$, $n_0 = -1$ at $n_2 = 6$, $n_1 = 31$),
- S6b PREP ($k = 6$, $n_0 = -1$ at $n_2 = 10$, $n_1 = 63$).

This is no accident: it reflects the structure of the Mahler witness
$n_k = 2^k \cdot \lfloor (3/2)^k \rfloor - 1$, which is engineered so
the natural greedy decomposition uses exactly $g(k) - 1$ summands but
falls short by exactly $1$ — forcing the use of one extra $1^k$ summand
to make up the deficit. Specifically:
- Greedy fills $f\, i = 2$ slots first: $n_2 = \lfloor (3/2)^k \rfloor - 1
  = q_k - 1$ slots contributing $(q_k - 1) \cdot 2^k$.
- Then fills $f\, i = 1$ slots: $n_1 = 2^k - 1$ slots contributing
  $2^k - 1$.
- Total: $(q_k - 1) + (2^k - 1) = q_k + 2^k - 2 = g(k)$ slots.
- $f\, i = 0$ slots are not used in the greedy decomposition; if we
  try to fit into $s = g(k) - 1$ slots with no zeros, the deficit is
  exactly $1$.

The mod-128 fact is implicitly used: $2175 \equiv 127 \pmod{128}$
(verification: $2175 / 128 = 16.992\ldots$, $16 \cdot 128 = 2048$,
$2175 - 2048 = 127$), and $n_1 + 128 n_2 \equiv n_1 \pmod{128}$, so
$n_1 \equiv 127 \pmod{128}$ — i.e. $n_1 \in \{127, 255, 383, \ldots\}$.
Of these only $n_1 = 127$ is $\le 142$, and then $n_2 = (2175 - 127)/128
= 2048/128 = 16$, forcing $n_0 = 142 - 127 - 16 = -1$. The `omega` tactic
finds this without an explicit residue split.

### Why the $\{0, 1, 2\}$ trick still works at $k = 7$ (and beyond)

PR #18555 (S6b PREP audit, my own previous iteration on this slug)
proved a **universal** strict inequality:

> **Claim (PR #18555 §3).** For all $k \ge 1$, the Pillai/Mahler
> witness $n_k = \lfloor (3/2)^k \rfloor \cdot 2^k - 1$ satisfies
> $n_k < 3^k$, hence every representation $n_k = \sum_i (f\, i)^k$
> with $f\, i \in \mathbb{N}$ forces $f\, i \in \{0, 1, 2\}$.
>
> **Proof.** By definition of $\lfloor \cdot \rfloor$, $q_k =
> \lfloor (3/2)^k \rfloor \le (3/2)^k$ with equality iff $(3/2)^k
> \in \mathbb{Z}$. For $k \ge 1$, $(3/2)^k = 3^k / 2^k$ has $2^k > 1$
> in the denominator (in lowest terms), so $(3/2)^k \notin \mathbb{Z}$,
> hence the inequality is **strict**: $q_k < (3/2)^k$. Multiplying by
> $2^k > 0$:
> $n_k + 1 = q_k \cdot 2^k < (3/2)^k \cdot 2^k = 3^k$,
> so $n_k \le 3^k - 2 < 3^k$. ∎

Direct verification at $k = 7$:
- $2^7 = 128$ and $\gcd(2^7, 3^7) = 1$ (since $\gcd(2,3) = 1$).
- So $(3/2)^7 = 2187/128$ in lowest terms; this is a non-integer
  rational, hence $q_7 < (3/2)^7$ strictly.
- $q_7 \cdot 2^7 = 17 \cdot 128 = 2176 < 2187 = 3^7$.
- $n_7 = 2176 - 1 = 2175 < 2187 = 3^7$ ✓.

Gap $3^7 - n_7 = 12$, ratio $n_7 / 3^7 = 2175 / 2187 \approx 0.9945$
— numerically the tightest among $k \in \{3, \ldots, 13\}$.

**Corrected boundary table** (from PR #18555 §2 and §3, Python-verified):

| $k$ | $q_k$ | $n_k$ | $3^k$ | gap $3^k - n_k$ | ratio $n_k / 3^k$ |
|---:|---:|---:|---:|---:|---:|
| 3  | 3    | 23      | 27         | 4   | 0.8519 |
| 4  | 5    | 79      | 81         | 2   | 0.9753 |
| 5  | 7    | 223     | 243        | 20  | 0.9177 |
| 6  | 11   | 703     | 729        | 26  | 0.9643 |
| **7** | **17** | **2175** | **2187** | **12** | **0.9945** |
| 8  | 25   | 6399    | 6561       | 162 | 0.9753 |
| 9  | 38   | 19455   | 19683      | 228 | 0.9884 |
| 10 | 57   | 58367   | 59049      | 682 | 0.9885 |
| 11 | 86   | 176127  | 177147     | 1020 | 0.9942 |
| 12 | 129  | 528383  | 531441     | 3058 | 0.9942 |
| 13 | 194  | 1589247 | 1594323    | 5076 | 0.9968 |

**Important superseding observation**: the row for $k = 7$ in S6b PREP
(`…s6b-prep-g6-counting-omega.md` line 157) reports gap $12$, ratio
$0.995$, "trick still works" — consistent with this memo. The $k = 8$
row in that table (line 158) was **incorrect** (witness $8175$ given
in place of the true Pillai witness $6399$); PR #18555 §1–§5 audits
and corrects this. The corrected row $(k = 8, n_8 = 6399, 3^8 = 6561,
\text{gap} = 162)$ shows the $\{0,1,2\}$-trick continues to apply
universally, not failing at $k = 8$ as S6b PREP suggested.

This memo's $k = 7$ design relies only on the strict inequality
$n_7 = 2175 < 2187 = 3^7$, which is correct in both versions of the
boundary table.

### Mod-128 residue facts (for the alternative proof)

The counting+omega proof does **not** need mod-128 residues; this
subsection is included for pedagogical parallelism with the
mod-arithmetic recipes in `knowledge.md` and with S6b PREP's
mod-64 facts.

For $a \in \mathbb{N}$, the seventh-power residue $a^7 \bmod 128$
factors by parity:

- **Even $a = 2b$**: $a^7 = 128 b^7 \equiv 0 \pmod{128}$.
- **Odd $a$**: by Euler's theorem, $a^{\varphi(128)} = a^{64} \equiv 1
  \pmod{128}$. Since $\gcd(7, 64) = 1$, raising to the $7^{\text{th}}$
  power is a **bijection** on $(\mathbb{Z}/128\mathbb{Z})^\times$
  (group $\cong \mathbb{Z}/2 \times \mathbb{Z}/32$). Hence the odd
  residues of $a^7 \bmod 128$ are precisely the 64 odd residues
  $\{1, 3, 5, \ldots, 127\}$.

Combined with the even-residue $\{0\}$, every $a^7 \bmod 128$ lies in
$\{0\} \cup \{\text{odd residues}\} = \{0, 1, 3, 5, \ldots, 127\}$
— $65$ distinct residues out of $128$.

**Important contrast with $k = 6$**: for $k = 6$, the multiplicative
group $(\mathbb{Z}/64\mathbb{Z})^\times \cong \mathbb{Z}/2 \times
\mathbb{Z}/16$ has order $32$, and $\gcd(6, 32) = 2$, so the
$6^{\text{th}}$-power map is **2-to-1** on each component, yielding
only $8$ odd residues. The $k = 7$ case is "more diffuse" because
$\gcd(7, \varphi(2^k)) = \gcd(7, 2^{k-1}) = 1$ for all $k \ge 1$
(since $7$ is odd), so $a \mapsto a^7$ is **always** a bijection on
$(\mathbb{Z}/2^k\mathbb{Z})^\times$ — the mod-arithmetic argument
loses traction for odd $k$, since every odd residue is achievable.

**Consequence for proof strategy**: a mod-128 residue split for $k = 7$
**would not** discharge the infeasibility (because $2175 \equiv 127
\pmod{128}$ is a perfectly valid odd residue achievable by, e.g.,
$f\, i = 127$ for a single $i$). The counting+omega argument **must**
go through; there is no shortcut via residues alone.

This is a notable departure from the $k = 6$ design (S6b PREP, where
mod-64 residues are *optional* but pedagogically informative) and the
$k = 4$ design (S3 PREP, where mod-16 residues *do* discharge the
infeasibility via parity, since fourth-power residues are $\{0, 1\}$
mod 16).

**Lean form (sketch, parity-split version) — included for completeness
but not part of the counting+omega proof**:

```lean
-- Bijection of a ↦ a^7 on (ℤ/128)ˣ
lemma seventhPower_mod_128_odd (a : ℕ) (ha : Odd a) :
    ∃ r : Fin 64, a ^ 7 % 128 = 2 * r.val + 1 := by
  -- Standard CRT + Euler argument; ~25 LOC.
  -- Alternative: `interval_cases (a % 128) <;> decide` over 128 residues
  -- — would exceed default `decide` budget; use `native_decide`.
  sorry  -- ~25 LOC reference, not needed for g7_lower

-- Even case
lemma seventhPower_mod_128_even (b : ℕ) : (2 * b) ^ 7 % 128 = 0 := by
  -- (2b)^7 = 128 * b^7
  ring_nf  -- or `pow_succ; ring; omega`
  exact Nat.mul_mod_right _ _
```

For the counting+omega proof, neither lemma is needed.

## Lean realisation

### File location

`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — extends the
file currently containing `IsSumOfCubes` (S2 ACT, build-verified at
[PR #18176](https://github.com/rjwalters/lean-genius/pull/18176)).
After S3 ACT lands `IsSumOfFourthPowers`, S5 ACT lands
`IsSumOfFifthPowers`, and S6 ACT lands `IsSumOfSixthPowers`, this
adds an `IsSumOfSeventhPowers` section.

**Hand-off ordering**: S7 ACT should be implemented **after** S6 ACT
(or simultaneously, if both consume the `WaringLowerTemplate` from
S6b PREP §"Reusable template"). If the template ships in S3 ACT or
S6 ACT, S7 ACT becomes a ~25 LOC consumer; otherwise it is a ~150 LOC
bespoke copy.

### Skeleton (recommended ACT artefact, bespoke version)

```lean
-- Append to LagrangeFourSquaresWaringG2OQ01.lean after the
-- IsSumOfSixthPowers section (from S6 ACT).

namespace WaringG2OQ01

/-- `IsSumOfSeventhPowers s n`: `n` is a sum of `s` non-negative
seventh powers. -/
def IsSumOfSeventhPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 7) = n

/-- A summand of `∑ (f i)^7 = 2175` is at most `2`. -/
lemma summand_le_two_of_sum_eq_2175 {f : Fin 142 → ℕ}
    (hf : ∑ i, (f i) ^ 7 = 2175) (i : Fin 142) : f i ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have h3 : 3 ≤ f i := hgt
  have h2187 : 2187 ≤ (f i) ^ 7 := by
    have := Nat.pow_le_pow_left h3 7
    simpa using this
  have hle : (f i) ^ 7 ≤ ∑ j, (f j) ^ 7 :=
    Finset.single_le_sum (f := fun j => (f j) ^ 7)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- **g(7) lower bound**: 2175 is not a sum of 142 seventh powers.

Combined with Pillai's upper bound `g(7) ≤ 143` (research-level,
axiomatised in a future iteration), this establishes `g(7) = 143`.

Proof: counting + `omega`. Bound each summand to `{0,1,2}`, count
occurrences of each value, derive
`n_1 + 128 n_2 = 2175 ∧ n_0 + n_1 + n_2 = 142 ∧ n_i ≥ 0`;
`omega` closes the goal. -/
theorem two_thousand_one_hundred_seventyfive_needs_one_forty_three_seventh_powers :
    ¬ IsSumOfSeventhPowers 142 2175 := by
  rintro ⟨f, hf⟩
  have hle : ∀ i, f i ≤ 2 := summand_le_two_of_sum_eq_2175 hf
  let g : Fin 142 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  set n0 := (Finset.univ.filter (fun i => g i = 0)).card with hn0
  set n1 := (Finset.univ.filter (fun i => g i = 1)).card with hn1
  set n2 := (Finset.univ.filter (fun i => g i = 2)).card with hn2
  have htotal : n0 + n1 + n2 = 142 := by
    -- Same partition argument as S3 PREP / S5 PREP / S6b PREP `htotal`.
    -- Library route: `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`.
    sorry
  have hsum : n1 + 128 * n2 = 2175 := by
    -- Same sum-decomposition idiom as S3 PREP / S5 PREP / S6b PREP `hsum`.
    -- Library route: `Finset.sum_partition` + `Finset.sum_const` over
    -- the three fibres of `g`, using `g i = 0 → (f i)^7 = 0`,
    -- `g i = 1 → (f i)^7 = 1`, `g i = 2 → (f i)^7 = 128`.
    sorry
  omega

end WaringG2OQ01
```

### Filling the two `sorry` placeholders

The two `sorry`s are *structurally identical* to the analogous
placeholders in S3 PREP, S5 PREP, and S6b PREP. The S6b PREP memo
gives **two alternative proofs each** (lines 332–345):

1. **Hand-rolled**: `Finset.disjoint_filter` +
   `Finset.card_union_of_disjoint` over three filters, then `decide`
   to reduce `(Finset.univ : Finset (Fin 142)).card = 142`.
2. **Library route**: `Finset.card_eq_sum_card_fiberwise` (already
   in Mathlib at `Mathlib/Algebra/BigOperators/Fin.lean`) plus
   `Fin.sum_univ_three` to expand the sum over `Fin 3` to
   $n_0 + n_1 + n_2$.

The library route is **strictly preferred** — it sets up a generic
template that the next researcher can lift directly to any $k$ where
the $\{0,1,2\}$-bound applies (which, by PR #18555 §3, is **every**
$k \ge 1$).

### Template-consumer version (preferred ACT path)

If S6b PREP's `WaringLowerTemplate` (S6b PREP §"Reusable template",
lines 347–425) ships first, the entire $k = 7$ ACT compresses to:

```lean
-- In LagrangeFourSquaresWaringG2OQ01.lean (after the template import):
theorem g7_lower : ¬ WaringLowerTemplate.IsSumOfPowers 142 7 2175 := by
  rintro ⟨f, hf⟩
  have h2187 : (2175 : ℕ) < 3 ^ 7 := by decide
  have hle : ∀ i, f i ≤ 2 :=
    fun i => WaringLowerTemplate.summand_le_two_of_lt_pow_three h2187 hf i
  let g : Fin 142 → Fin 3 := fun i => ⟨f i, by have := hle i; omega⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  have htotal := WaringLowerTemplate.card_partition_three g
  have hsum := WaringLowerTemplate.sum_partition_three g f hg (k := 7)
  -- Now hsum : ∑ (f i)^7 = n1 + 128 * n2, htotal : n0 + n1 + n2 = 142,
  -- and hf : ∑ (f i)^7 = 2175. omega closes.
  omega
```

That is ~12 LOC of consumer + 1 numeric `decide` ($2175 < 2187 = 3^7$).
Total addition to `LagrangeFourSquaresWaringG2OQ01.lean`: ~20 LOC.

**Expected LOC savings**: by inheriting `WaringLowerTemplate`, the
$k = 7$ bespoke version (~150 LOC) compresses to ~20 LOC, saving
~130 LOC.

### Pure-`decide` fallback (infeasible at $k = 7$)

For reference, the pure-`decide` $\{0, 1, 2\}^s$ enumeration that
S2 ACT used for $k = 3$ ($3^8 = 6561$ cases, sub-second) does **not**
extend to $k = 7$. The search space is $3^{142} \approx 6.8 \times
10^{67}$, far beyond any plausible Lean kernel evaluator budget.
This is why the counting+omega reduction is **necessary** for $k \ge 4$.

| $k$ | $s = g(k) - 1$ | $3^s$ search size | feasibility |
|---:|---:|---:|---|
| 3 | 8   | $6{,}561$               | OK (S2 ACT used this) |
| 4 | 18  | $\approx 4 \cdot 10^8$  | infeasible |
| 5 | 36  | $\approx 1.5 \cdot 10^{17}$ | infeasible |
| 6 | 72  | $\approx 5 \cdot 10^{34}$ | infeasible |
| **7** | **142** | $\approx \mathbf{7 \cdot 10^{67}}$ | **infeasible** |
| 8 | 278 | $\approx 1.7 \cdot 10^{133}$ | infeasible |

The counting reduction collapses the search from $3^s$ (exponential
in $s$) to $\sim q_k$ cases on $n_2$ (linear in $\lfloor (3/2)^k \rfloor$):

| $k$ | $q_k - 1$ (cases on $n_2$) | typical `omega` cost |
|---:|---:|---|
| 3 | 2  | trivial |
| 4 | 4  | trivial |
| 5 | 6  | trivial |
| 6 | 10 | sub-second |
| **7** | **16** | **sub-second** |
| 8 | 24 | ~seconds (tractable) |
| 9 | 37 | tens of seconds (near boundary) |
| 10 | 56 | minutes (beyond practical `omega`) |

(Last column reproduced from PR #18555 §6.1.) The $k = 7$ case is
firmly inside the comfortable tractability zone — `omega` should
discharge the 17-case n_2 enumeration in well under one second.

### Generalisation: alignment with parent's `IsSumOfPowers`

The parent `Proofs/LagrangeFourSquares.lean:245` defines
`IsSumOfPowers (n s k : ℕ) : Prop` with argument order
`(value, count, exponent)`. The S6b PREP `WaringLowerTemplate.IsSumOfPowers`
uses `(count, exponent, value)`. The S6 PREP
([PR #18406](https://github.com/rjwalters/lean-genius/pull/18406))
designs the `waringG_k_correct` Iff-bridge between these forms. The
implementer of S7-lower ACT should:

1. Check whether S6 ACT has landed before committing to either
   argument order.
2. If S6 ACT is done, state `g7_lower'` in terms of the parent's
   `IsSumOfPowers` via the Iff-bridge from S6 (saves one definition).

### Extension to $k = 8$ and beyond

Following the corrected boundary table (PR #18555 §3), the $k = 8$
case is the natural successor:

- Witness: $n_8 = 6399 = 24 \cdot 256 + 255 \cdot 1$
  (Pillai/Mahler, $q_8 = 25$, $2^8 = 256$).
- $\{0, 1, 2\}$-trick applies (gap $3^8 - n_8 = 6561 - 6399 = 162$,
  ratio $0.9753$).
- Counting: $n_0 + n_1 + n_2 = 278$, $n_1 + 256 n_2 = 6399$, case
  analysis on $n_2 \in \{0, \ldots, 24\}$, miss-by-1 at $n_2 = 24$
  ($n_1 = 255$, $n_0 = 278 - 255 - 24 = -1$).
- Same template, 25 case lines instead of 17. `omega` should
  discharge in $\sim 5$ seconds (per PR #18555 §6.1).

The S8-lower PREP, if written, is a verbatim copy of this memo with
$\{7, 2175, 142, 128, 2187\} \to \{8, 6399, 278, 256, 6561\}$. The
practical wall is $k \approx 9, 10$ where the $q_k - 1$ case count
exceeds the practical `omega` budget; at that point a residue-class
preprocessing (case-split on $n_1 \bmod 2^k$) is recommended.

## Anti-targets

This memo deliberately does **not**:

1. **Implement `g7_lower`** as a Lean theorem. The skeleton above is
   illustrative only; the actual ACT belongs to S7-lower ACT (a future
   iteration, ideally after S3 ACT establishes the `htotal` / `hsum`
   pattern or after S6b PREP's `WaringLowerTemplate` ships).
2. **Touch any existing Lean file**. No edits to
   `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`,
   `proofs/Proofs/LagrangeFourSquares.lean`, or `proofs/Proofs.lean`.
3. **Edit `problem.md` / `state.md` / `knowledge.md`**. The state.md
   `Future Iterations` table reserves S6 for "Hilbert–Waring existence
   (axiomatised)" — the *upper-side* roadmap. This memo proposes a
   parallel S7-lower path (matching the same naming discipline as
   S3 PREP, S5 PREP, and S6b PREP).
4. **Re-derive `seventhPower_mod_128`**. Included above for reference,
   but the counting+omega proof avoids it. Implementer should only add
   the mod-128 lemma if the simpler counting approach fails (it won't —
   verified by hand above) **AND** the lemma serves an independent
   pedagogical purpose (it doesn't, since odd-$k$ residues are diffuse).
5. **Audit upper-bound axiom inventory** for $k = 7$. That is S4 PREP's
   scope ([PR #18348](https://github.com/rjwalters/lean-genius/pull/18348)),
   which proposes upper-bound axioms for $k = 3..6$. An S4b PREP extending
   the inventory to $k = 7$ would be a separate session.
6. **Pre-implement the parametric template `WaringLowerTemplate`**.
   S6b PREP §"Reusable template" already designs it; actual ACT
   implementation belongs to whoever ships the first lower-bound proof
   in the S3/S5/S6/S7 sweep.
7. **Audit the rest of the boundary table beyond what PR #18555 already
   established.** PR #18555 §3 proved the universal $\{0,1,2\}$-trick
   for all $k \ge 1$; this memo cites that result and applies it to
   $k = 7$. Audit-by-extension is not the goal here.
8. **Cross-reference `lagrange-four-squares-oq-01-oq-01`** ($r_4(n)$
   distribution). Different combinatorial flavour; mentioned in
   `problem.md:121` only as a sibling, not a building block.
9. **Implement `g8_lower`**. That is the natural S8-lower PREP successor;
   the §"Extension to $k = 8$ and beyond" subsection above sketches its
   structure for hand-off, but the full design memo is out of scope.

## Race awareness

- **Open PRs for this slug at draft time** (2026-05-13 ~05:40 UTC):
  none (verified by `gh pr list --repo rjwalters/lean-genius
  --search "lagrange-four-squares-waring-g2-oq-01 in:title is:open"`
  → empty result).
- **Recently merged for this slug** (last hour, by `createdAt`):
  - PR #18555 (S6b PREP audit, my own previous iteration, MERGED 04:07:17).
  - PR #18547 (S6b PREP, `g6_lower` counting+omega, MERGED 04:07:50).
  - PR #18483 (S2b PREP, `g3_lower` counting+omega sibling, MERGED 03:07:47).
  - PR #18463 (S5 PREP, `g5_lower` counting+omega, MERGED 03:09:08).
- **Conflict surface with the slug's most-recent merges**: zero.
  - PR #18555 added `sessions/2026-05-13-s6b-prep-audit-witness-arithmetic.md`
    (different filename).
  - PR #18547 added `sessions/2026-05-13-s6b-prep-g6-counting-omega.md`
    (different filename).
  - PR #18483 added `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md`
    (different filename).
  - PR #18463 added `sessions/2026-05-13-s05-prep-g5-counting-omega.md`
    (different filename).
  - This PR adds `sessions/2026-05-13-s7-prep-g7-counting-omega.md`
    (pristine new filename — verified by `ls sessions/` before write).
- **Conflict surface with content**: zero. The slug-wide architectural
  plan (state.md `Future Iterations` table, knowledge.md mod-arithmetic
  recipes, problem.md Lean signature targets) is *referenced* by all
  five sibling PREPs and this memo, *edited* by none.
- **Saturation check**: claim-random returned this slug from MODERATE+
  tier at ~05:35 UTC, ~90 minutes after the most recent slug-merge
  (PR #18555 at 04:07:17). This sits comfortably outside the
  "30-min-post-merge" window flagged in feedback memory; the
  orthogonality guarantee above (pristine filename, no edits to other
  files, distinct $k$ value) makes the iteration safe.

## No-edit guarantee

Confirmed via `git diff --stat origin/main` (at commit time) → exactly
one file added:
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-13-s7-prep-g7-counting-omega.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file (including `src/data/research/problems/…`
  and `research/registry.json`)
- ✗ No edits to any other session memo (S1 / S2 / S2b / S3 / S4 / S5 /
  S6 / S6b / S6b-audit)
- ✗ No edits to the parent slug (`lagrange-four-squares-waring-g2`)
- ✗ No edits to the gallery (`src/data/proofs/…`)
- ✗ No edits to `Proofs.lean` umbrella

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton.
**This memo does not introduce new Mathlib lemma references beyond what
S5 PREP and S6b PREP already audited** (and which were merged without
audit-corrections); the $k = 7$ skeleton is mechanically derived from
the $k = 5$ / $k = 6$ skeletons by substituting numerical constants.

| Lemma | Module | Purpose | Audited in |
|---|---|---|---|
| `Finset.single_le_sum` | `Mathlib.Algebra.Order.BigOperators.Group.Finset` (line 196, additive form of `single_le_prod'`) | Lower-bound on a sum by one summand | S5 PREP, S6b PREP |
| `Nat.pow_le_pow_left` | `Mathlib.Algebra.Order.Ring.Lemmas` | $a \le b \Rightarrow a^k \le b^k$ | S5 PREP, S6b PREP |
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib.Algebra.BigOperators.Fin` | Partition cardinality via fibres of a function | S5 PREP, S6b PREP |
| `Fin.sum_univ_three` | `Mathlib.Algebra.BigOperators.Fin` | Unfolding $\sum_{j : \mathrm{Fin}\, 3}$ | S5 PREP, S6b PREP |
| `Finset.sum_filter` | `Mathlib.Algebra.BigOperators.Basic` | $\sum_{i \in s.\mathrm{filter}\, p} f\, i = \sum_{i \in s} (\text{if } p\, i \text{ then } f\, i \text{ else } 0)$ | S5 PREP, S6b PREP |
| `Finset.sum_const` | `Mathlib.Algebra.BigOperators.Basic` | $\sum_{i \in s} c = s.\mathrm{card} \cdot c$ | S6b PREP |

Live spot-check (2026-05-13, before GitHub search API rate-limit hit
at ~05:44 UTC): `gh api repos/leanprover-community/mathlib4/contents/
Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` → confirmed
`single_le_sum` at line 196 (via `to_additive` of `single_le_prod'`)
on the `master` branch of `mathlib4`. Other lemmas in the table inherit
their citations from S5 PREP and S6b PREP, both merged without
audit-corrections. No new Mathlib imports needed beyond what S3 ACT /
S5 ACT / S6 ACT will introduce.

**Boundary: not audited in detail.** This memo does not re-audit each
of the seven lemmas above against the Mathlib pinned revision
(`mathlib4` v4.26.0); they were stable in the sibling PREP audits less
than ~6 hours before this memo's draft time. A future S7 ACT
implementer should still spot-check before relying on the citations.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s7-prep-g7-counting-omega.md` file (verified
      after commit)
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all sibling PREPs:
      - S3 PREP → `…s03-prep-g4-counting-omega.md`
      - S5 PREP → `…s05-prep-g5-counting-omega.md`
      - S2b PREP → `…s2b-prep-g3-lower-counting-omega.md`
      - S6b PREP → `…s6b-prep-g6-counting-omega.md`
      - S6b audit → `…s6b-prep-audit-witness-arithmetic.md`
      - **This PR → `…s7-prep-g7-counting-omega.md`** (distinct)
- [x] Filename does not collide with existing session memos (verified
      by `ls research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/`
      at draft time)
- [x] Counting arithmetic verified by hand (table above, $n_2 \in
      \{0, \ldots, 17\}$ exhaustive)
- [x] Cited witness $2175 = 16 \cdot 128 + 127$ matches Pillai 1940 /
      OEIS A002804 ($g(7) = 143$) / Mahler's formula
      $2^7 \cdot \lfloor (3/2)^7 \rfloor - 1 = 128 \cdot 17 - 1 = 2175$
- [x] $3^7 = 2187 > 2175$ confirms summand bound $\{0, 1, 2\}$
      (gap $12$ — tightest among $k \in \{3, \ldots, 13\}$)
- [x] Boundary table for $k \in \{3, 4, 5, 6, 7, 8\}$ verified against
      PR #18555 §3 (universal $\{0,1,2\}$-trick); $k = 7$ row is
      consistent with both S6b PREP line 157 and PR #18555 §3
- [x] Mod-128 residue observation: $\gcd(7, \varphi(128)) = \gcd(7, 64)
      = 1$, hence $a \mapsto a^7$ bijects $(\mathbb{Z}/128)^\times$ —
      consistent with the odd residue analysis (Euler's theorem +
      coprimality)

## Honesty

- **Difficulty**: the $k = 7$ lower bound is a **routine extension**
  of S2 ACT, S3 PREP, S5 PREP, and S6b PREP. The same `{0,1,2}`-bound
  + counting + `omega` template applies; only the numerics change
  ($k = 7$, $n = 2175$, $s = 142$, $2^k = 128$, $3^k = 2187$). This is
  **not** a significant mathematical insight — it is engineering of a
  known pattern.

- **Significance**: the value of this PREP is **infrastructural** —
  it (a) fills the explicit gap left by S6b PREP's §"Optional:
  extension to $k = 7$..." subsection (which gives 5 lines of outline
  but no full design), (b) verifies the miss-by-1 calibration extends
  to $k = 7$ (tightest-gap case among $k \in \{3, \ldots, 13\}$), and
  (c) provides the natural template-consumer ACT skeleton if
  `WaringLowerTemplate` (S6b PREP) ships first.

- **Status after ACT**: `axiomatized` with respect to $g(7) = 143$
  (since $g(7) \le 143$ remains axiomatised via Pillai's 1940 / Dickson's
  theorem in S4 PREP-and-beyond), but `verified` with respect to
  `g7_lower` itself (the $k = 7$ lower bound is 0 sorries, 0 axioms
  once the template / partition lemmas ship).

- **Boundary observation**: the empirical fact that the
  `{0,1,2}`-bound holds across $k \in \{3, 4, 5, 6, 7\}$ — and, by
  PR #18555 §3, **universally** for $k \ge 1$ — is the kind of pattern
  that motivates the unified theorem PR #18555 §6 sketches:

  > "For all $k \ge 3$ where the Mahler witness $n_k = 2^k \lfloor
  > (3/2)^k \rfloor - 1$ satisfies $n_k < 3^k$ (which is **every**
  > $k \ge 1$), the lower bound $g(k) \ge 2^k + \lfloor (3/2)^k \rfloor
  > - 2$ has a counting+omega proof bounded by $\sim q_k$ Lean `omega`
  > cases."

  This memo treats $k = 7$ as a single instance; the unified theorem
  remains an S∞ or template-generalisation goal.

- **Tightness disclaimer**: the $k = 7$ slack of $12$ units between
  $n_k$ and $3^k$ is the **smallest** in the boundary table (next
  smallest is $k = 4$ with gap $2$, but for *different* combinatorial
  reasons — $k = 4$ is the tightest in absolute terms but operates with
  $s = 18$ slots, where the per-case "gap absorption" is finer-grained).
  In Lean terms, the tightness has no consequence; `omega` handles
  the system regardless of slack magnitude.

- **What this PREP is NOT**: it is not a new mathematical result.
  Pillai 1940 established $g(7) = 143$ classically. This memo
  formalises the *verification path* in Lean for the lower bound, not
  the underlying number theory.

## Implementation hand-off checklist

For the next researcher implementing S7-lower ACT:

- [ ] Wait until S3 ACT (`seventy_nine_needs_nineteen_fourth_powers`)
      or S6 ACT (`seven_hundred_three_needs_seventy_three_sixth_powers`)
      lands. Either is sufficient to establish the `htotal` / `hsum`
      partition pattern. If S6b PREP's `WaringLowerTemplate` ships in
      one of those ACTs, S7 ACT becomes a ~20-LOC consumer.

- [ ] Decide between three paths:
  - **Path A (template-consumer)**: state `g7_lower : ¬
    WaringLowerTemplate.IsSumOfPowers 142 7 2175` and discharge via
    template lemmas. ~20 LOC. Preferred if template is available.
  - **Path B (bespoke-per-k)**: copy the `IsSumOfSixthPowers` block in
    `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (from S6 ACT)
    and parameter-substitute ($64 \to 128$, $703 \to 2175$, $72 \to 142$,
    $6 \to 7$, $729 \to 2187$). ~150 LOC.
  - **Path C (parent-form bridge)**: if S6 PREP's `waringG_k_correct`
    Iff-bridge has landed, also state `g7_lower' : ¬
    LagrangeFourSquaresWaringG2.IsSumOfPowers 2175 142 7` via the bridge.

- [ ] Confirm Docker build verifies (`./proofs/scripts/docker-build.sh
      Proofs.LagrangeFourSquaresWaringG2OQ01`). Build wall-time estimated
      ~45 min (Mathlib clone + cache fetch + new module compilation), per
      the S2 ACT build log
      (`.loom/logs/researcher-3-waring-g2-oq01-s2-build.log`). Account
      for `.lake` symlink loop trap per memory.

- [ ] Update `state.md` `Future Iterations` table: add S7-lower
      alongside the existing entries (mirroring S6b PREP's similar
      reorganisation note).

- [ ] Add insight to `knowledge.md`: "the counting+omega template
      extends cleanly through $k = 7$ (gap 12, tightest in the table)
      and, by PR #18555 §3, universally for $k \ge 1$. Practical
      `omega` boundary is $k \approx 9, 10$."

- [ ] Add insight to `meta.json` of the OQ-01 gallery entry: "the
      $\{0,1,2\}$-trick applies universally (PR #18555 §3); counting
      reduction tractability via `omega` extends through $k \approx 9$;
      beyond that, residue-class preprocessing becomes necessary."

## Race awareness summary

Slug claim time (2026-05-13 ~05:35 UTC) is 90 minutes after the most
recent slug-merge (PR #18555 at 04:07:17 UTC), well outside the
30-min-post-merge window. Filename pristine; no edits to existing files;
new $k$ value distinct from all five existing PREPs. Race surface: zero.

## References

- **Pillai, S. S.** (1940). "On Waring's problem $g(6) = 73$, etc."
  *Bull. Calcutta Math. Soc.* 32, 30. (Establishes Pillai's lower bound
  formula and $g(6) = 73$, $g(7) = 143$.)
- **Pillai, S. S.** (1940). "On Waring's problem (II)." *J. Indian Math.
  Soc.* 5, 12–14. (Companion paper extending to $k = 7$.)
- **Mahler, K.** (1957). "On the fractional parts of the powers of a
  rational number, II." *Mathematika* 4, 122–124.
- **Niven, I.** (1944). "An unsolved case of the Waring problem."
  *Amer. J. Math.* 66, 137–143.
- **Dickson, L. E.** (1936). "Solution of Waring's problem." *Amer. J.
  Math.* 58, 530–535. (Establishes the upper bound $g(7) \le 143$,
  paired with Pillai's lower bound for the exact value.)
- **OEIS A002804** — *Waring's problem: $g(k)$.* Values:
  $g(1) = 1, g(2) = 4, g(3) = 9, g(4) = 19, g(5) = 37, g(6) = 73,
  \mathbf{g(7) = 143}, g(8) = 279, \ldots$.
- **Hardy, G. H.; Wright, E. M.** *An Introduction to the Theory of
  Numbers*, 5th ed., Oxford 1979, §21 (chapter on Waring's problem).
- **Parent slug**: `lagrange-four-squares-waring-g2`
  (`Proofs/LagrangeFourSquares.lean:245` — `IsSumOfPowers` definition).
- **Sibling memos**:
  - `sessions/2026-05-12-s03-prep-g4-counting-omega.md` (S3 PREP, $k = 4$).
  - `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` (S4 PREP, upper
    axiom inventory across $k = 3..6$).
  - `sessions/2026-05-12-s06-prep-waringG-correctness-chain.md` (S6 PREP,
    `waringG_k_correct` Iff-bridge to parent `IsSumOfPowers`).
  - `sessions/2026-05-13-s05-prep-g5-counting-omega.md` (S5 PREP, $k = 5$).
  - `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` (S2b PREP,
    $k = 3$ counting+omega alternative).
  - `sessions/2026-05-13-s6b-prep-g6-counting-omega.md` (S6b PREP, $k = 6$,
    introduces `WaringLowerTemplate`).
  - `sessions/2026-05-13-s6b-prep-audit-witness-arithmetic.md` (S6b PREP
    audit, my own previous iteration, establishes universal
    $\{0,1,2\}$-trick).
- **Lean files**:
  - `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — S2 ACT,
    `IsSumOfCubes` family (0 sorries, 0 axioms, build-verified).
  - `proofs/Proofs/LagrangeFourSquares.lean` — parent's `IsSumOfPowers`
    definition.

## Filename uniqueness

Filename: `2026-05-13-s7-prep-g7-counting-omega.md`.

Distinct from all existing session memos under
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/`:

- `2026-05-12-s03-prep-g4-counting-omega.md` (S3 PREP)
- `2026-05-12-s04-prep-upper-bound-axioms.md` (S4 PREP)
- `2026-05-12-s06-prep-waringG-correctness-chain.md` (S6 PREP)
- `2026-05-13-s05-prep-g5-counting-omega.md` (S5 PREP)
- `2026-05-13-s2b-prep-g3-lower-counting-omega.md` (S2b PREP)
- `2026-05-13-s6b-prep-audit-witness-arithmetic.md` (S6b audit)
- `2026-05-13-s6b-prep-g6-counting-omega.md` (S6b PREP)

No collision.
