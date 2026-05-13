# S6b PREP — Audit of `{0,1,2}`-trick boundary claim at $k = 8$

**Date**: 2026-05-13
**Agent**: researcher-4
**Phase**: PREP (doc-only)
**Scope**: audit-correction of one specific arithmetic claim in
  PR [#18547](https://github.com/rjwalters/lean-genius/pull/18547)
  ("S6b PREP — `g6_lower` via counting + omega").
**Anti-target**: do **not** rewrite, supersede, or re-design the
  reusable `WaringLowerTemplate` proposal in PR #18547; that
  proposal is orthogonal to this audit. The only claim under review
  is the boundary table at $k = 8$.

## Summary

PR [#18547](https://github.com/rjwalters/lean-genius/pull/18547)'s
boundary table (the "Why the $\{0, 1, 2\}$-trick still works at
$k = 6$" section, and again in the "Optional: extension to $k = 7$
and the $k = 8$ boundary" subsection) claims:

> "{0,1,2}-trick extends through $k = 7$ (witness $2175 < 3^7 = 2187$);
> fails first at $k = 8$ (**$8175 > 6561 = 3^8$**)"

The number **$8175$** is arithmetically incorrect for the canonical
Pillai witness $n_k = q \cdot 2^k - 1$ with $q = \lfloor (3/2)^k \rfloor$.
The true $k = 8$ Pillai witness is $\mathbf{6399}$, and
$6399 < 6561 = 3^8$, so the $\{0, 1, 2\}$-trick **continues to apply
at $k = 8$** — and, in fact, at every $k \ge 3$.

The qualitative consequence: the $\{0, 1, 2\}$-bound is **not** the
boundary at which the counting reduction stops being applicable.
The actual boundary is **Lean evaluator tractability** on the
$(q-1)$-case partition analysis, which grows as $q = \lfloor (3/2)^k \rfloor$.

## §1. The arithmetic claim under review

PR #18547 lines 154–164 (counts via `git show pr-18547:…/sessions/2026-05-13-s6b-prep-g6-counting-omega.md`):

```
| 8 | 8175 | 6561 | -1614 | 1.246 (trick fails) |
```

and:

> "At $k = 8$, the witness $8175$ exceeds $3^8 = 6561$ by 1614, so
> the bound widens to $\{0, 1, 2, 3\}$ and the counting reduction
> becomes a 3D integer feasibility check."

The same number $8175$ is repeated in the §"Optional: extension to
$k = 7$ and the $k = 8$ boundary" subsection (lines 441–457):

> "At $k = 8$: witness $n = 8175$, $3^8 = 6561$, $8175 > 6561$. The
> bound widens to $\{0, 1, 2, 3\}$ (since $4^8 = 65536 > 8175 >
> 6561 = 3^8$). Counting becomes a 3D system $n_0 + n_1 + n_2 + n_3
> = 278$, $n_1 + 256 n_2 + 6561 n_3 = 8175$ (with $2^8 = 256$,
> $3^8 = 6561$)."

The witness is also referenced indirectly in the §"Boundary table"
preamble:

> "The pattern shows that the $\{0,1,2\}$-bound holds with slack
> oscillating between 2 and 26 for $k \in \{3, 4, 5, 6, 7\}$ —
> never breaking."

The implicit claim is therefore: **for $k \le 7$ the Pillai witness
$n_k$ satisfies $n_k < 3^k$, and for $k \ge 8$ it does not**.

## §2. Pillai's witness formula and Mahler's bound

The classical Pillai witness for Waring's $g(k)$ lower bound (Pillai
1940, *Proc. Indian Acad. Sci.* 12:30–40) takes

$$
\boxed{\, n_k \;=\; q_k \cdot 2^k - 1 \quad\text{with}\quad
q_k = \lfloor (3/2)^k \rfloor \,}.
$$

The "miss-by-1" calibration partitions $n_k$ over summands in
$\{0, 1, 2\}$ as

$$
n_k = (q_k - 1) \cdot 2^k + (2^k - 1) \cdot 1^k,
$$

forcing $s_{\min} = (q_k - 1) + (2^k - 1) = 2^k + q_k - 2 = g(k)$
(Mahler's formula; Mahler 1957 conjectured and Niven 1944 had the
lower bound — Pillai gave the full identification of $g(k)$ for
sufficiently large $k$).

Pillai sibling-witness consistency across the family (confirmed by
S2, S3-PREP, S5-PREP, S6-PREP of the present slug):

| $k$ | $q_k$ | $n_k$ | $2^k$ | partition $((q_k{-}1) \cdot 2^k + (2^k{-}1) \cdot 1)$ | $g(k)$ |
|---:|---:|---:|---:|---|---:|
| 3 | 3   | 23    | 8   | $2 \cdot 8 + 7 \cdot 1 = 16 + 7$            | 9   |
| 4 | 5   | 79    | 16  | $4 \cdot 16 + 15 \cdot 1 = 64 + 15$         | 19  |
| 5 | 7   | 223   | 32  | $6 \cdot 32 + 31 \cdot 1 = 192 + 31$        | 37  |
| 6 | 11  | 703   | 64  | $10 \cdot 64 + 63 \cdot 1 = 640 + 63$       | 73  |
| 7 | 17  | 2175  | 128 | $16 \cdot 128 + 127 \cdot 1 = 2048 + 127$   | 143 |
| 8 | 25  | **6399** | 256 | $24 \cdot 256 + 255 \cdot 1 = 6144 + 255$ | 279 |

The $k = 8$ row gives Pillai witness $\mathbf{n_8 = 6399}$, **not**
$8175$.

## §3. The {0,1,2}-trick is universal

**Claim.** For all $k \ge 1$, the Pillai witness $n_k =
\lfloor (3/2)^k \rfloor \cdot 2^k - 1$ satisfies $n_k < 3^k$, hence
every representation $n_k = \sum_i (f i)^k$ with $f i \in \mathbb{N}$
forces $f i \in \{0, 1, 2\}$.

**Proof.** By definition of `floor`, $q_k = \lfloor (3/2)^k \rfloor
\le (3/2)^k$ with equality iff $(3/2)^k \in \mathbb{Z}$. For $k \ge 1$,
$(3/2)^k = 3^k / 2^k$ has $2^k > 1$ in the denominator (in lowest
terms), so $(3/2)^k \notin \mathbb{Z}$, hence the inequality is
**strict**: $q_k < (3/2)^k$. Multiplying by $2^k > 0$:

$$
n_k + 1 = q_k \cdot 2^k < (3/2)^k \cdot 2^k = 3^k,
$$

so $n_k \le 3^k - 2 < 3^k$. ∎

**Sanity-check table** (Python-verified, $k = 3 \ldots 13$):

| $k$ | $q_k$ | $n_k$ | $3^k$ | gap $3^k - n_k$ | ratio $n_k / 3^k$ |
|---:|---:|---:|---:|---:|---:|
| 3  | 3    | 23      | 27         | 4    | 0.8519 |
| 4  | 5    | 79      | 81         | 2    | 0.9753 |
| 5  | 7    | 223     | 243        | 20   | 0.9177 |
| 6  | 11   | 703     | 729        | 26   | 0.9643 |
| 7  | 17   | 2175    | 2187       | 12   | 0.9945 |
| 8  | 25   | **6399**| **6561**   | **162** | **0.9753** |
| 9  | 38   | 19455   | 19683      | 228  | 0.9884 |
| 10 | 57   | 58367   | 59049      | 682  | 0.9885 |
| 11 | 86   | 176127  | 177147     | 1020 | 0.9942 |
| 12 | 129  | 528383  | 531441     | 3058 | 0.9942 |
| 13 | 194  | 1589247 | 1594323    | 5076 | 0.9968 |

The ratio approaches $1$ from below but never reaches it. The
asymptotic gap is

$$
3^k - n_k = 3^k - q_k \cdot 2^k + 1 = \{(3/2)^k\} \cdot 2^k + 1
$$

where $\{x\}$ denotes fractional part; this grows like
$2^k \cdot \overline{(3/2)^k} \approx 2^{k-1}$ on average (by
equidistribution of $\{(3/2)^k\}$, a classical open problem).
Even in the worst case the gap is bounded below by $\ge 2$ for
$k \in \{3, \ldots, 13\}$.

## §4. Refutation of the $k = 8$ "boundary" claim

Substituting the correct Pillai witness $n_8 = 6399$ into PR #18547's
boundary table:

| $k$ | witness $n_k$ | $3^k$ | gap $3^k - n_k$ | ratio | PR #18547's "fails?" |
|---:|---:|---:|---:|---:|---|
| 6 | 703  | 729  | 26  | 0.9643 | "still works" ✓ |
| 7 | 2175 | 2187 | 12  | 0.9945 | "still works" ✓ |
| **8** | **6399** | **6561** | **162** | **0.9753** | claimed "fails" ✗ |
| 9 | 19455 | 19683 | 228 | 0.9884 | (claimed boundary already passed) |

In particular, the $k = 8$ gap of **162** is **larger** than the
$k = 6$ gap of 26 and the $k = 7$ gap of 12 — so by PR #18547's own
"slack oscillating between 2 and 26" narrative, $k = 8$ would
qualify as "still works", not "fails first".

The partition at $k = 8$ proceeds exactly as for $k \le 7$:

- $n_0 + n_1 + n_2 = 278$,  $n_1 + 256 \cdot n_2 = 6399$.
- Case analysis on $n_2 \in \{0, \ldots, 24\}$ (i.e., $q_8 - 1 = 24$ cases).
- Miss-by-1 at $n_2 = 24$: $n_1 = 6399 - 6144 = 255$, $n_0 = 278 - 255 - 24 = -1$ ✗.

No widening to $\{0, 1, 2, 3\}$ is required.

## §5. Where does the number 8175 come from?

I cannot identify a closed-form for $8175$ tied to the Pillai/Mahler
construction. Possibilities (none of which match):

- $q = 32 \Rightarrow q \cdot 2^k - 1 = 32 \cdot 256 - 1 = 8191$. Not 8175.
- $q = 32, n = q \cdot 256 - 17 = 8175$ — no principled origin.
- $\lceil (3/2)^8 \rceil \cdot 2^8 - 1 = 26 \cdot 256 - 1 = 6655$. Not 8175.
- $g(8) \cdot 2^8 - 1 = 279 \cdot 256 - 1 = 71423$. Not 8175.
- $g(8) - 1 + 2^k \cdot \text{something}$ — does not produce 8175.

The most likely explanation is an arithmetic slip during table
construction (perhaps reusing a partial formula from $k = 9$ where
$q_9 = 38$ but multiplying by an off-by-one power, or a transcription
error from an external source). The PR's Python-verification
checkboxes (test-plan items 4–6) cover the $k = 6$ witness $703$
and the mod-64 residue set, but the boundary-table entries for
$k \ge 7$ are not in the listed verification items.

## §6. What actually fails as $k$ grows

The $\{0, 1, 2\}$-bound on summands is **not** the boundary; it is
universal. The boundaries that actually matter:

### §6.1. Lean `omega` case-analysis size

The counting reduction has $q_k - 1$ cases on $n_2$. For:

| $k$ | $q_k - 1$ (cases) | typical `omega` cost |
|---:|---:|---|
| 3  | 2    | trivial |
| 4  | 4    | trivial |
| 5  | 6    | trivial |
| 6  | 10   | sub-second |
| 7  | 16   | sub-second |
| 8  | 24   | ~seconds; still tractable |
| 9  | 37   | tens of seconds; near boundary |
| 10 | 56   | minutes; beyond practical `omega` |
| 11 | 85   | infeasible in single `omega` call |

The natural Lean idiom (`interval_cases n_2 <;> omega`) becomes
expensive past $k \approx 9$, because each case spawns an
`omega`-decidable Presburger problem. This is the **actual** S8/S9
boundary, not a $\{0, 1, 2\}$ vs. $\{0, 1, 2, 3\}$ summand split.

### §6.2. Kernel `decide` evaluator budget

For the purely-syntactic $\{0, 1, 2\}^s$ search (the S2 ACT pattern
at $k = 3$), the search space is $3^s$. For:

| $k$ | $s = g(k) - 1$ | $3^s$ search size |
|---:|---:|---:|
| 3 | 8   | $6{,}561$        | OK |
| 4 | 18  | $\approx 4 \cdot 10^8$ | infeasible |
| 5 | 36  | $\approx 1.5 \cdot 10^{17}$ | infeasible |
| 6 | 72  | $\approx 5 \cdot 10^{34}$ | infeasible |

So the pure-`decide` $3^s$ enumeration scales out at $k = 4$,
regardless of the witness arithmetic. This is why all sibling
PREPs ($k = 4, 5, 6$) use the counting reduction rather than
pure `decide`.

### §6.3. Counter to PR #18547's recovery suggestion

PR #18547 §"Optional: extension to $k = 7$ and the $k = 8$ boundary"
suggests, in response to the (incorrect) $k = 8$ failure:

> "the bound widens to $\{0, 1, 2, 3\}$ (since $4^8 = 65536 > 8175 >
> 6561 = 3^8$). Counting becomes a 3D system $n_0 + n_1 + n_2 + n_3
> = 278$, $n_1 + 256 n_2 + 6561 n_3 = 8175$"

This 3D widening is **never needed for the Pillai witness**: at
$k = 8$ the witness $6399$ admits the standard 2D partition
$(n_2, n_1, n_0)$ with $n_2 \in \{0, \ldots, 24\}$. The only
scenario in which a 3D widening is required is if one chooses a
**different** witness exceeding $3^k$ — which the Pillai
construction explicitly avoids by design.

(If a researcher later wants to switch witnesses, e.g. to optimise
for a smaller value of $s$, they would need to verify the witness
they choose still satisfies $n < (k_{\max}{+}1)^k$ for the chosen
summand bound $k_{\max}$. This is a separate optimisation question
from "does Pillai's witness work at $k = 8$".)

## §7. Concrete patch suggestions for PR #18547

This memo is **doc-only** and does not edit the file under audit
(see "Anti-targets" below). However, for the author / merger of
PR #18547, the minimal correction would be:

### §7.1. Boundary table row for $k = 8$

Replace:
```
| 8 | 8175 | 6561 | -1614 | 1.246 (trick fails) |
```
with:
```
| 8 | 6399 | 6561 | 162 | 0.975 |
```

(and remove the "trick fails" annotation; the trick still works).

### §7.2. Surrounding paragraph

Replace the conclusion paragraph

> "At $k = 8$, the witness $8175$ exceeds $3^8 = 6561$ by 1614, so
> the bound widens to $\{0, 1, 2, 3\}$ and the counting reduction
> becomes a 3D integer feasibility check."

with the corrected version (matching the universal-applicability
proof in §3 of this memo):

> "The Pillai witness $n_k = q_k \cdot 2^k - 1$ satisfies
> $n_k < 3^k$ for **all** $k \ge 1$ (proof: $q_k = \lfloor
> (3/2)^k \rfloor < (3/2)^k$ strictly, since $(3/2)^k \notin
> \mathbb{Z}$). The $\{0, 1, 2\}$-bound is therefore universal,
> and the boundary at which the counting reduction stops being
> practical is **Lean evaluator tractability** on the $(q_k - 1)$-
> case partition analysis, which grows as $q_k = O((3/2)^k)$.
> The practical boundary is $k \approx 9 \ldots 10$, where
> $q_k - 1 \in \{37, 56\}$ cases on $n_2$ stress `omega` budgets."

### §7.3. §"Optional: extension to $k = 7$ and the $k = 8$ boundary"

Remove the "bound widens to $\{0, 1, 2, 3\}$" paragraph and replace
with the 2D Pillai partition at $k = 8$:

> "At $k = 8$: witness $n_8 = 6399 = 24 \cdot 256 + 255 \cdot 1$;
> $\{0, 1, 2\}$-bound applies (gap $162$). Counting:
> $n_0 + n_1 + n_2 = 278$, $n_1 + 256 \cdot n_2 = 6399$, case
> analysis on $n_2 \in \{0, \ldots, 24\}$, miss-by-1 at $n_2 = 24$
> ($n_1 = 255$, $n_0 = -1$). Same template as $k \in \{3, 4, 5, 6\}$,
> 25 case lines instead of 11. The S8-lower PREP, if written,
> would be a verbatim copy with $\{6, 703, 72, 64, 729\} \to
> \{8, 6399, 278, 256, 6561\}$."

## §8. Implications for the reusable `WaringLowerTemplate`

PR #18547's reusable-template proposal (§"Reusable template (key
payoff)") states four parametric lemmas:

```
IsSumOfPowers (s k n : ℕ) : Prop
summand_le_two_of_lt_pow_three : n < 3^k → ∀ i, f i ≤ 2
card_partition_three : ∀ g : Fin s → Fin 3, n_0 + n_1 + n_2 = s
sum_partition_three : ∑ i, (f i)^k = n_1 + 2^k · n_2
```

The hypothesis $n < 3^k$ in `summand_le_two_of_lt_pow_three` is
**precisely** the universal $\{0, 1, 2\}$-trick. Under the audit
correction, this hypothesis is **automatically satisfied** for the
Pillai witness $n_k$ at every $k$, and the template is therefore
applicable across the whole $k \ge 3$ family — including the
$k = 8, 9, \ldots$ rows that PR #18547 conditionally excludes.

The template's saving estimate (~500 LOC across S3 / S5 / S6 / S7)
should arguably be revised upward to account for $k = 8, 9$ as well,
provided one can manage the larger `omega` budgets. Concretely:

- S3 (k=4): 4 cases × 25 LOC = consumer ≈ 25 LOC
- S5 (k=5): 6 cases × similar = consumer ≈ 25 LOC
- S6 (k=6): 10 cases = ≈ 25 LOC
- S6b (k=6, this PR's target): same as S6, ≈ 25 LOC
- S7 (k=7): 16 cases = ≈ 30 LOC (slight bloat)
- S8 (k=8): 24 cases = ≈ 35 LOC (still tractable)

Adding $k \in \{7, 8\}$ to the family extends the LOC savings from
~500 to ~700 across S3 / S5 / S6 / S6b / S7 / S8.

## §9. Pre-flight verification (the PR's own test plan)

PR #18547's test-plan checklist:

- [x] Case-analysis arithmetic Python-verified
- [x] Witness $703 = 64 \cdot 11 - 1$ matches Pillai 1940 / OEIS A002804
- [x] Mod-64 residue set $\{0, 1, 9, 17, 25, 33, 41, 49, 57\}$ Python-confirmed
- [x] Boundary $k = 8$ identified ($8175 > 6561$)

The fourth checkbox is the one this audit refutes: $8175$ is not
the Pillai witness at $k = 8$. The actual Pillai witness $6399$
**does not** exceed $3^8 = 6561$.

(The first three test-plan items appear correct: $703 = 11 \cdot 64
- 1$ matches Pillai for $k = 6$; the mod-64 residue set
$\{0, 1, 9, 17, 25, 33, 41, 49, 57\}$ is the standard $6$th-power
residue set computed from $a^6 \equiv 1 + 24 k \pmod{64}$ for odd $a$
with $k = (a^2 - 1)/8$ via lifting-the-exponent.)

## §10. Honest scope and what this audit does **not** do

1. **No Lean edits.** This memo is doc-only.
2. **No edits to PR #18547.** The author / merger may choose to
   address the audit by amending the open PR, by merging as-is
   with a follow-up correction, or by closing and re-opening.
   This audit memo provides the arithmetic ground truth and patch
   suggestions; the dispositional choice is theirs.
3. **No claim about the reusable template's other content.** The
   `WaringLowerTemplate` proposal, the mod-64 residue facts, and
   the $k = 6$ counting reduction are all consistent with the
   sibling PREPs and not under review here.
4. **No new design for $g7_lower$ / $g8_lower$.** Those are the
   natural successors and remain open for separate PREP docs.
5. **No claim about the parent OQ-01 problem statement** ($g(k)$
   exact values for $k \ge 7$). This audit is about the design
   memo's boundary table, not about the underlying mathematics
   of Waring's problem.

## §11. Citations and verification

- **Pillai 1940**: S. S. Pillai, "On Waring's problem,"
  *Proc. Indian Acad. Sci. Sect. A* **12** (1940), 30–40.
- **Mahler 1957**: K. Mahler, "On the fractional parts of the
  powers of a rational number (II)," *Mathematika* **4** (1957),
  122–124.
- **OEIS A002804**: $g(k)$ for $k = 1, 2, 3, \ldots$ —
  $1, 4, 9, 19, 37, 73, 143, 279, 548, 1079, \ldots$
- **Python verification**: tables in §2 and §3 generated by
  ```python
  for k in range(3, 14):
      q = (3**k) // (2**k)
      n_k = q * (2**k) - 1
      print(k, q, n_k, 3**k, 3**k - n_k, n_k / 3**k)
  ```
  (output reproducible; the $k = 8$ row gives `8 25 6399 6561 162 0.9753`).

## §12. Decision matrix for the merger

| Disposition | Effort | Risk | Recommendation |
|---|---|---|---|
| Merge PR #18547 as-is, accept this audit follow-up | low | erroneous claim sits in `main` for ~hours | acceptable if S6b template is the priority |
| Author amends PR #18547 with §7 patches | low (≤10 line edit) | clean | preferred |
| Close PR #18547 and rewrite | high | rework cost | not necessary; only the boundary table is wrong, not the core proposal |

The recommended path is **author amends**: the patches in §7 are
~10 lines total and preserve the core reusable-template proposal.

## §13. Anti-targets (this PR)

This memo deliberately does **not**:

1. Edit `problem.md`, `state.md`, `knowledge.md`, or
   `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`.
2. Edit any sibling PREP under `sessions/` (S1 / S2 / S2b / S3 /
   S4 / S5 / S6).
3. Edit `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` or
   propose a `WaringLowerTemplate.lean` skeleton — that is
   PR #18547's domain.
4. Edit the parent slug `lagrange-four-squares-waring-g2` or its
   gallery data.
5. Make any claim about the merit of PR #18547 beyond the single
   audited arithmetic claim. (The reusable template is a strong
   proposal and should advance regardless of the $k = 8$ row.)

## §14. Filename uniqueness

Filename: `2026-05-13-s6b-prep-audit-witness-arithmetic.md`.

Distinct from PR #18547's `2026-05-13-s6b-prep-g6-counting-omega.md`
and from all sibling PREPs:

- `2026-05-12-s03-prep-g4-counting-omega.md`
- `2026-05-12-s04-prep-upper-bound-axioms.md`
- `2026-05-12-s06-prep-waringG-correctness-chain.md`
- `2026-05-13-s05-prep-g5-counting-omega.md`
- `2026-05-13-s2b-prep-g3-lower-counting-omega.md`
- `2026-05-13-s6b-prep-g6-counting-omega.md` (PR #18547)

No collision.
