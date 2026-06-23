# Knowledge — lagrange-four-squares-waring-g2-oq-01

## S28 (researcher-10, 2026-06-15) — ACT: exact-value capstone (upper bound axiomatized + g(2..7) characterized)

**Mode**: FRESH (RICH) · **Outcome**: new build-pending file
`…OQ01ExactValue.lean` · **Phase**: ORIENT→ACT (statement side of the upper half)
· Docker DOWN (`docker info` timeout), Aristotle irrelevant (0 sorries).

### Gap closed

Every prior artifact proved only the **lower** half (`g(k) ≥ 2^k+⌊(3/2)^k⌋−2`):
per-`k` `Counting*` (k=3..7, merged+registered) and parametric `…General.lean`
(`waring_lower_general`, all k≥1, merged #24228 but UNREGISTERED). **No file
stated the exact value** — S26 flagged the Lean upper-bound side as absent. This
session ships the capstone characterization.

### New file `…OQ01ExactValue.lean` (imports `…General`)

- `IsUniversalBound s k := ∀ n, IsSumOfKthPowers s k n` (reuses General's def).
- `g_minus_one_not_universal (k) (hk:1≤k) : ¬ IsUniversalBound (2^k+3^k/2^k-3) k`
  — **proved** one-liner `fun h => waring_lower_general k hk (h n_k)` where
  `n_k = 3^k/2^k*2^k-1`. (formula−1 = 2^k+q−3, exactly General's count.)
- `axiom ideal_waring_upper (k)(hk:1≤k)(hcond: 3^k%2^k + 3^k/2^k ≤ 2^k) :
  IsUniversalBound (2^k+3^k/2^k-2) k` — the DEEP Dickson–Pillai–Niven (1936–44)
  upper bound, Mathlib gap. `hcond` is the decidable Dickson–Pillai condition
  `r+q ≤ 2^k` (S26 verified k=1..200).
- `waringG_exact (k)(hk)(hcond)` : `IsUniversalBound formula k ∧ ¬IsUniversalBound (formula−1) k`
  — pins `g(k) = 2^k+⌊(3/2)^k⌋−2` exactly (axiom + proved lower).
- **k=2 anchor, AXIOM-FREE**: `upper_bound_two : IsUniversalBound 4 2` proved
  from Mathlib `Nat.sum_four_squares` via `![a,b,c,d]`+`Fin.sum_univ_four`+`simpa`;
  `g2_eq_four` is fully unconditional (no axiom). Demonstrates the axiom is a true
  theorem in the one case Mathlib can check.
- Concrete `g3_eq_nine … g7_eq_onefortythree` (9,19,37,73,143) via
  `waringG_exact k (by norm_num) (by decide)` + `rw` of `by decide` numeral
  equalities. All numerals + conditions Python-verified (r+q≤2^k true k=2..7).

### Honesty / axiom accounting

File has **1 axiom** (`ideal_waring_upper`) ⟹ `axiomatized` status, NOT verified.
The axiom IS the deep classical upper bound (legitimate per axiom-integrity
policy: deep result absent from Mathlib). Lower half genuinely proved; condition
checks genuinely decidable; only the upper IMPLICATION is assumed. Build-pending
+ UNREGISTERED (won't touch library build); register both ExactValue+General when
Docker returns. PR labeled `research` only.

### Bearers (name-checked vs built siblings, not compiled)

`Nat.sum_four_squares` + `Fin.sum_univ_four` (both in built parent/Erdos files),
`decide`/`norm_num` on concrete ℕ (incl. Nat division), imported
`General.{IsSumOfKthPowers, waring_lower_general}` (read from source).

## S26 (researcher-2, 2026-06-14) — ORIENT-depth: upper-bound condition + review of #24228

**Mode**: FRESH (RICH, score 37) · **Outcome**: durable verification (no Lean
built — Docker daemon down, Aristotle `Resource not found`) · **Phase**: ORIENT

### Context

The lower bound `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2` is now fully covered:
parametrically by open PR **#24228** (`…OQ01General.lean`, build-pending) and
per-`k` (k=3..7) by the merged Counting files. Every committed artifact
(`verify_witnesses.py`, `verify_general_lower.py`) certifies only the **lower**
half. Nothing checked the matching **upper** half. This session fills that gap
on the verification side and independently reviews the in-flight #24228 proof.

### Independent math review of #24228 (Step 6 `nlinarith`, the only new logic)

Confirmed the parametric proof's final discharge is **mathematically sound**.
Over `ℤ` with `M=2^k`, `Q=⌊(3/2)^k⌋`, fiber counts `c₀,c₁,c₂≥0`:
`hZeqn: c₁ + M·c₂ + 1 = Q·M` ⟹ `c₁ = M(Q−c₂) − 1`. The product hint
`(M−1)(Q−1−c₂) ≥ 0` expands to `M(Q−c₂) + c₂ ≥ M + Q − 1`, while
`hZpart` + `c₀≥0` gives `c₁ + c₂ = M(Q−c₂) − 1 + c₂ ≤ M + Q − 3`, i.e.
`M(Q−c₂) + c₂ ≤ M + Q − 2`. The two bounds (`≥ M+Q−1` vs `≤ M+Q−2`) are
contradictory — exactly what `nlinarith` needs. Residual build risk is only
v4.26.0 lemma-name drift, not the logic. (Posted as a confirming comment on
the PR.)

### New durable artifact — `verify_ideal_condition.py` (the UPPER-bound side)

Exact big-integer certificate for the **ideal-Waring** value
`g(k) = 2^k + ⌊(3/2)^k⌋ − 2`. With `q = ⌊(3/2)^k⌋`, `r = 3^k mod 2^k`:

- **Dickson–Pillai condition (*)** `r + q ≤ 2^k` — *necessary and sufficient*
  for the ideal value. Checked to hold for **all k = 1..200**.
- **Mahler condition (M)** `{(3/2)^k} ≤ 1 − (3/4)^k` ⟺ exact-integer
  `r·2^k ≤ 4^k − 3^k`; strictly stronger sufficient condition (M ⟹ *). Fails
  only at the trivial edge `k=1` in range; holds for every `k ≥ 2..200`.
- Formula `2^k + q − 2` cross-checked against **OEIS A002804** for k=1..12.

### Honesty boundary (which step is which)

| Step | Status |
|---|---|
| Lower bound `g(k) ≥ 2^k+q−2` | ELEMENTARY — formalised (#24228, build-pending) |
| Checking (*)/(M) for given k | ELEMENTARY — this script, exact arithmetic |
| Implication `(*) ⟹ upper bound` | **DEEP THEOREM** (Dickson–Pillai–Niven 1936–44), NOT formalised, Mathlib gap |

So the certificate establishes: for every checked `k`, the *hypothesis* of the
ideal-Waring theorem holds, hence `g(k)` equals the formula **modulo the
unformalised Dickson–Pillai–Niven implication**. It does NOT prove that
implication. The upper bound remains the deep open half of the slug.

### Files

- `research/problems/.../verify_ideal_condition.py` (new — upper-bound condition)

---

## S1 (researcher-3, 2026-05-12) — OBSERVE survey

### Historical values of $g(k)$

| $k$ | $g(k)$ | Year | Contributor | Reference |
|---:|------:|---|---|---|
| 1 | 1 | — | trivial | $\forall n, n = n$ |
| 2 | 4 | 1770 | Lagrange | *Additions au mémoire sur la résolution des équations numériques* |
| 3 | 9 | 1909 / 1912 | Wieferich / Kempner | Wieferich, *Math. Ann.* 66 (1909); Kempner correction *Math. Ann.* 72 (1912) |
| 4 | 19 | 1986 | Balasubramanian, Deshouillers, Dress | *C. R. Acad. Sci. Paris* 303 (1986) |
| 5 | 37 | 1964 | Chen Jingrun | *Sci. Sinica* 13 (1964) |
| 6 | 73 | 1940 | Pillai | *Bull. Calcutta Math. Soc.* 32 (1940) |
| 7 | 143 | 1936 | Niven (almost all); Kubina–Wunderlich (1990, verification) | $g(7) = 2^7 + 17 - 2 = 143$ ($\lfloor (3/2)^7 \rfloor = 17$) |
| 8 | 279 | conjectural per formula | $2^8 + 25 - 2 = 279$ ($\lfloor (3/2)^8 \rfloor = 25$) | Mahler 1957 |
| $k \ge 7$ | $2^k + \lfloor (3/2)^k \rfloor - 2$ | Mahler 1957 (all but finitely many); Kubina–Wunderlich 1990 (verified up to $\sim 4.7 \times 10^8$) | conjecturally all $k$ |

The general formula $g(k) = 2^k + \lfloor (3/2)^k \rfloor - 2$ holds for all $k$ such that
$$ \{(3/2)^k\} \le 1 - (3/4)^k, \tag{*} $$
where $\{x\}$ denotes the fractional part. Mahler proved (*) holds for all but finitely many $k$; numerical verification (Kubina–Wunderlich 1990) confirms (*) for $k \le 471,600,000$. The unconditional formula for all $k$ remains a conjecture, but it is widely believed (and would follow from any plausible irrationality-measure improvement on $(3/2)$).

### Hilbert–Waring (1909)

**Theorem (Hilbert)**: For every $k \ge 1$, there exists a finite $g(k)$ such that every $n \in \mathbb{N}$ is a sum of $\le g(k)$ perfect $k$-th powers.

**Original proof technique**: Hilbert's 1909 proof uses an integral representation
$$ I_s(n; \alpha) = \int_0^1 \left( \sum_{a=0}^{\lfloor n^{1/k} \rfloor} e^{2\pi i \alpha a^k} \right)^s e^{-2\pi i \alpha n} \, d\alpha, $$
which counts representations of $n$ as a sum of $s$ $k$-th powers. Showing $I_s(n) > 0$ for $s$ large enough establishes the existence of representations.

**Modern proof technique (Hardy–Littlewood 1922)**: Circle method. Decompose $[0, 1]$ into "major arcs" (rationals with small denominator) and "minor arcs" (everything else). The major-arc contribution gives the main term; the minor-arc contribution is bounded by Weyl's inequality and similar estimates.

**Mathlib status**: zero infrastructure for the circle method exists. Hardy–Littlewood is itself a major target (significantly beyond Waring); even basic exponential-sum estimates are absent.

### Reference for the $g(3) = 9$ proof

**Wieferich (1909)**: published the original argument with a gap; **Kempner (1912)** patched the gap. The combined Wieferich–Kempner proof case-splits on $n \pmod{6}$ for one half and uses a polynomial identity
$$ 6 \cdot (a^2 + b^2 + c^2)^2 = \text{(sum of cubes expression)} $$
for the other half. The classical reference is Hardy & Wright, *An Introduction to the Theory of Numbers*, §21.2 (5th edn 1979).

**Computational verification of "exactly 9 needed"**: The numbers $23$ and $239$ are the only two known to require exactly $9$ cubes. All other $n$ need $\le 8$ cubes. **Numerical conjecture**: $G(3) \le 7$ (every sufficiently large $n$ needs $\le 7$ cubes); conjecturally $G(3) = 4$ (the *cubical-fourths* conjecture), still open.

### Mod-arithmetic lower-bound recipe

The lower-bound proofs for $g(k)$ generalize the parent's mod-8 argument for $g(2)$:

**$k = 2$ (parent)**: every $a^2 \in \{0, 1, 4\} \pmod{8}$, so sums of $3$ squares are in $\{0, \ldots, 6\} \pmod{8}$, missing $7$.

**$k = 3$**: every $a^3 \pmod{9}$ — direct computation:
- $0^3 = 0, 1^3 = 1, 2^3 = 8, 3^3 = 27 = 0, 4^3 = 64 = 1, 5^3 = 125 = 8, 6^3 = 0, 7^3 = 1, 8^3 = 8 \pmod 9$
- So $a^3 \in \{0, 1, 8\} \pmod{9}$. Sums of $\le 4$ cubes cover at most $\{0, \ldots, 4 \cdot 8\} \pmod{9}$ but the constraint to $\{0, 1, 8\}$ means values like $4 \pmod 9, 5 \pmod 9$ may need more than 4 cubes — but this is NOT enough to push to $9$. Need a tighter argument for $23$.
- **Better approach for $23$ in particular**: direct computation. Since $a^3 \le 23 \Rightarrow a \le 2$, only $a_i \in \{0, 1, 2\}$. Then sum of 8 cubes is $\le 8 \cdot 8 = 64$, so the representation exists; need to enumerate to show none equals 23 with exactly 8 summands.
- Enumeration: $23 = 8 \cdot c_2 + c_1 \cdot 1 + (\text{zeros})$ where $c_2 + c_1 + (\text{zeros}) = 8$. So $8c_2 + c_1 = 23$, $c_2 \in \{0,1,2\}, c_1 \in \{0,\ldots,8\}$. Cases: $c_2 = 0 \Rightarrow c_1 = 23 > 8$ ✗; $c_2 = 1 \Rightarrow c_1 = 15 > 8$ ✗; $c_2 = 2 \Rightarrow c_1 = 7$, gives $c_0 = 8 - 2 - 7 = -1 < 0$ ✗. Hence no representation as sum of 8 cubes; $23$ requires $\ge 9$. ✓

**$k = 4$**: every $a^4 \pmod{16}$ — direct:
- $0^4 = 0, 1^4 = 1, 2^4 = 16 = 0, 3^4 = 81 = 1, 4^4 = 0, \ldots \pmod {16}$. So $a^4 \in \{0, 1\} \pmod{16}$.
- Sums of $\le 18$ fourth-powers are $\le 18 \pmod{16}$, i.e. in $\{0, 1, \ldots, 18\} \pmod{16} = \{0, 1, 2\} \pmod{16}$.
- $79 \equiv 15 \pmod{16}$. Since $15 \notin \{0, 1, \ldots, 18 \pmod{16}\}$, we'd need $\ge 19$ fourth-powers. ✓
- **Formal**: sums of $\le s$ fourth-powers have residue $\le s \pmod{16}$ (since each is $0$ or $1 \pmod{16}$). For $s = 18$: $\le 18 \pmod{16}$ doesn't include $15$ (since $18 - 16 = 2$). So $79 \equiv 15 \pmod{16}$ is unreachable with $18$ fourth-powers — needs $\ge 19$.

**$k = 5$**: every $a^5 \pmod{32}$: $0, 1, 32, 243, \ldots$ — actually $a^5 \pmod{32}$ takes values in $\{0, 1, 7, 17, 24, 25, 31\}$ (computed by enumerating $a = 0..31$). Not as clean; $g(5) = 37$ needs $223$ as a witness, and the lower bound for $223$ may need a more careful residue argument.

### Bibliographic references

1. **Hardy & Wright**, *An Introduction to the Theory of Numbers* (5th ed., Oxford 1979), §21 ("Sums of $k$-th Powers"), pp. 297–339.
2. **Vaughan**, *The Hardy–Littlewood Method* (Cambridge 1981, 2nd ed. 1997). The modern reference for the circle method as applied to Waring.
3. **Wieferich**, "Über das Waringsche Problem," *Math. Ann.* 66 (1909): 95–101.
4. **Kempner**, "Bemerkungen zum Waringschen Problem," *Math. Ann.* 72 (1912): 387–399.
5. **Balasubramanian, Deshouillers, Dress**, "Problème de Waring pour les bicarrés. I, II," *C. R. Acad. Sci. Paris Sér. I Math.* 303 (1986): 85–88, 161–163.
6. **Chen Jingrun**, "Waring's problem for g(5) = 37," *Sci. Sinica* 13 (1964): 1547–1568.
7. **Pillai**, "On Waring's problem g(6) = 73," *Bull. Calcutta Math. Soc.* 32 (1940): 30.
8. **Mahler**, "On the fractional parts of the powers of a rational number, II," *Mathematika* 4 (1957): 122–124.
9. **Kubina & Wunderlich**, "Extending Waring's conjecture to $471{,}600{,}000$," *Math. Comp.* 55 (1990): 815–820.
10. **OEIS A002804**: Waring's problem $g(k)$ — $1, 4, 9, 19, 37, 73, 143, 279, 548, 1079, 2132, 4223, \ldots$

### Mathlib API names (Lean 4, pinned revision 4.26.0)

- `Nat.sum_four_squares` — Lagrange's theorem; the only Waring-related Mathlib lemma.
- `Mathlib.NumberTheory.SumFourSquares` — Lagrange's theorem and Euler's identity.
- `Mathlib.NumberTheory.SumTwoSquares` — Fermat's two-square theorem.
- No `Mathlib.NumberTheory.Waring`, no `Mathlib.NumberTheory.SumCubes`, no `g(k)` definition.

### Insights (rough draft for S1 deliverable)

1. **Pattern: lower bounds are mod arguments, upper bounds are research**. The parent demonstrated this for $g(2)$; the extension to $g(3), g(4), \ldots$ makes it a meta-pattern of the family.

2. **Tractability gradient**: $k = 3, 4, 5, 6$ have known explicit $g(k)$ values, but the upper-bound proofs are at the "axiomatize-only" tier for Lean. Only the lower bounds are realistic single-session targets.

3. **$g(k)$ existence vs. value**: Hilbert (1909) shows $g(k) < \infty$; the explicit value requires separate work for each $k$. Defining $g(k)$ in Lean has two options:
   - **Definitional**: explicit case-split on $k$ giving the known values. Doesn't depend on Hilbert.
   - **Spec-based**: `noncomputable def g (k : ℕ) : ℕ := Nat.find (hilbert_waring k)`. Depends on Hilbert's theorem (which Mathlib lacks).

4. **mod-16 for $k = 4$**: the clean lower bound for $g(4) \ge 19$ uses the fact that fourth-powers are $0$ or $1$ mod $16$. A direct decide-based enumeration of $3^{18} \approx 4 \times 10^8$ tuples is **infeasible**; the mod argument is essential.

5. **OEIS A079611**: numbers requiring exactly $g(3) = 9$ cubes are precisely $\{23, 239\}$. This is a finite list — once Lean can verify both via the bounded-search lower bound, Wieferich–Kempner's upper bound completes the picture (modulo axiomatization).

6. **No infrastructure for the circle method**: Hardy–Littlewood circle method is a Mathlib gap larger than Waring itself. Any proof of Hilbert–Waring in Lean must either (a) use the circle method and require multi-year Mathlib work, or (b) use Linnik's elementary 1943 proof which is shorter but still substantial. Both are far beyond a single research iteration.

7. **Family planning**: the slug graph is

   ```
   lagrange-four-squares (Lagrange's theorem) — verified
   ├── lagrange-four-squares-waring-g2 (g(2) = 4) — verified
   │   └── lagrange-four-squares-waring-g2-oq-01 (g(k) for k ≥ 3) — this OQ, OBSERVE phase
   │       ├── -oq-01-oq-01 (potential: g(3) = 9 specifically)
   │       ├── -oq-01-oq-02 (potential: g(4) = 19 specifically)
   │       └── -oq-01-oq-03 (potential: Hilbert–Waring existence axiom)
   └── (siblings: lagrange-four-squares-oq-01, -oq-02, -oq-04 — different angle)
   ```

   The current OQ-01 is the umbrella; each $k$ may eventually spawn its own descendant slug.

8. **Honesty boundary**: any claim "we've formalized $g(3) = 9$ in Lean" must clearly distinguish the lower bound (which can be `verified`) from the upper bound (which is `axiomatized` via the Wieferich–Kempner axiom). The gallery `badge` and `status` fields must reflect this — likely `status = axiomatized, badge = axiom` once the upper-bound axiom is introduced.

## S2 (researcher-3, 2026-05-12) — ACT: $g(3) \ge 9$ lower bound

### Theorem proved (0 sorries, 0 axioms)

`WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23`

where

```lean
def IsSumOfCubes (s n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n
```

### Proof technique: bound + lift + decide

The proof has three steps:

**1. Bound (omega + Nat.pow_le_pow_left):** if $\sum_{i=0}^{7} (f_i)^3 = 23$ then for each $i$, $(f_i)^3 \le \sum_j (f_j)^3 = 23 < 27 = 3^3$, hence $f_i \le 2$ by monotonicity of $x \mapsto x^3$.

Lean tactic: `Finset.single_le_sum` to extract the inequality, then `Nat.pow_le_pow_left h 3` and `omega`.

**2. Lift (definitional Fin.val):** the map $f : \text{Fin } 8 \to \mathbb{N}$ with each $f_i < 3$ lifts to $g : \text{Fin } 8 \to \text{Fin } 3$ via $g i := \langle f i, h_i \rangle$. The coercion $(g i : \mathbb{N})$ equals $f i$ *definitionally* (`Fin.val ⟨f i, _⟩ = f i` by projection), so the lifted sum equals the original sum without rewriting — the `change` tactic suffices.

**3. Decide ($3^8 = 6561$ tuples):**

```lean
lemma representations23_empty :
    (Finset.univ.filter (fun f : Fin 8 → Fin 3 => ∑ i, ((f i : ℕ)) ^ 3 = 23)) = ∅ := by
  decide
```

Kernel `decide` enumerates the 6561 elements of `Fin 8 → Fin 3` (via the `Fintype` instance on dependent functions over finite types) and checks the predicate on each. The whole computation fits well within Lean's default tactic budget. (Sub-second on local laptop; ~2-3 seconds in Docker build.)

### Witness verification

The matching upper-bound witness `IsSumOfCubes 9 23 = ⟨![2,2,1,1,1,1,1,1,1], by decide⟩` is included as an `example`, verifying that nine cubes *do* suffice ($2 \cdot 8 + 7 \cdot 1 = 23$).

### Why not `interval_cases` on each Fin?

The original S1 sketch suggested `interval_cases` on each of 8 indices ($3^8$ cases unrolled). This works but is slower (rough Lean compilation budget ~10x larger for explicit case splits). The `decide`-via-filter route is cleaner: a single `Finset.univ.filter` reduces to a single kernel reduction, with no tactic-state branching.

### What `decide` actually verifies

The `decide` lemma `representations23_empty` is reduced to the proposition

> for all $f \in \text{Fin } 8 \to \text{Fin } 3$, $\sum_{i} (f i)^3 \neq 23$

which is a decidable closed proposition. Lean's kernel computes the truth value by exhaustive enumeration. Since `decide` (not `native_decide`) is used, the computation is performed by the *kernel* (not native code), giving the strongest soundness guarantee.

### Generalisation outlook

The proof pattern (bound → lift → decide) generalises:

| $k$ | $n$ | $s$ (target) | Bound | Lift target | Search size | Tractable by `decide`? |
|---:|---:|---:|---:|---|---:|---|
| 3 | 23 | 8 | $f_i \le 2$ | `Fin 8 → Fin 3` | $3^8 = 6561$ | **YES** (S2) |
| 3 | 239 | 8 | $f_i \le 6$ | `Fin 8 → Fin 7` | $7^8 \approx 5.8 \times 10^6$ | borderline (likely `native_decide`) |
| 4 | 79 | 18 | $f_i \le 2$ | `Fin 18 → Fin 3` | $3^{18} \approx 4 \times 10^8$ | **NO** — mod-16 required |
| 5 | 223 | 36 | $f_i \le 2$ | `Fin 36 → Fin 3` | $3^{36} \approx 1.5 \times 10^{17}$ | **NO** — mod-32 required |

This frames the next iterations: S3 *must* introduce the mod-16 lemma (analogous to `sq_mod_eight` in the parent file).

### New insight: `Fin.val` definitional equality enables `change`

A pitfall: many lift-and-rewrite proofs use `simp only [Fin.val_mk]` or coercion rewrites to align the lifted sum with the original. *Not needed here*: `Fin.val ⟨n, h⟩ = n` holds *definitionally* (by structure projection), so `change ∑ i, (f i)^3 = 23` after the lift, where the goal mentions `(g i : ℕ)`, succeeds via defeq.

This is a small but reusable Lean idiom for bounded-search proofs.

### S2 build status

Docker build of `Proofs.LagrangeFourSquaresWaringG2OQ01` succeeded end-to-end against Mathlib v4.26.0 (~45 minutes including a fresh `lake update` due to the worktree's `Proofs/.lake` symlink loop).

### Outlook for S3 (mod-16 fourth-powers)

Plan:

1. **Mod-16 fourth-power lemma**:
   ```lean
   lemma fourth_pow_mod_sixteen (x : ℕ) : x ^ 4 % 16 = 0 ∨ x ^ 4 % 16 = 1
   ```
   Proof: `interval_cases (x % 16)` plus `decide` on each of the 16 residues.

2. **Sum-of-18 residue lemma**:
   ```lean
   lemma sum_eighteen_fourth_pows_mod_sixteen (f : Fin 18 → ℕ) :
       (∑ i, (f i) ^ 4) % 16 ≤ 18
   ```
   Each summand is $\le 1 \pmod{16}$, so the sum is $\le 18 \pmod{16}$.

3. **Witness mod-16**:
   ```lean
   theorem g4_lower : ¬ IsSumOfFourthPowers 18 79 := by
     rintro ⟨f, hsum⟩
     have hmod : (∑ i, (f i) ^ 4) % 16 ≤ 18 := sum_eighteen_fourth_pows_mod_sixteen f
     rw [hsum] at hmod
     -- 79 % 16 = 15, but mod-sum is in {0, 1, ..., 18} ∩ {0, ..., 15} = {0, ..., 15}
     -- Need to argue: 18 % 16 = 2, so possible residues for sum-of-18 are {0, 1, 2}
     ...
   ```

The argument is *not* just $\sum \le 18 \pmod{16}$ — it's $\sum \pmod{16} \in \{r : 0 \le r \le 18, r \le 18\}$, but the residues themselves of $\sum_i a_i$ where $a_i \in \{0, 1\}$ are integers $\sum a_i \in \{0, 1, \ldots, 18\}$. After reducing mod 16, these become $\{0, 1, \ldots, 15, 0, 1, 2\}$. We need $79 \pmod{16} = 15$ to be in this set: actually 15 *is* in $\{0, \ldots, 15\}$ since $\sum a_i = 15$ is allowed.

Wait — this exposes a subtlety. The mod-16 argument doesn't work as stated! Let me re-examine.

**Correction**: each $a_i \in \{0, 1\} \pmod{16}$, so $\sum_{i=0}^{17} a_i \in \{0, 1, \ldots, 18\}$ as integers. Reducing mod 16: $\{0, 1, \ldots, 18\} \pmod{16} = \{0, 1, \ldots, 15, 0, 1, 2\} = \{0, 1, \ldots, 15\}$ — *every* residue is achievable!

So the simple mod-16 argument is **insufficient** for $g(4) \ge 19$. The actual Wieferich–Kempner-style argument for $g(4) \ge 19$ requires a refined analysis: it's the *integer* sum that's bounded by 18, and *separately* needs the integer value to equal 79 with each summand $\le 79^{1/4} \approx 3$. This gives a finite search of size $4^{18} \approx 7 \times 10^{10}$, which is still infeasible.

**Standard proof of $g(4) \ge 19$**: each $a_i^4 \in \{0, 1, 16, 81, 256, \ldots\}$, restricted to $a_i^4 \le 79$, so $a_i \le 2$ (since $3^4 = 81 > 79$). Then $a_i^4 \in \{0, 1, 16\}$. Sum of 18 such = $79$ requires $c_2 \cdot 16 + c_1 \cdot 1 = 79$, $c_2 + c_1 + c_0 = 18$, $c_0, c_1, c_2 \ge 0$. Cases:
- $c_2 = 0$: $c_1 = 79$, but $c_1 \le 18$. ✗
- $c_2 = 1$: $c_1 = 63$. ✗
- $c_2 = 2$: $c_1 = 47$. ✗
- $c_2 = 3$: $c_1 = 31$. ✗
- $c_2 = 4$: $c_1 = 15$, $c_0 = -1$. ✗

So $g(4) \ge 19$ holds via **enumeration of $(c_2, c_1)$ pairs**, not mod-16. This is the same pattern as $g(3) \ge 9$, just with a different power. The search space is $3^{18}$ tuples in the naive lift, but the *constrained* enumeration $(c_2, c_1, c_0)$ with $c_2 \cdot 16 + c_1 = 79, c_2 + c_1 + c_0 = 18$ has only $\sim 5$ cases.

**Better S3 approach**: replicate the S2 pattern with `Fin 18 → Fin 3` (bound: $a^4 \le 79 \Rightarrow a \le 2$), then `decide` on $3^{18}$ tuples — but this is infeasible. Use `native_decide` on a *compressed* representation: count multiplicities of each value (a `Fin 19 × Fin 19` for $(c_2, c_1)$) and `decide` on that small space.

Even better: prove via `omega` directly on the integer equation $16 c_2 + c_1 = 79 \land c_2 + c_1 + c_0 = 18 \land c_0, c_1, c_2 \ge 0$. This is a linear arithmetic problem; `omega` handles it.

**Revised S3 plan**:

```lean
theorem g4_lower : ¬ IsSumOfFourthPowers 18 79 := by
  rintro ⟨f, hsum⟩
  -- Each f i ≤ 2 (since 3^4 = 81 > 79)
  have hbound : ∀ i, f i ≤ 2 := ...  -- analogous to S2
  -- Count multiplicities of 0, 1, 2 among the f i
  let c0 := (Finset.univ.filter (fun i => f i = 0)).card
  let c1 := (Finset.univ.filter (fun i => f i = 1)).card
  let c2 := (Finset.univ.filter (fun i => f i = 2)).card
  -- Then c0 + c1 + c2 = 18 and c1 + 16 * c2 = 79
  -- Apply omega
  sorry
```

This avoids the $3^{18}$ blowup entirely. ~80 Lean lines, single-session.

(Insight: linear arithmetic — `omega` — discharges most "exhaustive enumeration" problems if framed correctly. The naive `decide` on `Fin 18 → Fin 3` is what makes the proof appear infeasible; reframing as multiplicities makes it trivial.)

### Updated session-tier progression

| Iter | Predicate | Bound | Technique | Status |
|---:|---|---|---|---|
| S2 | $\neg \text{IsSumOfCubes } 8\ 23$ | $f_i \le 2$ | lift + `decide` $3^8$ | **DONE** |
| S3 | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | $f_i \le 2$ | multiplicity + `omega` | TODO |
| S4 | $\neg \text{IsSumOfCubes } 8\ 239$ | $f_i \le 6$ | lift + `native_decide` $7^8$ | TODO (optional) |
| S5+ | upper bounds | — | axiomatise | TODO |

## S24 (researcher-1, 2026-06-14) — S8 ACT-readiness (Python-verified, build-free)

**Goal**: discharge the S8 picker caveat ("g(8) ≥ 279 … case-load grows, confirm
tractability before paste-porting") so that the next ACT session can paste-port
without re-deriving. All numbers below are computed and cross-checked against the
five shipped siblings (k = 3..7) with `python3` — see the verification block at
the end. **No Lean was built (Docker outage continues); this is ORIENT-depth, not ACT.**

### The lower-bound recipe (parametric, already shipped for k = 3..7)

For the witness $N_k = 2^k\lfloor (3/2)^k\rfloor - 1$, the statement is
$\neg\,\mathrm{IsSumOf}k\mathrm{thPowers}\;(g(k)-1)\;N_k$ where
$g(k)-1 = 2^k + \lfloor (3/2)^k\rfloor - 3$. The proof is the 6-step
counting+omega template: (1) bound each base $f_i \le 2$ because $3^k > N_k$ so no
$k$-th power $\ge 3^k$ fits; (2) lift to multiplicity counts $(c_0,c_1,c_2)$ of the
values $\{0,1,2\}$; (3) fiber/partition `Finset.univ`; (4) expand the sum to
$c_1\cdot 1 + c_2\cdot 2^k$; (5) the integer system
$c_2\,2^k + c_1 = N_k,\; c_0+c_1+c_2 = g(k)-1,\; c_i\ge 0$; (6) `omega` closes it
(linear, no `decide`/`native_decide` blowup).

### Exact S8 parameters (k = 8) — paste-ready

| Quantity | Value | Note |
|---|---:|---|
| $2^8$ | 256 | base power |
| $\lfloor (3/2)^8\rfloor$ | 25 | $(3/2)^8 = 6561/256 = 25.62\ldots$ |
| $g(8)$ lower bound | **279** | $256 + 25 - 2$ |
| witness $N_8$ | **6399** | $256\cdot 25 - 1$ |
| statement bound $s = g(8)-1$ | **278** | `¬ IsSumOfEighthPowers 278 6399` |
| $3^8$ | 6561 | $> 6399$ ⟹ each $f_i \le 2$ (only $1^8,2^8$ usable) |
| $n_2^{\max} = \lfloor N_8/2^8\rfloor$ | 24 | max copies of $2^8$ |
| remainder $r = N_8 - 24\cdot 2^8$ | 255 | copies of $1^8$ |
| terms needed | **279** | $24 + 255 = g(8)$ ✓ |
| max sum reachable with 278 terms | 6398 | $24\cdot 256 + (278-24)\cdot 1$ |
| **miss-by** | **1** | $6399 - 6398$ — identical calibration to k = 7 |

So the formal target is
```lean
theorem g8_lower_counting : ¬ WaringG2OQ01.CountingG8.IsSumOfEighthPowers 278 6399
```
with `IsSumOfEighthPowers (s n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 8) = n`,
a **byte-mirror of `…CountingG7.lean` at $k=8$** (witness `6399 = 24·256 + 255`,
`Fin 278`, `n_2^{max} = 24`, `n_0 = 278 − 255 − 24 = −1` ⟹ "miss by 1").

### Tractability verdict: **READY** (was "lower readiness")

The "case-load grows" worry is bounded and harmless: the only growth from k = 7 to
k = 8 is $n_2^{\max}$ 16 → 24 and the term count 142 → 278, both of which enter
`omega` as plain linear bounds — no exponential `decide` space is ever
materialised (the $f_i \le 2$ reduction kills it, exactly as in g3..g7). The
$f_i \le 2$ bound itself is sound because $3^8 = 6561 > 6399$ — the same
strict inequality that licenses k = 3..7. Conclusion: S8 is paste-port-ready;
no new proof bearers, no new tactic risk. Estimated ~140 LOC, single session,
0 sorries / 0 axioms (mirroring `…CountingG7.lean`'s 139 LOC).

### Look-ahead: k = 9 sanity (not yet targeted)

For completeness the same script confirms k = 9 keeps the structure: $N_9 = 2^9\cdot 38 - 1 = 19455$,
$3^9 = 19683 > 19455$, $g(9)$ lb $= 512 + 38 - 2 = 548$, miss-by-1. So the template
does not break at k = 9 either; only the omega bounds keep growing linearly.

### Python verification (reproducible)

```python
from math import floor
def waring_lower(k):
    twok, f = 2**k, floor((3/2)**k)
    N, s = twok*f - 1, (twok + f - 2) - 1
    n2 = N // twok; r = N - n2*twok
    return dict(g_lb=twok+f-2, N=N, s=s, only12=3**k>N,
                n2=n2, r=r, terms=n2+r, maxsum=n2*twok+(s-n2), miss=N-(n2*twok+(s-n2)))
# k=8 → g_lb=279, N=6399, s=278, only12=True, n2=24, r=255, terms=279, maxsum=6398, miss=1
```
Cross-checked for k = 3..8: every row has `terms == g_lb` and `miss == 1`,
matching the shipped witnesses (g3:23/8, g4:79/18, g5:223/36, g6:703/72, g7:2175/142).

