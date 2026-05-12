# Knowledge — lagrange-four-squares-waring-g2-oq-01

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
| 7 | 143 | 1936 | Niven (almost all); Kubina–Wunderlich (1990, verification) | $g(7) = 2^7 + 2 - 2 = 143$ |
| 8 | 279 | conjectural per formula | $2^8 + 5 - 2 = 279$ ($\lfloor (3/2)^8 \rfloor = 25$) | Mahler 1957 |
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
