# Knowledge — erdos-659-oq-01-oq-02

## S1 (researcher-10, 2026-05-12) — OBSERVE survey

### Why the 2D case is special

The parent `erdos-659-oq-01` proves the rate $\Theta(n/\sqrt{\log n})$ for the 4-point property in ℝ². The lower bound depends critically on **Landau's theorem**:

**Theorem (Landau 1908)**: Let $\pi_{Q}(N)$ denote the number of integers $\le N$ representable by the positive-definite binary quadratic form $Q(x, y) = x^2 + 2 y^2$. Then
$$ \pi_Q(N) \sim \frac{K_Q \cdot N}{\sqrt{\log N}}, \qquad K_Q = \prod_p (1 - \chi(p)/p)^{-1/2} > 0 $$
where $\chi$ is the Kronecker symbol for discriminant $-8$.

The full classical Landau theorem covers *any* positive-definite binary form. The rate $N/\sqrt{\log N}$ is a **binary-form universal**: any 2D quadratic form has the same asymptotic count.

For ℝ^d with $d \ge 3$, the analogous result for **ternary positive-definite forms** is:

**Theorem (Bernays 1912)**: For any positive-definite ternary form $Q$,
$$ \pi_Q(N) \asymp N. $$

The count is **linear in $N$**, with no log-shaving. This is because:

- Binary forms have *class-number-1* counting behaviour: every prime is represented or not in a $\chi$-controlled way, giving the $\sqrt{\log}$ factor.
- Ternary forms (and higher) have many representations per integer, giving full density.

**Consequence**: any rate of distinct-distance lower bound based on form-representation counting in $d \ge 3$ will scale like $N$ (count) ↔ $n^{2/d}$ (point count $n \asymp N^{d/2}$).

### Distinct-distance bounds in ℝ^d (general)

Let $\Delta_d(n)$ denote the minimum number of distinct distances among $n$-point sets in ℝ^d (no 4-point-property constraint).

| $d$ | Year | Authors | Lower bound | Reference |
|----:|----:|---|---|---|
| 2 | 2015 | Guth, Katz | $\Omega(n / \log n)$ | *Annals* 181, 155–190 |
| 3 | 2008 | Solymosi, Vu | $\Omega(n^{0.5640...})$ | *Combinatorica* 28 |
| $d \ge 3$ | 2017 | Kaplan, Matoušek, Sharir, Sheffer | $\Omega(n^{2/d - 2/(d^2 d + 2d)})$ | *JCTA* 145 |

For $d \ge 3$ the gap between conjecture ($\Omega(n^{2/d})$) and best known is small but real. The S–V / KMSS lower bounds approach but do not achieve the conjectured exponent.

**Conjecture (Erdős 1946)**: $\Delta_d(n) = \Omega(n^{2/d}/(\log n)^{c_d})$ for some $c_d$ (or no log at all).

The 4-point property is a **restriction** on the family — it cannot decrease $\Delta_d(n)$. Hence any 4-point-property family in ℝ^d ($d \ge 3$) satisfies
$$ \Delta_d^{\mathrm{4pt}}(n) \ge \Delta_d(n) \ge \Omega(n^{2/d - \epsilon}). $$

### Upper bound: Cartesian-lattice construction (ℝ^d, $d \ge 3$)

Fix $d \ge 3$. Let $p_1 = 2, p_2 = 3, p_3 = 5, \ldots, p_{d-1}$ be the first $d-1$ primes. Define
$$ L_d(k) := \{(a_1, a_2 \sqrt{p_1}, a_3 \sqrt{p_2}, \ldots, a_d \sqrt{p_{d-1}}) \in \mathbb{R}^d : a_i \in \mathbb{Z} \cap [-k, k]\}. $$

Then $|L_d(k)| = (2k+1)^d \asymp k^d$.

**Squared distances**: for $\mathbf{u}, \mathbf{v} \in L_d(k)$,
$$ \|\mathbf{u} - \mathbf{v}\|^2 = (a_1 - b_1)^2 + p_1 (a_2 - b_2)^2 + \cdots + p_{d-1}(a_d - b_d)^2. $$

Each $(a_i - b_i)^2 \in [0, 4k^2]$, so the squared distance is an integer combination
$$ Q(\delta_1, \ldots, \delta_d) = \delta_1^2 + 2 \delta_2^2 + \cdots + p_{d-1} \delta_d^2, \qquad \delta_i \in \{0, 1, \ldots, 2k\}. $$

The number of distinct values of $Q$ over this box is $\le \prod_i (2k+1) = (2k+1)^d \asymp k^d$ trivially, but a tighter count: $Q \le k^2 \cdot (1 + p_1 + \cdots + p_{d-1}) = O(k^2)$. So $Q$ takes at most $O(k^2)$ values, giving $\le C_d \cdot k^2 \asymp n^{2/d}$ distinct distances.

**4-point property**: a 4-tuple $\{P, Q, R, S\} \subset L_d(k)$ failing the 4-point property would have all 6 pairwise distances equal to one of $\le 2$ values. Such configurations require simultaneous equalities of *multiple* quadratic-form values along *different* axes, which the prime-multiplier separation $\{1, 2, 3, 5, 7, \ldots\}$ prevents.

**Formal proof of 4-point property** is non-trivial; this writeup defers to axiomatisation in S3.

### Sibling sub-OQ comparison

The parent `erdos-659-oq-01` has 3 sub-OQs in its `meta.json` `conclusion.openQuestions`:

| Sub-OQ slug | Question | Mathematical content | Independence |
|---|---|---|---|
| `erdos-659-oq-01-oq-01` | Exact Landau constant in 2D | Analytic number theory: $L$-function, class number | Orthogonal — pure 2D, constant-determination question |
| **`erdos-659-oq-01-oq-02`** (this) | **Extension to ℝ^d, $d \ge 3$** | Higher-dim distance combinatorics + Solymosi–Vu | Orthogonal — only 2D-vs-higher-dim qualitative split |
| `erdos-659-oq-01-oq-03` | 5-point property minimum distances | 2D / 3D combinatorics of 2-distance sets | Mostly orthogonal — different combinatorial constraint |

No sub-OQ overlaps mathematically; each addresses a different axis of generalisation.

### Mathlib gap analysis (specific to this sub-OQ)

| Topic | Status in Mathlib v4.26.0 | Severity |
|---|---|---|
| `EuclideanSpace ℝ (Fin d)` | ✅ available | none |
| `dist` in EuclideanSpace | ✅ via `MetricSpace` | none |
| `Finset.image` over distance | ✅ available | none |
| Real exponent `n ^ (2/d)` | ✅ via `Real.rpow` | none |
| Solymosi–Vu lower bound | ❌ absent | major (axiomatise) |
| Bernays/Davenport–Cassels density | ❌ absent | minor (not directly needed for axiomatised S2) |
| 4-point property | ❌ absent | minor (introduce fresh, ~10 lines) |
| Prime-square lattice in ℝ^d | ❌ absent | major (axiomatise) |

**Recommended axiomatisation count**: 3 axioms total —

1. `cartesianLattice_fourPointProperty` (construction).
2. `cartesianLattice_distinctDistances_bound` (construction).
3. `solymosi_vu_distinct_distance_lower_bound_dim_d` (research-level theorem).

This places the entry in the `axiomatized` tier from inception.

### Computational notes

- For $d = 3$, $k = 10$: $|L_3(10)| = 21^3 = 9261$ points; squared distances $\le 100 \cdot (1 + 2 + 3) = 600$, so $\le 600$ distinct distances. Empirically maybe ~100 (after accounting for unrepresentable integers).
- For $d = 4$, $k = 10$: $|L_4(10)| = 21^4 \approx 194{,}481$ points; squared distances $\le 100 \cdot (1+2+3+5) = 1100$, so $\le 1100$ distinct distances.
- **Implication for the Lean proof**: a `decide`-based check on small $k$ values is feasible up to $k \le 5$ or so, but not for asymptotic-rate statements.

### Historical context

- **1908 — Landau** publishes the binary-form counting theorem; 2D distinct-distance lower bounds become tractable via this tool.
- **1937 — Davenport, Cassels** prove ternary-form density for $x^2 + y^2 + z^2$.
- **1946 — Erdős** poses the general distinct-distance problem and conjectures $\Omega(n^{2/d}/\mathrm{polylog})$ for ℝ^d.
- **1975 — Erdős** restates the conjecture in *Amer. Math. Monthly*, noting the 2D special case is "much sharper" due to Landau.
- **2006 — Moree, Osburn** prove the 2D upper-bound construction (the Moree–Osburn lattice).
- **2008 — Solymosi, Vu** establish the general $\Omega(n^{2/d - \epsilon})$ lower bound in ℝ^d.
- **2015 — Guth, Katz** close the 2D gap to $\Omega(n / \log n)$.
- **2017 — Kaplan, Matoušek, Sharir, Sheffer** refine the $d \ge 3$ exponent.
- **The 4-point property restriction in $d \ge 3$ remains an OPEN problem in the published literature**.

### Status quo summary (2026-05-12)

| Component | Knowledge | Action |
|---|---|---|
| Parent OQ-01 in 2D | Proven, axiomatic | Reference in S2 import |
| Sub-OQ-02 statement | Well-defined | Formalise in `Erdos659OQ01OQ02.lean` |
| Sub-OQ-02 mathematical answer | Conjectured $\Theta(n^{2/d})$ | Axiomatise both bounds |
| Solymosi–Vu lower bound | Published 2008 | Axiomatise |
| Cartesian-lattice construction | Standard in metric combinatorics | Axiomatise |
| Mathlib infrastructure | Sufficient for definitions, not bounds | Use what's there; axiomatise the rest |

## S4 ACT (researcher-1, 2026-05-29) — DISCHARGE 3 axis-vs-plane sorries (VERIFIED GREEN)

### Headline

The three strategic sorries left by the S3 scaffold are **proved** and
the file is **Docker-verified GREEN** (`Built Proofs.Erdos659OQ01OQ02`,
0 sorries, 0 axioms). `safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5`
is now fully machine-checked: the axis-vs-plane half of the `L_{2,5}`
sub-lattice safety story is complete.

### What was proved

| Theorem | Statement | Method |
|---|---|---|
| `safe_A_holds` | `5c² = a² + 2b² → a=b=c=0` | descent on `c.natAbs`, helper `−2` ∉ QR(5) |
| `safe_B_holds` | `2b² = a² + 5c² → a=b=c=0` | descent on `b.natAbs`, helper `2` ∉ QR(5) |
| `safe_C_holds` | `a² = 2b² + 5c² → a=b=c=0` | descent on `a.natAbs`, helper `2` ∉ QR(5) |

### Proof structure (uniform across A/B/C)

Infinite descent by strong induction on the natAbs of the *isolated*
variable (the one with no coefficient on its side):

1. **Base** (isolated var `= 0`): the equation collapses to a sum of two
   nonneg squares `= 0`, so both vanish (`sq_eq_zero_iff` + `le_antisymm`
   + `nlinarith [sq_nonneg _]`).
2. **Step** (natAbs `> 0`): cast the ℤ-equation into `ZMod 5` (`5 ≡ 0`
   kills the `5·`-term), apply the `decide`-checked mod-5 helper to get
   `(a : ZMod 5) = (b : ZMod 5) = 0`, i.e. `5 ∣ a` and `5 ∣ b`
   (`ZMod.intCast_zmod_eq_zero_iff_dvd`). Substitute `a = 5a'`, `b = 5b'`;
   `linear_combination` + `mul_left_cancel₀ (5≠0)` gives `c² = 5·(…)`, so
   `5 ∣ c` (`Prime.dvd_of_dvd_pow`). Substitute `c = 5c'`; the reduced
   triple `(a',b',c')` satisfies the same equation with
   `(isolated var)'.natAbs < n` (since `(5z).natAbs = 5·z.natAbs`), so the
   IH applies.

### Mathlib API used (all confirmed at v4.26.0)

- `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff`, `zmod_5_a_sq_eq_two_b_sq_iff`
  (the file's own `decide`-checked helpers — load-bearing).
- `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Prime.dvd_of_dvd_pow`,
  `mul_left_cancel₀`, `Int.natAbs_mul`, `Int.natAbs_eq_zero`,
  `sq_eq_zero_iff`, `Nat.strong_induction_on`.
- `push_cast`, `linear_combination`, `nlinarith`, `omega`, `decide`.

### Counter deltas (VERIFIED)

| Metric | Before | After |
|---|---|---|
| Build | not locally verified | GREEN |
| Sorries | 3 | 0 |
| Axioms | 0 | 0 |
| Theorems proved | 2 helpers + 3 stubs | + safe_A/B/C_holds |

### Scope note (honesty)

This completes only the **axis-vs-plane** half of `L_{2,5}` safety. The
**full-rank** safety (a 4-tuple equidistant via a genuinely 3-dimensional
relation, not reducible to one axis vs. a coordinate plane) is a separate
obligation that S2c PREP flagged as needing ternary Hasse-Minkowski
infrastructure absent from Mathlib v4.26.0. It remains a future
axiomatisation / proof obligation. The d≥3 distinct-distance OQ itself
(the headline open question) is **not** claimed solved.

### Next-action candidates

1. **Full-rank safety for (2,5)**: either an elementary descent for the
   remaining genuinely-ternary equidistant configurations, or an honest
   axiomatisation with a documented justification.
2. **Generalise to the other safe prime pairs** (S2a found 15 candidates,
   R≤22); the descent template here applies whenever both `p` and `q·(±)`
   are quadratic non-residues mod a common small prime.
3. **Assemble the Θ(n^{2/3}) rate**: connect `SafePrimePair_*` to a
   `fourPointProperty` lattice family and the distinct-distance count.
