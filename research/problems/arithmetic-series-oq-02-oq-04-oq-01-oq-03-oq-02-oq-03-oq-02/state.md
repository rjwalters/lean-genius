# Current State

**Phase**: PREP (S6 latest, post-S1 OBSERVE; S2 ACT pending — no Lean file yet)
**Since**: 2026-05-12 (S1 OBSERVE) → 2026-05-13 (5 doc-only PREPs through S6)
**Iteration**: 6 (S1 OBSERVE + S2/S3/S4/S5/S6 PREP)

`proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` **does not yet exist**. After 5 doc-only PREP iterations the recommended S2-ACT skeleton has pivoted: from Pascal-style recurrence (S2 PREP Option α — falsified at 4 data points by S6) to **k-direction telescoping** (S6 Option γ-refined), plus the **Path A vs Path C** split that S4 PREP (`Field R` 0/0 trap) and S5 PREP (`RatFunc.eval` rescue) crystallized.

## Session Log (S1 → S6)

Doc-only PREP chain after the S1 OBSERVE merge. All memos in `sessions/`; no Lean changes.

| Iter | Phase    | PR     | Author        | Merge time (UTC)     | Memo                                                              | Outcome |
|------|----------|--------|---------------|----------------------|-------------------------------------------------------------------|---------|
| 1    | OBSERVE  | #18327 | researcher-10 | 2026-05-12T23:18:50Z | (this `state.md` + `problem.md` + `knowledge.md` + gallery JSON)  | Macdonald-type candidate `qtBinom`/`qtMultichoose`; two Pascal conjectures (A) and (B) recorded; the `a(n,k)` exponent for (A) flagged as open S4. |
| 2    | PREP     | #18382 | researcher-6  | 2026-05-13T02:10:55Z | `2026-05-12-s02-prep-pascal-falsification.md`                     | Small-case falsification of (A) and (B) at `(1,1)` and `(1,0)`. §6.4 enumerates Options α / β / γ with `???` for α. |
| 3    | PREP     | #18558 | researcher-12 | 2026-05-13T05:07:19Z | `2026-05-13-s03-prep-qtmc-rationality-and-iterated-limit.md`      | `qtMC` is genuinely rational over $\mathbb{Q}(q,t)$, not polynomial; polynomial sub-lattice characterized; S5 joint $(1,1)$ limit retired in favour of iterated limits. |
| 4    | PREP     | #18616 | researcher-5  | 2026-05-13T07:02:30Z | `2026-05-13-s04-prep-field-trap-and-polynomial-sublattice.md`     | **F1**: Lean `Field R` 0/0 = 0 convention falsifies S3 PREP's planned `qtMC q 1 n k = qMC q n k` at $q = 1$. Three rescues: (Path A) add `hq : ∀ i, q^{i+1} ≠ 1`; (Path B) piecewise re-define `qtBinom`; (Path C) switch to `RatFunc ℚ(q,t)`. **Recommends Path A** for S2 ACT. Rigorous polynomial sub-lattice = {k ≤ 1} ∪ {(2,2)}. |
| 5    | PREP     | #18639 | researcher-9  | 2026-05-13T08:10:04Z | `2026-05-13-s05-prep-ratfunc-eval-rescues-path-c-no-q-ne-one-hypothesis.md` | **Flips S4's Path C dismissal**: Mathlib's `RatFunc.eval` makes Path C viable, and uniquely **eliminates the `q ≠ 1` hypothesis** for the `t = 1` substitution under iterated `RatFunc (RatFunc ℚ)`. Path C deferred to S6/S7. |
| 6    | PREP     | #18734 | researcher-6  | 2026-05-13T10:16:47Z | `2026-05-13-s06-prep-option-alpha-falsification-and-k-direction-recurrence-pivot.md` | Closes S2 PREP §6.4's `???`: Option α conjectural form is **falsified** at 4 data points. Denominator shape varies with $(n,k)$; no uniform $(1-qt)$-denominator works. **Pivot recommendation**: replace Pascal-style recurrence with **k-direction telescoping ratio** (Option γ-refined). The product formula factorizes most naturally along $k$, not Pascal's two-direction. |

## Current Focus

S1 (researcher-10): OBSERVE survey for `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02` — the seeker-extracted child of the verified gallery entry `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03` ("q-Multichoose: The Gaussian Binomial as q-Analog of Multiset Coefficients"). The sub-OQ asks:

> Can `qMultichoose` be generalized to a $(q,t)$-deformation (Macdonald-type) where `qMultichoose(q,t,n,k)` recovers `qMultichoose` at $t = 1$ and classical `multichoose` at $q = t = 1$? This would connect to the theory of Macdonald polynomials and Hall–Littlewood functions.

This iteration produces:

- `problem.md` — formal problem statement with full Lean target signatures (`qtBinom`, `qtMultichoose`, the three specialization theorems, and the conjectural $(q,t)$-Pascal); S2–S7 decomposition; Mathlib gap analysis.
- `knowledge.md` — historical timeline (Macdonald 1973 → 1988 → 1995, Haiman 2001); detailed specialization analysis showing $\mathrm{qtMultichoose}(q, t, 2, 2)$ is independent of $t$; risk-and-uncertainty table for S2–S6.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json` — gallery JSON.

No Lean changes in S1.

## Active Approach

**Candidate $(q,t)$-deformation** (from Macdonald 1995, §VI.6):
$$ \mathrm{qtBinom}(q, t, n, k) := \prod_{i=1}^{k} \frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}, \qquad \mathrm{qtMultichoose}(q, t, n, k) := \mathrm{qtBinom}(q, t, n + k - 1, k). $$

**Key technical observation (from S1 small-case calculation)**: For $(n, k) = (2, 2)$:
$$ \mathrm{qtMultichoose}(q, t, 2, 2) = \frac{1 - q^3}{1 - q} \cdot \frac{1 - q^2 t}{1 - q^2 t} = \frac{1 - q^3}{1 - q} = 1 + q + q^2, $$
**independent of $t$**. This suggests the $(q,t)$-multichoose has more cancellation than a generic $(q,t)$-binomial; the full $t$-dependence emerges only at larger $(n, k)$.

**Pascal-recurrence direction (S2 PREP Option α) — FALSIFIED by S6**:

The S2 PREP §6.4 conjectured "Option α" Pascal coefficient
$$ \frac{P(q, t, n, k)}{Q(q, t, n, k)} \stackrel{?}{=} \frac{q^{k+1} \, (1 - q^{n+k+1} t)}{(1+q)(1-qt)} $$
was tested by S6 PREP (#18734) against exact data at $(n,k) \in \{(1,0), (0,1), (1,1), (2,1)\}$ and **disagrees at every test point**. The actual `C(q,t,n,k)` has a denominator shape that varies with $(n,k)$ (the factor $(1 - q^? t)$ shifts from $(1-qt)$ at $n=1$ to $(1-q^2 t)$ at $n=2$); no uniform $(1-qt)$-denominator works. Boundary slices $C(n, 0) = q$ and $C(0, 1) = q$ are $t$-independent, making any uniform rational ansatz incompatible with the $t$-dependence "kicking in" only when **both** $n, k \geq 1$.

**Pivot to k-direction telescoping (S6 PREP, Option γ-refined)**:

The product formula factorizes most naturally along $k$, not Pascal's two-direction $(n+1, k+1) \to (n+1, k) + ?\cdot(n, k+1)$. The S6 PREP recommends exposing the **k-direction ratio**
$$ \frac{\mathrm{qtBinom}(q, t, n, k+1)}{\mathrm{qtBinom}(q, t, n, k)} = \frac{1 - q^{n-k} t^k}{1 - q^{k+1} t^k}, $$
giving a one-step telescope that the product formula natively provides. This **strengthens S2 PREP §6.4's "Option β — bypass Pascal entirely"** recommendation: not just bypass, but replace.

**Path A vs Path C (`Field R` 0/0 trap and `RatFunc.eval` rescue)**:

S4 PREP (#18616) surfaced the Lean `Field R` 0/0 = 0 convention trap: under the naïve `[Field R]` ambient, `qtMC 1 1 n k = 0` for all $k \geq 1$, falsifying any "$\mathrm{qtMC}(q, 1, n, k) = \mathrm{qMC}(q, n, k)$" statement at $q = 1$. Three rescues:

| Path | Mechanism | S4 → S5 status |
|---|---|---|
| **A** | Add hypothesis `hq : ∀ i, q^{i+1} ≠ 1` | S4 recommended for S2 ACT. Cheapest in Lean but restricts $q$ domain. |
| **B** | Piecewise re-define `qtBinom` to handle zero-denominator factors explicitly | S4 noted; lossy for downstream identities. |
| **C** | Switch ambient from `Field R` to `RatFunc ℚ(q,t)` (formal-rational-function ring) | S4 dismissed as "substantially higher complexity"; **S5 PREP (#18639) flipped this**: Mathlib's `RatFunc.eval` makes Path C viable, and uniquely **eliminates the `q ≠ 1` hypothesis** for the $t = 1$ substitution theorem under iterated `RatFunc (RatFunc ℚ)`. |

**S5 specialisation at $q = t = 1$ (post-S3 retirement)**: S3 PREP (#18558) **retired** the joint $(1,1)$ limit in favour of iterated limits $q \to 1$ then $t \to 1$ (or vice versa), since `qtMC(q,t,n,k)` is rational, not polynomial, over $\mathbb{Q}(q,t)$ outside the polynomial sub-lattice $\{k \leq 1\} \cup \{(2,2)\}$. The Pascal-induction route to $\mathrm{qtMultichoose}(1,1,n,k) = \binom{n+k-1}{k}$ is **superseded** by the k-direction telescope (S6) plus the `RatFunc.eval` route (S5).

## Blockers

(Updated to reflect S2 → S6 PREP findings.)

- **`Field R` 0/0 trap (resolved with caveats)**: S4 PREP recommends Path A (`hq` hypothesis); S5 PREP makes Path C viable. Path B abandoned. The S2 ACT must pick A or C before writing the Lean file.
- **Pascal-style recurrences are structurally awkward**: S6 PREP falsifies S2 PREP Option α and recommends pivoting to the k-direction telescoping ratio. The original "interpolating Pascal" plan (S1 line 36-39, S4 conjecture) is **abandoned**.
- **Joint $(q,t) \to (1,1)$ limit retired** (S3 PREP): use iterated limits or sub-lattice-restricted statements; do not write `qtMultichoose_at_one_one` as a literal joint-substitution theorem.
- **Macdonald polynomial infrastructure absent from Mathlib**: any S6+ connection to $P_\lambda(x; q, t)$ must be axiomatised. (Unchanged from S1.)
- **S2 ACT skeleton still unwritten**: 5 PREPs into the chain, no `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` file exists. Risk of indefinite PREP-cascade saturation; see "Next Action" below.

## Next Action

**S2 ACT (any researcher) — first Lean skeleton, post-PREP-cascade**: define `qtBinom` and `qtMultichoose` and prove four boundary cases, **picking Path A or Path C explicitly** based on the S4/S5 PREP guidance. Critically, the recurrence target has **pivoted** from Pascal to k-direction telescope (per S6 PREP).

**Recommended Path A skeleton** (cheaper, builds first):

```lean
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03  -- qMultichoose

namespace QtMultichooseCoefficients

variable {R : Type*} [Field R]

noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

@[simp] theorem qtMultichoose_zero_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = 1 := by simp [qtMultichoose, qtBinom]

@[simp] theorem qtMultichoose_one_left (q t : R) (k : ℕ) :
    qtMultichoose q t 1 k = 1 := by sorry  -- product telescopes
-- additional boundary cases (S2 ACT) — protect each with `hq : ∀ i, q^{i+1} ≠ 1`
-- per S4 PREP Path A, or move to `RatFunc ℚ` per S5 PREP Path C.
end QtMultichooseCoefficients
```

Expected ~40 Lean lines, ~3-5 sorries on boundary cases. **Add `hq` hypothesis to every theorem that substitutes a specific $q$ value** (Path A); or switch the ambient ring to `RatFunc (RatFunc ℚ)` and use `RatFunc.eval` for substitutions (Path C, per S5 PREP). Picking is a S2-ACT design decision — both have been pre-flighted.

**S3 ACT (after S2)**: `qtMultichoose_at_t_eq_one : qtMultichoose q 1 n k = qMultichoose q n k`. Under Path A this needs `hq : ∀ i, q^{i+1} ≠ 1`; under Path C (per S5 PREP) **no** hypothesis is needed. Expected ~25 lines, 0 sorries.

**S4 ACT (after S3) — pivoted from Pascal to k-direction telescope**: prove the k-direction recurrence
$$ \mathrm{qtBinom}(q, t, n, k+1) \cdot (1 - q^{k+1} t^k) = \mathrm{qtBinom}(q, t, n, k) \cdot (1 - q^{n-k} t^k) $$
(the natural product-of-ratios identity). Expected ~30 lines, 0 sorries; **single-direction induction on $k$ replaces the failed Option α Pascal**.

**S5 ACT (after S4)**: $\mathrm{qtMultichoose}(q, 1, n, k) = \mathrm{qMultichoose}(q, n, k)$ via the k-direction telescope, the polynomial sub-lattice characterization (S3 PREP), and the `RatFunc.eval` substitution (S5 PREP) — **NOT** via a joint $(q,t) \to (1,1)$ limit (S3 retired). Expected ~30-50 lines, possibly 1-2 axioms for the iterated-limit step if `RatFunc` instances are missing.

**S6 ACT (optional)**: axiomatise Macdonald polynomial principal-specialization identity (unchanged from S1).

**S7**: gallery JSON `meta.json` integration with `status: "verified"` if S5 ships clean, else `"axiomatized"`.

**Anti-pattern note (for the next researcher)**: per researcher memory, this slug has been in PREP-cascade for 5 iterations without writing the Lean skeleton. The S2 ACT is now well-scoped (Path A or C, k-direction not Pascal); ship the Lean skeleton **before** opening a 7th PREP. The remaining open questions can be answered from the running Lean code instead of by another small-case calculator.

## Honesty

The cumulative S1 OBSERVE → S6 PREP chain is **pure documentation**. Across six iterations:

- 0 new Lean theorems
- 0 sorry deltas (file doesn't exist yet)
- 0 axiom deltas
- 9 markdown files (`problem.md`, `knowledge.md`, `state.md`, 5 PREP session memos under `sessions/`, this STATE-SYNC)
- 1 gallery JSON entry (updated by this STATE-SYNC)

The candidate $(q,t)$-deformation is from Macdonald's textbook (well-established mathematics). The Lean formalisation is genuinely new — this would be the **first Lean entry to mention Macdonald theory at any depth**. The deepest technical step has *shifted*: originally S4 was an "interpolating $(q,t)$-Pascal" derivation, but S6 PREP falsified that approach (Option α at 4 data points). The new deepest step is **S5 ACT** (`qtMultichoose_at_t_eq_one` over `RatFunc` or with `hq` hypothesis) since it touches both the `Field R` 0/0 trap (S4 PREP) and the iterated-limit retirement (S3 PREP).

The future Lean entry will be `status: "verified"` if S5 ACT ships without axioms; `"axiomatized"` if a `RatFunc.eval` iterated-substitution axiom or a Macdonald-polynomial axiom is required.
