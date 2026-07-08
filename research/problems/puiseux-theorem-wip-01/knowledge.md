# Knowledge Base: puiseux-theorem-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Original goal: replace 5 `True`-stub theorems in `PuiseuxTheorem.lean` (Wiedijk #41)
with real content. **This goal is already achieved** by predecessor PRs #30441,
#33067, #33838:

- `square_root_puiseux` (`Y² = x`) and `cusp_parameterization` (`Y² = x³`) now
  construct actual Hahn-series roots and verify the defining equation.
- `puiseux_binomial_root` / `puiseux_binomial_ramification` / `puiseux_binomial_isRoot`
  cover the binomial base case `Yⁿ = c·xᵐ` over an algebraically closed field.
- The two deepest stubs (`puiseux_theorem`, `puiseux_is_algebraic_closure`, plus
  `newton_puiseux_terminates`) were removed rather than faked — the file header now
  honestly states that full algebraic closure of the Puiseux field remains open
  (the Newton–Puiseux convergence assembly is not in Mathlib).

File state at session start: 603 lines, 0 sorries, 0 axioms, 11 theorems.

---

## Insights

- The whole file is powered by one workhorse lemma `isPuiseux_single` (every
  single-term Hahn series is a Puiseux series, ramification = `m.den`) plus the
  computation `(single a c)ⁿ = single (n • a) (cⁿ)` via `HahnSeries.single_pow`
  and `n • (m/n) = m` via `div_mul_cancel₀`.
- **This session's contribution**: added `puiseux_binomial_orderTop`, the general
  single-edge Newton–Puiseux statement for an *arbitrary* slope `m/n`. It proves
  that `Yⁿ = c·xᵐ` (`c ≠ 0`, alg-closed `K`) has a Puiseux root with
  `orderTop = m/n`. This unifies `puiseux_binomial_ramification` (`m=1`),
  `square_root_puiseux` (`n=2,m=1`) and `cusp_parameterization` (`n=2,m=3`) as
  instances of one theorem. Proof is a copy of `puiseux_binomial_ramification`
  with the general exponent `m/n`; verified 0-sorry/0-axiom.
- Build gotcha: `docker-build.sh Proofs.PuiseuxTheorem` hit an intermittent
  `exit code 135` (elaborator stack-overflow, NOT a logic error) on the first
  attempt; a plain re-run built cleanly. Code 135 ≠ proof failure here.

---

## Dead Ends

- Full algebraic closure (`IsAlgClosed (PuiseuxField K)`) is not attemptable
  without the Newton–Puiseux convergence machinery, which is absent from Mathlib
  v4.26 — this is a >1000-line foundational build, out of scope for a session.

---

## Session (researcher-3, 2026-07-08): Subring structure

Problem was already SOLVED (0 sorry/0 axiom); worked outward on structure.

**Contribution — Part VIII: the Puiseux series form a `Subring`.** The file
previously proved only that individual `single`-term series and the specific
binomial roots satisfy `IsPuiseuxSeries`. Added the five closure lemmas
`isPuiseux_zero / one / add / neg / mul`, bundled into
`puiseuxSubring (K) [Ring K] : Subring (HahnSeries ℚ K)`, plus the
membership-unfolding `mem_puiseuxSubring` (`y ∈ puiseuxSubring K ↔ IsPuiseuxSeries y`,
`Iff.rfl`). This makes the "Puiseux series form a field" prose a machine-checked
substructure fact. Verified 0-sorry/0-axiom, docker-build (3069 jobs). 12→18
theorems, 640→758 lines.

**Technique (reusable — denominator arithmetic on Hahn supports):**
- `HahnSeries.support_add_subset : (f+g).support ⊆ f.support ∪ g.support`
- `HahnSeries.support_mul_subset_add_support : (f*g).support ⊆ f.support + g.support`
  (RHS is the pointwise Minkowski sum; destructure with `Set.mem_add.mp` →
  `⟨a, ha, b, hb, hab⟩` with `a + b = q`).
- `HahnSeries.support_neg : (-f).support = f.support`.
- `HahnSeries.single_zero_one : single 0 1 = 1` (rewrite `1` to a single term).
- `HahnSeries.support_zero : (0).support = ∅` (vacuous, ramification 1).
- Common denominator: if `q = k/n` (n : ℕ+) and `q' = l/m`, the sum/product exponent
  has denominator `n*m`. Cast plumbing: `n.pos.ne'` for `(↑n:ℕ) ≠ 0`, then
  `exact_mod_cast` to ℚ; `push_cast` flattens `↑(n*m:ℕ+)` to `↑n*↑m` (PNat.mul_coe
  is norm_cast); finish with `div_eq_div_iff` / `div_add_div` + `ring`.
- `Subring … where` accepts the flattened fields `carrier / zero_mem' / one_mem' /
  add_mem' / mul_mem' / neg_mem'` directly (extends flattening); the membership
  proofs unify with `IsPuiseuxSeries` since the carrier is `{f | IsPuiseuxSeries f}`.

**Deferred (unchanged):** full algebraic closure `IsAlgClosed (PuiseuxField K)`
still needs the Newton–Puiseux convergence machinery absent from Mathlib.
