# Knowledge Base: dirichlets-theorem-oq-03-oq-01

Derived open question of the Linnik-constant problem (parent: dirichlets-theorem-oq-03).

---

## Problem Understanding

The parent entry formalizes the **Linnik constant**
`L* = inf { L > 0 : ∃ c > 0, ∀ coprime (a,q), p(a,q) ≤ c·q^L }`
but carries 2 axioms (Linnik's theorem, Xylouris's bound) and 3 sorries (existence of
primes in AP, lower bound L* ≥ 1).

This derived question asks: **which properties of L* are structural** (true of the
infimum of *any* admissible-exponent set) **versus genuinely analytic** (needing the
deep number theory)?

---

## Result (2026-06-27, VERIFIED)

New file `proofs/Proofs/DirichletsTheoremOQ03OQ01.lean`, namespace `LinnikAdmissible`,
**0 axioms, 0 sorries**, machine-checked offline against Mathlib v4.26.0
(`#print axioms` ⇒ only `propext, Classical.choice, Quot.sound`).

Abstract setup: growth function `f : I → ℝ` over base `b : I → ℝ` with `b ≥ 1`,
`admissible f b = { L > 0 : ∃ c > 0, ∀ i, f i ≤ c · b i ^ L }`.

Proved (11 theorems, 3 defs):
- `admissible_bddBelow` — bounded below by 0.
- `admissible_upward_closed` — upward-closed ray (via `Real.rpow_le_rpow_of_exponent_le`).
- `criticalExponent := sInf (admissible f b)`; `criticalExponent_le`, `criticalExponent_nonneg`.
- `mem_admissible_of_gt` — **ray property**: every exponent above the critical one is admissible
  (`exists_lt_of_csInf_lt` + upward closure).
- `admissible_sandwich` — **Ioi(c) ⊆ admissible ⊆ Ici(c)**; the critical exponent pins the
  admissible set to a ray up to its single boundary point.
- `admissible_mono` / `criticalExponent_mono` — pointwise domination shrinks the admissible
  set and lowers the critical exponent (`csInf_le_csInf`).
- Linnik specialization `linnikConstantOf`, `linnik_threshold`.

**Key separation achieved**: well-definedness of the Linnik constant (ray, bound, sandwich,
monotonicity) is *elementary* — needs only rpow-monotonicity and the conditional-infimum
API. The number theory enters **only** through nonemptiness of the admissible set (Linnik's
theorem), supplied here as an explicit hypothesis, which is why the file is axiom-free.

---

## Insights

- The parent's `linnik_theorem` axiom and `leastPrimeInAP` sorries are unnecessary for the
  *structural* facts: abstracting the growth function removes all of them.
- The sandwich theorem is the precise sense in which "the Linnik constant is the answer":
  c determines the whole admissible set except possibly whether c itself is admissible
  (open/closed endpoint) — which for Linnik is the genuinely open sub-question.
- Monotonicity formalizes why sharper bounds on p(a,q) can only *lower* L*, never raise it —
  implicit in the parent's chain of historical bounds.

---

## Dead Ends / Open

- Whether the critical exponent is *attained* (admissible = Ici c vs Ioi c) is left open —
  for Linnik this is the question of whether L* is itself admissible.
- Did not redefine `leastPrimeInAP` concretely (would reintroduce sorries/axioms); kept the
  growth function abstract to preserve the axiom-free status.
