# Knowledge Base: geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Two claims about the alternating Eulerian sum
`A(n,k) = ∑_{i=0}^{k} (−1)ⁱ·C(n+1,i)·(k+1−i)ⁿ`:
1. **Non-negativity** `A(n,k) ≥ 0`.
2. **Descent count** `A(n,k) = |{σ ∈ Sₙ : des σ = k}|`.

The parent `...oq-02` already proved `A(n,k) = ⟨n,k⟩` (`eulerian_eq_explicit`), `⟨n,k⟩ : ℕ`.

---

## Insights / Dedup map (CRITICAL — cluster is saturated)

- **Claim (1) is ALREADY DONE** by sibling `...oq-02-oq-02` (`eulerianExplicit_nonneg`, identical
  name/statement) and the palindromy `⟨n,k⟩=⟨n,n−1−k⟩` is ALSO there + in `...oq-05`.
- The **descent MEAN (n−1)/2** and higher moments are ALREADY DONE in `...oq-03` (via the
  Eulerian polynomial derivatives). Row sum `∑⟨n,k⟩=n!` in `...oq-01`.
- ⇒ A non-negativity/symmetry entry would be a PURE DUPLICATE. First draft (recurrence-induction
  proof of palindromy + nonneg) was DISCARDED for this reason.

## What was SHIPPED (genuinely new)

Pivoted to the only genuinely-open, distinct part = **claim (2), the literal descent bijection on
`Equiv.Perm`**. The whole cluster treats descents only ANALYTICALLY (polynomial coefficients);
NONE defines an actual `des : Perm → ℕ`. Mathlib has none either (only Coxeter descents).
- `descentCount σ = |{i:Fin n | σ i.succ < σ i.castSucc}|` on `σ : Perm (Fin (n+1))`.
- `descentCount_eq_zero_iff : descentCount σ = 0 ↔ σ = 1` (descent-free ⟺ increasing identity).
- `card_descentFree : |{σ : descentCount σ = 0}| = ⟨n+1,0⟩ = 1` — FIRST gallery bridge from an
  abstract Eulerian number to a real descent-class cardinality (k=0 rung of the bijection).
- Reusable helper `perm_eq_one_of_strictMono`: strict-mono `σ : Perm (Fin n)` = 1, via
  `Equiv.toOrderIso` + `Subsingleton (Fin n ≃o Fin n)` (NO induction).
- 127 lines, 3 thm + 1 def, 0-axiom, sorry-free. Built host `lake env lean` (docker down).

## Gotchas

- `Fin.castSucc_lt_succ` takes its index IMPLICITLY → `(Fin.castSucc_lt_succ (i := i))`.
- Empty descent set gives only `≤`; injectivity (`i.castSucc ≠ i.succ`) upgrades to `<` for
  `Fin.strictMono_iff_lt_succ`.
- `σ.symm` monotone from `σ` strict-mono: `by_contra; push_neg; hσ h; simp apply_symm_apply`.

## Still open (left as follow-up questions)

- k=n dual rung `descentCount σ = n ↔ σ = Fin.revPerm` (strict-antitone analogue).
- Full bijection k≥1 via the descent insertion recurrence matched to the Eulerian triangle —
  substantial, Mathlib-unsupported.
