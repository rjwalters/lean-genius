# Problem: Transfer Chebyshev bounds from psi(n) to theta(n) = Theta(n)

## Statement

### Plain Language
The parent entry proves the **second** Chebyshev function satisfies `ψ(x) = Θ(x)` (explicit
two-sided linear bounds `(log 2/3)·m ≤ ψ(m) ≤ (log 4 + 4)·m`).  Transfer this growth rate to the
**first** Chebyshev function `θ(x) = ∑_{p ≤ x} log p`, obtaining `θ(x) = Θ(x)`.

### Formal Statement
$$
\theta(x) = \Theta(x) \quad\text{as } x \to \infty,
$$
formalized as `Asymptotics.IsTheta atTop θ (fun x => x)`, i.e. `θ =Θ[atTop] id`.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - analytic-number-theory
  - chebyshev
  - prime-counting
  - theta-function
  - asymptotics
  - seeker-selected
```

**Significance**: 6/10
**Tractability**: 6/10

## Why This Matters

`θ(x) = Θ(x)` is the Chebyshev estimate underlying the prime number theorem's order of magnitude:
it is equivalent (by partial summation) to `π(x) = Θ(x/log x)`.  The parent formalized the analogous
statement for `ψ`; here we complete the elementary picture by transferring it to `θ`, the more
directly prime-counting function.

## Approach

The transfer is short given two Mathlib facts:

* `Chebyshev.theta_le_psi : θ x ≤ ψ x`, and
* `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log : |ψ x − θ x| ≤ 2√x·log x` (the prime-power
  correction).

**Upper bound.** `θ(x) ≤ ψ(x) ≤ (log 4 + 4)·x` (`Chebyshev.psi_le_const_mul_self`).

**Lower bound.** `θ(x) = ψ(x) − (ψ(x) − θ(x)) ≥ ψ(x) − 2√x·log x`.  The parent gives
`ψ(x) ≥ (log 2 / 6)·x` for real `x ≥ 2` (via the floor bridge `ψ(x) = chebyshevPsi ⌊x⌋₊` and
`⌊x⌋₊ ≥ x − 1 ≥ x/2`), and `2√x·log x = o(x)` (from `log x/√x → 0`), so eventually
`θ(x) ≥ (log 2 / 12)·x`.  Package both as `IsTheta`.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `chebyshev-bounds-oq-02-oq-01` (parent) | Explicit `ψ(m) = Θ(m)` bounds; supplies `chebyshevPsi_lower_linear`, `chebyshevPsi_eq_psi`. |
| `chebyshev-bounds-oq-03` | `ψ ∼ θ`; supplies the `log x/√x → 0` fact (inlined here). |
| `chebyshev-bounds-oq-02-oq-01-oq-01` | States explicit two-sided `θ` bounds (not yet formalized). |
