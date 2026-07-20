# Knowledge: Erdős 818 — Product Set Lower Bound for Small Sumsets (completion)

## Session 2026-07-20 (researcher-1)

Target file: `proofs/Proofs/Erdos818Problem.lean` (gallery entry `erdos-818`).
Started at 1 axiom (`solymosi_theorem`) + 1 sorry (`proof_outline`).

### What was added (axiom-free, host-verified under Mathlib v4.31)

- **`sumset_eq_add`** — `sumset A = A + A` (pointwise), the additive analogue of
  the file's `productSet_eq_mul`.
- **`sumset_lower_bound`** — `2|A| - 1 ≤ |A + A|` for nonempty `A ⊆ ℤ`, via
  Mathlib's `cauchy_davenport_add_of_linearOrder_isCancelAdd`. Fills the
  previously comment-only Part II.
- **`product_lower_of_mult_energy`** — the faithful Solymosi reduction. From
  `cauchy_schwarz_energy` (already proved) plus the multiplicative-energy upper
  bound `E×(A) ≤ C·|A+A|²·log|A|` supplied as an **explicit hypothesis**, it
  proves `|A·A| ≥ |A|² / (C·K²·log|A|)` when `|A+A| ≤ K·|A|`. This machine-checks
  the whole reduction and isolates the single genuine external input WITHOUT
  adding a new axiom.

Required adding `import Mathlib.Combinatorics.Additive.CauchyDavenport` (the
Cauchy–Davenport lemma is not transitively imported by `...Additive.Energy`).

### The remaining open sorry (`proof_outline`)

`proof_outline` claims the sharper `|A·A| ≥ |A|² / (K·log|A|)` (denominator
`K`, not `K²`). Two honest facts:

1. It is **not** derivable from the `solymosi_theorem` axiom (absolute constant
   `c·|A|²/log|A|`): that would require `c·K ≥ 1`, which the existential `c` does
   not provide.
2. It is **stronger** than the standard energy argument yields. Substituting
   `|A+A| ≤ K·|A|` into `E×(A) ≤ C·|A+A|²·log|A|` costs a square, giving only
   `1/(C·K²·log|A|)` (exactly `product_lower_of_mult_energy`). The `K`-linear
   form needs a materially different argument, or Solymosi's energy inequality
   formalized in Mathlib.

### Blocker (structured, in tracker `currentState.blockers`)

- route: proof_outline sharp `1/(K·log|A|)` product-set bound via multiplicative
  energy — reopen only with a materially new mechanism.

### Next external input to formalize

Solymosi's multiplicative-energy inequality `E×(A) ≤ C·|A+A|²·log|A|` (dyadic
pigeonhole on the multiplicative fibers `{(a,b) : ab = m}`) — not currently in
Mathlib. Formalizing it would discharge `product_lower_of_mult_energy`'s
hypothesis and give the `K²` product-set bound unconditionally.
