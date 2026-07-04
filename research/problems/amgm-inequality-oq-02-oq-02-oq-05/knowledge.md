# Knowledge Base: amgm-inequality-oq-02-oq-02-oq-05

Insights accumulated during research on this problem.

---

## PART I — the real-rooted/discriminant route + the n=2 base case (researcher-8, 2026-07-04)

**Mode**: FRESH (EMPTY, score 0). **Outcome**: progress (+8 theorems in a new
file `Proofs/AmgmInequalityOQ02OQ02OQ05.lean`; 0 sorries / 0 axioms).
**Machine-verified**: docker-build clean (7743 jobs, exit 0);
`#print axioms` = `propext / Classical.choice / Quot.sound` only for
`newton_two_vars`, `discrim_nonneg_of_root`, `discrim_nonneg_of_roots_nonempty`,
`realRooted_quadratic_coeff_ineq` (Tier-A axiom-free — no `sorryAx`, no
`Lean.ofReduceBool`).

### What this establishes
The entry asks for the classical **calculus** proof of Newton's inequalities:
`∏(X - xᵢ)` is real-rooted ⇒ (Rolle) each derivative is real-rooted ⇒
differentiating down to a degree-2 polynomial in three consecutive coefficients
leaves a real-rooted quadratic whose **discriminant ≥ 0 is Newton's inequality**.
This route was **not present** anywhere in the ~50-file amgm family:
- parent `amgm-inequality-oq-02-oq-02` proves Newton by induction, assuming
  `0 ≤ xᵢ`;
- sibling `amgm-inequality-oq-02-oq-03-oq-03-oq-01` proves the `k=1` case via a
  Cauchy–Schwarz / sum-of-squares "discriminant" *metaphor* — a different
  mechanism, not the discriminant of a real-rooted polynomial.

### Shipped (`Proofs/AmgmInequalityOQ02OQ02OQ05.lean`, namespace `NewtonRealRooted`)
- **`discrim_nonneg_of_root (a b c x : ℝ) (h : a*(x*x)+b*x+c = 0) : 0 ≤ discrim a b c`**
  — the reusable **per-derivative atom**. Two lines:
  `rw [discrim_eq_sq_of_quadratic_eq_zero h]; exact sq_nonneg _`.
- **`monic_quadratic_discrim_nonneg`** / **`discrim_nonneg_of_roots_nonempty`**
  — the atom phrased through `Polynomial.IsRoot` and through a nonempty
  `Polynomial.roots` multiset (genuine real-rootedness), respectively.
- **`realRooted_quadratic_coeff_ineq`** — coefficient form `4*c ≤ b^2`.
- **`prod_two_linear_eq`** / **`root_of_prod_two_linear`** — Vieta:
  `(X - x)(X - y) = X² - (x+y)X + xy`, and `x` is a root.
- **`newton_two_vars (x y : ℝ) : x*y ≤ ((x+y)/2)^2`** — Newton's `p₁² ≥ p₀p₂` at
  `n = 2`, obtained as the discriminant of the real-rooted `(X-x)(X-y)`.
  **No sign hypothesis**: the roots need only be real. This is the signed-input
  generalization the real-rootedness route enables (the parent needs `0 ≤ xᵢ`).

### Reusable Lean gotchas (researcher-8)
- **`discrim_eq_sq_of_quadratic_eq_zero {x} (h : a*(x*x)+b*x+c=0) :
  discrim a b c = (2*a*x+b)^2`** (Mathlib `Algebra/QuadraticDiscriminant.lean`,
  `CommRing`) is the completed-square identity. It makes "real root ⇒ nonneg
  discriminant" a 2-line proof over ℝ (`rw` + `sq_nonneg`). `discrim a b c` is
  defined as `b^2 - 4*a*c`.
- Bridging `Polynomial.IsRoot` to the atom: `simpa [IsRoot, eval_add, eval_mul,
  eval_pow, eval_X, eval_C] using hr` gives `r^2 + b*r + c = 0`; the atom wants
  `1*(r*r)+b*r+c = 0`, so close with **`linear_combination hroot`** (ring knows
  `r^2 = r*r`).
- `Multiset.exists_mem_of_ne_zero : s ≠ 0 → ∃ a, a ∈ s` + `mem_roots'.1 hr : p ≠ 0
  ∧ IsRoot p r` extract a real root from a nonempty `roots` multiset.
- Pushing `C` through a product: `rw [C_neg, C_add, C_mul]; ring` proves
  `(X - C x)*(X - C y) = X² + C(-(x+y))*X + C(x*y)` in `ℝ[X]`.

### Still open (the crux)
The general `n ≥ 3` case needs **"differentiation preserves full real-rootedness
counting multiplicity"** — iterated Rolle on `∏(X - xᵢ)`. Mathlib has Rolle
(`exists_hasDerivAt_eq_zero`) and `Polynomial.derivative` / `Polynomial.roots`
but **not** the packaged lemma
`p.roots.card = p.natDegree → (derivative p).roots.card = (derivative p).natDegree`.
`problem.md` estimates this at multi-week difficulty; it is honestly retained as
open and deliberately **not** stubbed in the file.

### Recommended next increments
1. Prove the derivative-preserves-real-rootedness lemma (Rolle between
   consecutive roots + multiplicity at repeated roots).
2. Newton at `n = 3` as the first nontrivial instance: the derivative of a monic
   cubic is a quadratic, and Rolle gives its two real roots directly (no general
   multiplicity machinery needed for this special case).

---

## Problem Understanding

Newton's inequalities `pₖ² ≥ pₖ₋₁ pₖ₊₁` for the normalized elementary symmetric
means `pₖ = eₖ / C(n,k)` of real numbers. This entry wants the **real-rooted**
(Rolle/discriminant) proof, which also extends to signed inputs.

---

## Insights

See PART I above.

---

## Dead Ends

None yet.

## PART II — Newton at n=3 via SOS discriminant certificates (researcher-5, 2026-07-04)

**Mode**: ACT (MODERATE, score 13). **Outcome**: progress (+5 verified theorems, axiom-free).
docker-build clean, 7743 jobs, foundational axioms only; no `decide`/`native_decide`, 0 sorries.

### What this adds
Extends the PART-I real-rooted/discriminant route from the `n = 2` base case to the first
nontrivial arity `n = 3` — both Newton log-concavity steps, for SIGNED reals:
- `newton_three_first`: `3(xy+yz+zx) ≤ (x+y+z)²` (`e₁² ≥ 3e₂`); SOS `½[(x−y)²+(y−z)²+(z−x)²]`.
- `newton_three_second`: `3(x+y+z)·xyz ≤ (xy+yz+zx)²` (`e₂² ≥ 3e₁e₃`);
  SOS `½[(xy−yz)²+(yz−zx)²+(zx−xy)²]`.
- `discrim_deriv_cubic_first` / `discrim_recip_deriv_cubic_second`: same two facts as the
  nonneg discriminants of `P' = 3X²−2e₁X+e₂` and `−3e₃X²+2e₂X−e₁`.
- `newton_three_normalized`: both steps in normalized p-mean form.

### Technique
Each `nlinarith [sq_nonneg …]` closes the Newton inequality directly; the discriminant-form
theorems are then `rw [discrim]; nlinarith [newton_three_*]`. The Rolle/derivative picture
(cubic real-rooted ⇒ derivative quadratic real-rooted ⇒ discriminant ≥ 0) is the *motivation*;
the SOS certificate is the *proof*, so no iterated-Rolle machinery is needed and no sign
hypothesis is required (only real roots).

SOS derivation of the second: `e₂² − 3e₁e₃ = x²y²+y²z²+z²x² − xyz(x+y+z) = ½Σ(xy−yz)²`.

### Still open (unchanged)
The GENERAL (arbitrary-`n`) Newton still needs "differentiation preserves full
real-rootedness counting multiplicity" (iterated Rolle) — not in Mathlib, multi-week
(`problem.md`). The per-arity SOS route works for each fixed small `n` but does not scale
symbolically; n=4 would be a further concrete instance approaching enumeration.

## PART V — the GENERAL Rolle crux, closed via Mathlib (researcher-5, 2026-07-04)

**Mode**: ACT (MODERATE, score 13). **Outcome**: progress — retires the
long-flagged "multi-week" blocker. **+4 verified theorems (20 → 24), 0 sorries,
0 axioms** (foundational only; no `decide`/`native_decide`). docker-build clean,
7743 jobs.

### The key discovery
The blocker recorded across Parts I–IV — "differentiation preserves full
real-rootedness counting multiplicity" (iterated Rolle on `∏(X−xᵢ)`), estimated
multi-week in `problem.md` and "not in Mathlib" in this knowledge base — is
WRONG about Mathlib. Mathlib supplies the hard half directly:

- **`Polynomial.card_roots_le_derivative (p : ℝ[X]) :
  Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1`**
  in `Mathlib/Analysis/Calculus/LocalExtr/Polynomial.lean` (Benjamin Davidson,
  Yury Kudryashov) — the multiplicity-counted Rolle bound. Also there:
  `card_roots_toFinset_le_derivative`, `card_rootSet_le_derivative`.

### Shipped (`Proofs/AmgmInequalityOQ02OQ02OQ05.lean`, Part V)
- **`derivative_roots_card_eq {p : ℝ[X]}
  (hp : card p.roots = p.natDegree) : card (derivative p).roots =
  (derivative p).natDegree`** — THE CRUX, general (all `n`). A full-real-rooted
  `p` forces its derivative to be full-real-rooted. Proof is a 4-line sandwich:
  `card_roots_le_derivative` gives `card(p') ≥ natDegree p − 1`;
  `card_roots'` gives `card(p') ≤ natDegree p'`; `natDegree_derivative_lt` gives
  `natDegree p' < natDegree p` (so `≤ natDegree p − 1`); `omega` closes. Constant
  case `natDegree p = 0` handled via `natDegree_eq_zero.mp` + `derivative_C`.
- **`splits_derivative {p : ℝ[X]} (hp : Splits p) : Splits (derivative p)`** — the
  `Splits`-level phrasing, via `splits_iff_card_roots` (note: modern Mathlib
  `Splits` is the single-argument `Polynomial.Splits (f : R[X])` in
  `Algebra/Polynomial/Factors.lean`, NOT the classical `Splits (i : K →+* L) f`).
- **`splits_iterate_derivative {p} (hp : Splits p) (k : ℕ) :
  Splits (derivative^[k] p)`** — trivial induction; the full program output
  (all k derivatives of `∏(X−xᵢ)` split).
- **`exists_isRoot_derivative_Ioo {p} (hab : a < b) (ha : p.IsRoot a)
  (hb : p.IsRoot b) : ∃ c ∈ Ioo a b, (derivative p).IsRoot c`** — the per-gap
  Rolle atom, packaged for the `Polynomial` API from `exists_hasDerivAt_eq_zero`
  + `Polynomial.hasDerivAt` + `Polynomial.continuousOn`.

### Reusable Lean gotchas (researcher-5, Part V)
- `Polynomial.hasDerivAt (x) : HasDerivAt (fun x => p.eval x) ((derivative p).eval x) x`
  (in `Analysis/Calculus/Deriv/Polynomial.lean`) is the analytic-derivative
  bridge; feed it to Rolle's `exists_hasDerivAt_eq_zero` as
  `fun x _ => p.hasDerivAt x`, with `p.continuousOn` for the `ContinuousOn` arg.
- `IsRoot p a` is DEFEQ to `p.eval a = 0`, so `have h : p.eval a = 0 := ha`
  coerces directly (no `unfold`); then plain `rw` works.
- `card_roots'` (NOT `card_roots`, which is the `≠0` degree-eq form) is the
  unconditional `card q.roots ≤ q.natDegree`.
- The whole crux is `omega` after three `have`s — the Nat sandwich is linear.

### Still open (narrowed)
The real-rootedness HALF of the classical Newton proof is now closed for all `n`.
What remains is purely the **coefficient bookkeeping**: identifying the
`(n−k−1)`-th derivative of the (reversed) splitting polynomial as the quadratic
`a eₖ₋₁ X² − b eₖ X + c eₖ₊₁`, so that its real-rootedness
(`derivative_roots_card_eq`) feeds the Part I discriminant atom
`discrim_nonneg_of_roots_nonempty` to yield `pₖ² ≥ pₖ₋₁ pₖ₊₁` for general `k`.
This is Vieta/`coeff`-level algebra (no more analysis), and is the honest next
increment — no longer blocked on the "multi-week" real-rootedness lemma.

## PART VII — the general-`n` TOP step, end-to-end via the Rolle route (researcher-8, 2026-07-04)

**Mode**: ACT (MODERATE, score 13). **Outcome**: progress — closes the
"coefficient bookkeeping" gap for the TOP Newton step at arbitrary arity.
**+2 verified theorems (26 → 28), 0 sorries, 0 axioms** (foundational only).
docker-build clean, 7743 jobs.

### What this adds
Parts V–VI proved the two engine halves but only ever applied the discriminant
join to an *abstract* degree-2 polynomial. Part VII runs the WHOLE program on one
split polynomial of arbitrary degree — the first genuine end-to-end use:
- **`discrim_iterate_derivative_top (m) {p} (hp : Splits p)
  (hdeg : p.natDegree = m + 2)`** :
  `0 ≤ discrim ((2+m).descFactorial m • p.coeff (2+m))
  ((1+m).descFactorial m • p.coeff (1+m)) ((0+m).descFactorial m • p.coeff (0+m))`.
  Differentiate `m` times (Part V `splits_iterate_derivative` keeps it split) down
  to a quadratic, apply Part VI `discrim_coeff_nonneg_of_splits_deg_two`, then read
  the three coefficients back on `p` via `Polynomial.coeff_iterate_derivative`.
  No sign hypothesis (real-rootedness suffices).
- **`newton_top_coeff_ineq (m) {p} …`** : the recognizable `b² ≥ 4ac` form
  `4·(2+m)!desc·m!desc·p.coeff(m+2)·p.coeff m ≤ ((1+m)!desc)²·p.coeff(m+1)²`.

### Key Lean facts (Mathlib API confirmed)
- `Polynomial.coeff_iterate_derivative {k} (p) (m) :
  ((⇑derivative)^[k] p).coeff m = (m + k).descFactorial k • p.coeff (m + k)` —
  THE bridge from the reduced quadratic's coefficients back to `p`'s. Rewriting
  leaves the index as `m + k` (e.g. `0 + m`), so state targets in `(i + m)` form.
- `Polynomial.natDegree_iterate_derivative` gives only `≤ natDegree p − k`; get
  equality by pairing with `le_natDegree_of_ne_zero` on the (nonzero) top coeff.
- `Nat.descFactorial_pos : 0 < n.descFactorial k ↔ k ≤ n`;
  `Nat.descFactorial_self : n.descFactorial n = n !`.

### Still open (narrowed to Vieta)
The ONLY remaining piece for the general TOP step is the Vieta substitution
`p = ∏(X−xᵢ)` ⇒ `p.coeff (n−k) = (−1)^k eₖ`, turning `newton_top_coeff_ineq` into
`pₙ₋₁² ≥ pₙ₋₂ pₙ`. General *interior* steps need the same machinery on a
sub-window derivative (isolating `eₖ₋₁,eₖ,eₖ₊₁` instead of the top three). Both
are purely algebraic — no analysis blocker remains.
