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

## PART VIII — Vieta closure of the TOP step: the calculus route reaches Newton's inequality on esymm(roots) (researcher-5, 2026-07-04)

**Mode**: ACT (MODERATE, score 13). **Outcome**: progress — CLOSES the
"coefficient bookkeeping / Vieta" gap for the TOP Newton step at arbitrary arity.
**+2 verified theorems (28 → 30), 0 sorries, 0 axioms** (foundational only; no
`decide`/`native_decide`). docker-build clean, 7743 jobs, Lean 4.26.0.

### What this closes
Part VII left the top step one purely-algebraic increment short: substitute the
top coefficients of the split polynomial via Vieta to turn the coefficient
inequality `newton_top_coeff_ineq` into the classical Newton inequality on the
elementary symmetric functions of the *roots*. Part VIII does exactly that, so
the classical calculus proof now runs end-to-end (differentiate → discriminant →
Vieta) to a symmetric-function inequality for every arity `n = m + 2`:

- **`newton_top_esymm_roots (m) {p} (hp : p.Splits) (hdeg : p.natDegree = m + 2)`** :
  `4·(m+2)!desc·m!desc·lc²·e₂ ≤ ((m+1)!desc)²·lc²·e₁²`, with `lc = p.leadingCoeff`,
  `e₁ = p.roots.esymm 1`, `e₂ = p.roots.esymm 2`. The Vieta substitution of
  `newton_top_coeff_ineq`'s three coefficients.
- **`newton_top_esymm_roots_monic (m) {p} (hp : p.Splits) (hmonic : p.Monic)
  (hdeg : p.natDegree = m + 2)`** : the recognizable classical form
  `2·(m+2)·e₂ ≤ (m+1)·e₁²`, i.e. the first Newton/Maclaurin inequality
  `e₁² ≥ (2n/(n-1))·e₂` for every `n = m+2` — reached via the calculus route (the
  same inequality Part III proves independently by QM–AM).

### Key Lean facts (Mathlib API confirmed, Mathlib 4.26.0)
- **`Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
  (hsplit : p.Splits) {k} (h : k ≤ p.natDegree) : p.coeff k = p.leadingCoeff *
  (-1)^(p.natDegree - k) * p.roots.esymm (p.natDegree - k)`** (in
  `RingTheory/Polynomial/Vieta.lean`) — THE Vieta substitution, ready-made for a
  split polynomial's coefficients. No need to build `∏(X−xᵢ)` by hand.
- `Polynomial.coeff_natDegree : p.coeff p.natDegree = p.leadingCoeff` — the top
  coefficient directly (avoid Vieta at `k = natDegree`, where `esymm 0` needs
  extra unfolding).
- **`Nat.succ_descFactorial (n) (k) : (n+1-k)*(n+1).descFactorial k =
  (n+1)*n.descFactorial k`** collapses the three `descFactorial` weights: with
  `n=m+1,k=m` it gives `2·(m+2).descFactorial m = (m+2)·(m+1).descFactorial m`;
  with `n=m,k=m` it gives `(m+1).descFactorial m = (m+1)·m.descFactorial m`. These
  two identities (cast to ℝ) reduce the raw weights to the clean `2(m+2)` / `(m+1)`.
- `Polynomial.Monic.leadingCoeff : p.Monic → p.leadingCoeff = 1`;
  `Nat.descFactorial_pos : 0 < n.descFactorial k ↔ k ≤ n` (positivity for the
  `B²`-cancellation).

### Reusable Lean gotchas (researcher-5, Part VIII)
- `newton_top_coeff_ineq` states its indices/weights in `(2+m),(1+m),(0+m)` form.
  `2+m` is a STUCK nat term (add recurses on 2nd arg), so `Nat.succ_descFactorial`
  can't fire on it. Normalize first: `rw [show (2:ℕ)+m = m+2 from by omega, …] at h`
  to get the `succ`-reducible `(m+2)` bases. `(m+1)+1` IS defeq `m+2`, so
  `exact e` closes the cast identities without extra rewriting.
- The weight collapse `2(m+2)B² = (m+1)·4AC` is one `linear_combination
  (-2*B)*id1R + (4*A)*id2R` from the two cast identities `id1R : 2A=(m+2)B`,
  `id2R : B=(m+1)C`. Then multiply the coeff inequality by `(m+1) ≥ 0`
  (`mul_le_mul_of_nonneg_left`) and cancel `B² > 0`
  (`le_of_mul_le_mul_right … hBsq`) — no `nlinarith` blowup on the esymm atoms.
- `set A/B/C/e1/e2` BEFORE the arithmetic so `linear_combination`/`ring` see small
  opaque variables rather than `((m+2).descFactorial m : ℝ)` / `p.roots.esymm _`.

### Still open (narrowed to interior steps)
The TOP step is now fully closed via the calculus route for every arity. What
remains is the GENERAL *interior* Newton step `pₖ² ≥ pₖ₋₁pₖ₊₁` for `2 ≤ k ≤ n−2`:
apply the same engine to a *sub-window* iterated derivative that isolates
`eₖ₋₁,eₖ,eₖ₊₁` (rather than the top three). The reciprocal polynomial
`Xⁿ·p(1/X)` maps the bottom window to a top window, so the top-step machinery plus
a reciprocal-coefficient (`reverse`) bridge should reach the second-from-top and
second-from-bottom steps next; the strictly interior windows need differentiating
both `p` and its reverse. Purely algebraic — no analysis blocker.

## PART IX — the general-`n` INTERIOR Newton step: an arbitrary window (researcher-5, 2026-07-04)

**Mode**: REVISIT/continue (RICH). **Outcome**: progress — **CLOSES the last
documented gap**, the general interior Newton step, for every window and every
arity at once. **+2 verified theorems (36 → 38), 0 sorries, 0 axioms**
(foundational only; no `decide`/`native_decide`). docker-build clean, 7743 jobs,
Lean 4.26.0. (The BOTTOM step `splits_reverse` / `discrim_reverse_bottom` /
`newton_bottom_coeff_ineq` — Part VIII, reversal-mirror of the top step — is
already merged into the Lean file, though its knowledge section was lost in a
concurrent merge; Part IX below generalizes it to every window.)

### What this closes
Parts VII/VIII gave the TOP window (`discrim_iterate_derivative_top`, `p`'s three
top coefficients) and the BOTTOM window (`discrim_reverse_bottom`, `j = 0`). The
strictly interior windows `p.coeff j, p.coeff (j+1), p.coeff (j+2)` (any `j` with
`j + 2 ≤ natDegree p`) needed the differentiate-**and**-reverse composition the
prior "Still open" note anticipated. Part IX supplies exactly that, so the honest
calculus route now reaches Newton's log-concavity inequality on *every*
consecutive coefficient window of an arbitrary real-rooted polynomial.

### Shipped (`Proofs/AmgmInequalityOQ02OQ02OQ05.lean`, Part IX)
- **`discrim_reverse_interior (j m) {p} (hp : Splits p) (hcj : p.coeff j ≠ 0)
  (hdeg : p.natDegree = j + (m + 2))`** : `0 ≤ discrim` of the three consecutive
  coefficients `p.coeff j, p.coeff (j+1), p.coeff (j+2)`, each weighted by the
  `descFactorial` factors `(i+m).descFactorial m · (i+j).descFactorial j` of the
  two differentiation passes. Proof: `q := derivative^[j] p` splits (Part V) and
  has `q.coeff 0 = j!·p.coeff j ≠ 0` (so `natTrailingDegree q = 0`) and
  `q.natDegree = m+2`; apply the TOP engine `discrim_iterate_derivative_top` to
  `reverse q` (splits by Part VIII, degree `m+2`), whose top three coefficients
  are `q`'s bottom three = `p`'s window (`coeff_reverse` + `revAt_le` +
  `coeff_iterate_derivative`), then fold the two nested `•` weights with
  `← mul_smul`. The `j = 0` case is definitionally `discrim_reverse_bottom`.
- **`newton_interior_coeff_ineq (j m) {p} …`** : the recognizable
  `4·(weights)·p.coeff j·p.coeff (j+2) ≤ (weight)²·p.coeff (j+1)²` — Newton's
  log-concavity step on an arbitrary window, subsuming both `newton_top_coeff_ineq`
  and `newton_bottom_coeff_ineq`.

### Key realization
Differentiation alone can never reach an interior window: for `q = derivative^[r] p`,
`coeff_iterate_derivative` sends `q`'s *top* three coefficients back to `p`'s top
three (always). To slide the window down you must reverse. The clean composition is
"differentiate `j` times → reverse → apply the top engine": after `j` derivatives
the window `p.coeff j, j+1, j+2` sits at the *bottom* of `q`, and reversing lifts it
to the top of a genuine quadratic where the discriminant is read off. This is why a
single `reverse` (Part VIII, `j = 0`) only reached the very bottom, while general
`j` needs the derivative pass first.

### Reusable Lean gotchas (researcher-5, Part IX)
- `coeff_iterate_derivative` emits the base/index in `0 + j` form (NOT normalized
  to `j`). When the result must unify with a hypothesis stated on `p.coeff j`
  (here `hcj`), insert `Nat.zero_add` in the same `rw` chain
  (`rw […, nsmul_eq_mul, Nat.zero_add]`) — one rewrite fixes both the `descFactorial`
  base and the `coeff` index (rw hits all `0 + j` occurrences of that instantiation).
- Nested `ℕ`-scalar weights `a • (b • x)` from composing two `coeff_iterate_derivative`
  / reverse passes fold to `(a * b) • x` with **`← mul_smul`** (`mul_smul : (a*b)•x =
  a•b•x`); apply once per discriminant slot.
- The coefficient-inequality corollary's `nlinarith` **SIGBUS-crashes the elaborator
  (exit 135)** on the raw `↑((i+m).descFactorial m · (i+j).descFactorial j)` casts and
  `p.coeff` subterms. Fix (same as Part VI): `simp only [nsmul_eq_mul, Nat.cast_mul]`
  to split the cast product, then `set A := …` each of the six `descFactorial` casts
  and three coefficients to opaque atoms BEFORE `nlinarith [h]`.
- `set q := derivative^[j] p with hq` does NOT auto-fold `derivative^[j] p` in
  hypotheses generated *after* the `set` (e.g. `natDegree_iterate_derivative p j`);
  fold them manually with `rw [← hq] at hle`.

### Still open (the remaining Vieta polish)
The interior *coefficient* inequality is closed for all windows. The only remaining
increment mirrors Part VIII's TOP Vieta closure: substitute
`p.coeff k = lc·(-1)^(n-k)·eₙ₋ₖ` (`coeff_eq_esymm_roots_of_splits`) into
`newton_interior_coeff_ineq` to state the interior step directly on the elementary
symmetric functions `eₖ₋₁, eₖ, eₖ₊₁` of the roots (the classical `eₖ² ≥ eₖ₋₁eₖ₊₁`
form). Purely algebraic — the calculus engine is complete.
