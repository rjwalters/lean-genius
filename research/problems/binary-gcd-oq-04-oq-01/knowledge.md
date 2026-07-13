# Knowledge Base: binary-gcd-oq-04-oq-01 (A total computable binary GCD for ℤ[i])

## Problem Understanding

Target: define a **total** `binaryGcdGaussian : ℤ[i] → ℤ[i] → ℤ[i]` packaging the
parent's (`binary-gcd-oq-04`) reduction identities, and prove
`Associated (binaryGcdGaussian a b) (EuclideanDomain.gcd a b)`.

## Parent interface available (`Proofs/BinaryGcdOQ04.lean`, `namespace BinaryGcdOQ04`)

All VERIFIED, 0-axiom. `open Zsqrtd`; `pi : GaussianInt := ⟨1,1⟩` (= 1+i, N π = 2).

- `pi_ne_zero`, `pi_norm : Zsqrtd.norm pi = 2`, `pi_prime : Prime pi`.
- `pi_dvd_iff (z) : pi ∣ z ↔ (2:ℤ) ∣ (z.re + z.im)`  — π-evenness is a parity check
  on `re + im` (ℤ[i]/(π) ≅ 𝔽₂). This makes π-evenness **decidable** without a
  Mathlib `Decidable (pi ∣ z)` instance: branch on `decide ((2:ℤ) ∣ (z.re+z.im))`.
- `pi_dvd_sub_of_not_dvd (u v) (¬pi∣u)(¬pi∣v) : pi ∣ (u - v)`  — both-odd difference is π-even.
- `divPi (z) : ⟨(z.re+z.im)/2, (z.im-z.re)/2⟩`; `pi_mul_divPi (z)(pi∣z) : pi * divPi z = z`;
  `norm_divPi (z)(pi∣z) : Zsqrtd.norm z = 2 * Zsqrtd.norm (divPi z)`  — exact halving.
- `gcd_pi_mul (a b) : Associated (gcd (pi*a)(pi*b)) (pi * gcd a b)`      — both even.
- `gcd_pi_mul_odd (a v)(¬pi∣v) : Associated (gcd (pi*a) v)(gcd a v)`     — one even.
- `gcd_sub (u v) : Associated (gcd u v)(gcd (u-v) v)`                    — both odd (subtract).

## KEY FINDING (this session, researcher-4): the NAIVE Stein algorithm does NOT terminate over ℤ[i]

The parent's three identities are each true *up to `Associated`*, but **packaging them
into the obvious recursion loops forever**. Concretely, the naive algorithm

```
bgcd a b = if a=0 then b else if b=0 then a else if a=b then a
           else if π∣a ∧ π∣b then π * bgcd (divPi a) (divPi b)
           else if π∣a then bgcd (divPi a) b
           else if π∣b then bgcd a (divPi b)
           else {- both odd -} bgcd (a - b) b
```

**infinite-loops on `(a,b) = (1, -1)`** (both are units, N = 1):

```
(1, -1)      both odd, a≠b  → (1-(-1), -1) = (2, -1)
(2, -1)      π∣2, π∤-1       → (divPi 2, -1) = (1-i, -1)      [divPi ⟨2,0⟩ = ⟨1,-1⟩]
(1-i, -1)    π∣(1-i), π∤-1   → (divPi(1-i), -1) = (-i, -1)     [divPi ⟨1,-1⟩ = ⟨0,-1⟩]
(-i, -1)     both odd, a≠b   → (-i-(-1), -1) = (1-i, -1)       ← back to two steps ago
(1-i, -1) → (-i, -1) → (1-i, -1) → …                          CYCLE, never hits base case
```

Root cause = **two independent failures the integer algorithm is immune to because ℤ is ordered**:

1. **Norm is not monotone under subtraction.** Over ℤ the both-odd step `gcd(u,v)↦gcd(u-v,v)`
   with `u>v` strictly shrinks the larger operand (order). Over ℤ[i] there is no order, and
   `N(u-v)` can *exceed* `N(u)`: e.g. `u=1, v=-1 ⇒ N(u-v)=N(2)=4 > 1 = N(u)`. So `N(a)+N(b)`
   is **not** a valid termination measure for `gcd_sub`.
2. **Unit cycling.** For π-odd operands of equal small norm the difference stays small-norm,
   and the recursion oscillates among associates (`1-i`, `-i`, …) without ever reaching
   `a=0`/`b=0`/`a=b`. The base case must recognize associates (units), not just literal equality.

⇒ The OQ is genuinely harder than "assemble the three parent identities". It needs a
**termination strategy the parent does not supply.**

## The lever for a CORRECT terminating variant: the parallelogram law

For any `a b : ℤ[i]`,  `N(a+b) + N(a-b) = 2·(N a + N b)`  (real inner-product parallelogram law;
`Zsqrtd.norm` is the quadratic form `re² + im²`). Consequences for π-odd `a, b`:

- Both `a+b` **and** `a-b` are π-even (each has even `re+im`: odd±odd). So a terminating
  algorithm may choose *either* `a±b` (not just `a-b`) as the reducible operand.
- `min(N(a+b), N(a-b)) ≤ N a + N b`. Combined with a π-strip (`divPi`, norm ×½) this gives the
  progress the naive single-direction subtraction lacks — this is exactly the mechanism of the
  **(1+i)-ary GCD** of A. Weilert, *"(1+i)-ary GCD Computation in ℤ[i] as an Analogue to the
  Binary GCD Algorithm"*, J. Symbolic Comp. 30 (2000) 605–617; see also Damgård & Frandsen,
  *"Efficient Algorithms for the gcd and cubic residuosity in the ring of Eisenstein integers"*.
- `(a+b)+(a-b) = 2a = -i·π²·a`, so `a+b` and `a-b` have the **same π-adic parity**: either both
  are divisible by `π²` (strip two π's ⇒ norm ×¼ ⇒ strict decrease vs. `max(Na,Nb)`), or both are
  exactly-once π-divisible and their π-quotients are again both π-odd (recurse). This dichotomy is
  the induction skeleton for a well-founded `decreasing_by` on `(Zsqrtd.norm ·).natAbs`.

## Recommended construction (for the next session, once the host disk unblocks builds)

Prefer a **`Nat`-fuel** definition `bgcdFuel : ℕ → ℤ[i] → ℤ[i] → ℤ[i]` (structurally recursive on
fuel ⇒ trivially total, no `termination_by` obligation for the *definition*), then
`binaryGcdGaussian a b := bgcdFuel (N a + N b).natAbs.succ … a b` for a bound justified by the
parallelogram/`π²` decrease above. Correctness splits cleanly:

1. **Base + unit handling.** `a=0 ⇒ b`; `b=0 ⇒ a`; and terminate on associates (a unit divides
   out): the loop above shows literal `a=b` is insufficient.
2. **Step preservation (EASY — direct from parent).** Each recursive step is one of
   `gcd_pi_mul` / `gcd_pi_mul_odd` / `gcd_sub` (or the `a+b` analogue of `gcd_sub`, provable the
   same way via `EuclideanDomain.dvd_gcd` + `associated_of_dvd_dvd`), composed with `Associated.trans`
   and `Associated.mul_left pi`. So `Associated (bgcdFuel n a b) (gcd a b)` follows by induction on
   `n` **provided the fuel does not run out** — the *only* hard part is (3).
3. **Fuel sufficiency / termination (HARD — the crux).** Show the chosen bound never exhausts,
   i.e. a base case is reached within `(N a + N b)`-ish steps. This is where the Weilert `π²`
   decrease and the associate-normalized base case are required. This is the residual open work.

## Dead Ends

- Naive single-direction Stein subtraction (`gcd_sub` only, terminate on literal `a=b`):
  non-terminating — proven above by the `(1,-1)` cycle. Do not re-attempt as-is.
- `N(a)+N(b)` as a `decreasing_by` measure for the both-odd step: fails (`N(u-v)` non-monotone).

## Next Steps

1. Implement `bgcdFuel` (π-even test via `decide ((2:ℤ) ∣ (re+im))`, `divPi` for strips), using the
   `min(N(a±b))` / `π²`-parity choice for the both-odd step, and an associate-aware base case.
2. Prove step preservation (obligation 2) — should be short given the parent identities; add the
   `a+b` analogue of `gcd_sub` if the algorithm uses it.
3. Prove the parallelogram law `N(a+b)+N(a-b) = 2(N a + N b)` in ℤ[i] (unfold `Zsqrtd.norm_def`,
   `ring`) as the termination lever, then the fuel-sufficiency bound (obligation 3).
4. Only after a `sorry`-free build (`docker-build.sh Proofs.BinaryGcdOQ04OQ01`) create the gallery
   entry + PR. Do NOT ship unverified Lean for this problem — the math is subtle (see the loop above).

## Session log

- researcher-4 (2026-07-02): SURVEY. Inventoried the parent interface; **proved the naive Stein
  packaging is non-terminating over ℤ[i]** (explicit `(1,-1)` cycle); identified the parallelogram
  law + Weilert (1+i)-ary π²-decrease as the correct termination lever. **No Lean produced/verified:
  host disk at 97% (430 MiB free) blocked worktree checkout ("No space left on device") and all
  Mathlib builds (#33336). Left a concrete, mostly-mechanical construction plan for a disk-unblocked
  session.**
