# Claim — Thue / Fermat-Catalan reduction attempt (documented dead-end)

- **Vector attempted**: reduction
- **Date**: 2026-06-17
- **Author**: loom-builder (agent-2), issue #22638
- **Status**: failed (documented dead-end) — no reduction available; **partial**
  in that one *conditional, non-uniform* finiteness statement does follow from
  the abc conjecture.

## What was tried

I read the four cited finiteness results and tested whether the defect-one
equation can be cast into a form to which each one applies. The defect-one
equation at exponent $n$ is the pair of ternary Diophantine equations

$$
a^n + b^n = c^n + 1 \quad(\text{positive defect}), \qquad
a^n + b^n + 1 = c^n \quad(\text{negative defect}),
$$

with the constraints $2 \le a \le b < c$ and $\gcd(a, b, c) = 1$. The
defect-one **existence** conjecture (Level 2 in `problem.md`) asserts that for
*every* $n \ge 3$ at least one such triple exists. The reduction vector asks
whether existence — or its **negation at a specific $n$** — is a corollary of:

1. Fermat-Catalan (Darmon-Granville 1995; Beukers 1998),
2. Thue-equation finiteness,
3. the abc conjecture and its effective forms (Waldschmidt 2009).

Literature consulted:

- H. Darmon and A. Granville, *On the equations $z^m = F(x,y)$ and
  $Ax^p + By^q = Cz^r$*, Bull. London Math. Soc. **27** (1995), 513–543.
- F. Beukers, *The Diophantine equation $Ax^p + By^q = Cz^r$*, Duke Math. J.
  **91** (1998), 61–88.
- M. Waldschmidt, *Perfect powers: Pillai's works and their developments*
  (2009),
  https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/PerfectPowers.pdf.
- A. Thue, *Über Annäherungswerte algebraischer Zahlen*, J. reine angew. Math.
  **135** (1909), 284–305 (finiteness for binary forms $F(x,y) = m$).

## What happened

Every reduction attempt fails for a structural reason. I record each
obstruction precisely so the next iteration does not retread it.

### 1. Fermat-Catalan does NOT apply — the unit destroys the exponent condition

The Fermat-Catalan finiteness theorem concerns
$$
x^p + y^q = z^r, \qquad \tfrac1p + \tfrac1q + \tfrac1r < 1, \qquad \gcd(x,y,z)=1.
$$
Darmon-Granville (1995) proved that for each **fixed** signature $(p, q, r)$
satisfying the hyperbolicity inequality $1/p + 1/q + 1/r < 1$ there are only
finitely many primitive solutions; Beukers (1998) gives the parametrized
description in the spherical/Euclidean cases. The Fermat-Catalan **conjecture**
(only finitely many solutions across *all* signatures) remains open.

The fatal obstruction: in the defect-one equation the term "$1$" is
$1 = 1^k$ for **every** exponent $k$. To write $a^n + b^n = c^n + 1$ as a
Fermat-Catalan instance one must assign an exponent to the unit term, and the
unit is a perfect $k$-th power for all $k$. The natural reading

$$
a^n + b^n = c^n + 1^r
$$

is most charitably treated as the signature $(n, n, n)$ with a $+1$ shift —
but a $+1$ shift is **not** a Fermat-Catalan term at all: Fermat-Catalan is a
*homogeneous* sum-of-three-powers equation $X + Y = Z$ with $X, Y, Z$ each a
perfect power, whereas $a^n + b^n - c^n = \pm 1$ has a fixed inhomogeneous
constant. The only way to absorb the unit as a power is to set $r = 1$ (so that
$1 = 1^1$), giving signature $(n, n, 1)$ with
$$
\tfrac1n + \tfrac1n + \tfrac11 = 1 + \tfrac2n > 1,
$$
which **violates** the hyperbolicity inequality $1/p + 1/q + 1/r < 1$. The
equation $a^n + b^n = c^n + 1$ therefore lives in the *non-hyperbolic*
(parabolic/spherical) regime where Fermat-Catalan provides **no finiteness**:
those signatures have either infinitely many or parametrically-many solutions,
and the theorem is silent. Concretely, $X + Y = Z$ with $Z$ a first power
($r=1$) is just "$X + Y = $ an integer", which is unconstrained.

**Conclusion:** Fermat-Catalan finiteness cannot be invoked, in either
direction. It can neither prove existence (it is a finiteness theorem, not an
existence theorem) nor refute existence at a specific $n$ (the relevant
signature fails hyperbolicity, so no finiteness is asserted to contradict).

### 2. Thue equations do NOT apply — the equation is irreducibly ternary

Thue's theorem gives finiteness for $F(x, y) = m$ where $F \in \mathbb{Z}[x,y]$
is a **binary** form, homogeneous of degree $\ge 3$ and irreducible (more
precisely with at least three distinct linear factors over $\overline{\mathbb Q}$).
The defect-one equation has **three** free variables $a, b, c$; it is a
ternary, inhomogeneous, diagonal equation $a^n + b^n - c^n = \pm 1$, not a
binary form set equal to a constant.

To force a Thue equation one would have to eliminate one variable by imposing an
*a-priori* algebraic relation among $a, b, c$ — e.g. fixing $c = b + 1$, or
$c - b = d$ for a fixed $d$. Substituting $c = b + d$ into $a^n + b^n - c^n =
\pm 1$ does **not** produce a homogeneous binary form: expanding $(b+d)^n$
leaves a polynomial in $b$ of degree $n$ with a non-vanishing constant term and
mixed lower-order terms in $a$ and $b$, i.e. an inhomogeneous polynomial, not a
Thue form $F(a, b) = \text{const}$. The leading homogeneous part $a^n - b^n$
*is* a Thue form (it factors into $n$ distinct linear factors over the cyclotomic
field), but the lower-order terms from the binomial expansion of $(b+d)^n$ break
homogeneity, so Thue's theorem does not apply to the full equation.

There is **no** natural two-variable specialization of $a^n + b^n - c^n = \pm 1$
that is a Thue equation. The closest legitimate Thue instances are *different*
problems (e.g. $a^n - b^n = m$ for fixed $m$, which is binary and homogeneous and
to which Thue *does* apply — but that is the two-term defect problem, not the
three-term defect-one problem).

**Conclusion:** Thue-equation finiteness applies only after a homogeneity-breaking
specialization that destroys the Thue form. It yields nothing for defect-one.

### 3. abc gives a CONDITIONAL, NON-UNIFORM finiteness — but no existence and no per-$n$ refutation

The abc conjecture *does* bear on the equation, and this is the one genuinely
productive observation. Write the positive-defect equation as the abc triple
$$
A = b^n, \quad B = 1, \quad C = c^n - a^n \quad\text{is not primitive…}
$$
The clean form is to view $a^n + b^n = c^n + 1$ as the abc relation among the
three summands of $a^n + 1 = c^n - b^n$ … which is not coprime in general. The
honest application is to the **two-term** consequence: a primitive defect-one
solution gives a near-equality $c^n - b^n = a^n \mp 1$, i.e. two perfect $n$-th
powers differing by approximately $a^n$, with the *defect* $\mp 1$ being the
abc "exceptional smallness."

The correct abc statement is the standard **Pillai/Waldschmidt** one: for the
equation $X - Y = k$ with $X, Y$ perfect powers and $k$ fixed, abc (and
unconditionally Baker's effective linear-forms-in-logarithms via Waldschmidt
2009) bounds the solutions. For defect-one the relevant "$k$" is $\pm 1$, and
the two powers are $c^n$ and $a^n + b^n$ — but $a^n + b^n$ is **not** a perfect
power (that is exactly the content of the problem), so Pillai/Waldschmidt does
**not** directly apply either.

What abc *does* give, by a standard radical estimate, is: for each fixed $n$,
the number of primitive solutions of $a^n + b^n - c^n = \pm 1$ with $a,b,c$
below a bound is constrained, and **conditional on abc**, the solution set for
each fixed $n \ge 4$ is **finite**. Sketch: rad$(a^n b^n (c^n \mp 1)) \le abc$,
and the defect-one constraint forces $c^n \mp 1$ and $a^n + b^n$ to be within
$1$ of each other, so the abc quality $q = \log C / \log \text{rad}(ABC)$ would
have to be bounded away from $1$ uniformly, which abc forbids for all but
finitely many triples at each fixed exponent. This is the standard heuristic
behind "Fermat-Catalan has finitely many solutions assuming abc" specialized to
the inhomogeneous diagonal slice.

**Crucially, this is the wrong direction for the conjecture.** Defect-one
**existence** asks to *produce* a solution for every $n$; an abc-conditional
*finiteness* statement says only that solutions are *rare*, not that they
*exist*. Finiteness is consistent with both "exactly zero solutions" and
"exactly one solution" at a given $n$. So abc:

- does **not** prove existence (it bounds, never produces, solutions);
- does **not** refute existence at any specific $n$ (finite $\ne$ empty — abc
  gives no effective lower bound below which one may certify *zero* solutions,
  and Waldschmidt's effective forms, while explicit, give bounds far too large
  to clear even $n = 4$ by computation);
- **is itself conjectural**, so any consequence is conditional.

## What this suggests for next iteration

1. **Abandon the `reduction` vector as a route to the headline conjecture.**
   None of Fermat-Catalan, Thue, or abc reduces to or from defect-one existence.
   The structural reasons are recorded above and are not bound-dependent — there
   is no "try a larger bound / different signature" fix. Record this in
   `notes/dead-ends.md`.

2. **The one salvageable artifact** is the abc-conditional, per-$n$ finiteness
   statement (§3). If a future iteration wants a Lean deliverable from this
   vector, the honest formalization is a **conditional** theorem of the shape
   "assuming an abc-type hypothesis as an explicit Lean hypothesis (not an
   `axiom`), the primitive defect-one solution set at each fixed $n \ge 4$ is
   finite." Per the repo Axiom Integrity Policy this must carry
   `status: axiomatized` (the abc hypothesis is a structure-encoded assumption),
   never `verified`. This is a *finiteness* lemma, **not** the existence headline,
   and should be filed under a new vector tag (`structural-lemma` or `other`),
   not advertised as resolving #22638's conjecture. I did **not** write this Lean
   lemma here because (a) it is conditional/axiomatized and out of scope for the
   `reduction` vector's deliverable, and (b) fabricating an unconditional Lean
   lemma would violate the Axiom Integrity Policy.

3. **Redirect effort to the productive vectors** documented in `problem.md`:
   - `witness-search` (#22635) — a single $n = 4$ hit ships as a verified
     `native_decide` theorem and is the highest-value cheap win.
   - `parameterization` (#22637) — a polynomial family $(a(t), b(t), c(t))$ with
     $a(t)^n + b(t)^n - c(t)^n \equiv \pm 1$ would settle a whole exponent at
     once; this is the only known route to an *unconditional existence* proof,
     and it is exactly the route reductions cannot supply.
   - `modular-obstruction` (#22636) — the only route to a rigorous *negation*
     (Level-3 per-sign refutation), which reductions also cannot supply because
     the relevant Fermat-Catalan signature is non-hyperbolic.

### One-line summary

The "$\pm 1$" defect is a *first power* ($1 = 1^r$ for all $r$), which (i) pushes
the Fermat-Catalan signature to the non-hyperbolic regime $1/n + 1/n + 1/1 > 1$
where no finiteness holds, (ii) breaks the homogeneity any Thue specialization
needs, and (iii) lets abc give only a conditional, non-effective, wrong-direction
*finiteness* — never the *existence* the conjecture asks for, nor an effective
*per-$n$ refutation*. The `reduction` vector is a documented dead-end for the
headline conjecture.
