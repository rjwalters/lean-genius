# A-REG owner square-closure rooted audit

Status: exact general identity and faithful `q=4` falsifier, 2026-08-27.
This records the bounded probe selected in divergence round 95.  The proposed
rooted nonnegative defect is cut: the square-closure variation is compensated
pointwise by defect codegrees and the selector triangle bit.

## Setup

Use the notation of `A_REG_OWNER_ALGEBRA.md`.  Thus the defect components have
normalized sizes `m_c`, with

```text
sum_c m_c = q,
```

the owner graphs have adjacency matrices `O_c`, and

```text
H := sum_c O_c = J - I - D.
```

Put `S2 := sum_c m_c^2`.  Fix a `c`-owned edge `xy`.  Since it is not a
defect edge, direct expansion gives

```text
(H^2)_{xy} = q(q-2) + (D^2)_{xy}.                         (1)
```

For distinct owner colors, OWNER-CROSS says

```text
(O_a O_b)_{xy} =
  m_b(m_c-1)   if a=c,
  m_a(m_c-1)   if b=c,
  m_a m_b      if a,b != c.
```

Consequently the ordered cross-color sum is

```text
sum_{a != b} (O_a O_b)_{xy}
  = 2(m_c-1)(q-m_c) + (q-m_c)^2 - (S2-m_c^2)
  = q^2 - 2q + 2m_c - S2.                                (2)
```

Subtracting (2) from (1) yields the exact rooted square identity

```text
sum_d (O_d^2)_{xy} = S2 - 2m_c + (D^2)_{xy}.              (3)
```

This is the complete content of summing the square-closure defects over the
owner colors at an owned edge.  In particular it has no unaccounted positive
remainder.

## Size-two specialization

When every component has normalized size two, `S2=2q` and (3) becomes

```text
sum_d (O_d^2)_{xy} = 2q - 4 + (D^2)_{xy}.                 (4)
```

The selector equivalence identifies `O_c` with the line graph of the
`q`-regular graph `H_c = complement(D_c)`.  Two adjacent selector edges share
one endpoint, so their common-neighbor count in the line graph is

```text
(O_c^2)_{xy} = q - 2 + t_c(x,y),                          (5)
```

where `t_c(x,y)` is zero or one according as the two selector edges do not or
do lie in a triangle of `H_c`.  Equations (4) and (5) give

```text
sum_{d != c} (O_d^2)_{xy}
  = q - 2 + (D^2)_{xy} - t_c(x,y).                        (6)
```

Thus the hoped-for rooted surplus is exactly traded between the local
selector triangle and the defect codegree.

## Faithful `q=4` check

An exact enumeration of the formalized `sixteenRegular` graph reconstructs
its two eight-vertex defect components and both owner matrices from

```text
(O_c)_{xy} = number of common G-neighbors of x,y in component c.
```

For owner edges whose endpoints lie in distinct defect components,
`(D^2)_{xy}=0`, and both profiles occur in each owner color:

```text
t_c=0:  ((O_c^2)_{xy}, (O_d^2)_{xy}) = (2,2),
t_c=1:  ((O_c^2)_{xy}, (O_d^2)_{xy}) = (3,1).
```

Same-component owner edges also realize the compensating profiles

```text
(D^2)_{xy}=1, t_c=0:  (2,3),
(D^2)_{xy}=2, t_c=1:  (3,3),
```

up to swapping the owner colors.  Hence neither summing square defects nor
Hadamard-projecting them onto an owner color forces square closure: variation
already occurs pointwise in the faithful exceptional graph.

## Verdict

**Cut.**  The local square-closure/max-principle route reduces to (3), and in
the size-two line-graph form to (6).  Any surviving ambient argument must use
more than the one-edge square data: for example simultaneous three-color
placement, a global arithmetic coupling, or a genuinely canonical routing
operation.  Raw associativity, owner-color summation, and nonnegativity do not
provide a terminal.
