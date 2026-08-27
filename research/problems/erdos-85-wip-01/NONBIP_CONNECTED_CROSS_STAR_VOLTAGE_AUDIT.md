# NONBIP-CONNECTED cross-star voltage audit

## Candidate

For a defect edge xy, the ambient neighborhoods `N_A(x)` and `N_A(y)` are
disjoint.  C4-freeness makes the ambient edges between the two stars a
matching.  Its cardinality is exactly the length-three walk count

```text
m_xy = e_A(N_A(x),N_A(y)) = (A^3)_{xy}.
```

The only ordering-free first voltage is

```text
sigma_xy = m_xy (mod 2).
```

It defines a signed defect graph.  If every D-cycle has even voltage, sigma is
a coboundary `sigma_xy=p_x+p_y`, giving a split double cover and a possible
vertex potential to compare with rooted triangle data.

## Full q=4 calibration

`nonbip_connected_cross_star_voltage_q4.py` checks all 256 labelled models.
The voltage is balanced in every model, but its potential does not track
triangle parity.  Each model has two eight-vertex defect components:

```text
component 1: t=1 at all 8 vertices, potential split 4 zero / 4 one;
component 2: t=2 at all 8 vertices, potential split 4 zero / 4 one.
```

Thus `p_x+t_x (mod 2)` takes both values on each component.  The exact
defect-edge profiles are

```text
(Axy,t_x,t_y,m_xy,sigma_xy), count
(0,1,1,4,0), 4
(0,2,2,2,0), 4
(0,2,2,3,1), 8
(1,1,1,7,1), 8.
```

The cover balance is therefore real calibration, but it produces a new shore
unrelated to the already-constant rooted triangle class.

## Why Z/4 does not repair it canonically

One might retain `m_xy mod4` rather than parity.  A voltage on an undirected
edge must change sign when its orientation is reversed.  Without a canonical
orientation or ordering of the two stars, relabeling invariance requires
`v_xy=-v_xy`; over Z/4 this restricts values to 0 or2.  The observed matching
sizes 3 and7 are odd, so raw `m_xy mod4` cannot define an ordering-free Z/4
voltage.  Choosing vertex labels supplies an artificial orientation and no
graph invariant.

More detailed matching placement also has no canonical sign: the two stars
are unlabeled q-sets and a partial matching has only its size as an invariant
under independent star permutations.  Extracting a permutation sign requires
the missing coordinate/geometry structure.

## Verdict

The canonical Z/2 cross-star voltage is **cut as a propagation mechanism**.
It may be balanced, but its potential varies inside constant-t defect
components and therefore cannot force `t_x=t_y mod4` or the rooted mass
congruence.  There is no natural Z/4 refinement when odd cross-star matching
sizes occur.  Reopening the voltage idea requires an independently constructed
orientation or coordinate system on every star, which is additional finite
geometry rather than a consequence of the current graph axioms.
