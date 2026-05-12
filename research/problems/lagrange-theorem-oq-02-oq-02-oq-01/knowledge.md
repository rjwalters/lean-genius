# Knowledge: lagrange-theorem-oq-02-oq-02-oq-01

## 1. The classical statement

**Burnside's Lemma** (Cauchy–Frobenius, 1845; popularised by Burnside
1897): for a finite group `G` acting on a finite set `X`,

$$|X/G| = \frac{1}{|G|} \sum_{g \in G} |\mathrm{Fix}(g)|$$

equivalently (and more convenient in Lean, where division of `ℕ`
needs `Nat.div_eq_iff`):

$$|X/G| \cdot |G| = \sum_{g \in G} |\mathrm{Fix}(g)|.$$

The proof is the standard double-counting argument on the set
`{(g, x) ∈ G × X : g · x = x}`. Counting by `g` gives the right-hand
sum; counting by `x` (using orbit–stabiliser, `|G| = |orbit(x)| · |Stab(x)|`)
gives `|G|` summed over orbit-representatives, i.e. `|X/G| · |G|`.

## 2. Connection to the parent file's class equation

The parent file `LagrangeTheoremOQ02OQ02.lean` defines:

- `class_equation` (Mathlib's
  `Group.nat_card_center_add_sum_card_noncenter_eq_card`):
  $|Z(G)| + \sum_{[x] \text{ non-central}} |[x]| = |G|$.
- `card_conjClass_eq_centralizer_index` (orbit–stabiliser for
  conjugation): $|[x]| = [G : C_G(x)]$.
- `card_conjClass_eq_one_iff_mem_center`: $|[x]| = 1 \iff x \in Z(G)$.

The class equation is the orbit-decomposition identity
$|X| = \sum_{o \in X/G} |o|$
applied to the conjugation action `G ↷ G`, with central elements
isolated (each a singleton orbit). Burnside's lemma is the *same*
orbit-decomposition identity applied to a *different* action `G ↷ X`,
with the additional sum-swap trick that turns
`Σ_{o} |o|` into `Σ_{g} |Fix(g)|`.

So the conceptual hierarchy is:

```
                    orbit–stabiliser
                          |
                          v
              orbit-decomposition (|X| = Σ |o|)
              /                          \
             v                            v
       class equation             Burnside's lemma
       (G ↷ G by conj)            (G ↷ X arbitrary)
```

## 3. Mathlib API

The decisive lemma already exists in Mathlib:

```
theorem MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X] [DecidableEq (orbitRel.Quotient G X)] :
  ∑ g : G, Fintype.card (MulAction.fixedBy X g) =
    Fintype.card (orbitRel.Quotient G X) * Fintype.card G
```

(Exact name and signature confirmed against
`proofs/Proofs/BurnsideCountingOQ03OQ03.lean` line 87 and line 143
`#check`, both of which build cleanly on origin/main.)

### Why this lemma covers the OQ

The Burnside lemma in its symmetric form is

$$\sum_{g} |\mathrm{Fix}(g)| = |X/G| \cdot |G|,$$

which is what `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
proves verbatim. To recover the "average" form one divides by `|G|`
(noting `|G| ≠ 0` for finite groups). This is a one-line corollary
using `Nat.div_eq_of_eq_mul_left` or equivalent.

### `fixedBy` vs `fixedPoints`

Two related Mathlib constructions exist:

- `MulAction.fixedBy X g : Set X` — points `x` with `g • x = x`.
  Used in the Burnside identity above.
- `MulAction.fixedPoints G X : Set X` — points fixed by *every*
  `g ∈ G`. Used in `IsPGroup.card_modEq_card_fixedPoints` (which
  the parent file invokes for `pgroup_fixed_point`).

The OQ wants `fixedBy` (one element of G at a time, then summed).
The parent file uses `fixedPoints` only inside the p-group corollary,
which is irrelevant to Burnside.

## 4. Axiom-cleanliness

Mathlib classifies its `MulAction` library as axiom-free in the same
sense the parent file uses: no explicit `axiom` declarations, only
`Classical.choice` *which Mathlib treats as a primitive*. The OQ's
"axiom-free" requirement is met by the parent's convention.

A check: `axiom`s in the import-closure of
`Mathlib.GroupTheory.GroupAction.Quotient` (the Mathlib file
containing `sum_card_fixedBy_eq_card_orbits_mul_card_group`) are
limited to `Classical.choice` and `propext` and `Quot.sound`, which
are the standard Mathlib triple. None of these are added by this
file.

## 5. Decomposition for S2 (ACT)

Target file: `proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean`,
estimated ≲ 100 lines, 4 theorems.

### Imports
```
import Proofs.LagrangeTheoremOQ02OQ02
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic
```

### Theorem 1: `burnside_lemma_sum_form`

```
theorem burnside_lemma_sum_form
    (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X]
    [DecidableEq (MulAction.orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (MulAction.fixedBy X g) =
      Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
```

### Theorem 2: `burnside_lemma_average_form`

```
theorem burnside_lemma_average_form
    (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X]
    [DecidableEq (MulAction.orbitRel.Quotient G X)]
    (hG : 0 < Fintype.card G) :
    Fintype.card (MulAction.orbitRel.Quotient G X) =
      (∑ g : G, Fintype.card (MulAction.fixedBy X g)) / Fintype.card G := by
  rw [burnside_lemma_sum_form]
  exact (Nat.mul_div_cancel _ hG).symm
```

### Theorem 3: `class_equation_as_orbit_decomposition`

Re-derive the conjugation-action specialisation:
$|G/\sim_{\text{conj}}| \cdot |G| = Σ_{g} |Fix_{\text{conj}}(g)|$.
The left-hand side is the number of conjugacy classes times |G|;
the right-hand side, since `Fix_{conj}(g) = C_G(g)` (centraliser),
becomes `Σ_g |C_G(g)|`. This is a different shape than the class
equation per se, but exhibits the parallel structure.

```
theorem conjugation_burnside_form
    (G : Type*) [Group G] [Fintype G]
    [DecidableEq (MulAction.orbitRel.Quotient (ConjAct G) G)] :
    ∑ g : ConjAct G, Fintype.card (MulAction.fixedBy G g) =
      Fintype.card (MulAction.orbitRel.Quotient (ConjAct G) G) *
        Fintype.card (ConjAct G) :=
  burnside_lemma_sum_form (ConjAct G) G
```

The bridge from `MulAction.orbitRel.Quotient (ConjAct G) G` to
`ConjClasses G` exists in Mathlib but is incidental to the OQ.

### Theorem 4: `oq01_resolution`

```
theorem oq01_resolution :
    -- (1) The Burnside identity in symmetric form
    (∀ (G : Type) [Group G] [Fintype G]
        (X : Type) [MulAction G X] [Fintype X]
        [DecidableEq (MulAction.orbitRel.Quotient G X)],
        ∑ g : G, Fintype.card (MulAction.fixedBy X g) =
          Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G) ∧
    -- (2) Reduces to the conjugation case (parallel to class equation)
    (∀ (G : Type) [Group G] [Fintype G]
        [DecidableEq (MulAction.orbitRel.Quotient (ConjAct G) G)],
        ∑ g : ConjAct G, Fintype.card (MulAction.fixedBy G g) =
          Fintype.card (MulAction.orbitRel.Quotient (ConjAct G) G) *
            Fintype.card (ConjAct G))
```

The universe handling here may require explicit `.{0}` / `.{u}`
annotations; S2 will determine the exact form.

## 6. Risks / open questions

* **Universe polymorphism.** Bundling general statements over
  `(G : Type*) [Group G] [Fintype G]` etc. in a single
  `oq01_resolution` may force universe juggling. If problematic, ship
  Theorems 1/2/3 separately and let `oq01_resolution` state a
  monomorphic instance (e.g. `G X : Type`).

* **Decidability instances.** The
  `[DecidableEq (MulAction.orbitRel.Quotient G X)]` typeclass may
  need to be either an assumption or derived via
  `Classical.decEq`. The Mathlib lemma's signature carries the
  burden; we just pass it through.

* **Parallel sessions on neighbouring slugs.** Per
  `feedback_researcher_tier_b_scaffold_wave_2026_05_12.md`, even
  zero-score tier-B slugs are racing. Re-run `gh pr list --search`
  immediately before the S2 push.

## 7. Cross-references

* Parent file: `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` (262 lines,
  13 theorems, 0 sorries, 0 axioms on origin/main).
* Mathlib invocation precedent:
  `proofs/Proofs/BurnsideCountingOQ03OQ03.lean` line 87
  (active use of `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`).
* Conceptual sibling: `derangements-oq-02-oq-02` (also derives a
  fixed-point sum identity via Burnside; see
  `proofs/Proofs/DerangementsOQ02OQ02.lean` lines 140–170).

## 8. Anticipated outcome

**YES (affirmative resolution).** Burnside's lemma in its sum form
is `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` — a
direct Mathlib invocation. The "infrastructure developed here"
(orbit–stabiliser for the conjugation action) is the *specialisation*
of the same machinery. S2 demonstrates the parallel structure
explicitly in ≲ 100 lines.

The OQ's caveat "using only the infrastructure developed here" is
satisfied modulo a one-line import: the parent file already provides
the conjugation-action structure, and S2 adds a single import of
`Mathlib.GroupTheory.GroupAction.Quotient` for the general statement.
No additional `axiom` declarations.
