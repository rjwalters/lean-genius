# lagrange-theorem-oq-02-oq-02-oq-01: Burnside's Lemma via the Class Equation

## Source

Open question OQ-01 of `lagrange-theorem-oq-02-oq-02` ("The Class
Equation for Finite Groups"). The parent file
`proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` proves the class equation

  |G| = |Z(G)| + Σ_{[x] non-central} [G : C_G(x)]

and identifies it as a *specialisation* of orbit–stabiliser to the
conjugation action.

## Question (verbatim)

> Can the class equation be used to formally prove the Burnside lemma
> (number of orbits = average number of fixed points) in Lean 4 using
> only the infrastructure developed here?

## Plain-language restatement

The parent file's "infrastructure" consists of:

1. The class equation itself (`class_equation`,
   `class_equation_symm`).
2. The bridge `card_conjClass_eq_centralizer_index` between conjugacy
   class size and the index of the centraliser — i.e.
   orbit–stabiliser specialised to conjugation.
3. The centre-vs-singleton-orbit equivalence
   `card_conjClass_eq_one_iff_mem_center`.
4. Standard `MulAction` / `ConjAct` glue (`conj_orbit_eq_carrier`,
   `conj_stabilizer_eq_centralizer`).
5. p-group corollaries (irrelevant to Burnside; included only for
   downstream applications).

The Burnside lemma (a.k.a. Cauchy–Frobenius lemma) states: for any
finite group G acting on any finite set X,

  |X/G| · |G| = Σ_{g ∈ G} |Fix(g)|

equivalently |X/G| = (1/|G|) Σ_{g} |Fix(g)|, *the* "number of orbits
= average number of fixed points" identity.

The OQ asks whether the *technique* used to derive the class equation
— orbit–stabiliser applied to a specific action — can be re-applied
to derive Burnside's lemma for an *arbitrary* action. The answer is
expected to be YES on conceptual grounds: the class equation is
exactly the orbit-decomposition identity `|X| = Σ_{orbits o} |o|` for
the *conjugation* action of G on G, and the same orbit-decomposition
identity for an *arbitrary* action `G ↷ X` is precisely Burnside.

The formal question is which Mathlib lemma carries the load, and
whether the result lands `axiom`-free with zero `sorry`s.

## Target Lean theorems

In a new file `proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean`:

1. `burnside_lemma_sum_form` —
   For a finite group `G` acting on a finite type `X`,
   `Σ_{g : G} |Fix(g)| = |X/G| · |G|`.
   Anticipated proof: `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`.

2. `burnside_lemma_average_form` —
   Re-stated with `|G| ≠ 0` and a `/ |G|` cast: gives the textbook
   form. Anticipated proof: `Nat.div_eq_of_eq_mul_left` on (1).

3. `class_equation_as_orbit_decomposition` —
   Reconstruct the class equation from orbit-decomposition for the
   conjugation action, *without* invoking
   `Group.nat_card_center_add_sum_card_noncenter_eq_card` directly.
   The intent is to make the conceptual parallel explicit: class
   equation = Burnside's premise (orbit decomposition) for a
   specific action.

4. `oq01_resolution` —
   Bundle theorem affirmatively answering the OQ.

## Significance

The OQ is genuinely Mathlib-API-bound:
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` is in
Mathlib (already invoked in `proofs/Proofs/BurnsideCountingOQ03OQ03.lean`,
line 87), so the scaffolding is fully discharged before the writer
even begins.

The conceptual content is the *connection*: Burnside and the class
equation are the same theorem (orbit-decomposition counting) applied
to two different actions. Articulating this in Lean produces a small
amount of new formal content (≲ 100 lines) and clarifies the
gallery's organisation of the orbit/class story.

## Decomposition

| Step | Deliverable | Cost | Risk |
|------|-------------|------|------|
| S1   | OBSERVE: this scaffold + JSON registry | LOW | LOW |
| S2   | ACT: write `LagrangeTheoremOQ02OQ02OQ01.lean` (~100 lines, 4 theorems) | MEDIUM | LOW — Mathlib API confirmed via cross-reference |
| S3   | POLISH: gallery `meta.json` + `annotations.json` + `index.ts` | LOW | LOW |
| S4   | (optional) audit / Docker build verification | MEDIUM | LOW |

## Cross-references

- Parent: `cantors-theorem-oq-01-oq-03` style (Mathlib-API-bound, low-risk SCAFFOLD pattern).
- Sibling: `lagrange-theorem-oq-02-oq-02-oq-01` has no sibling (oq-02-oq-02 has only one
  sub-OQ).
- Mathlib API in active use: `proofs/Proofs/BurnsideCountingOQ03OQ03.lean` line 87,
  which already builds cleanly on origin/main.
