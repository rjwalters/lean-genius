# Knowledge: Categorical Schroeder-Bernstein

## Historical timeline of SBP in categories

| Year | Author | Category | Verdict |
|-----:|---|---|---|
| 1898 | Bernstein (orbit proof) | $\mathbf{Set}$ | **Holds** (classical SB) |
| 1965 | Bumby | $\mathbf{Ab}$ (divisible abelian groups) | **Holds** (Bumby's theorem) |
| 1986 | Banaschewski–Brummer | "retraction condition" categories | **Holds** (sufficient) |
| 1995 | Trnková | concrete categories with limits | partial criteria |
| 1996 | Gowers | $\mathbf{Ban}$ (separable Banach spaces) | **Fails** (counter-example) |
| 2019 | Pradic–Brown | $\mathbf{Set}$ in IZF+Infinity | SBP $\Leftrightarrow$ LEM |

## The Banaschewski–Brummer sufficient condition

**Hypothesis (split-mono / retraction condition).** Every monomorphism
in $\mathcal{C}$ is a *split* monomorphism: for each mono $m : X \to Y$
there is a retract $r : Y \to X$ with $r \circ m = \mathrm{id}_X$.

**Statement.** If $\mathcal{C}$ satisfies the split-mono condition, then
$\mathcal{C}$ has SBP.

**Sketch.** Given monos $m : X \to Y, n : Y \to X$ with sections
$r_m, r_n$, the composite $n \circ m : X \to X$ is a mono with section
$r_m \circ r_n$, hence an iso (mono + split-mono = iso in any category
where mono = split-mono). Symmetric argument gives $m \circ n : Y \to Y$
an iso. From this one extracts $X \cong Y$ (e.g. via $m$ paired with
$r_m \circ (n \circ m)^{-1} \circ r_n$ — formal details deferred to S4).

## Concrete failure example (Bumby and beyond)

**Counter-example in $\mathbf{Grp}$.** Let $G_1 = \mathbb{Z}$ and
$G_2 = \mathbb{Z} \oplus (\mathbb{Z}/2\mathbb{Z})$. There are injective
group homomorphisms $G_1 \hookrightarrow G_2$ ($n \mapsto (n, 0)$) and
$G_2 \hookrightarrow G_1$ (more subtle — uses an embedding constructed
via prime indexing; existence is classical). The two groups have
different torsion subgroups so $G_1 \not\cong G_2$. **Conclusion:**
$\mathbf{Grp}$ lacks SBP.

**Gowers' Banach counter-example.** Gowers (1996) constructed a separable
Banach space $X$ with $X \not\cong X \oplus X$ but with mutual embeddings.
Stronger counter-examples (Anisca, Argyros–Haydon) exhibit infinite
incomparability towers.

## What Mathlib has and lacks

### Has

- `CategoryTheory.Category` and the full categorical bestiary
  (`Mathlib.CategoryTheory.*`).
- `CategoryTheory.Mono` / `Epi` / `SplitMono` / `SplitEpi` and the iso
  characterizations (`isIso_of_mono_of_splitEpi` etc.).
- For concrete instances:
  - `Mathlib.SetTheory.Cardinal.SchroederBernstein` — proves SB in
    `Type u` via embeddings.
  - `Mathlib.Algebra.Category.Grp.Basic` — `Grp` as a category.

### Lacks

- A definition `HasSchroederBernsteinProperty (C : Type*) [Category C]`.
- An instance `HasSchroederBernsteinProperty (Type u)`.
- A theorem `[HasSplitMonos C] → HasSchroederBernsteinProperty C`
  (the Banaschewski–Brummer sufficient condition).
- A `failure` witness (counter-example) in any non-SBP category.

## Mathematical subtleties

1. **Mono vs. injection in $\mathbf{Set}$.** A function is mono iff
   injective, so `Function.Injective f ↔ Mono (CategoryTheory.ofHom f)`
   in `Type u`. The bridge lemma exists in Mathlib but is sometimes
   re-derived.

2. **Split-mono vs. retract.** `SplitMono m` packages the retraction
   data; `Mono m + ∃ r, r ∘ m = id` is equivalent but unbundled. Mathlib
   has both styles; prefer `SplitMono` for cleaner statements.

3. **Equivalence vs. iso in `Type u`.** `Equiv α β` and `α ≅ β` (in
   `CategoryTheory.Cat` / `Type u`) are bridged via
   `Equiv.toIso` / `Iso.toEquiv`; classical SB returns an `Equiv`, the
   categorical conclusion is an `Iso`.

4. **Classical logic.** Mathlib's `SchroederBernstein` uses
   `Classical.choice`. Pradic–Brown (2019) showed SBP is constructively
   equivalent to LEM; any Mathlib SBP proof inherits classical logic.

## Related Mathlib targets

- `Mathlib.CategoryTheory.Skeletal` — skeletal categories (every iso is
  an identity) — orthogonal to SBP but a useful framing.
- `Mathlib.CategoryTheory.Subobject.Basic` — `Subobject X` as the poset
  of monos modulo iso — directly models the "$X \hookrightarrow Y$"
  side of SBP.
- `Mathlib.CategoryTheory.Limits.Shapes.Equivalence` — equivalences of
  categories preserve SBP (folklore; not stated in Mathlib).

## Open research-level questions inherited

- Does SBP for $\mathcal{C}$ imply SBP for $\mathrm{Fun}(\mathcal{D}, \mathcal{C})$?
- For which monoidal $\mathcal{C}$ does mutual $X \otimes A \cong Y$ and
  $Y \otimes B \cong X$ imply $X \cong Y$? (Open in general.)
- Is the Banaschewski–Brummer condition strictly weaker than "$\mathcal{C}$
  is a topos"? (Believed yes; no proof in literature.)

## References

- Banaschewski, B. & Brummer, G. C. L. (1986). *Thoughts on the Cantor–
  Bernstein theorem.* Quaestiones Mathematicae 9, 1–27.
- Bernstein, F. (1898). *Beitrag zur Mengenlehre.* Göttingen dissertation.
- Bumby, R. T. (1965). *Modules which are isomorphic to submodules of
  each other.* Arch. Math. 16, 184–185.
- Gowers, W. T. (1996). *A solution to the Schroeder-Bernstein problem
  for Banach spaces.* Bull. LMS 28, 297–304.
- Hinkis, A. (2013). *Proofs of the Cantor-Bernstein Theorem: A
  Mathematical Excursion.* Birkhauser/Springer.
- Pradic, C. & Brown, C. E. (2019). *Cantor–Bernstein implies Excluded
  Middle.* arXiv:1904.09193.
- Trnková, V. (1975). *On a Schroeder–Bernstein type theorem for
  concrete categories.* Comment. Math. Univ. Carolin.
