# Knowledge Base: abel-ruffini-galois-extensions-oq-04-oq-03

Zassenhaus (butterfly) lemma and Schreier refinement — an independent (non-lattice)
route to Jordan–Hölder. Neither is currently in Mathlib.

---

## Problem Understanding

Goal: formalize the Zassenhaus butterfly lemma for subgroups
```
    A(A' ∩ B') ⧸ A(A' ∩ B)  ≃*  B(B' ∩ A') ⧸ B(B' ∩ A)       (A ⊴ A', B ⊴ B')
```
and then Schreier refinement (any two subnormal series admit equivalent
refinements), giving a second proof of Jordan–Hölder logically independent of
Mathlib's abstract `JordanHolderLattice` (used by the parent oq-04).

---

## Session 2026-07-04 (Session 1) — ORIENT → ACT — build-blocked

**Mode**: FRESH.  **Outcome**: architecture fixed + statement + scaffolding written
(NOT machine-checked: Docker and Aristotle both unavailable this session).

### Key structural insight (the whole proof in one line)

Both butterfly quotients are isomorphic to a **single common middle quotient**
```
    (A' ∩ B') ⧸ D ,     D := (A ∩ B')(A' ∩ B) = (A ⊓ B') ⊔ (A' ⊓ B).
```
So the butterfly lemma = (half-diamond on the A-side)⁻¹ ∘ (bridge) ∘ (half-diamond
on the B-side).  No degree-of-freedom is lost; the entire content is the single
"half-diamond" isomorphism, run twice.

### The half-diamond is a *refined* second isomorphism theorem

`(A' ∩ B') ⧸ D  ≃*  A(A'∩B') ⧸ A(A'∩B)` is realized by the homomorphism
```
    ψ : (A' ⊓ B')  →  (A ⊔ (A'⊓B')) ⧸ (A ⊔ (A'⊓B)) ,      ψ = mk' ∘ inclusion.
```
* **Surjective**: any element of `upper = A ⊔ (A'⊓B')` is `a·h` with `a ∈ A`,
  `h ∈ A'⊓B'`; since `A ⊴ A'` and `h ∈ A' `, `h⁻¹ a h ∈ A ≤ lower`, so `mk'(a·h) =
  mk'(h) = ψ(h)`.  (Verbatim analogue of the parent's `hn_sup.conj_mem'` step.)
* **ker ψ = D**: `h ∈ (A'⊓B') ∩ lower` ⟺ `h ∈ D`.  Forward: `h = a·c` with `a∈A`,
  `c ∈ A'⊓B`; then `a = h·c⁻¹`, and `h,c ∈ A'` ⟹ `a∈A'`, while `h∈B'`, `c∈B≤B'` ⟹
  `a∈B'`; with `a∈A` this gives `a ∈ A⊓B'`, so `h = a·c ∈ (A⊓B')⊔(A'⊓B) = D`.
  Reverse: `D ≤ lower` (`D_le_lower`) and `D ≤ A'⊓B'` (`D_le_mid`).
Then `QuotientGroup.quotientKerEquivOfSurjective` closes it — exactly the mechanism
the sibling `AbelRuffiniGaloisExtensionsOQ04.second_iso` uses (there sorry-free).

### Critical discovery for tractability

The parent file `AbelRuffiniGaloisExtensionsOQ04.lean` already contains a
**fully-compiled diamond isomorphism** (`second_iso`, `(x⊔y)/x ≃* y/(x⊓y)`) built
from `mk' ∘ inclusion` + `quotientKerEquivOfSurjective` +
`normal_subgroupOf_of_le_normalizer`.  The Zassenhaus half-diamond is the *same
construction* with `x := A`, `y := A'⊓B'`, and a product denominator `D` in place
of `x⊓y`.  Only the kernel computation genuinely changes (product `D`, not a plain
`⊓`).  So the "1–2 weeks, no template" estimate in problem.md is too pessimistic:
there IS a template, and the remaining work is one kernel-membership lemma.

### What I built (proofs/Proofs/AbelRuffiniGaloisExtensionsOQ04OQ03.lean)

- `ZConfig` structure packaging `A ⊴ A'`, `B ⊴ B'`; abbreviations `upper`, `lower`,
  `mid`, `D`.
- Verified-quality scaffolding (bedrock lattice API, mirrors compiled parent):
  `lower_le_upper`, `mid_le_upper`, `inf_A_B'_le_mid`, `inf_A'_B_le_mid`,
  `D_le_mid`, `inf_A'_B_le_lower`, `inf_A_B'_le_lower`, `D_le_lower`.
- `half_diamond_iso` — statement + full proof skeleton; `sorry` on exactly two
  concrete sub-goals (`hφ_surj`, `hker`) with inline sketches above.
- `mirror` — role-swap `ZConfig`; `zassenhaus_butterfly` — assembles two
  half-diamonds; `sorry` only on the `inf_comm`/`sup_comm` `bridge`.

### Files Modified
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ04OQ03.lean` (new)
- `research/problems/abel-ruffini-galois-extensions-oq-04-oq-03/knowledge.md`

### Honest status
The **main theorem is not proved** — 3 `sorry`s remain (surjectivity, kernel,
comm-bridge). The statement and architecture are complete and the scaffolding
lemmas are bedrock-safe, but nothing was machine-checked (build blackout). Each
`sorry` is a fully-specified closed obligation, not an axiom.

### Next Steps
1. Discharge `hker`: replicate parent `second_iso`'s `ext`/`mem_subgroupOf`/
   `Subgroup.mem_sup` pattern; forward direction needs the `a = h·c⁻¹ ∈ A⊓B'`
   membership computation.
2. Discharge `hφ_surj`: `q.inductionOn'` + `Subgroup.mem_sup.mp` + conjugation
   `hAn.conj_mem'` to absorb the `A`-part (copy parent lines 192–202).
3. Discharge `bridge`: `mirror.mid = B'⊓A' = A'⊓B'` and `mirror.D = (B⊓A')⊔(B'⊓A)
   = (A⊓B')⊔(A'⊓B)` via `inf_comm`/`sup_comm`; transport quotient with
   `QuotientGroup.quotientMulEquivOfEq` — or restate `mirror` so the two middle
   quotients are definitionally equal.
4. Provide the four `Normal` instances as lemmas (products of relatively-normal
   subgroups are normal in `A'⊓B'`) so the theorems can drop those hypotheses.
5. Then Schreier refinement: Zassenhaus is the inductive step interleaving two
   subnormal series; the multiset-of-factors equivalence is the separate effort.
6. Submit the whole file to Aristotle once the 404 blackout lifts — it is now
   KNOWN math with an explicit skeleton, a strong Aristotle candidate.

---

## Dead Ends / Cautions
- `A(A'∩B')` is a subgroup **only because** `A ⊴ A'` normalizes `A'⊓B' ≤ A'`; do
  not treat set-product `A * (A'∩B')` generically — always use the join `⊔`.
- Building `ψ` *out of* the product `upper` is awkward; build it *into* the
  quotient *from* the clean subgroup `mid = A'⊓B'` (as the parent does from `y`).
