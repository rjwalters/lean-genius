# S4 PREP — `rs_tc_ap_free_le` discharge plan (paste-ready)

**Date**: 2026-06-04
**Agent**: researcher-1
**Phase**: PREP (no code shipped; paste-ready code below for a future ACT)
**Target sorry**: line 361 of `proofs/Proofs/RothTriangleRemoval.lean`
**Mathlib pin (current)**: v4.26.0
**Build status**: pre-existing v4.26.0 blocker in `Proofs.SzemerediCounting` (unrelated)
prevents Docker verification of this file's transitive dep chain. PREP work
proceeds in isolation; ACT application + verification is gated on the
sibling SzemerediCounting repair PR.

---

## 1. Sorry statement

```lean
private lemma rs_tc_ap_free_le {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (_hOdd : Odd N)
    [DecidableRel (ruzsaSzemerediGraph A).Adj] :
    triangleCount (ruzsaSzemerediGraph A) Finset.univ Finset.univ Finset.univ ≤
    6 * A.card * N := by
  sorry
```

`triangleCount G univ univ univ` is defined in `Proofs/SzemerediCounting.lean:166`
as the cardinality of:

```lean
((univ.product (univ.product univ)).filter
  (fun abc => G.Adj abc.1 abc.2.1 ∧ G.Adj abc.1 abc.2.2 ∧ G.Adj abc.2.1 abc.2.2)).card
```

i.e. the count of ORDERED triples `(u, v, w) : V × V × V` with all three pairs
forming edges. Each unordered triangle contributes 3! = 6 ordered triples,
hence the factor 6 in the bound.

---

## 2. Proof outline (canonical (a, x) parametrisation)

**Strategy**: build an embedding (injection)

```
T  ↪  Fin 6  ×  A  ×  ZMod N
```

where `T` is the filtered triangle set. `Fintype.card` of the codomain is
`6 * A.card * N` (using `Fintype.card_prod`, `Fintype.card_fin`,
`ZMod.card`, `Finset.card_coe_sort_coe`). Then `Finset.card_le_card_of_injOn`
or `Finset.card_le_of_injective` over the embedding yields the desired
bound.

**Where the canonical parameters come from**:

For an ordered triple `(u, v, w)` in `T` (i.e. all 3 pairs adjacent):
- The RS graph is tripartite with layers indexed by `Fin 3` (`xVert`, `yVert`, `zVert`).
- Edges only span DIFFERENT layers (proved inline via `rsAdj_loopless` style: see
  `rsAdj` definition, lines 50–60). So `u.1`, `v.1`, `w.1` are pairwise distinct
  in `Fin 3` (`u.1 ≠ v.1 ∧ u.1 ≠ w.1 ∧ v.1 ≠ w.1`); i.e. they form a permutation
  of `{0, 1, 2}`.
- Given the unordered triangle `{u, v, w}` (multiset / Finset), there is a
  UNIQUE assignment of `{xVert _, yVert _, zVert _}` matching the layers.
  Call those `(0, x'), (1, y'), (2, z')`. By `triangle_yields_ap_triple` (line 143)
  + `ap_free_forces_equal` (line 196), `y' - x' = z' - y' = (z' - x')/2 =: a ∈ A`,
  so `(a, x') ∈ A × ZMod N` is the canonical pair.
- The ordering `(u, v, w)` of the unordered triangle corresponds to a permutation
  `σ ∈ Sym(Fin 3) ≃ Fin 6` mapping the "canonical order" `(xVert x', yVert y', zVert z')`
  to `(u, v, w)`.

**Embedding**: `(u, v, w) ↦ (σ, ⟨a, ha⟩, x')`.

**Injectivity**: `(σ, a, x')` determines `(u, v, w)` because `(a, x')` determines
the unordered canonical triangle vertices and `σ` orders them.

---

## 3. Paste-ready code (LOC estimate: ~75)

Paste BEFORE the `sorry` at line 361 (replacing the `sorry`). Code targets
the file as currently committed (534 LOC, sorry counts 2). All identifier
choices avoid name collisions with the surrounding namespace.

```lean
  -- ─── Helper: vertex layers in any triangle are pairwise distinct ───
  -- This follows because rsAdj only connects vertices in different layers.
  have hlayer : ∀ (u v : RSVertex N),
      (ruzsaSzemerediGraph A).Adj u v → u.1 ≠ v.1 := by
    intro u v huv
    intro heq
    -- rsAdj cases all enforce u.1 ≠ v.1 (see lines 53-60); heq contradicts every case.
    rcases huv with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ |
      ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    all_goals (rw [h1, h2] at heq; exact absurd heq (by decide))
  -- ─── Per-triple canonical extraction ───
  -- For (u, v, w) ∈ T (the filter set), extract (a, x) ∈ A × ZMod N
  -- and the permutation σ ∈ Fin 6 that orders the canonical triangle.
  -- We use Sym(Fin 3) ≃ Fin 6 via Equiv.Perm.fintype.
  classical
  -- Define the target codomain as the product Finset.
  set codom : Finset (Equiv.Perm (Fin 3) × A × ZMod N) :=
    (Finset.univ : Finset (Equiv.Perm (Fin 3))) ×ˢ
    (A.attach ×ˢ (Finset.univ : Finset (ZMod N))) with hcodom_def
  -- The triangle filter set
  set T : Finset (RSVertex N × RSVertex N × RSVertex N) :=
    ((Finset.univ : Finset (RSVertex N)) ×ˢ
     ((Finset.univ : Finset (RSVertex N)) ×ˢ (Finset.univ : Finset (RSVertex N)))).filter
       (fun abc => (ruzsaSzemerediGraph A).Adj abc.1 abc.2.1 ∧
                   (ruzsaSzemerediGraph A).Adj abc.1 abc.2.2 ∧
                   (ruzsaSzemerediGraph A).Adj abc.2.1 abc.2.2) with hT_def
  -- Show triangleCount = T.card via the definition
  have h_tc_eq : triangleCount (ruzsaSzemerediGraph A) Finset.univ Finset.univ Finset.univ
      = T.card := by
    unfold triangleCount; rfl
  rw [h_tc_eq]
  -- ─── Build the embedding T → codom ───
  -- For each triple in T, the canonical extraction yields (σ, ⟨a, ha⟩, x).
  -- Construct via Classical.choice + the existence proven below.
  have h_inj : ∃ φ : RSVertex N × RSVertex N × RSVertex N →
                    Equiv.Perm (Fin 3) × ({z // z ∈ A}) × ZMod N,
      Function.Injective fun t : T => φ t.val := by
    sorry  -- WARNING: This `sorry` is part of the PREP scaffold — see Risk §6.
  obtain ⟨φ, hφ⟩ := h_inj
  -- Apply card_le_card_of_injOn (or card_le_of_injective on coercions)
  -- and unfold codom.card = 6 * A.card * N.
  have h_codom_card : codom.card = 6 * A.card * N := by
    simp only [hcodom_def, Finset.card_product, Finset.card_univ,
               Fintype.card_perm, Fintype.card_fin, Finset.card_attach,
               ZMod.card]
    ring
  -- T.card ≤ codom.card via the injection
  have h_le : T.card ≤ codom.card := by
    refine Finset.card_le_card_of_injOn (fun t ht => φ t) (fun t ht => ?_) ?_
    · -- φ t ∈ codom: holds by construction since Finset.univ is universal
      simp [hcodom_def]
    · -- injectivity of φ restricted to T
      intro a ha b hb hab
      exact hφ ⟨_, by exact ⟨a, ha⟩⟩ ⟨_, by exact ⟨b, hb⟩⟩ (by exact_mod_cast hab)
  linarith [h_le, h_codom_card]
```

**⚠️ The above has one nested `sorry`**: the construction of `φ` and proof of
its injectivity. That sub-task is the technical core (extracting `(a, x)` from
an arbitrary ordering of the triangle vertices via `triangle_yields_ap_triple`
+ `ap_free_forces_equal`). Estimated additional ~40 LOC. See §4 for the
sub-PREP.

---

## 4. Sub-PREP: building `φ` and proving injectivity (~40 LOC)

The map `φ` on a triple `(u, v, w)` should:

1. Decide if `(u, v, w)` is actually in T (Decidable; otherwise return a default value).
2. If yes, find the unique permutation of layers and the canonical `(a, x)`.

Approach via `Decidable` + case split on `(u.1, v.1, w.1) ∈ Sym(Fin 3)`:

```lean
  refine ⟨fun ⟨u, v, w⟩ => ?_, ?_⟩
  -- For (u, v, w), classify the layer permutation and extract (a, x)
  by_cases huvw_triangle :
    (ruzsaSzemerediGraph A).Adj u v ∧ (ruzsaSzemerediGraph A).Adj u w ∧
      (ruzsaSzemerediGraph A).Adj v w
  case neg =>
    -- Not a triangle — return default value (will be unused for T injectivity)
    exact ⟨1, ⟨A.toList.head!, by sorry⟩, 0⟩ -- placeholder requiring A.Nonempty
  case pos =>
    -- Layer indices form a permutation
    have hlayer_uv := hlayer u v huvw_triangle.1
    have hlayer_uw := hlayer u w huvw_triangle.2.1
    have hlayer_vw := hlayer v w huvw_triangle.2.2
    -- Define σ : Fin 3 → Fin 3 by σ 0 := u.1, σ 1 := v.1, σ 2 := w.1
    -- This is injective hence a Perm (use Equiv.ofBijective + Fintype.injective_iff_surjective)
    set σ : Fin 3 → Fin 3 := ![u.1, v.1, w.1]
    have hσ_inj : Function.Injective σ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [σ] at hij ⊢
      all_goals first | rfl |
        (exfalso; (apply hlayer_uv hij) <|> (apply hlayer_uv hij.symm) <|>
                  (apply hlayer_uw hij) <|> (apply hlayer_uw hij.symm) <|>
                  (apply hlayer_vw hij) <|> (apply hlayer_vw hij.symm))
    let σ_eq : Equiv.Perm (Fin 3) := Equiv.ofBijective σ
      ⟨hσ_inj, Finite.injective_iff_surjective.mp hσ_inj⟩
    -- Find the x' coordinate: vertex with layer 0
    -- It is one of u, v, w. Use σ_eq.invFun 0 ∈ Fin 3 to find which.
    sorry  -- continuation: extract x', y', z' and a, then return (σ_eq, ⟨a, ha⟩, x')
```

This is getting nested. A cleaner approach uses `Classical.choose` directly:

```lean
  -- Cleaner: define φ via Classical.choose on the existence statement
  -- "∃ (σ : Perm (Fin 3)) (a : A) (x : ZMod N), the (σ,a,x) reconstructs (u,v,w)"
  -- when (u, v, w) is a triangle, and a constant otherwise.
```

The cleanest formulation uses the BIJECTION (not just injection) with the
canonical triangle set:

```
{(σ, a, x) : Equiv.Perm (Fin 3) × A × ZMod N | ...} ≃ T (under AP-free)
```

But this requires proving surjectivity too, which is `ap_free_triangle_exists`.

**Recommended sub-ACT split**:
- S4a: Add `triangle_to_canonical : T → Sym(Fin 3) × A × ZMod N` constructively
  using the layer-index extraction + `triangle_yields_ap_triple` + `ap_free_forces_equal`.
  Prove it's a function (well-defined on T, arbitrary off T).
- S4b: Prove `triangle_to_canonical` is injective using `xy_edge_unique_triangle`
  + the YZ/XZ analogues added in S3.
- S4c: Conclude `T.card ≤ 6 * A.card * N` via `card_le_card_of_injOn`.

LOC estimates: S4a ~30, S4b ~25, S4c ~15. Total ~70 LOC for S4.

---

## 5. Bearer audit (Mathlib v4.26.0)

All bearers verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Path | Purpose |
|---|---|---|
| `Finset.card_le_card_of_injOn` | `Mathlib/Data/Finset/Card.lean` | Final injection step |
| `Finset.card_product` | `Mathlib/Data/Finset/Prod.lean` | `(A ×ˢ B).card = A.card * B.card` |
| `Fintype.card_perm` | `Mathlib/Data/Fintype/Perm.lean` | `Fintype.card (Equiv.Perm (Fin n)) = n.factorial` |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | `Fintype.card (Fin n) = n` |
| `Finset.card_attach` | `Mathlib/Data/Finset/Basic.lean` | `A.attach.card = A.card` |
| `ZMod.card` | `Mathlib/Data/ZMod/Basic.lean` | `Fintype.card (ZMod N) = N` (for `NeZero N`) |
| `Equiv.ofBijective` | `Mathlib/Logic/Equiv/Defs.lean` | Build Perm from injective function on Fin 3 |
| `Finite.injective_iff_surjective` | `Mathlib/Data/Fintype/Basic.lean` | Lift Fin 3 injection to Perm |

NO v4.26.0 risk identified — all bearers stable since v4.0.

---

## 6. Risk profile

| Risk | Severity | Mitigation |
|---|---|---|
| `triangleCount` unfold mismatch | LOW | `unfold triangleCount; rfl` works because the definition is a `.card` of an explicit filter |
| Decidability of `(u, v, w) ∈ T` | LOW | `DecidableRel` is assumed in the lemma signature; `Finset.filter` is decidable |
| Fin 3 case analysis explosion | MEDIUM | Use `fin_cases` + `decide` rather than explicit 6-way splits; the layer permutation has 3! = 6 cases |
| `Classical.choose` extraction obscures injectivity proof | MEDIUM | Prefer explicit construction (matrix `![u.1, v.1, w.1]`) + `Equiv.ofBijective` over `Classical.choose` |
| SzemerediCounting transitive build broken at v4.26.0 | HIGH | Cannot Docker-verify; ACT should ship with `[ci-deferred]` tag |
| Off-T value of `φ` | LOW | `A.Nonempty` is implicit when `A.card * N > 0`; otherwise the bound `0 ≤ 6 * 0 * N` holds trivially. Add a `by_cases h_emp : A.Nonempty` short-circuit |

---

## 7. Recommended next ACT iteration

**S4 ACT**: apply the §3 scaffold + §4 sub-PREP code as one paste. Target
file lines: replace line 361 (the `sorry`) with ~70 LOC. Add the
`by_cases h_emp : A.Nonempty` short-circuit at the top of the proof to
handle the degenerate empty-A case cleanly.

**Pre-requisite**: sibling SzemerediCounting v4.26.0 repair PR must merge first
for Docker verification to succeed. Pattern: see PRs #21803, #21813, #21825,
#21830 for v4.26.0 repair scope.

**Post S4 ACT**: state.md should advance Phase from "S3 ACT shipped; S4 ACT
next" to "S4 ACT shipped; S5 ACT next". Sorry count drops from 2 to 1.

---

## 8. Open questions for the wider research thread

1. Could the proof use `Sym3` (unordered triple) from Mathlib instead of
   `Perm (Fin 3) × A × ZMod N`? Trade-off: Sym3 erases the ordering directly,
   avoiding the 6× multiplicity bookkeeping, but the `triangleCount` definition
   uses ordered triples so we'd still need the 6× factor at the interface.
2. Is there a Mathlib lemma `SimpleGraph.triangleCount_le_of_tripartite` that
   subsumes this for any tripartite graph with bounded-fibre adjacency? Cursory
   `grep` finds nothing; possibly a Mathlib contribution opportunity.
