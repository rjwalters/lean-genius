# Knowledge: sperner-ndim-mathlib-oq-03

**Open question** (from `sperner-ndim-mathlib`): *Generalize to the Borsuk–Ulam
theorem: does the abstract cell complex framework extend to antipodal colorings?*

## Established Facts

- The combinatorial shadow of **Borsuk–Ulam** is **Tucker's lemma** (Tucker 1946):
  an antipodally symmetric triangulation of `Bⁿ`, labelled `{±1,…,±n}`
  antisymmetrically on the boundary sphere, has a *complementary edge* (endpoints
  `+k`, `−k`). Tucker : Borsuk–Ulam :: Sperner : Brouwer.
- The reusable core of the parent framework is the parity engine
  `even_card_fpf_invol` (fixed-point-free involution ⟹ even cardinality) feeding
  `sperner_parity` (panchromatic count ≡ boundary door count mod 2).
- **1-D Tucker is fully provable from the same parity philosophy, 0 axioms.**
  `signChanges_odd_iff`: the number of sign-change edges along a path `0—1—…—n`
  is odd iff the endpoints disagree (a discrete fundamental theorem of calculus
  mod 2). This is the Tucker analogue of `sperner_parity`. Antipodal boundary
  (`g 0 = ! g n`) forces an odd, hence nonzero, complementary-edge count.

## Failed Approaches

(None — the 1-D case went through directly via the parity engine.)

## Promising Leads

- **AntipodalCellComplex refinement**: extend `CellComplex` with a free
  ℤ/2-action `α : Simplex → Simplex` (`α∘α = id`) compatible with `vertices`/`adj`,
  plus an antisymmetric boundary labelling. The engine `even_card_fpf_invol`
  should then yield an n-dim Tucker parity theorem. The missing datum is the
  *equivariant boundary bookkeeping*, NOT the involution machinery.
- **2-D Tucker** via the Freund–Todd 'special simplices' constructive path is the
  natural first higher-dimensional test.
- **Discrete ⟹ continuous Borsuk–Ulam** by subdivision limit, mirroring
  `sperner-ndim-mathlib-oq-02` (Sperner ⟹ Brouwer).

## Session Log

### Session 2026-06-25 (Session 1, researcher-4) — 1-D Tucker / antipodal parity engine

**Mode**: FRESH | **Outcome**: progress (base case completed, 0 axioms)

**What I Did**
- Translated the prose OQ into a precise Lean target: Tucker's lemma (combinatorial
  Borsuk–Ulam), base case `n = 1`.
- Built `proofs/Proofs/SpernerNDimMathlibOQ03.lean` (156 lines, 0 sorries, 0 axioms;
  `#print axioms` = propext/Classical.choice/Quot.sound only):
  `signChanges`, `signChanges_succ`, `signChanges_odd_iff` (parity engine),
  `complementary_edges_odd`, `tucker_one_dim`, `tucker_one_dim_antipodal`,
  `tucker_one_dim_int` ({±1}-integer phrasing).
- Authored gallery entry `src/data/proofs/sperner-ndim-mathlib-oq-03/`
  (meta.json + annotations.json), status `verified`, badge `original`.

**Key Findings**
- In dimension one the interior door-pairing involution degenerates; the entire
  parity is the boundary endpoint mismatch (telescoping mod 2).
- The structural obstruction for higher dimensions is the absence of an antipodal
  involution on the boundary subcomplex in the current `CellComplex` — a precise,
  actionable next step rather than a vague "harder".

**Files Modified**
- `proofs/Proofs/SpernerNDimMathlibOQ03.lean` (new)
- `src/data/proofs/sperner-ndim-mathlib-oq-03/{meta,annotations}.json` (new)

**Next Steps**
- Define `AntipodalCellComplex` and attempt the n-dim Tucker parity theorem.
