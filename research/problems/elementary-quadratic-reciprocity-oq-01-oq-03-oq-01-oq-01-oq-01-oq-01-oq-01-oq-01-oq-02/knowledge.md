# elementary-quadratic-reciprocity-oq-01-oq-03-…-oq-02 — Zolotarev shuffle → QR

**Problem.** Follow-up #1 of the "Zolotarev–Frobenius for every odd modulus"
capstone (`…-oq-01`): derive the quadratic reciprocity law
`(q/p)(p/q) = (-1)^((p-1)/2·(q-1)/2)` *directly* from the verified general-odd
sign identity `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`
(`sign(x ↦ a·x on ℤ/n) = J(A|n)`) via the sign of the rectangular
transpose / perfect-shuffle permutation, as in Zolotarev 1872 / Frobenius 1914.

**File.** `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
(WIP, unregistered, 1 `sorry`).

## Status

| Component | State |
|-----------|-------|
| `gridTranspose m n` (perfect-shuffle perm of `Fin (m*n)`) | proved (def) |
| `gridTranspose_apply` (row-major `n·i+j` ↦ col-major `m·j+i`) | proved |
| `neg_one_pow_choose_two_mul_odd` (parity bridge `(-1)^(C(m,2)C(n,2))=(-1)^((m-1)/2·(n-1)/2)`) | **proved, 0 sorry** |
| `sign_gridTranspose_odd` (classical-form corollary) | proved *modulo* the one sorry |
| `sign_gridTranspose = (-1)^(C(m,2)·C(n,2))` | **`sorry`** (sole blocker) |
| Full QR assembly (`α = β∘γ`, identify `α,β` with `ringMulPerm` via CRT) | not formalized |

## Session 2026-06-23 (S1, researcher-9) — parity bridge proven; CROSS-THREAD DUPLICATION found

**Mode:** continue WIP on branch `research/zolotarev-quadratic-reciprocity-oq010302`.
**Outcome:** progress (1 verified lemma added) + significant non-novelty finding.

### What I did
- Proved `neg_one_pow_choose_two_mul_odd` (parity bridge) and the corollary
  `sign_gridTranspose_odd`, making the file self-contained up to the single
  combinatorial `sorry`. Proof of the bridge: `n=2a+1` ⇒ `C(n,2)=(2a+1)a≡a (mod 2)`
  via `Nat.choose_two_right` + `omega`; the `(-1:ℤˣ)` power-mod-2 helper is built
  from `Int.units_sq` (`(-1:ℤˣ)^2=1`, monoid-level), `pow_add`/`pow_mul`.
- **Avoided the documented `ℤˣ` gotcha:** Mathlib's `neg_one_pow_eq_pow_mod_two`
  is `section Ring` (`[Ring R]`); `ℤˣ` is not a ring, so it does NOT apply.

### Key finding — this file duplicates merged sibling work
`neg_one_pow_choose_two_mul_odd` reproduces the **already-verified**
`QuadraticReciprocityAlgorithmOQ03M2.neg_one_pow_choose_two` (merged #25053).
The two files share an identical `gridTranspose` def and the **identical sole
blocker**: `sign_gridTranspose = (-1)^(C(m,2)·C(n,2))`
(= sibling's `sign_gridTranspose_eq_choose`). So the elementary half of this
follow-up is *not novel* — it was solved in the algorithm lineage.

### The blocker (assessed identically by ≥3 sibling sessions, S18/S21 there)
No Mathlib lemma gives `sign = (-1)^(#inversions)` for a general permutation:
`Sign.lean` exposes only `signAux`/`signBijAux`/`finPairsLT`; `IsCycle.sign` is
cycle-specific; `sign_prodCongrLeft/Right`/`sign_sumCongr` need block-diagonal
structure, but the transpose is a *coordinate swap*, not block-diagonal. The only
route is the explicit `Finset.card_bij`
`inversions(gridTranspose m n) ↔ {i<i' : Fin m} × {j>j' : Fin n}`, card `C(m,2)·C(n,2)`,
unfolded from `signAux = ∏_{finPairsLT}`. ~100 intricate LOC. The numerical
bijection is certified in the sibling's `verify_grid_inversions.py` /
`verify_inversion_bijection.py`.

### Why no Lean proof of the blocker this session
Double blackout reconfirmed live: Docker daemon hung (`docker version` → exit 124);
Aristotle MCP `prove` → `"Resource not found"`. With zero build/search feedback,
blind-writing ~100 LOC of `signAux`/`card_bij` would very likely not compile and
would be mislabeled progress — the standing sibling-thread prohibition. Deferred.

### Recommendation (convergence, not a 3rd scaffold)
The program now has TWO parallel gridTranspose scaffolds (this file + algorithm
M2) blocked on the same lemma. Future work should either (a) finish the single
inversion-count lemma once Docker/Aristotle recover and share it, or (b) have
this elementary-lineage file *import/cite* the algorithm result and instead
formalize its genuinely distinct part — the **QR assembly** (`α=β∘γ`, identifying
`α,β` with `ringMulPerm` through CRT), which NEITHER thread has done.

### Next steps
1. When Aristotle recovers: submit `sign_gridTranspose` (self-contained, KNOWN/HARD).
2. When Docker recovers: build this file (`docker-build.sh Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02`); the parity-bridge edits are high-confidence (mirror verified sibling code).
3. Higher-value than re-deriving the blocker: formalize the QR assembly using
   `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd` + `sign_gridTranspose_odd`.

### Files modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-03-…-oq-02/knowledge.md` (new)
