import Mathlib.Tactic

/-
  Property B — *independent* recoloring cannot beat Erdős's 2^(k-1).

  Open question (property-b-first-moment-oq-03): sharpen Erdős's 1963 bound
  m(k) ≥ 2^(k-1) to the Radhakrishnan–Srinivasan m(k) = Ω(2^k·√(k/log k)) via the
  "asymmetric / recoloring" refinement of the first moment argument.

  The OQ names two ingredients — *asymmetry* of the random coloring and a *recoloring*
  repair step. The sibling `PropertyBFirstMomentAsymmetric.lean`
  (`property-b-first-moment-oq-03-oq-01`) settled asymmetry *negatively*. This file
  isolates the recoloring ingredient and shows that, in the **independent** product model,
  it too is worthless — pinning the entire Radhakrishnan–Srinivasan gain on the *conditional,
  order-dependent* structure of the true recoloring step.

  Setup. After the uniform first round, suppose every vertex is, independently, *recolored*
  by flipping its colour with probability `p` (the naive product-space recoloring). The final
  colour of each vertex is `c XOR f`, where `c` is the uniform first-round colour and `f` is
  an independent Bernoulli(`p`) flip. Then for a *fixed* vertex and a *fixed* target colour,

      vertexFinalProb p = (1/2)(1 - p) + (1/2)·p  =  1/2,

  independently of `p`: XOR-ing a uniform bit with anything independent stays uniform. By
  independence across the `k` vertices of an edge, the edge is monochromatic with probability

      monoIndep k p = 2 · (vertexFinalProb p)^k = 2 · (1/2)^k = 2^(1-k),

  again independent of `p` — exactly the one-round Erdős value `monoOneStage k`.

  Results (all over the real first-moment model, 0 axioms):

    • `vertexFinalProb_eq_half`     : the per-vertex final colour stays uniform for every `p`.
    • `monoIndep_eq_oneStage`       : `monoIndep k p = monoOneStage k = 2^(1-k)` for ALL `p`.
    • `monoIndep_const`             : `monoIndep` is constant in `p` — no flip rate helps.
    • `expMono_indep_const`         : the expected number of monochromatic edges
                                      `m · monoIndep k p` is independent of `p`.
    • `threshold_indep`             : the first-moment threshold is *unchanged* by independent
                                      recoloring — `m · monoIndep k p < 1 ↔ 2·m < 2^k`,
                                      i.e. exactly Erdős's `m < 2^(k-1)`.

  Conclusion. Independent (product-space) recoloring leaves the first-moment monochromatic
  probability *exactly* invariant, so — like asymmetry — it cannot move Erdős's `2^(k-1)`
  threshold at all. The Radhakrishnan–Srinivasan improvement therefore depends essentially on
  recoloring only the vertices of *dangerous* edges, in a *fixed order* (a conditional, non-
  product probability model). This is a structural ORIENT result for oq-03 that converts the
  knowledge-base remark "the recoloring step is NOT expressible by summing over a single
  product sample space `V → Bool`" into a theorem, and sharply scopes the remaining moonshot.

  Companion to `PropertyBFirstMoment.lean` (Erdős 1963) and the sibling
  `PropertyBFirstMomentAsymmetric.lean` (asymmetry is worthless).
-/

namespace ProbMethod.PropertyB.IndepRecoloring

/-- Per-vertex final-colour probability after independent two-stage recoloring: the first
round colours the vertex uniformly, the second flips it with probability `p`. The probability
that the final colour equals a fixed target is `(1/2)(1 - p) + (1/2)·p`. -/
noncomputable def vertexFinalProb (p : ℝ) : ℝ := (1 / 2) * (1 - p) + (1 / 2) * p

/-- Monochromatic probability of a `k`-edge under the **independent** two-stage recoloring
model: the `k` vertices are flipped independently with probability `p`, so by independence the
edge is monochromatic (in either colour) with probability `2 · (vertexFinalProb p)^k`. -/
noncomputable def monoIndep (k : ℕ) (p : ℝ) : ℝ := 2 * (vertexFinalProb p) ^ k

/-- The one-round (Erdős) monochromatic probability of a `k`-edge: `2 · (1/2)^k = 2^(1-k)`. -/
noncomputable def monoOneStage (k : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ k

/-- **The per-vertex final colour stays uniform.** XOR-ing a uniform first-round colour with an
independent Bernoulli flip leaves the colour uniform, for every flip probability `p`. -/
@[simp]
theorem vertexFinalProb_eq_half (p : ℝ) : vertexFinalProb p = 1 / 2 := by
  unfold vertexFinalProb; ring

/-- **Independent recoloring is worthless.** For every flip probability `p` and every edge size
`k`, the independent two-stage model gives *exactly* the one-round monochromatic probability
`monoIndep k p = monoOneStage k = 2^(1-k)`. No `p` lowers the first-moment monochromatic
probability. -/
theorem monoIndep_eq_oneStage (k : ℕ) (p : ℝ) : monoIndep k p = monoOneStage k := by
  unfold monoIndep monoOneStage
  rw [vertexFinalProb_eq_half]

/-- The closed form `monoOneStage k = 2^(1-k)` as a real zpow, exhibiting the Erdős value. -/
theorem monoOneStage_eq_zpow (k : ℕ) : monoOneStage k = (2 : ℝ) ^ (1 - (k : ℤ)) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  unfold monoOneStage
  rw [one_div, inv_pow, sub_eq_add_neg, zpow_add₀ h2, zpow_one, zpow_neg, zpow_natCast]

/-- **Recoloring is constant in the flip rate.** `monoIndep k p` does not depend on `p`. -/
theorem monoIndep_const (k : ℕ) (p q : ℝ) : monoIndep k p = monoIndep k q := by
  rw [monoIndep_eq_oneStage, monoIndep_eq_oneStage]

/-- The expected number of monochromatic edges of an `m`-edge `k`-uniform hypergraph under the
independent recoloring model, `m · monoIndep k p`, is independent of the flip rate `p`. -/
theorem expMono_indep_const (m k : ℕ) (p q : ℝ) :
    (m : ℝ) * monoIndep k p = (m : ℝ) * monoIndep k q := by
  rw [monoIndep_const k p q]

/-- **The threshold is unmoved.** The first-moment criterion under independent recoloring,
`m · monoIndep k p < 1`, is equivalent to `2·m < 2^k`, i.e. exactly Erdős's `m < 2^(k-1)`. So no
choice of flip rate `p` raises the threshold above `2^(k-1)`. -/
theorem threshold_indep (m k : ℕ) (p : ℝ) :
    (m : ℝ) * monoIndep k p < 1 ↔ 2 * (m : ℝ) < 2 ^ k := by
  rw [monoIndep_eq_oneStage]
  unfold monoOneStage
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [show (2 * (1 / 2 : ℝ) ^ k) = 2 / 2 ^ k by rw [one_div, inv_pow]; ring,
    ← mul_div_assoc, div_lt_one hpos]
  constructor <;> intro h <;> linarith

end ProbMethod.PropertyB.IndepRecoloring
