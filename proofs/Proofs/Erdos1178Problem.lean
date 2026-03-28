/-
# Erdős Problem #1178: Brown-Erdős-Sós Conjecture (General Form)

Source: https://erdosproblems.com/1178
Status: OPEN

Statement:
For r ≥ 3, let d_r(e) be the minimal d such that
  ex_r(n, F) = o(n²),
where F is the family of r-uniform hypergraphs on d vertices with e edges.

Conjecture: d_r(e) = (r-2)e + 3 for all r, e ≥ 3.

Known Results:
- Brown-Erdős-Sós (1973): Proved d_r(e) ≥ (r-2)e + 3 (lower bound)
- Ruzsa-Szemerédi (1978): d_3(3) = 6 (the (6,3)-problem, see #716)
- Erdős-Frankl-Rödl (1986): d_r(3) = (r-2)·3 + 3 for all r ≥ 3
- Sárközy-Selkow (2005): d_r(e) ≤ (r-2)e + 2 + ⌊log₂ e⌋
- Conlon-Gishboliner-Levanzov-Shapira (2023): d_3(e) ≤ e + O(log e / log log e)

Related Problems:
- #716: The (6,3)-problem (d_3(3) = 6)
- #1076: Extremal numbers for 3-uniform hypergraphs (F_k problem)
- #1157: General case

References:
- [BES73] Brown-Erdős-Sós, "Some extremal problems on r-graphs" (1973)
- [Er75b] Erdős, "Problems and results on graphs and hypergraphs" (1975)
- [Er81] Erdős, "On the combinatorial problems I most would like to see solved" (1981)
- [EFR86] Erdős-Frankl-Rödl, "The asymptotic number of graphs..." (1986)
- [RuSz78] Ruzsa-Szemerédi, "Triple systems with no six points..." (1978)
- [SaSe05] Sárközy-Selkow, "On a Turán-type hypergraph problem..." (2005)
- [CGLS23] Conlon-Gishboliner-Levanzov-Shapira, "On the Brown-Erdős-Sós conjecture" (2023)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Real Filter

namespace Erdos1178

/- ## Part I: r-Uniform Hypergraphs -/

/-- An r-uniform hypergraph on vertex set Fin n, represented as a collection
    of r-element subsets (stored as Finsets). -/
structure UniformHypergraph (r n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- The number of edges in an r-uniform hypergraph. -/
def numEdges (H : UniformHypergraph r n) : ℕ := H.edges.card

/-- The vertex set spanned by the hypergraph: all vertices appearing in some edge. -/
def spannedVertices (H : UniformHypergraph r n) : Finset (Fin n) :=
  H.edges.biUnion id

/-- The number of vertices spanned by the hypergraph. -/
def numVerticesSpanned (H : UniformHypergraph r n) : ℕ :=
  (spannedVertices H).card

/- ## Part II: The Family F(r, d, e) -/

/-- The family F(r, d, e): all r-uniform hypergraphs on at most d vertices
    with exactly e edges. An r-uniform hypergraph is in this family if it spans
    at most d vertices and has exactly e edges. -/
def InFamily (r d e : ℕ) (H : UniformHypergraph r n) : Prop :=
  numVerticesSpanned H ≤ d ∧ numEdges H = e

/-- An r-uniform hypergraph is F(r,d,e)-free if it contains no subhypergraph
    in the family. -/
def IsFamilyFree (r d e : ℕ) (H : UniformHypergraph r n) : Prop :=
  ∀ S : Finset (Finset (Fin n)), S ⊆ H.edges → S.card = e →
    (S.biUnion id).card > d

/- ## Part III: Extremal Numbers -/

/-- The extremal number ex_r(n, F(r,d,e)): maximum number of edges in an
    r-uniform n-vertex hypergraph that is F(r,d,e)-free.
    Axiomatized since constructive definition requires decidability. -/
axiom exr (r n d e : ℕ) : ℕ

/-- Little-o notation: f(n) = o(g(n)) means f(n)/g(n) → 0. -/
def isLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * |g n|

/- ## Part IV: The Function d_r(e) -/

/-- d_r(e) is the minimal d such that ex_r(n, F(r,d,e)) = o(n²).
    That is, the threshold number of vertices above which the extremal number
    becomes subquadratic. Axiomatized as the definition involves a minimization
    over an existential condition. -/
axiom dr (r e : ℕ) : ℕ

/-- dr is well-defined: ex_r(n, F(r, dr(r,e), e)) = o(n²). -/
axiom dr_spec (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
  isLittleO (fun n => (exr r n (dr r e) e : ℝ)) (fun n => (n : ℝ)^2)

/-- dr is minimal: for any d < dr(r,e), ex_r(n, F(r,d,e)) is NOT o(n²). -/
axiom dr_minimal (r e d : ℕ) (hr : r ≥ 3) (he : e ≥ 3) (hd : d < dr r e) :
  ¬isLittleO (fun n => (exr r n d e : ℝ)) (fun n => (n : ℝ)^2)

/- ## Part V: Brown-Erdős-Sós Lower Bound (1973) -/

/-- The conjectured value: d_r(e) = (r-2)·e + 3. -/
def conjecturedValue (r e : ℕ) : ℕ := (r - 2) * e + 3

/-- **Brown-Erdős-Sós Lower Bound (1973):**
    d_r(e) ≥ (r-2)·e + 3 for all r, e ≥ 3.
    This was proved in the original paper [BES73]. -/
theorem bes_lower_bound (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
    dr r e ≥ conjecturedValue r e := by
  sorry

/- ## Part VI: Known Upper Bounds -/

/-- **Sárközy-Selkow Upper Bound (2005):**
    d_r(e) ≤ (r-2)·e + 2 + ⌊log₂ e⌋ for all r, e ≥ 3. -/
axiom sarkozy_selkow_upper (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
  dr r e ≤ (r - 2) * e + 2 + Nat.log 2 e

/- ## Part VII: Solved Cases -/

/-- **Ruzsa-Szemerédi (1978):** d_3(3) = 6.
    This is the (6,3)-problem, Erdős Problem #716. -/
theorem ruzsa_szemeredi_d3_3 : dr 3 3 = conjecturedValue 3 3 := by
  sorry

/-- **Erdős-Frankl-Rödl (1986):** d_r(3) = (r-2)·3 + 3 for all r ≥ 3.
    The e=3 case of the conjecture is fully resolved. -/
theorem efr_e3 (r : ℕ) (hr : r ≥ 3) : dr r 3 = conjecturedValue r 3 := by
  sorry

/-- **Conlon-Gishboliner-Levanzov-Shapira (2023):**
    d_3(e) ≤ e + O(log e / log log e) for all e ≥ 3.
    Note: the conjecture predicts d_3(e) = e + 3. -/
axiom cgls_upper_r3 (e : ℕ) (he : e ≥ 3) :
  ∃ C : ℝ, C > 0 ∧ (dr 3 e : ℝ) ≤ (e : ℝ) + C * Real.log e / Real.log (Real.log e)

/- ## Part VIII: Specific Values -/

/-- d_3(3) = 6: The Ruzsa-Szemerédi (6,3)-theorem. -/
theorem d3_3_value : conjecturedValue 3 3 = 6 := by norm_num

/-- d_3(4) should be 7 according to the conjecture. -/
theorem d3_4_conjectured : conjecturedValue 3 4 = 7 := by norm_num

/-- d_4(3) should be 9 according to the conjecture. -/
theorem d4_3_conjectured : conjecturedValue 4 3 = 9 := by norm_num

/-- d_3(10): Solymosi-Solymosi (2017) proved d_3(10) ≤ 14.
    The conjecture predicts d_3(10) = 13. -/
axiom solymosi_d3_10 : dr 3 10 ≤ 14

/- ## Part IX: The Main Conjecture -/

/-- **The Brown-Erdős-Sós Conjecture (General Form):**
    d_r(e) = (r-2)·e + 3 for all r, e ≥ 3.

    This is OPEN. The lower bound is proved [BES73], and partial upper bounds
    are known (Sárközy-Selkow, CGLS), but the exact value remains unresolved
    for general r and e. -/
def BrownErdosSosGeneralConjecture : Prop :=
  ∀ r e : ℕ, r ≥ 3 → e ≥ 3 → dr r e = conjecturedValue r e

/-- The conjecture equivalently states that dr r e = (r-2)*e + 3. -/
theorem conjecture_expanded :
    BrownErdosSosGeneralConjecture ↔
    ∀ r e : ℕ, r ≥ 3 → e ≥ 3 → dr r e = (r - 2) * e + 3 := by
  simp [BrownErdosSosGeneralConjecture, conjecturedValue]

/- ## Part X: Connection to Related Problems -/

/-- Connection to Erdős #1076: The special case r=3 of the BES conjecture
    about F_k families. When r=3, d=k+3, e=k, the conjecture d_3(k) = k+3
    asks whether ex_3(n, F(3,k+3,k)) = o(n²). -/
theorem connection_to_1076 : conjecturedValue 3 k = k + 3 := by
  simp [conjecturedValue]

/-- Connection to Erdős #716: The (6,3)-problem is the case r=3, e=3. -/
theorem connection_to_716 : conjecturedValue 3 3 = 6 := d3_3_value

/- ## Part XI: Implications of the Conjecture -/

/-- If the conjecture holds, then for any d < (r-2)e+3, there exist
    r-uniform hypergraphs with Ω(n²) edges that are F(r,d,e)-free. -/
theorem conjecture_implies_dense_free (r e d : ℕ) (hr : r ≥ 3) (he : e ≥ 3)
    (hd : d < conjecturedValue r e) (hconj : BrownErdosSosGeneralConjecture) :
    ¬isLittleO (fun n => (exr r n d e : ℝ)) (fun n => (n : ℝ)^2) := by
  have hdr := hconj r e hr he
  rw [hdr] at *
  exact dr_minimal r e d hr he hd

/-- If the conjecture holds, then for d = (r-2)e+3, the extremal number
    drops to o(n²). -/
theorem conjecture_implies_subquadratic (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3)
    (hconj : BrownErdosSosGeneralConjecture) :
    isLittleO (fun n => (exr r n (conjecturedValue r e) e : ℝ)) (fun n => (n : ℝ)^2) := by
  have hdr := hconj r e hr he
  rw [← hdr]
  exact dr_spec r e hr he

/- ## Part XII: Summary -/

/-- **Erdős Problem #1178: OPEN**

The Brown-Erdős-Sós Conjecture in its general form asks:

  d_r(e) = (r-2)·e + 3 for all r, e ≥ 3,

where d_r(e) is the minimal d such that ex_r(n, F(r,d,e)) = o(n²).

- Lower bound d_r(e) ≥ (r-2)e+3 proved [BES73]
- Upper bound d_r(e) ≤ (r-2)e+2+⌊log₂ e⌋ proved [SaSe05]
- Case e=3: d_r(3) = (r-2)·3+3 proved [EFR86]
- Case r=3: d_3(e) ≤ e + O(log e / log log e) proved [CGLS23]
- Full conjecture: OPEN -/
axiom erdos_1178 : BrownErdosSosGeneralConjecture

end Erdos1178
