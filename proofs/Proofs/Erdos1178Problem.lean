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
- Erdős-Frankl-Rödl (1986): d_r(3) = (r-2)·3 + 3 for all r ≥ 3 [PROVED from axioms]
- Sárközy-Selkow (2005): d_r(e) ≤ (r-2)e + 2 + ⌊log₂ e⌋
- Conlon-Gishboliner-Levanzov-Shapira (2023): d_3(e) ≤ e + O(log e / log log e)
- Ruzsa-Szemerédi d_3(3) = 6 [PROVED from BES + Sárközy-Selkow + ⌊log₂ 3⌋ = 1]

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
import Mathlib.Data.Nat.Lattice
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
    Defined as the supremum over all F(r,d,e)-free hypergraphs on n vertices. -/
noncomputable def exr (r n d e : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : UniformHypergraph r n, IsFamilyFree r d e H ∧ numEdges H = m}

/-- Little-o notation: f(n) = o(g(n)) means f(n)/g(n) → 0. -/
def isLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * |g n|

/- ## Part IV: The Function d_r(e) -/

/-- d_r(e) is the minimal d such that ex_r(n, F(r,d,e)) = o(n²).
    That is, the threshold number of vertices above which the extremal number
    becomes subquadratic. Defined as the infimum over the set of such d. -/
noncomputable def dr (r e : ℕ) : ℕ :=
  sInf {d : ℕ | isLittleO (fun n => (exr r n d e : ℝ)) (fun n => (n : ℝ)^2)}

/-- **Sárközy-Selkow (2005):** The value d₀ = (r-2)e + 2 + ⌊log₂ e⌋ gives
    a subquadratic extremal number. This is the primitive form from which
    dr_spec and the upper bound theorem are derived. -/
axiom sarkozy_selkow_result (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
  isLittleO (fun n => (exr r n ((r - 2) * e + 2 + Nat.log 2 e) e : ℝ))
    (fun n => (n : ℝ)^2)

/-- dr is well-defined: ex_r(n, F(r, dr(r,e), e)) = o(n²).
    Proof: dr = sInf S where S is nonempty (by Sárközy-Selkow).
    For ℕ, sInf of a nonempty set is in the set. -/
theorem dr_spec (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
    isLittleO (fun n => (exr r n (dr r e) e : ℝ)) (fun n => (n : ℝ)^2) := by
  unfold dr
  exact Nat.sInf_mem ⟨_, sarkozy_selkow_result r e hr he⟩

/-- dr is minimal: for any d < dr(r,e), ex_r(n, F(r,d,e)) is NOT o(n²).
    Proof: if d ∈ S, then sInf S ≤ d, contradicting d < sInf S. -/
theorem dr_minimal (r e d : ℕ) (hr : r ≥ 3) (he : e ≥ 3) (hd : d < dr r e) :
    ¬isLittleO (fun n => (exr r n d e : ℝ)) (fun n => (n : ℝ)^2) := by
  intro h
  have hle : dr r e ≤ d := Nat.sInf_le h
  omega

/- ## Part V: Brown-Erdős-Sós Lower Bound (1973) -/

/-- The conjectured value: d_r(e) = (r-2)·e + 3. -/
def conjecturedValue (r e : ℕ) : ℕ := (r - 2) * e + 3

/-- **Brown-Erdős-Sós Lower Bound (1973):**
    d_r(e) ≥ (r-2)·e + 3 for all r, e ≥ 3.
    Proved via explicit construction in [BES73]. Axiomatized as a deep
    published result (the construction uses Steiner systems). -/
axiom bes_lower_bound (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
    dr r e ≥ conjecturedValue r e

/- ## Part VI: Known Upper Bounds -/

/-- **Sárközy-Selkow Upper Bound (2005):**
    d_r(e) ≤ (r-2)·e + 2 + ⌊log₂ e⌋ for all r, e ≥ 3.
    Proof: sInf S ≤ d₀ since d₀ ∈ S (by sarkozy_selkow_result). -/
theorem sarkozy_selkow_upper (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
    dr r e ≤ (r - 2) * e + 2 + Nat.log 2 e :=
  Nat.sInf_le (sarkozy_selkow_result r e hr he)

/- ## Part VII: Solved Cases -/

/-- **Ruzsa-Szemerédi (1978):** d_3(3) = 6.
    This is the (6,3)-problem, Erdős Problem #716.
    Proof: BES lower bound gives dr 3 3 ≥ 6, Sárközy-Selkow upper bound
    gives dr 3 3 ≤ (3-2)·3 + 2 + ⌊log₂ 3⌋ = 3+2+1 = 6. -/
theorem ruzsa_szemeredi_d3_3 : dr 3 3 = conjecturedValue 3 3 := by
  apply le_antisymm
  · -- Upper bound: dr 3 3 ≤ 6
    have h := sarkozy_selkow_upper 3 3 (by omega) (by omega)
    have hlog : Nat.log 2 3 = 1 := by native_decide
    rw [hlog] at h
    unfold conjecturedValue; omega
  · -- Lower bound: dr 3 3 ≥ 6
    exact bes_lower_bound 3 3 (by omega) (by omega)

/-- **Erdős-Frankl-Rödl (1986):** d_r(3) = (r-2)·3 + 3 for all r ≥ 3.
    The e=3 case of the conjecture is fully resolved.
    Proof: BES lower bound gives dr r 3 ≥ (r-2)·3+3, Sárközy-Selkow gives
    dr r 3 ≤ (r-2)·3 + 2 + ⌊log₂ 3⌋ = (r-2)·3 + 3 since ⌊log₂ 3⌋ = 1. -/
theorem efr_e3 (r : ℕ) (hr : r ≥ 3) : dr r 3 = conjecturedValue r 3 := by
  apply le_antisymm
  · -- Upper bound: dr r 3 ≤ (r-2)·3 + 3
    have h := sarkozy_selkow_upper r 3 hr (by omega)
    have hlog : Nat.log 2 3 = 1 := by native_decide
    rw [hlog] at h
    unfold conjecturedValue; omega
  · -- Lower bound: dr r 3 ≥ (r-2)·3 + 3
    exact bes_lower_bound r 3 hr (by omega)

/- **Conlon-Gishboliner-Levanzov-Shapira (2023):**
    d_3(e) ≤ e + O(log e / log log e) for all e ≥ 3.
    Note: the conjecture predicts d_3(e) = e + 3.
    Formally: ∃ C > 0, (dr 3 e : ℝ) ≤ e + C * log e / log (log e). -/

/- ## Part VIII: Specific Values -/

/-- d_3(3) = 6: The Ruzsa-Szemerédi (6,3)-theorem. -/
theorem d3_3_value : conjecturedValue 3 3 = 6 := by norm_num

/-- d_3(4) should be 7 according to the conjecture. -/
theorem d3_4_conjectured : conjecturedValue 3 4 = 7 := by norm_num

/-- d_4(3) should be 9 according to the conjecture. -/
theorem d4_3_conjectured : conjecturedValue 4 3 = 9 := by norm_num

/-- **Solymosi-Solymosi (2017):** d_3(10) ≤ 14.
    The conjecture predicts d_3(10) = 13. Axiomatized as a deep published result.
    Reference: Solymosi-Solymosi, "On a hypergraph Turán problem of Frankl",
    Combinatorica 37 (2017). -/
axiom solymosi_d3_10 : dr 3 10 ≤ 14

/-- The Solymosi-Solymosi bound differs from the conjectured value by at most 1. -/
theorem solymosi_d3_10_gap : dr 3 10 ≤ conjecturedValue 3 10 + 1 := by
  unfold conjecturedValue
  have h := solymosi_d3_10
  omega

/-- Lower bound on d_3(10) from BES: d_3(10) ≥ 13. -/
theorem bes_d3_10_lower : dr 3 10 ≥ 13 := by
  have h := bes_lower_bound 3 10 (by omega) (by omega)
  unfold conjecturedValue at h
  omega

/-- Combined bounds: 13 ≤ d_3(10) ≤ 14 (the conjecture says equality at 13). -/
theorem d3_10_bounds : 13 ≤ dr 3 10 ∧ dr 3 10 ≤ 14 :=
  ⟨bes_d3_10_lower, solymosi_d3_10⟩

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

/- **Erdős Problem #1178: OPEN**

The Brown-Erdős-Sós Conjecture in its general form asks:

  d_r(e) = (r-2)·e + 3 for all r, e ≥ 3,

where d_r(e) is the minimal d such that ex_r(n, F(r,d,e)) = o(n²).

- Lower bound d_r(e) ≥ (r-2)e+3 proved [BES73]
- Upper bound d_r(e) ≤ (r-2)e+2+⌊log₂ e⌋ proved [SaSe05]
- Case e=3: d_r(3) = (r-2)·3+3 proved [EFR86]
- Case r=3: d_3(e) ≤ e + O(log e / log log e) proved [CGLS23]
- Full conjecture: OPEN
Formally: BrownErdosSosGeneralConjecture. -/

end Erdos1178
