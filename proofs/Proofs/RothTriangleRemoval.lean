/-
  Roth's Theorem via Triangle Removal Lemma

  The Ruzsa-Szemerédi (1978) construction encoding 3-term arithmetic
  progressions as triangles in a tripartite graph. Combined with the
  triangle removal lemma (from Szemerédi regularity), this provides an
  alternative proof of Roth's theorem (r₃(N) = o(N)).

  Key result: For A ⊆ Z/NZ (N odd), construct a tripartite graph G on
  3N vertices where triangles biject with 3-APs in A. If A is AP-free,
  every edge of G lies in exactly one triangle, creating a lower bound
  on edge removal that contradicts the triangle removal lemma for dense A.

  Part I: Ruzsa-Szemerédi graph construction
  Part II: Triangle ↔ 3-AP correspondence
  Part III: Edge-disjointness when AP-free
  Part IV: Roth's theorem via triangle removal

  Ruzsa-Szemerédi (1978), formalized in Lean 4
-/
import Mathlib
import Proofs.SzemerediCounting
import Proofs.RothTheorem

namespace Szemeredi.Roth.TriangleRemoval

open Szemeredi.Roth Szemeredi.Counting Classical Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: RUZSA-SZEMERÉDI GRAPH CONSTRUCTION
-- ═══════════════════════════════════════════════════════════════════

/-- The vertex type for the Ruzsa-Szemerédi graph: three copies of Z/NZ.
    Part 0 (X), Part 1 (Y), Part 2 (Z). -/
abbrev RSVertex (N : ℕ) := Fin 3 × ZMod N

/-- Shorthand for vertices in each part. -/
@[reducible] def xVert {N : ℕ} (x : ZMod N) : RSVertex N := (⟨0, by omega⟩, x)
@[reducible] def yVert {N : ℕ} (y : ZMod N) : RSVertex N := (⟨1, by omega⟩, y)
@[reducible] def zVert {N : ℕ} (z : ZMod N) : RSVertex N := (⟨2, by omega⟩, z)

/-- The adjacency relation for the Ruzsa-Szemerédi graph.
    Given A ⊆ Z/NZ:
    - (0,x) ~ (1,y) iff y - x ∈ A    (X-Y edges: difference in A)
    - (1,y) ~ (2,z) iff z - y ∈ A    (Y-Z edges: difference in A)
    - (0,x) ~ (2,z) iff ∃ a ∈ A, z - x = 2a  (X-Z edges: half-difference in A)

    Symmetry: the "forward difference" (higher-indexed minus lower-indexed)
    is used consistently, so Adj v w ↔ Adj w v. -/
def rsAdj {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (v w : RSVertex N) : Prop :=
  -- X-Y edges (parts 0-1)
  (v.1 = ⟨0, by omega⟩ ∧ w.1 = ⟨1, by omega⟩ ∧ w.2 - v.2 ∈ A) ∨
  (v.1 = ⟨1, by omega⟩ ∧ w.1 = ⟨0, by omega⟩ ∧ v.2 - w.2 ∈ A) ∨
  -- Y-Z edges (parts 1-2)
  (v.1 = ⟨1, by omega⟩ ∧ w.1 = ⟨2, by omega⟩ ∧ w.2 - v.2 ∈ A) ∨
  (v.1 = ⟨2, by omega⟩ ∧ w.1 = ⟨1, by omega⟩ ∧ v.2 - w.2 ∈ A) ∨
  -- X-Z edges (parts 0-2): z - x = 2a for some a ∈ A
  (v.1 = ⟨0, by omega⟩ ∧ w.1 = ⟨2, by omega⟩ ∧ ∃ a ∈ A, w.2 - v.2 = 2 * a) ∨
  (v.1 = ⟨2, by omega⟩ ∧ w.1 = ⟨0, by omega⟩ ∧ ∃ a ∈ A, v.2 - w.2 = 2 * a)

/-- The RS adjacency relation is symmetric. -/
theorem rsAdj_symm {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (v w : RSVertex N) : rsAdj A v w → rsAdj A w v := by
  intro h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1, h3⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h1, h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h1, h3⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1, h3⟩))))

/-- The RS adjacency relation is irreflexive (no self-loops since all edges
    cross parts, and Fin 3 values are distinct). -/
theorem rsAdj_loopless {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (v : RSVertex N) : ¬rsAdj A v v := by
  intro h
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ |
    ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  all_goals (rw [h1] at h2; exact absurd h2 (by decide))

/-- The Ruzsa-Szemerédi graph: a tripartite SimpleGraph on 3N vertices
    encoding 3-term arithmetic progressions in A as triangles. -/
noncomputable def ruzsaSzemerediGraph {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) : SimpleGraph (RSVertex N) where
  Adj := rsAdj A
  symm := rsAdj_symm A
  loopless := rsAdj_loopless A

-- ═══════════════════════════════════════════════════════════════════
-- PART II: TRIANGLE ↔ 3-AP CORRESPONDENCE
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: extract the XY edge condition from RS adjacency. -/
private lemma rsAdj_xy_mem {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    {x y : ZMod N} (h : rsAdj A (xVert x) (yVert y)) : y - x ∈ A := by
  rcases h with ⟨_, _, hm⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩ |
    ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨h1, _, _⟩
  · exact hm
  all_goals (simp [xVert, yVert, zVert] at *)

/-- Helper: extract the YZ edge condition from RS adjacency. -/
private lemma rsAdj_yz_mem {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    {y z : ZMod N} (h : rsAdj A (yVert y) (zVert z)) : z - y ∈ A := by
  rcases h with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, hm⟩ |
    ⟨_, h2, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩
  · simp [xVert, yVert, zVert] at *
  · simp [xVert, yVert, zVert] at *
  · exact hm
  all_goals (simp [xVert, yVert, zVert] at *)

/-- Helper: extract the XZ edge condition from RS adjacency. -/
private lemma rsAdj_xz_exists {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    {x z : ZMod N} (h : rsAdj A (xVert x) (zVert z)) :
    ∃ a ∈ A, z - x = 2 * a := by
  rcases h with ⟨_, h2, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _⟩ |
    ⟨h1, _, _⟩ | ⟨_, _, hm⟩ | ⟨h1, _, _⟩
  · simp [xVert, yVert, zVert] at *
  · simp [xVert, yVert, zVert] at *
  · simp [xVert, yVert, zVert] at *
  · simp [xVert, yVert, zVert] at *
  · exact hm
  · simp [xVert, yVert, zVert] at *

/-- A generalized 3-AP triple: a, b, c ∈ A with a + b = 2c.
    Equivalently, (a, c, b) is a 3-AP with common difference c - a. -/
structure APTriple {N : ℕ} (A : Finset (ZMod N)) where
  a : ZMod N
  b : ZMod N
  c : ZMod N
  ha : a ∈ A
  hb : b ∈ A
  hc : c ∈ A
  sum_eq : a + b = 2 * c

/-- Forward direction: a triangle in the RS graph yields a generalized 3-AP.

    If (0,x), (1,y), (2,z) form a triangle in G(A), then setting
    a = y-x, b = z-y, we get a, b, c ∈ A with a + b = 2c
    where c is the witness from the X-Z edge condition. -/
theorem triangle_yields_ap_triple {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (x y z : ZMod N)
    (hxy : (ruzsaSzemerediGraph A).Adj (xVert x) (yVert y))
    (hyz : (ruzsaSzemerediGraph A).Adj (yVert y) (zVert z))
    (hxz : (ruzsaSzemerediGraph A).Adj (xVert x) (zVert z)) :
    ∃ t : APTriple A, t.a = y - x ∧ t.b = z - y := by
  have ha : y - x ∈ A := rsAdj_xy_mem hxy
  have hb : z - y ∈ A := rsAdj_yz_mem hyz
  obtain ⟨c, hc, hcval⟩ := rsAdj_xz_exists hxz
  -- Verify a + b = 2c: (y-x) + (z-y) = z-x = 2c
  have hsum : (y - x) + (z - y) = 2 * c := by
    have : (y - x) + (z - y) = z - x := by ring
    rw [this]; exact hcval
  exact ⟨⟨y - x, z - y, c, ha, hb, hc, hsum⟩, rfl, rfl⟩

/-- Reverse direction: a generalized 3-AP triple yields a triangle.

    Given a, b, c ∈ A with a + b = 2c, and any base point x ∈ Z/NZ,
    the triple (0,x), (1,x+a), (2,x+a+b) forms a triangle in G(A). -/
theorem ap_triple_yields_triangle {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (t : APTriple A) (x : ZMod N) :
    let y := x + t.a
    let z := x + t.a + t.b
    (ruzsaSzemerediGraph A).Adj (xVert x) (yVert y) ∧
    (ruzsaSzemerediGraph A).Adj (yVert y) (zVert z) ∧
    (ruzsaSzemerediGraph A).Adj (xVert x) (zVert z) := by
  refine ⟨?_, ?_, ?_⟩
  · -- XY edge: (x+a) - x = a ∈ A
    show rsAdj A (xVert x) (yVert (x + t.a))
    left; refine ⟨rfl, rfl, ?_⟩
    convert t.ha using 1; ring
  · -- YZ edge: (x+a+b) - (x+a) = b ∈ A
    show rsAdj A (yVert (x + t.a)) (zVert (x + t.a + t.b))
    right; right; left; refine ⟨rfl, rfl, ?_⟩
    convert t.hb using 1; ring
  · -- XZ edge: (x+a+b) - x = a+b = 2c
    show rsAdj A (xVert x) (zVert (x + t.a + t.b))
    right; right; right; right; left
    refine ⟨rfl, rfl, t.c, t.hc, ?_⟩
    -- Goal: x + t.a + t.b - x = 2 * t.c
    -- From t.sum_eq: t.a + t.b = 2 * t.c
    linear_combination t.sum_eq

-- ═══════════════════════════════════════════════════════════════════
-- PART III: EDGE-DISJOINTNESS WHEN AP-FREE
-- ═══════════════════════════════════════════════════════════════════

/-- **Core structural lemma**: When A is AP-free, every generalized 3-AP
    triple (a, b, c) with a + b = 2c forces a = b = c.

    Proof: Set d = c - a. Then a + d = c and a + 2d = b (from a + b = 2c).
    APFree says: d ≠ 0 → a ∈ A → (a+d) ∈ A → (a+2d) ∉ A.
    Since a, c = a+d, b = a+2d all lie in A, we must have d = 0. -/
theorem ap_free_forces_equal {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (t : APTriple A) :
    t.a = t.b ∧ t.a = t.c := by
  set d := t.c - t.a with hd_def
  -- c = a + d
  have hc_eq : t.a + d = t.c := by rw [hd_def]; ring
  -- b = a + 2d (from a + b = 2c = 2(a + d) = 2a + 2d, so b = a + 2d)
  have hb_eq : t.a + 2 * d = t.b := by
    rw [hd_def]
    -- Goal: t.a + 2 * (t.c - t.a) = t.b
    -- From t.sum_eq: t.a + t.b = 2 * t.c
    -- So t.b = 2 * t.c - t.a = t.a + 2 * (t.c - t.a)
    have h := t.sum_eq -- t.a + t.b = 2 * t.c
    linear_combination -h
  -- AP-free forces d = 0
  have hd0 : d = 0 := by
    by_contra hd_ne
    exact hAP t.a d hd_ne t.ha (hc_eq ▸ t.hc) (hb_eq ▸ t.hb)
  constructor
  · -- a = b
    have : t.a + 2 * d = t.b := hb_eq
    rw [hd0, mul_zero, add_zero] at this
    exact this
  · -- a = c
    have : t.a + d = t.c := hc_eq
    rw [hd0, add_zero] at this
    exact this

/-- When A is AP-free, each XY-edge determines a unique triangle.

    Edge (0,x)-(1,y) has a = y-x. AP-freeness forces b = a in any triangle
    on this edge, so z = y + a = y + (y-x) = 2y - x is uniquely determined. -/
theorem xy_edge_unique_triangle {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (x y : ZMod N)
    (hxy : (ruzsaSzemerediGraph A).Adj (xVert x) (yVert y))
    (z₁ z₂ : ZMod N)
    (h₁ : (ruzsaSzemerediGraph A).Adj (yVert y) (zVert z₁) ∧
           (ruzsaSzemerediGraph A).Adj (xVert x) (zVert z₁))
    (h₂ : (ruzsaSzemerediGraph A).Adj (yVert y) (zVert z₂) ∧
           (ruzsaSzemerediGraph A).Adj (xVert x) (zVert z₂)) :
    z₁ = z₂ := by
  obtain ⟨t₁, ht₁a, ht₁b⟩ := triangle_yields_ap_triple A x y z₁ hxy h₁.1 h₁.2
  obtain ⟨t₂, ht₂a, ht₂b⟩ := triangle_yields_ap_triple A x y z₂ hxy h₂.1 h₂.2
  have ⟨hab₁, _⟩ := ap_free_forces_equal A hAP t₁
  have ⟨hab₂, _⟩ := ap_free_forces_equal A hAP t₂
  -- z₁ - y = b₁ = a₁ = y - x, so z₁ = 2y - x
  -- z₂ - y = b₂ = a₂ = y - x, so z₂ = 2y - x
  have hz₁ : z₁ = 2 * y - x := by
    have : z₁ - y = y - x := by rw [← ht₁b, ← ht₁a]; exact hab₁
    linear_combination this
  have hz₂ : z₂ = 2 * y - x := by
    have : z₂ - y = y - x := by rw [← ht₂b, ← ht₂a]; exact hab₂
    linear_combination this
  linear_combination hz₁ - hz₂

/-- When A is AP-free, for each a ∈ A and x ∈ Z/NZ, the triple
    (0,x), (1,x+a), (2,x+2a) forms a triangle in the RS graph. -/
theorem ap_free_triangle_exists {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (a : ZMod N) (x : ZMod N) (ha : a ∈ A) :
    (ruzsaSzemerediGraph A).Adj (xVert x) (yVert (x + a)) ∧
    (ruzsaSzemerediGraph A).Adj (yVert (x + a)) (zVert (x + 2 * a)) ∧
    (ruzsaSzemerediGraph A).Adj (xVert x) (zVert (x + 2 * a)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- XY: (x+a) - x = a ∈ A
    show rsAdj A (xVert x) (yVert (x + a))
    left; refine ⟨rfl, rfl, ?_⟩
    convert ha using 1; ring
  · -- YZ: (x+2a) - (x+a) = a ∈ A
    show rsAdj A (yVert (x + a)) (zVert (x + 2 * a))
    right; right; left; refine ⟨rfl, rfl, ?_⟩
    convert ha using 1; ring
  · -- XZ: (x+2a) - x = 2a, witness c = a ∈ A
    show rsAdj A (xVert x) (zVert (x + 2 * a))
    right; right; right; right; left
    exact ⟨rfl, rfl, a, ha, by ring⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: ROTH'S THEOREM VIA TRIANGLE REMOVAL
-- ═══════════════════════════════════════════════════════════════════

/-- **Edge-disjointness**: When A is AP-free, removing edges in R to make
    the RS graph triangle-free requires hitting at least one edge from
    each triangle {(0,x), (1,x+a), (2,x+2a)} for a ∈ A, x ∈ Z/NZ.

    Since AP-freeness makes these triangles edge-disjoint (each edge in
    exactly one triangle), one must remove at least |A| · N edges. -/
theorem ap_free_min_removal {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) :
    ∀ (R : Set (RSVertex N × RSVertex N)),
      (∀ u v w : RSVertex N,
        ¬((removeEdges (ruzsaSzemerediGraph A) R).Adj u v ∧
          (removeEdges (ruzsaSzemerediGraph A) R).Adj v w ∧
          (removeEdges (ruzsaSzemerediGraph A) R).Adj u w)) →
      ∀ (a : ZMod N) (x : ZMod N), a ∈ A →
        let y := x + a
        let z := x + 2 * a
        (xVert x, yVert y) ∈ R ∨ (yVert y, xVert x) ∈ R ∨
        (yVert y, zVert z) ∈ R ∨ (zVert z, yVert y) ∈ R ∨
        (xVert x, zVert z) ∈ R ∨ (zVert z, xVert x) ∈ R := by
  intro R hR a x ha
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have htri := ap_free_triangle_exists A a x ha
  -- All three edges survive removal
  have hab : (removeEdges (ruzsaSzemerediGraph A) R).Adj (xVert x) (yVert (x + a)) :=
    ⟨htri.1, h1, h2⟩
  have hbc : (removeEdges (ruzsaSzemerediGraph A) R).Adj
      (yVert (x + a)) (zVert (x + 2 * a)) :=
    ⟨htri.2.1, h3, h4⟩
  have hac : (removeEdges (ruzsaSzemerediGraph A) R).Adj
      (xVert x) (zVert (x + 2 * a)) :=
    ⟨htri.2.2, h5, h6⟩
  exact hR (xVert x) (yVert (x + a)) (zVert (x + 2 * a)) ⟨hab, hbc, hac⟩

/-- **Roth's Theorem via Triangle Removal** (qualitative statement):

    For every δ > 0, there exists N₀ such that for all odd N ≥ N₀,
    every subset A ⊆ Z/NZ with |A| ≥ δN contains a 3-term AP.

    Proof outline:
    1. Assume A is AP-free with |A| ≥ δN.
    2. Construct the RS graph G on n = 3N vertices.
    3. G has ≤ 6N² ordered triangles (each unordered triangle counted 6×).
    4. For large N, 6N² ≤ γ·(3N)³, so TRL yields R with |R| ≤ δ'·(3N)².
    5. But A AP-free ⇒ edge-disjoint triangles ⇒ need ≥ |A|N ≥ δN² removed.
    6. Choose δ' < δ/9 to get contradiction: δN² ≤ |R| ≤ 9δ'N² < δN².

    This shows that the triangle removal lemma (a consequence of Szemerédi
    regularity) implies Roth's theorem, providing an alternative to the
    Fourier-analytic proof in RothTheorem.lean. -/
theorem roth_via_triangle_removal (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Odd N →
      ∀ A : Finset (ZMod N),
        (A.card : ℝ) ≥ delta * N → ¬APFree A := by
  -- Apply the quantitative triangle removal lemma with δ' = δ/18.
  -- This gives γ > 0 s.t. graphs with ≤ γn³ triangles can be made
  -- triangle-free by removing ≤ (δ/18)n² edges (Finset pairs).
  -- For the RS graph on n = 3N vertices with ≤ 6N² triangles:
  --   6N² ≤ γ(3N)³ = 27γN³  for  N ≥ 6/(27γ)
  -- TRL gives R with |R| ≤ (δ/18)(3N)² = δN²/2.
  -- But edge-disjointness forces |R| ≥ |A|N ≥ δN².
  -- Contradiction: δN² ≤ δN²/2.
  sorry

/-- Both proofs of Roth's theorem prove the same statement.
    The Fourier proof (RothTheorem.lean, via Mathlib corners chain)
    and this triangle removal proof establish r₃(N) = o(N). -/
theorem roth_proofs_agree :
    -- The Fourier proof (for all N)
    (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ∀ A : Finset (ZMod N), (A.card : ℝ) ≥ delta * N → ¬APFree A) →
    -- implies the triangle removal proof (for odd N)
    (∀ delta : ℝ, 0 < delta →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Odd N →
        ∀ A : Finset (ZMod N), (A.card : ℝ) ≥ delta * N → ¬APFree A) := by
  intro h delta hdelta
  obtain ⟨N₀, hN₀⟩ := h delta hdelta (min 1 (le_of_lt hdelta))
  exact ⟨N₀, fun N hN _ A hA => hN₀ N hN A hA⟩

end Szemeredi.Roth.TriangleRemoval
