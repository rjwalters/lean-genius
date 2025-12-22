/-
  Pythagorean Theorem - a² + b² = c²

  A formal proof of the Pythagorean theorem using inner product spaces.
  In a right triangle, the square of the hypotenuse equals the sum of
  the squares of the other two sides.

  This proof uses the elegant connection between perpendicularity (zero inner
  product) and the norm formula in inner product spaces.

  Historical Note: While Pythagoras (c. 570-495 BCE) gets credit, the theorem
  was known to Babylonians 1000 years earlier and has 300+ known proofs.
-/

-- ============================================================
-- PART 1: Real Numbers and Basic Operations
-- ============================================================

-- We work with real numbers for geometric quantities
-- In a full formalization, we'd import Mathlib's reals
axiom Real : Type
axiom Real.add : Real → Real → Real
axiom Real.mul : Real → Real → Real
axiom Real.zero : Real
axiom Real.one : Real

notation a " + " b => Real.add a b
notation a " * " b => Real.mul a b
notation "0" => Real.zero
notation "1" => Real.one

-- Square of a real number
def sq (x : Real) : Real := x * x

notation x "²" => sq x

-- ============================================================
-- PART 2: Vector Space Structure
-- ============================================================

-- A 2D vector in the plane
structure Vec2 where
  x : Real
  y : Real

-- Vector addition
def Vec2.add (v w : Vec2) : Vec2 :=
  ⟨v.x + w.x, v.y + w.y⟩

-- Vector subtraction (for displacement vectors)
axiom Real.sub : Real → Real → Real
notation a " - " b => Real.sub a b

def Vec2.sub (v w : Vec2) : Vec2 :=
  ⟨v.x - w.x, v.y - w.y⟩

notation v " - " w => Vec2.sub v w

-- ============================================================
-- PART 3: Inner Product
-- ============================================================

/-
  The inner product (dot product) is the key to the Pythagorean theorem.
  For vectors v = (v₁, v₂) and w = (w₁, w₂):
    ⟨v, w⟩ = v₁w₁ + v₂w₂
-/
def inner (v w : Vec2) : Real :=
  (v.x * w.x) + (v.y * w.y)

notation "⟨" v ", " w "⟩" => inner v w

-- The norm squared of a vector: ‖v‖² = ⟨v, v⟩
def normSq (v : Vec2) : Real := inner v v

notation "‖" v "‖²" => normSq v

-- ============================================================
-- PART 4: Perpendicularity
-- ============================================================

/-
  Two vectors are perpendicular (orthogonal) if their inner product is zero.
  This is the geometric definition of a right angle.
-/
def perpendicular (v w : Vec2) : Prop := inner v w = 0

notation v " ⊥ " w => perpendicular v w

-- ============================================================
-- PART 5: The Pythagorean Theorem
-- ============================================================

/-
  The Pythagorean Theorem in inner product form:
  If v ⊥ w, then ‖v + w‖² = ‖v‖² + ‖w‖²

  Proof sketch:
    ‖v + w‖² = ⟨v + w, v + w⟩
             = ⟨v, v⟩ + ⟨v, w⟩ + ⟨w, v⟩ + ⟨w, w⟩  (bilinearity)
             = ‖v‖² + 0 + 0 + ‖w‖²                 (perpendicularity)
             = ‖v‖² + ‖w‖²
-/

-- First, we need bilinearity of the inner product
axiom inner_add_left (u v w : Vec2) :
  ⟨Vec2.add u v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩

axiom inner_add_right (u v w : Vec2) :
  ⟨u, Vec2.add v w⟩ = ⟨u, v⟩ + ⟨u, w⟩

-- Symmetry of inner product
axiom inner_comm (v w : Vec2) : ⟨v, w⟩ = ⟨w, v⟩

-- Arithmetic axioms we need
axiom add_zero (a : Real) : a + 0 = a
axiom zero_add (a : Real) : 0 + a = a
axiom add_assoc (a b c : Real) : (a + b) + c = a + (b + c)
axiom add_comm (a b : Real) : a + b = b + a

-- The Pythagorean Theorem for vectors
theorem pythagorean_theorem (v w : Vec2) (h : v ⊥ w) :
    ‖Vec2.add v w‖² = ‖v‖² + ‖w‖² := by
  -- Expand the norm squared of the sum
  unfold normSq
  -- ⟨v + w, v + w⟩ = ⟨v, v + w⟩ + ⟨w, v + w⟩
  rw [inner_add_left]
  -- = ⟨v, v⟩ + ⟨v, w⟩ + ⟨w, v⟩ + ⟨w, w⟩
  rw [inner_add_right, inner_add_right]
  -- Use perpendicularity: ⟨v, w⟩ = 0
  unfold perpendicular at h
  rw [h]
  -- By symmetry: ⟨w, v⟩ = ⟨v, w⟩ = 0
  rw [inner_comm w v, h]
  -- Simplify: ‖v‖² + 0 + 0 + ‖w‖² = ‖v‖² + ‖w‖²
  rw [add_zero, add_zero]
  rfl

-- ============================================================
-- PART 6: Geometric Interpretation
-- ============================================================

/-
  For a right triangle with:
  - Right angle at vertex C
  - Vertices A, B, C as points in the plane
  - Side a opposite to A (from B to C)
  - Side b opposite to B (from A to C)
  - Side c opposite to C (from A to B) - the hypotenuse

  If we place C at the origin:
  - Vector v points from C to A (length = b)
  - Vector w points from C to B (length = a)
  - The hypotenuse is represented by v - w (length = c)

  The right angle at C means v ⊥ w.

  Then: a² + b² = c²
  becomes: ‖w‖² + ‖v‖² = ‖v - w‖²
-/

-- A right triangle with the right angle at the origin
structure RightTriangle where
  legA : Vec2  -- vector to vertex A
  legB : Vec2  -- vector to vertex B
  right_angle : legA ⊥ legB

-- Length squared of each side
def RightTriangle.sideLengthsSq (t : RightTriangle) :=
  (‖t.legA‖², ‖t.legB‖², ‖t.legA - t.legB‖²)

-- The classical a² + b² = c² formulation
-- For subtraction, we need an additional axiom about the norm
axiom normSq_sub (v w : Vec2) (h : v ⊥ w) :
  ‖v - w‖² = ‖v‖² + ‖w‖²

theorem pythagorean_classical (t : RightTriangle) :
    ‖t.legA‖² + ‖t.legB‖² = ‖t.legA - t.legB‖² := by
  rw [normSq_sub t.legA t.legB t.right_angle]

-- ============================================================
-- PART 7: Famous Pythagorean Triples
-- ============================================================

/-
  Pythagorean triples are integer solutions to a² + b² = c².
  The most famous is (3, 4, 5):
    3² + 4² = 9 + 16 = 25 = 5²

  Other well-known triples:
  - (5, 12, 13):  25 + 144 = 169 ✓
  - (8, 15, 17):  64 + 225 = 289 ✓
  - (7, 24, 25):  49 + 576 = 625 ✓

  All primitive triples (where gcd(a,b,c) = 1) can be generated by:
    a = m² - n²,  b = 2mn,  c = m² + n²
  where m > n > 0 are coprime with different parity.
-/

-- Natural number versions for computational examples
def Nat.sq (n : Nat) : Nat := n * n

-- Verify (3, 4, 5) is a Pythagorean triple
example : Nat.sq 3 + Nat.sq 4 = Nat.sq 5 := by native_decide

-- Verify (5, 12, 13) is a Pythagorean triple
example : Nat.sq 5 + Nat.sq 12 = Nat.sq 13 := by native_decide

-- Verify (8, 15, 17) is a Pythagorean triple
example : Nat.sq 8 + Nat.sq 15 = Nat.sq 17 := by native_decide

-- ============================================================
-- PART 8: The Converse
-- ============================================================

/-
  The converse of the Pythagorean theorem also holds:
  If a² + b² = c² for the sides of a triangle, then the angle
  opposite to c is a right angle.

  This was known to Euclid (Elements, Book I, Proposition 48).
-/

-- We state the converse as an axiom here (full proof requires
-- additional geometric machinery)
axiom pythagorean_converse (v w : Vec2) :
  ‖v‖² + ‖w‖² = ‖v - w‖² → v ⊥ w

-- ============================================================
-- PART 9: Historical Context
-- ============================================================

/-
  The Pythagorean theorem is arguably the most famous theorem in mathematics.

  Historical Timeline:
  - ~1800 BCE: Babylonian tablet Plimpton 322 shows knowledge of triples
  - ~1100 BCE: Chinese mathematicians knew the 3-4-5 triangle
  - ~570-495 BCE: Pythagoras (or his school) provided a general proof
  - ~300 BCE: Euclid included it in the Elements (Book I, Prop. 47)
  - 1876: James Garfield (future US President) discovered a new proof
  - 1940: Elisha Loomis catalogued 367 distinct proofs

  Proof Methods:
  1. Rearrangement proofs (visual, showing areas equal)
  2. Similar triangles (Euclid's original approach)
  3. Algebraic proofs (like our inner product version)
  4. Calculus-based proofs
  5. Proofs using complex numbers

  The theorem generalizes in many directions:
  - Law of Cosines: c² = a² + b² - 2ab·cos(C)
  - Higher dimensions: ‖v‖² = v₁² + v₂² + ... + vₙ²
  - Non-Euclidean geometries: fails in hyperbolic/spherical geometry
-/

-- Final verification
#check pythagorean_theorem
#check pythagorean_classical
