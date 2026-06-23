/-
# The Angle-Defect Condition Is Necessary but Not Sufficient for Archimedean Solids

The parent classification (`PlatonicSolidsOQ02.lean`) verifies that all 13
Archimedean vertex types have *positive angle defect* — the regular polygons
meeting at a vertex leave an angular gap (their interior angles sum to strictly
less than `2π`). It leaves open:

> **Open question.** Can the angle constraint alone (without geometric analysis)
> determine the 13 Archimedean types?

This file answers that question: **No.** The positive-defect condition is a
genuine *necessary* condition with real combinatorial force — it caps the number
of faces meeting at a vertex at five (`degree_le_five`) — but it is far from
*sufficient*. We exhibit an infinite family of vertex types `[3, 3, n]` that
each satisfy positive defect yet are non-uniform and absent from the 13. Hence:

* The defect condition admits **infinitely many** vertex types
  (`infinitely_many_positiveDefect`).
* Even after excluding the Platonic (uniform) types and the 13 Archimedean
  types, infinitely many positive-defect configurations remain
  (`infinitely_many_nonArchimedean_positiveDefect`).

So no purely angular/combinatorial criterion at the level of a single vertex can
single out the 13: the missing ingredient is exactly the *global geometric
realizability* (convex closure) that the angle condition cannot see.

Everything here is over `ℚ` and proved with `norm_num` / `nlinarith` /
`induction` — no `native_decide`, hence genuinely axiom-free (only the standard
`propext` / `Classical.choice` / `Quot.sound`).
-/
import Mathlib.Tactic

namespace ArchimedeanAngleDefect

-- ============================================================
-- Section 1: The Angle Model (over ℚ)
-- ============================================================

/-- Interior angle of a regular `n`-gon, measured in units of `π`:
    `(n - 2)/n = 1 - 2/n`. (A triangle: `1/3`; a square: `1/2`; → `1` as
    `n → ∞`.) -/
def angleFrac (n : ℕ) : ℚ := 1 - 2 / (n : ℚ)

/-- Total angle (in units of `π`) of the regular polygons meeting at a vertex
    whose face sizes are `faces`. -/
def vertexAngleSum (faces : List ℕ) : ℚ := (faces.map angleFrac).sum

/-- A vertex has **positive angle defect** when its faces leave a gap, i.e. the
    interior angles sum to strictly less than `2π` (`< 2` in units of `π`). -/
def PositiveDefect (faces : List ℕ) : Prop := vertexAngleSum faces < 2

/-- The interior angle of any regular polygon (`n ≥ 3`) is at least that of an
    equilateral triangle, `1/3` of `π`. This is the key monotonicity fact. -/
theorem angleFrac_ge_third {n : ℕ} (hn : 3 ≤ n) : (1 : ℚ) / 3 ≤ angleFrac n := by
  have hn' : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < (n : ℚ) := by linarith
  set t : ℚ := 2 / (n : ℚ) with ht
  have htn : t * (n : ℚ) = 2 := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hle : t ≤ 2 / 3 := by
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℚ) ≤ (n : ℚ) - 3)]
  unfold angleFrac
  rw [← ht]
  linarith

-- ============================================================
-- Section 2: The Necessary Direction — Degree Is at Most Five
-- ============================================================

/-- Generic list bound: if `f n ≥ c` for every entry, then `Σ f ≥ (length)·c`. -/
theorem list_sum_lb (f : ℕ → ℚ) (c : ℚ) :
    ∀ (l : List ℕ), (∀ n ∈ l, c ≤ f n) → (l.length : ℚ) * c ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a (by simp)
    have ht := ih (fun n hn => h n (by simp [hn]))
    push_cast
    nlinarith [ha, ht]

/-- If every face has at least three sides, the angle sum is bounded below by
    `(degree) · (1/3)`: each face contributes at least a triangle's angle. -/
theorem vertexAngleSum_ge (faces : List ℕ) (hreg : ∀ n ∈ faces, 3 ≤ n) :
    (faces.length : ℚ) * (1 / 3) ≤ vertexAngleSum faces :=
  list_sum_lb angleFrac (1 / 3) faces (fun n hn => angleFrac_ge_third (hreg n hn))

/-- **Degree bound (necessary condition).** At most five regular polygons can
    meet at a vertex with positive angle defect. (Six equilateral triangles
    already tile flatly: angle sum exactly `2`.) -/
theorem degree_le_five (faces : List ℕ) (hreg : ∀ n ∈ faces, 3 ≤ n)
    (hdef : PositiveDefect faces) : faces.length ≤ 5 := by
  have hlb := vertexAngleSum_ge faces hreg
  unfold PositiveDefect at hdef
  have hlt : (faces.length : ℚ) * (1 / 3) < 2 := lt_of_le_of_lt hlb hdef
  have h6 : (faces.length : ℚ) < 6 := by linarith
  have : faces.length < 6 := by exact_mod_cast h6
  omega

-- ============================================================
-- Section 3: The 13 Archimedean Types All Satisfy It (axiom-free)
-- ============================================================

/-- The 13 Archimedean vertex types (same data as the parent file). -/
def archimedeanTypes : List (List ℕ) :=
  [[3, 6, 6], [3, 4, 3, 4], [3, 8, 8], [4, 6, 6], [3, 4, 4, 4], [4, 6, 8],
   [3, 3, 3, 3, 4], [3, 5, 3, 5], [3, 10, 10], [5, 6, 6], [3, 4, 5, 4],
   [4, 6, 10], [3, 3, 3, 3, 5]]

/-- All 13 Archimedean vertex types have positive angle defect — re-proved here
    with `norm_num` over `ℚ`, replacing the parent's `native_decide`
    (which depends on `Lean.ofReduceBool`). -/
theorem all_archimedean_positiveDefect :
    ∀ v ∈ archimedeanTypes, PositiveDefect v := by
  intro v hv
  simp only [archimedeanTypes, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (subst h
     unfold PositiveDefect vertexAngleSum angleFrac
     simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
     norm_num)

-- ============================================================
-- Section 4: Insufficiency — An Infinite Family Passes the Test
-- ============================================================

/-- The witness family: two triangles and one `n`-gon meet at a vertex. -/
def family (k : ℕ) : List ℕ := [3, 3, k + 4]

/-- Every member of the family has positive angle defect: its angle sum is
    `5/3 - 2/n`, which is `< 2` for all `n ≥ 3` (indeed it is `< 5/3`). -/
theorem family_positiveDefect {n : ℕ} (hn : 3 ≤ n) : PositiveDefect [3, 3, n] := by
  unfold PositiveDefect vertexAngleSum angleFrac
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have hge : (0 : ℚ) ≤ 2 / (n : ℚ) := by positivity
  nlinarith [hge]

/-- The family is injective in `k`, so it has infinitely many distinct members. -/
theorem family_injective : Function.Injective family := by
  intro a b hab
  simp only [family, List.cons.injEq, and_true, true_and] at hab
  omega

/-- No member of the family is one of the 13 Archimedean types: every length-3
    Archimedean type has a face of size `≥ 6` in its second slot, whereas the
    family's second face is a triangle. -/
theorem family_not_archimedean (k : ℕ) : family k ∉ archimedeanTypes := by
  simp [family, archimedeanTypes]

/-- A vertex type is **uniform** (Platonic) when all its faces are congruent. -/
def IsUniform (faces : List ℕ) : Prop := ∀ a ∈ faces, ∀ b ∈ faces, a = b

/-- No member of the family is uniform: it pairs a triangle with an `(k+4)`-gon,
    and `k + 4 ≠ 3`. -/
theorem family_not_uniform (k : ℕ) : ¬ IsUniform (family k) := by
  intro h
  have : (3 : ℕ) = k + 4 :=
    h 3 (by simp [family]) (k + 4) (by simp [family])
  omega

-- ============================================================
-- Section 5: The Answer — Infinitely Many Non-Archimedean Witnesses
-- ============================================================

/-- **Insufficiency, basic form.** Infinitely many vertex types satisfy the
    positive-defect condition. A finite list (the 13) can never be carved out by
    this condition alone. -/
theorem infinitely_many_positiveDefect :
    {v : List ℕ | PositiveDefect v}.Infinite :=
  Set.infinite_of_injective_forall_mem family_injective
    (fun k => by
      show PositiveDefect [3, 3, k + 4]
      exact family_positiveDefect (by omega))

/-- **Insufficiency, sharp form — the answer to the open question.** Even after
    excluding the Platonic (uniform) types *and* the 13 Archimedean types,
    infinitely many vertex types still satisfy positive angle defect. Therefore
    the angle constraint alone — at the level of a single vertex — cannot
    determine the 13 Archimedean solids; the decisive missing ingredient is the
    global geometric realizability that the angle sum cannot detect. -/
theorem infinitely_many_nonArchimedean_positiveDefect :
    {v : List ℕ |
        PositiveDefect v ∧ ¬ IsUniform v ∧ v ∉ archimedeanTypes}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := family) family_injective
  intro k
  refine ⟨?_, family_not_uniform k, family_not_archimedean k⟩
  show PositiveDefect [3, 3, k + 4]
  exact family_positiveDefect (by omega)

/-- Two concrete smallest witnesses, `[3,3,4]` and `[3,3,5]`: both have positive
    defect, neither is among the 13 Archimedean types nor uniform. -/
theorem concrete_witnesses :
    (PositiveDefect [3, 3, 4] ∧ [3, 3, 4] ∉ archimedeanTypes ∧ ¬ IsUniform [3, 3, 4]) ∧
    (PositiveDefect [3, 3, 5] ∧ [3, 3, 5] ∉ archimedeanTypes ∧ ¬ IsUniform [3, 3, 5]) := by
  refine ⟨⟨family_positiveDefect (by norm_num), ?_, ?_⟩,
          ⟨family_positiveDefect (by norm_num), ?_, ?_⟩⟩
  · have := family_not_archimedean 0; simpa [family] using this
  · have := family_not_uniform 0; simpa [family] using this
  · have := family_not_archimedean 1; simpa [family] using this
  · have := family_not_uniform 1; simpa [family] using this

end ArchimedeanAngleDefect
