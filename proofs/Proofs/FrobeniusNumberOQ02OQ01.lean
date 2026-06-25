import Mathlib
import Proofs.FrobeniusNumber
import Proofs.FrobeniusNumberOQ01OQ03
import Proofs.FrobeniusNumberOQ01OQ03OQ01

/-
# Apéry sets and the Kunz symmetry criterion for numerical semigroups

`frobenius-number-oq-02-oq-01`. Building on the generator-agnostic numerical
semigroup infrastructure of `FrobeniusNumberOQ01OQ03OQ01`
(`IsNumericalSemigroup`, `IsFrobeniusNumber`, `IsSymmetric`), this file
introduces the **Apéry set** and proves two foundational, fully machine-checked
results about it.

For a numerical semigroup `S` and a nonzero `m ∈ S`, the Apéry set is
  `Ap(S, m) = { s ∈ S : s − m ∉ S }`
(with `s − m` read over `ℤ`, so `0 ∈ Ap(S, m)` always). It selects, in each
residue class mod `m`, the *smallest* element of `S` — a finite certificate of
the whole semigroup, central to Kunz's (1970) coordinate description.

## Results

* `InApery` — the Apéry-set membership predicate, with the `ℤ`-subtraction
  encoded faithfully in `ℕ` as `s < m ∨ s − m ∉ S`.
* `mem_iff_exists_apery` — **the Apéry covering theorem**: `n ∈ S` iff `n = w + j·m`
  for some Apéry element `w` and some `j : ℕ`. The forward direction selects the
  minimal element of `S` in `n`'s residue class via `Nat.find`; the converse is
  closure under adding `m`. This is the structural backbone of Apéry theory.
* `frobenius_add_m_inApery` — the Frobenius number's mirror `g + m` is the
  largest Apéry element.
* `inApery_le_frobenius_add_m` — every Apéry element is `≤ g + m`.
* `apery_mirror_of_isSymmetric` — **one direction of Kunz's symmetry criterion**:
  if `S` is symmetric then its Apéry set is closed under the involution
  `w ↦ (g + m) − w`. Concretely, `S` symmetric ⟹ `Ap(S, m)` is symmetric about
  its top element `g + m`.

## Scope (honest statement)

The *converse* of Kunz's criterion — Apéry-mirror-symmetry ⟹ `S` symmetric, and
the explicit ≥ 3-generator Kunz-coordinate characterization sought by the parent
problem — is **not** proved here; it requires relating an arbitrary `k ≤ g` to
the Apéry decomposition of its class and remains open. What is established is the
Apéry set itself, its covering theorem, and the forward symmetry implication —
genuine, reusable Apéry/Kunz infrastructure that the gallery did not previously
have.
-/

namespace FrobeniusNumberOQ02OQ01

open FrobeniusNumberOQ01OQ03OQ01

open scoped Classical

variable {S : Set ℕ} {m g w : ℕ}

/-- **Apéry-set membership.** `s` lies in the Apéry set `Ap(S, m)` when `s ∈ S`
and `s − m ∉ S`, where the difference is taken over `ℤ`: in `ℕ` this is `s < m`
(so `s − m < 0 ∉ S`) or `s − m ∉ S`. In particular `0 ∈ Ap(S, m)` whenever
`0 < m`. -/
def InApery (S : Set ℕ) (m s : ℕ) : Prop :=
  s ∈ S ∧ (s < m ∨ s - m ∉ S)

/-- `0` is always an Apéry element (for `m > 0`). -/
theorem zero_inApery (h0 : 0 ∈ S) (hm : 0 < m) : InApery S m 0 :=
  ⟨h0, Or.inl hm⟩

/-- Adding any multiple of `m ∈ S` to a semigroup element stays in `S`. -/
theorem add_mul_mem (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hm : m ∈ S)
    (hw : w ∈ S) (j : ℕ) : w + j * m ∈ S := by
  induction j with
  | zero => simpa using hw
  | succ k ih =>
    have : w + (k + 1) * m = (w + k * m) + m := by ring
    rw [this]
    exact hadd _ ih _ hm

/-- **Apéry covering theorem.** `n ∈ S` if and only if `n = w + j·m` for some
Apéry element `w ∈ Ap(S, m)` and some `j : ℕ`. The forward direction takes `w`
to be the least element of `S` in `n`'s residue class mod `m` (via `Nat.find`),
which is automatically an Apéry element; the converse is closure under adding
`m`. This expresses every semigroup element through the finite Apéry data. -/
theorem mem_iff_exists_apery (hS : IsNumericalSemigroup S) (hm : m ∈ S)
    (hmpos : 0 < m) (n : ℕ) :
    n ∈ S ↔ ∃ w, InApery S m w ∧ ∃ j, n = w + j * m := by
  constructor
  · intro hn
    have hP : ∃ s, s ∈ S ∧ s % m = n % m := ⟨n, hn, rfl⟩
    obtain ⟨hwS, hwmod⟩ := Nat.find_spec hP
    set w := Nat.find hP with hwdef
    have hwle : w ≤ n := Nat.find_le ⟨hn, rfl⟩
    -- `w` is an Apéry element: if `w - m ∈ S` (with `m ≤ w`) it would be a
    -- strictly smaller element of `S` in the same class, contradicting minimality.
    have hap : InApery S m w := by
      refine ⟨hwS, ?_⟩
      by_cases hlt : w < m
      · exact Or.inl hlt
      · right
        intro hcontra
        have hmw : m ≤ w := not_lt.mp hlt
        have hmod : (w - m) % m = n % m := by
          calc (w - m) % m = ((w - m) + m) % m := (Nat.add_mod_right (w - m) m).symm
            _ = w % m := by rw [Nat.sub_add_cancel hmw]
            _ = n % m := hwmod
        exact Nat.find_min hP (show w - m < w by omega) ⟨hcontra, hmod⟩
    -- `w ≤ n` with `w ≡ n (mod m)` gives `m ∣ n - w`, hence `n = w + j·m`.
    have hdvd : m ∣ n - w := (Nat.modEq_iff_dvd' hwle).mp hwmod
    obtain ⟨j, hj⟩ := hdvd
    exact ⟨w, hap, j, by rw [Nat.mul_comm]; omega⟩
  · rintro ⟨w, ⟨hwS, _⟩, j, rfl⟩
    exact add_mul_mem hS.2.1 hm hwS j

/-- The mirror `g + m` of the Frobenius number is an Apéry element: it lies in
`S` (being `> g`) while `(g + m) − m = g ∉ S`. It is the *largest* Apéry
element, the top of the Apéry set's symmetry. -/
theorem frobenius_add_m_inApery (hg : IsFrobeniusNumber S g) (hmpos : 0 < m) :
    InApery S m (g + m) := by
  refine ⟨hg.2 (g + m) (by omega), Or.inr ?_⟩
  rw [Nat.add_sub_cancel]
  exact hg.1

/-- Every Apéry element is `≤ g + m`: its predecessor `w - m` is a gap, hence
`≤ g`. So `g + m` indeed bounds the Apéry set. -/
theorem inApery_le_frobenius_add_m (hg : IsFrobeniusNumber S g)
    (h : InApery S m w) : w ≤ g + m := by
  obtain ⟨_, hcond⟩ := h
  by_cases hmw : m ≤ w
  · -- `w - m ∉ S` (since `m ≤ w` rules out `w < m`), so `w - m ≤ g`.
    have hsub : w - m ∉ S := by
      rcases hcond with h1 | h2
      · exact absurd h1 (not_lt.mpr hmw)
      · exact h2
    have : w - m ≤ g := by
      by_contra hgt
      exact hsub (hg.2 (w - m) (by omega))
    omega
  · omega

/-- **Kunz symmetry criterion (forward direction).** If `S` is symmetric with
Frobenius number `g`, then its Apéry set `Ap(S, m)` is closed under the
involution `w ↦ (g + m) − w`. Equivalently, the Apéry set is symmetric about its
top element `g + m`. This is the elementary, generator-agnostic half of Kunz's
characterization of symmetric numerical semigroups via Apéry sets. -/
theorem apery_mirror_of_isSymmetric (hg : IsFrobeniusNumber S g)
    (hsym : IsSymmetric S g) (_hmpos : 0 < m) (h : InApery S m w) :
    InApery S m (g + m - w) := by
  have hwle : w ≤ g + m := inApery_le_frobenius_add_m hg h
  obtain ⟨hwS, hcond⟩ := h
  refine ⟨?_, ?_⟩
  · -- `(g + m) - w ∈ S`.
    by_cases hwm : w < m
    · -- Then `(g + m) - w > g`, so it is in `S`.
      exact hg.2 _ (by omega)
    · -- `m ≤ w`: the gap `w - m ≤ g` mirrors under symmetry to `g + m - w ∈ S`.
      have hmw : m ≤ w := not_lt.mp hwm
      have hsub : w - m ∉ S := by
        rcases hcond with h1 | h2
        · exact absurd h1 (not_lt.mpr hmw)
        · exact h2
      have hsuble : w - m ≤ g := by
        by_contra hgt
        exact hsub (hg.2 (w - m) (by omega))
      have hsymwm := hsym (w - m) hsuble
      have hin : g - (w - m) ∈ S := by
        by_contra hc
        exact hsub (hsymwm.mpr hc)
      have heq : g - (w - m) = g + m - w := by omega
      rwa [heq] at hin
  · -- Apéry condition for `(g + m) - w`.
    by_cases hwg : w ≤ g
    · -- `(g + m - w) - m = g - w`, and `w ∈ S` with `w ≤ g` forces `g - w ∉ S`.
      right
      have heq : (g + m - w) - m = g - w := by omega
      rw [heq]
      exact (hsym w hwg).mp hwS
    · -- `w > g` gives `(g + m) - w < m`.
      left
      omega

end FrobeniusNumberOQ02OQ01
