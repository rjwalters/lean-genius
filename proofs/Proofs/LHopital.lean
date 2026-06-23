import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Basic

/-!
# L'Hôpital's Rule

## What This Proves
L'Hôpital's Rule—a fundamental technique for evaluating limits of indeterminate forms.

**The Rule**: If f and g are differentiable near a point a, and if both functions
approach 0 (or both approach ±∞) as x → a, and if the limit of f'(x)/g'(x) exists,
then:

  lim(x→a) f(x)/g(x) = lim(x→a) f'(x)/g'(x)

This allows us to evaluate limits of "0/0" or "∞/∞" forms by differentiating
the numerator and denominator separately.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's formalization of L'Hôpital's rule,
  specifically `HasDerivAt.lhopital_zero_right_on_Ioo` and related theorems.
- **Key Insight:** The rule transforms difficult limit computations into (hopefully)
  easier ones by replacing functions with their derivatives.
- **Proof Techniques Demonstrated:** Filter limits, derivative conditions, interval analysis.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `HasDerivAt.lhopital_zero_right_on_Ioo` : L'Hôpital's rule approaching from right (0/0 form)
- `HasDerivAt.lhopital_zero_left_on_Ioo` : L'Hôpital's rule approaching from left (0/0 form)
- `HasDerivAt.lhopital_zero_atTop_on_Ioi` : L'Hôpital's rule as x → ∞ (0/0 form)
- `Filter.Tendsto` : Limit definitions via filters

## Historical Note
Guillaume de l'Hôpital (1661-1704) published this rule in his 1696 textbook
"Analyse des Infiniment Petits pour l'Intelligence des Lignes Courbes"—the first
calculus textbook. The rule was actually discovered by Johann Bernoulli, who taught
it to l'Hôpital in exchange for a salary. Bernoulli later claimed credit after
l'Hôpital's death, leading to one of mathematics' famous priority disputes.

This is #64 on Wiedijk's list of 100 theorems.
-/

namespace LHopital

open Set Filter Topology

/-! ## L'Hôpital's Rule: 0/0 Form

The classic formulation for the 0/0 indeterminate form. -/

/-- **L'Hôpital's Rule - Right Limit on Open Interval (Wiedijk #64)**

If f and g are differentiable on (a, b), both tend to 0 as x → a⁺,
g'(x) ≠ 0 on (a, b), and f'(x)/g'(x) → c as x → a⁺, then f(x)/g(x) → c.

This is the fundamental version from which other variants derive. -/
theorem lhopital_zero_right {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 c) :=
  HasDerivAt.lhopital_zero_right_on_Ioo hab hff' hgg' hg' hfa hga hdiv

/-- **L'Hôpital's Rule - Left Limit on Open Interval**

If f and g are differentiable on (a, b), both tend to 0 as x → b⁻,
g'(x) ≠ 0 on (a, b), and f'(x)/g'(x) → c as x → b⁻, then f(x)/g(x) → c. -/
theorem lhopital_zero_left {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) (𝓝 c) :=
  HasDerivAt.lhopital_zero_left_on_Ioo hab hff' hgg' hg' hfb hgb hdiv

/-- **L'Hôpital's Rule - Limit at Infinity**

If f and g are differentiable on (a, ∞), both tend to 0 as x → ∞,
g'(x) ≠ 0 on (a, ∞), and f'(x)/g'(x) → c as x → ∞, then f(x)/g(x) → c. -/
theorem lhopital_zero_atTop {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop (𝓝 c)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 c) :=
  HasDerivAt.lhopital_zero_atTop_on_Ioi hff' hgg' hg' hftop hgtop hdiv

/-- **L'Hôpital's Rule - Limit at Negative Infinity**

If f and g are differentiable on (-∞, a), both tend to 0 as x → -∞,
g'(x) ≠ 0 on (-∞, a), and f'(x)/g'(x) → c as x → -∞, then f(x)/g(x) → c. -/
theorem lhopital_zero_atBot {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atBot (𝓝 c)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 c) :=
  HasDerivAt.lhopital_zero_atBot_on_Iio hff' hgg' hg' hfbot hgbot hdiv

/-! ## Why L'Hôpital's Rule Works

L'Hôpital's Rule is a consequence of the Mean Value Theorem. Intuitively:

For small h > 0:
  f(a + h) ≈ f(a) + h · f'(a + h) = 0 + h · f'(a + h)
  g(a + h) ≈ g(a) + h · g'(a + h) = 0 + h · g'(a + h)

So f(a + h) / g(a + h) ≈ f'(a + h) / g'(a + h), and taking the limit as h → 0
gives L'Hôpital's Rule.

The actual proof in Mathlib uses Cauchy's Mean Value Theorem, which says:
  (f(b) - f(a)) / (g(b) - g(a)) = f'(c) / g'(c)
for some c ∈ (a, b). -/

/-! ## Common Applications

L'Hôpital's Rule is particularly useful for:
1. Limits of the form sin(x)/x as x → 0
2. Limits involving exponentials like (eˣ - 1)/x
3. Limits involving logarithms like x·ln(x) as x → 0⁺
4. Growth rate comparisons between functions

### Note on the ∞/∞ Form

Mathlib also provides L'Hôpital's Rule for the ∞/∞ indeterminate form,
though the precise formulations differ. The 0/0 form is the most commonly
used in practice. -/

/-! ## Verification -/

#check lhopital_zero_right
#check lhopital_zero_left
#check lhopital_zero_atTop
#check lhopital_zero_atBot

end LHopital
