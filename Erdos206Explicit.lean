import StageRecurrence

/-!
# Explicit-example supplement to Erdős #206

This is not a new proof of Kovač's almost-everywhere theorem. The specified
number `ExplicitEgyptian.explicitNumber` is the limit of the concrete executable
rational recurrence in StageRecurrence.lean. The final statement includes its
positive irrationality, failure of eventual greediness under the original
strict/distinct-denominator convention, and a certified approximation modulus.
-/

namespace ExplicitEgyptian

theorem erdos206_explicit_resolution :
    (1/4:ℝ) < explicitNumber ∧ explicitNumber < 1/2 ∧
    Irrational explicitNumber ∧
    ¬ Erdos206.EgyptianFractions.EventuallyGreedy explicitNumber ∧
    ∀ n : ℕ, |explicitNumber - (approximate n : ℝ)| ≤ (1/2:ℝ)^n/2 :=
  ⟨explicitNumber_bounds.1, explicitNumber_bounds.2, explicitNumber_irrational,
    explicitNumber_not_eventuallyGreedy, approximate_error⟩

#print erdos206_explicit_resolution
#print axioms erdos206_explicit_resolution

end ExplicitEgyptian
