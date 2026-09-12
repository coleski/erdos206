import StageRecurrence

namespace IndependentErdos206Audit

open ExplicitEgyptian Erdos206.EgyptianFractions

/-- Failure is not caused by nonexistence of optimal sums at the constructed real. -/
theorem all_optimal_sums_exist (n : ℕ) :
    ∃ S : Finset ℕ, IsBestNTerm S n explicitNumber :=
  exists_bestNTerm n explicitNumber
    (lt_trans (by norm_num : (0:ℝ)<1/4) explicitNumber_bounds.1)

/-- The candidate negation expanded into the original universal-sequence quantifiers. -/
theorem full_sequence_target :
    ∀ m : ℕ → ℕ, StrictMono m → (∀ k, 0 < m k) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        ¬ IsBestNTerm (Finset.image m (Finset.range n)) n explicitNumber := by
  intro m hm hp N
  by_contra h
  push Not at h
  apply explicitNumber_not_eventuallyGreedy
  refine ⟨lt_trans (by norm_num : (0:ℝ)<1/4) explicitNumber_bounds.1,
    m, hm, hp, N, ?_⟩
  exact h

/-- Independent statement of the complete individual example, not a supplied interval hypothesis. -/
theorem particular_irrational_example :
    0 < explicitNumber ∧ Irrational explicitNumber ∧
    ∀ m : ℕ → ℕ, StrictMono m → (∀ k, 0 < m k) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        ¬ IsBestNTerm (Finset.image m (Finset.range n)) n explicitNumber := by
  exact ⟨lt_trans (by norm_num : (0:ℝ)<1/4) explicitNumber_bounds.1,
    explicitNumber_irrational, full_sequence_target⟩

/-- This compiles as executable code; it does not evaluate the expensive stages here. -/
def rationalApproximationProgram (n : ℕ) : ℚ := approximate n

theorem approximation_certificate (n : ℕ) :
    |explicitNumber - (rationalApproximationProgram n : ℝ)| ≤ (1/2:ℝ)^n/2 :=
  approximate_error n

#print axioms particular_irrational_example
#print axioms approximation_certificate
#print axioms all_optimal_sums_exist

end IndependentErdos206Audit
