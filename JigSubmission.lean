import Erdos206Explicit

/-!
Submission wrapper for Jig's canonical statement. The existential witnesses are
the concrete real and executable rational approximation function defined in
`StageRecurrence.lean`; they are not chosen nonconstructively here.
-/

namespace Submissions.Erdos206ExplicitWitness.Coleski

open scoped BigOperators

noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  S.sum (fun m => (1 : ℝ) / m)

def ValidEgyptian (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, 0 < m

def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  ValidEgyptian S ∧ egyptianSum S < x

def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x →
      egyptianSum T ≤ egyptianSum S

def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x

theorem proof :
    ∃ (x : ℝ) (approximate : ℕ → ℚ),
      (1 / 4 : ℝ) < x ∧ x < 1 / 2 ∧ Irrational x ∧
      ¬ EventuallyGreedy x ∧
      ∀ n : ℕ, |x - (approximate n : ℝ)| ≤ (1 / 2 : ℝ) ^ n / 2 := by
  refine ⟨ExplicitEgyptian.explicitNumber, ExplicitEgyptian.approximate, ?_⟩
  have h := ExplicitEgyptian.erdos206_explicit_resolution
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  simpa [EventuallyGreedy, IsBestNTerm, IsUnderapprox, ValidEgyptian, egyptianSum,
    Erdos206.EgyptianFractions.EventuallyGreedy,
    Erdos206.EgyptianFractions.IsBestNTerm,
    Erdos206.EgyptianFractions.IsUnderapprox,
    Erdos206.EgyptianFractions.ValidEgyptian,
    Erdos206.EgyptianFractions.egyptianSum] using h.2.2.2.1

#print axioms proof

end Submissions.Erdos206ExplicitWitness.Coleski
