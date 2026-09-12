import PriorErdos206

namespace ExplicitEgyptian

open Erdos206.EgyptianFractions

theorem best_sum_above_of_bound (L z : ℝ) (hL : 0 < L) (hLz : L < z)
    (hz : z < 1) (t : ℕ) (ht : 2 ≤ t)
    (hbound : 1 / (z - L) < (t : ℝ))
    (S : Finset ℕ) (hS : IsBestNTerm S t z) :
    L < egyptianSum S := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hdelta : 0 < z - L := sub_pos.mpr hLz
  have h1 : harmonicNumber 1 = 1 := by norm_num [harmonicNumber]
  have hH : 1 ≤ harmonicNumber t := by
    rw [← h1]
    exact harmonicNumber_mono (by omega)
  have hgap := best_sum_gap_bound t ht z (lt_trans hL hLz)
    (le_trans (le_of_lt hz) hH) S hS
  have hmul : 1 < (z - L) * t := by
    have := (div_lt_iff₀ hdelta).mp hbound
    nlinarith
  have hprod : (z - L) * t ≤ (z - L) * (t * (t + 1)) := by
    have hp := mul_pos hdelta htpos
    nlinarith
  have hfrac : 1 / ((t : ℝ) * (t + 1)) < z - L := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < t * (t + 1))).mpr
    exact lt_of_lt_of_le hmul hprod
  linarith

def densityCutoff (N : ℕ) (L z : ℚ) : ℕ :=
  N + ⌈1 / (z - L)⌉₊ + 2

theorem densityCutoff_ge (N : ℕ) (L z : ℚ) : N ≤ densityCutoff N L z := by
  unfold densityCutoff
  omega

theorem densityCutoff_two (N : ℕ) (L z : ℚ) : 2 ≤ densityCutoff N L z := by
  unfold densityCutoff
  omega

theorem densityCutoff_bound (N : ℕ) (L z : ℚ) :
    1 / ((z : ℝ) - L) < (densityCutoff N L z : ℝ) := by
  have hc : (1 : ℚ) / (z - L) ≤ (⌈1 / (z - L)⌉₊ : ℚ) := Nat.le_ceil _
  have hq : (1 : ℚ) / (z - L) < (densityCutoff N L z : ℚ) := by
    unfold densityCutoff
    push_cast
    have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith
  exact_mod_cast hq

theorem best_sum_above_at_cutoff (N : ℕ) (L z : ℚ)
    (hL : 0 < L) (hLz : L < z) (hz : z < 1)
    (S : Finset ℕ) (hS : IsBestNTerm S (densityCutoff N L z) z) :
    (L : ℝ) < egyptianSum S := by
  exact best_sum_above_of_bound L z (by exact_mod_cast hL)
    (by exact_mod_cast hLz) (by exact_mod_cast hz) _
    (densityCutoff_two N L z) (densityCutoff_bound N L z) S hS

theorem exists_large_best_above (N : ℕ) (L z : ℚ)
    (hL : 0 < L) (hLz : L < z) (hz : z < 1) :
    ∃ t : ℕ, N ≤ t ∧ ∀ S : Finset ℕ,
      IsBestNTerm S t z → (L : ℝ) < egyptianSum S := by
  exact ⟨densityCutoff N L z, densityCutoff_ge N L z,
    fun S hS => best_sum_above_at_cutoff N L z hL hLz hz S hS⟩

end ExplicitEgyptian
