import Mathlib

namespace Erdos206

open Set Filter

/-- Rational stage data only; computation of these sequences belongs to the recurrence. -/
structure RationalNestedData where
  lower : ℕ → ℚ
  upper : ℕ → ℚ
  approx : ℕ → ℚ
  lower_le_upper : ∀ n, lower n ≤ upper n
  lower_mono : Monotone lower
  upper_anti : Antitone upper
  width_le : ∀ n, (upper n - lower n : ℚ) ≤ (1 / 2 : ℚ) ^ n
  approx_lt_lower : ∀ n, approx n < lower n
  upper_sub_approx_lt : ∀ n,
    upper n - approx n < 1 / ((approx n).den : ℚ) ^ (n + 2)
  two_le_den : ∀ n, 2 ≤ (approx n).den

noncomputable def RationalNestedData.limit (d : RationalNestedData) : ℝ :=
  ⨆ n, (d.lower n : ℝ)

theorem RationalNestedData.limit_mem (d : RationalNestedData) (n : ℕ) :
    d.limit ∈ Icc (d.lower n : ℝ) (d.upper n : ℝ) := by
  have hl : Monotone (fun n => (d.lower n : ℝ)) := by
    intro a b h
    exact Rat.cast_le.mpr (d.lower_mono h)
  have hu : Antitone (fun n => (d.upper n : ℝ)) := by
    intro a b h
    exact Rat.cast_le.mpr (d.upper_anti h)
  have h : ∀ n, (d.lower n : ℝ) ≤ (d.upper n : ℝ) := by
    intro n
    exact_mod_cast d.lower_le_upper n
  exact mem_iInter.mp (hl.ciSup_mem_iInter_Icc_of_antitone hu h) n

theorem RationalNestedData.mem_unique (d : RationalNestedData) {x y : ℝ}
    (hx : ∀ n, x ∈ Icc (d.lower n : ℝ) (d.upper n : ℝ))
    (hy : ∀ n, y ∈ Icc (d.lower n : ℝ) (d.upper n : ℝ)) : x = y := by
  have hbound : ∀ n, |x-y| ≤ (1/2 : ℝ)^n := by
    intro n
    have hw : (d.upper n : ℝ) - (d.lower n : ℝ) ≤ (1/2 : ℝ)^n := by
      simpa only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
        Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (d.width_le n)
    obtain ⟨hxl, hxu⟩ := hx n
    obtain ⟨hyl, hyu⟩ := hy n
    exact (abs_le.mpr ⟨by linarith, by linarith⟩)
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : |x-y| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht
      (Filter.Eventually.of_forall hbound)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

theorem RationalNestedData.existsUnique_mem (d : RationalNestedData) :
    ∃! x : ℝ, ∀ n, x ∈ Icc (d.lower n : ℝ) (d.upper n : ℝ) := by
  exact ⟨d.limit, d.limit_mem, fun y hy => d.mem_unique hy d.limit_mem⟩

theorem RationalNestedData.midpoint_error (d : RationalNestedData) (n : ℕ) :
    |d.limit - (((d.lower n + d.upper n) / 2 : ℚ) : ℝ)| ≤
      (1/2 : ℝ) ^ n / 2 := by
  obtain ⟨hl, hu⟩ := d.limit_mem n
  have hw : (d.upper n : ℝ) - (d.lower n : ℝ) ≤ (1/2 : ℝ)^n := by
    simpa only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (d.width_le n)
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem RationalNestedData.limit_approx (d : RationalNestedData) (n : ℕ) :
    0 < d.limit - (d.approx n : ℝ) ∧
    d.limit - (d.approx n : ℝ) < 1 / ((d.approx n).den : ℝ) ^ (n + 2) := by
  obtain ⟨hl, hu⟩ := d.limit_mem n
  have ha : (d.approx n : ℝ) < (d.lower n : ℝ) := by
    exact_mod_cast d.approx_lt_lower n
  have hb : (d.upper n : ℝ) - (d.approx n : ℝ) <
      1 / ((d.approx n).den : ℝ) ^ (n + 2) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_natCast] using (Rat.cast_lt (K := ℝ)).mpr (d.upper_sub_approx_lt n)
  constructor <;> linarith

theorem RationalNestedData.limit_liouville (d : RationalNestedData) : Liouville d.limit := by
  intro n
  refine ⟨(d.approx n).num, ((d.approx n).den : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast d.two_le_den n
  · have h := (d.limit_approx n).1
    have hq : ((d.approx n).num : ℝ) / ((d.approx n).den : ℝ) =
        (d.approx n : ℝ) := by
      exact_mod_cast (Rat.num_div_den (d.approx n))
    simpa only [Int.cast_natCast, hq, ne_eq] using ne_of_gt (sub_pos.mp h)
  · have hq : ((d.approx n).num : ℝ) / ((d.approx n).den : ℝ) =
        (d.approx n : ℝ) := by
      exact_mod_cast (Rat.num_div_den (d.approx n))
    simp only [Int.cast_natCast, hq]
    rw [abs_of_pos (d.limit_approx n).1]
    apply lt_of_lt_of_le (d.limit_approx n).2
    have hd : (1 : ℝ) ≤ ((d.approx n).den : ℝ) := by
      have := d.two_le_den n
      exact_mod_cast (show 1 ≤ (d.approx n).den by omega)
    apply one_div_le_one_div_of_le (pow_pos (lt_of_lt_of_le zero_lt_one hd) _)
    exact pow_le_pow_right₀ hd (by omega)

theorem RationalNestedData.limit_irrational (d : RationalNestedData) : Irrational d.limit :=
  d.limit_liouville.irrational

end Erdos206

#print axioms Erdos206.RationalNestedData.existsUnique_mem
#print axioms Erdos206.RationalNestedData.midpoint_error
#print axioms Erdos206.RationalNestedData.limit_irrational
