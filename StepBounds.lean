import LocalObstruction

/-! Executable rational interval updates for the #206 explicit-example supplement. -/

namespace Erdos206.EgyptianFractions

def badLowerQ (i : ℕ) : ℚ :=
  1 / (i+1:ℕ) + 1 / (i*(i+1)/2+1:ℕ)

def badUpperQ (i : ℕ) : ℚ :=
  1 / (i:ℚ) + 1 / (i*(i+1)+4:ℕ)

@[simp] theorem badLowerQ_cast (i : ℕ) : (badLowerQ i : ℝ) = badLower i := by
  simp [badLowerQ, badLower]

@[simp] theorem badUpperQ_cast (i : ℕ) : (badUpperQ i : ℝ) = badUpper i := by
  simp [badUpperQ, badUpper]

lemma bad_intervalQ_positive_small (i : ℕ) (hi : 4 ≤ i) :
    0 < badLowerQ i ∧ badLowerQ i < badUpperQ i ∧ badUpperQ i < 2/(i:ℚ) := by
  have h := bad_interval_positive_small i hi
  rw [← badLowerQ_cast i, ← badUpperQ_cast i] at h
  constructor
  · exact_mod_cast h.1
  constructor
  · exact_mod_cast h.2.1
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using h.2.2

/-- An explicit oversized integer; no minimization or unbounded search. -/
def stepIndex (s M : ℕ) (q z : ℚ) : ℕ :=
  M + 4 + ⌈2/(z-q)⌉₊ + 2^(s+2) + 2*q.den^(s+2) + 1

def stepLower (s M : ℕ) (q z : ℚ) : ℚ :=
  q + (2 * badLowerQ (stepIndex s M q z) + badUpperQ (stepIndex s M q z))/3

def stepUpper (s M : ℕ) (q z : ℚ) : ℚ :=
  q + (badLowerQ (stepIndex s M q z) + 2 * badUpperQ (stepIndex s M q z))/3

theorem stepIndex_bounds (s M : ℕ) (q z : ℚ) :
    4 ≤ stepIndex s M q z ∧ M < stepIndex s M q z ∧
    ⌈2/(z-q)⌉₊ < stepIndex s M q z ∧
    2^(s+2) < stepIndex s M q z ∧
    2*q.den^(s+2) < stepIndex s M q z := by
  unfold stepIndex
  generalize 2^(s+2) = p
  generalize q.den^(s+2) = d
  omega

lemma den_two_le_of_between_zero_one (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    2 ≤ q.den := by
  by_contra h
  have hd : q.den = 1 := by have := q.den_pos; omega
  have heq := Rat.coe_int_num_of_den_eq_one hd
  have hn0 : (0:ℤ) < q.num := by exact_mod_cast (show (0:ℚ) < q.num by linarith)
  have hn1 : q.num < (1:ℤ) := by exact_mod_cast (show (q.num:ℚ) < 1 by linarith)
  omega

theorem step_reciprocal_bounds (s M : ℕ) (q z : ℚ) (hqz : q < z) :
    2/(stepIndex s M q z:ℚ) < z-q ∧
    2/(stepIndex s M q z:ℚ) < 1/(q.den:ℚ)^(s+2) ∧
    2/(stepIndex s M q z:ℚ) < (1/2:ℚ)^s := by
  obtain ⟨hi, _, hc, hp, hd⟩ := stepIndex_bounds s M q z
  have hiq : (0:ℚ) < stepIndex s M q z := by exact_mod_cast (show 0 < stepIndex s M q z by omega)
  have hgap : (0:ℚ) < z-q := sub_pos.mpr hqz
  have hceil : (2:ℚ)/(z-q) < stepIndex s M q z :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hc)
  have hden : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
  refine ⟨?_, ?_, ?_⟩
  · apply (div_lt_iff₀ hiq).mpr
    have := (div_lt_iff₀ hgap).mp hceil
    nlinarith
  · apply (div_lt_div_iff₀ hiq (pow_pos hden _)).mpr
    have hcast : (2:ℚ)*(q.den:ℚ)^(s+2) < stepIndex s M q z := by exact_mod_cast hd
    simpa using hcast
  · rw [div_pow, one_pow]
    apply (div_lt_div_iff₀ hiq (pow_pos (by norm_num : (0:ℚ)<2) _)).mpr
    have hcast : (2:ℚ)^(s+2) < stepIndex s M q z := by exact_mod_cast hp
    rw [pow_add] at hcast
    norm_num at hcast
    have : (0:ℚ) < 2^s := by positivity
    nlinarith

/-- All interval and approximation properties required of one explicit stage. -/
theorem step_bounds (s M : ℕ) (L q z U : ℚ)
    (hL : 1/4 ≤ L) (hLq : L < q) (hqz : q < z) (hzU : z < U) (hU : U ≤ 1/2) :
    4 ≤ stepIndex s M q z ∧ M < stepIndex s M q z ∧
    L < stepLower s M q z ∧
    stepLower s M q z < stepUpper s M q z ∧
    stepUpper s M q z < z ∧ z < U ∧
    q < stepLower s M q z ∧
    stepUpper s M q z-q < 1/(q.den:ℚ)^(s+2) ∧
    stepUpper s M q z-stepLower s M q z ≤ (1/2:ℚ)^s ∧
    2 ≤ q.den ∧
    q+badLowerQ (stepIndex s M q z) < stepLower s M q z ∧
    stepUpper s M q z < q+badUpperQ (stepIndex s M q z) := by
  obtain ⟨hi, hM, _⟩ := stepIndex_bounds s M q z
  obtain ⟨hu0, huv, hv⟩ := bad_intervalQ_positive_small (stepIndex s M q z) hi
  obtain ⟨hgap, hden, hwidth⟩ := step_reciprocal_bounds s M q z hqz
  have hd : 2 ≤ q.den := den_two_le_of_between_zero_one q (by linarith) (by linarith)
  unfold stepLower stepUpper
  refine ⟨hi, hM, ?_, ?_, ?_, hzU, ?_, ?_, ?_, hd, ?_, ?_⟩ <;> linarith

#print axioms step_bounds

end Erdos206.EgyptianFractions
