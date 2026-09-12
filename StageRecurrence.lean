import RationalOptimizer
import Density
import StepBounds
import NestedIntervals

namespace ExplicitEgyptian

open Erdos206 Erdos206.EgyptianFractions

/-- All data fields are rational or natural; invariant fields are erased proofs. -/
structure IntervalState where
  lower : ℚ
  upper : ℚ
  level : ℕ
  quarter_le : 1/4 ≤ lower
  lower_lt_upper : lower < upper
  upper_le_half : upper ≤ 1/2

def initialState : IntervalState where
  lower := 1/4
  upper := 1/2
  level := 0
  quarter_le := by norm_num
  lower_lt_upper := by norm_num
  upper_le_half := by norm_num

def middle (a : IntervalState) : ℚ := (a.lower + a.upper)/2

theorem middle_bounds (a : IntervalState) :
    0 < a.lower ∧ a.lower < middle a ∧ middle a < a.upper ∧ middle a < 1 := by
  have := a.quarter_le
  have := a.lower_lt_upper
  have := a.upper_le_half
  unfold middle
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

def nextLevel (a : IntervalState) : ℕ :=
  densityCutoff (a.level + 1) a.lower (middle a)

def nextBest (a : IntervalState) : Finset ℕ :=
  optimize (nextLevel a) 0 (middle a)

def nextQ (a : IntervalState) : ℚ := qsum (nextBest a)

theorem nextBest_best (a : IntervalState) :
    IsBestNTerm (nextBest a) (nextLevel a) (middle a) := by
  apply optimize_isBestNTerm
  linarith [(middle_bounds a).1, (middle_bounds a).2.1]

theorem nextQ_bounds (a : IntervalState) : a.lower < nextQ a ∧ nextQ a < middle a := by
  have hb := nextBest_best a
  have hlow := best_sum_above_at_cutoff (a.level+1) a.lower (middle a)
    (middle_bounds a).1 (middle_bounds a).2.1 (middle_bounds a).2.2.2
    (nextBest a) hb
  have hhigh := hb.2.1.2
  have hcast : ((nextQ a : ℚ) : ℝ) = egyptianSum (nextBest a) := by
    exact cast_qsum _
  constructor
  · exact_mod_cast (show (a.lower : ℝ) < (nextQ a : ℝ) by rw [hcast]; exact hlow)
  · exact_mod_cast (show (nextQ a : ℝ) < (middle a : ℝ) by rw [hcast]; exact hhigh)

def nextMax (a : IntervalState) : ℕ := (nextBest a).sup id

theorem nextBest_le_max (a : IntervalState) (m : ℕ) (hm : m ∈ nextBest a) :
    m ≤ nextMax a := Finset.le_sup (f := id) hm

theorem nextLevel_gt (a : IntervalState) : a.level < nextLevel a := by
  have := densityCutoff_ge (a.level+1) a.lower (middle a)
  change a.level < densityCutoff (a.level+1) a.lower (middle a)
  omega

def nextState (s : ℕ) (a : IntervalState) : IntervalState where
  lower := stepLower s (nextMax a) (nextQ a) (middle a)
  upper := stepUpper s (nextMax a) (nextQ a) (middle a)
  level := nextLevel a
  quarter_le := by
    have h := step_bounds s (nextMax a) a.lower (nextQ a) (middle a) a.upper
      a.quarter_le (nextQ_bounds a).1 (nextQ_bounds a).2
      (middle_bounds a).2.2.1 a.upper_le_half
    exact le_trans a.quarter_le h.2.2.1.le
  lower_lt_upper := by
    exact (step_bounds s (nextMax a) a.lower (nextQ a) (middle a) a.upper
      a.quarter_le (nextQ_bounds a).1 (nextQ_bounds a).2
      (middle_bounds a).2.2.1 a.upper_le_half).2.2.2.1
  upper_le_half := by
    have h := step_bounds s (nextMax a) a.lower (nextQ a) (middle a) a.upper
      a.quarter_le (nextQ_bounds a).1 (nextQ_bounds a).2
      (middle_bounds a).2.2.1 a.upper_le_half
    exact le_trans (lt_trans h.2.2.2.2.1 (middle_bounds a).2.2.1).le a.upper_le_half

theorem nextState_properties (s : ℕ) (a : IntervalState) :
    a.lower < (nextState s a).lower ∧
    (nextState s a).upper < middle a ∧
    nextQ a < (nextState s a).lower ∧
    (nextState s a).upper - nextQ a < 1/((nextQ a).den:ℚ)^(s+2) ∧
    (nextState s a).upper - (nextState s a).lower ≤ (1/2:ℚ)^s ∧
    2 ≤ (nextQ a).den ∧
    nextQ a + badLowerQ (stepIndex s (nextMax a) (nextQ a) (middle a)) <
      (nextState s a).lower ∧
    (nextState s a).upper <
      nextQ a + badUpperQ (stepIndex s (nextMax a) (nextQ a) (middle a)) := by
  obtain ⟨_, _, h1, _, h2, _, h3, h4, h5, h6, h7, h8⟩ :=
    step_bounds s (nextMax a) a.lower (nextQ a) (middle a) a.upper
      a.quarter_le (nextQ_bounds a).1 (nextQ_bounds a).2
      (middle_bounds a).2.2.1 a.upper_le_half
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

def state : ℕ → IntervalState
  | 0 => initialState
  | n+1 => nextState n (state n)

theorem state_lower_mono : Monotone (fun n => (state n).lower) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (nextState_properties n (state n)).1.le

theorem state_upper_anti : Antitone (fun n => (state n).upper) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (lt_trans (nextState_properties n (state n)).2.1
    (middle_bounds (state n)).2.2.1).le

theorem state_level_ge (n : ℕ) : n ≤ (state n).level := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := nextLevel_gt (state n)
    change n+1 ≤ nextLevel (state n)
    omega

def nestedData : RationalNestedData where
  lower := fun n => (state (n+1)).lower
  upper := fun n => (state (n+1)).upper
  approx := fun n => nextQ (state n)
  lower_le_upper := fun n => (state (n+1)).lower_lt_upper.le
  lower_mono := by intro n m h; exact state_lower_mono (by omega)
  upper_anti := by intro n m h; exact state_upper_anti (by omega)
  width_le := fun n => (nextState_properties n (state n)).2.2.2.2.1
  approx_lt_lower := fun n => (nextState_properties n (state n)).2.2.1
  upper_sub_approx_lt := fun n => (nextState_properties n (state n)).2.2.2.1
  two_le_den := fun n => (nextState_properties n (state n)).2.2.2.2.2.1

/-- The specified real: the supremum of the executable rational lower endpoints. -/
noncomputable def explicitNumber : ℝ := nestedData.limit

/-- A total executable rational approximation, with a certified dyadic error below. -/
def approximate (n : ℕ) : ℚ := ((state (n+1)).lower + (state (n+1)).upper)/2

theorem approximate_error (n : ℕ) :
    |explicitNumber - (approximate n : ℝ)| ≤ (1/2:ℝ)^n/2 :=
  nestedData.midpoint_error n

theorem explicitNumber_irrational : Irrational explicitNumber := nestedData.limit_irrational

theorem explicitNumber_bounds : (1/4:ℝ) < explicitNumber ∧ explicitNumber < 1/2 := by
  have hmem := nestedData.limit_mem 0
  have h := nextState_properties 0 initialState
  have hm := (middle_bounds initialState).2.2.1
  change ((state 1).lower : ℝ) ≤ explicitNumber ∧ explicitNumber ≤ ((state 1).upper : ℝ) at hmem
  have hlo : (1/4:ℚ) < (state 1).lower := h.1
  have hup : (state 1).upper < (1/2:ℚ) := lt_trans h.2.1 hm
  constructor
  · exact lt_of_lt_of_le (by simpa using (Rat.cast_lt (K := ℝ)).mpr hlo) hmem.1
  · exact lt_of_le_of_lt hmem.2 (by simpa using (Rat.cast_lt (K := ℝ)).mpr hup)

theorem explicitNumber_not_eventuallyGreedy : ¬ EventuallyGreedy explicitNumber := by
  apply not_eventuallyGreedy_of_bad_intervals
  intro N
  let a := state N
  let i := stepIndex N (nextMax a) (nextQ a) (middle a)
  have hs := nextState_properties N a
  have hi := stepIndex_bounds N (nextMax a) (nextQ a) (middle a)
  have hmem := nestedData.limit_mem N
  change ((nextState N a).lower : ℝ) ≤ explicitNumber ∧
    explicitNumber ≤ ((nextState N a).upper : ℝ) at hmem
  have hcast : ((nextQ a : ℚ) : ℝ) = egyptianSum (nextBest a) := cast_qsum _
  refine ⟨nextBest a, nextLevel a, i, (middle a : ℝ), ?_, nextBest_best a,
    hi.1, ?_, ?_, ?_, ?_⟩
  · have hge := state_level_ge N
    have hgt := nextLevel_gt a
    change N ≤ nextLevel a
    change N ≤ a.level at hge
    omega
  · intro m hm
    exact lt_of_le_of_lt (nextBest_le_max a m hm) hi.2.1
  · have hh : (nextQ a : ℝ) + badLower i < ((nextState N a).lower : ℝ) := by
      simpa [i] using (Rat.cast_lt (K := ℝ)).mpr hs.2.2.2.2.2.2.1
    rw [hcast] at hh
    exact lt_of_lt_of_le hh hmem.1
  · have hh : ((nextState N a).upper : ℝ) < (nextQ a : ℝ) + badUpper i := by
      simpa [i] using (Rat.cast_lt (K := ℝ)).mpr hs.2.2.2.2.2.2.2
    rw [hcast] at hh
    exact lt_of_le_of_lt hmem.2 hh
  · exact le_trans hmem.2 (by exact_mod_cast hs.2.1.le)

theorem explicit_example : (1/4:ℝ) < explicitNumber ∧ explicitNumber < 1/2 ∧
    Irrational explicitNumber ∧ ¬ EventuallyGreedy explicitNumber :=
  ⟨explicitNumber_bounds.1, explicitNumber_bounds.2,
    explicitNumber_irrational, explicitNumber_not_eventuallyGreedy⟩

#print axioms explicit_example
#print axioms approximate_error

end ExplicitEgyptian
