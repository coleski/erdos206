import PriorErdos206

/-!
Local obstruction for the explicit-example supplement to Erdős #206.
Uses the definitions and the competitor lemma formalized by Matteo Del Vecchio
and Aristotle for Vjekoslav Kovač's proof; see PriorErdos206.lean for credits.
-/

namespace Erdos206.EgyptianFractions

open Finset

lemma prefix_sum_succ (m : ℕ → ℕ) (hm : StrictMono m) (t : ℕ) :
    egyptianSum (image m (range (t+1))) =
      egyptianSum (image m (range t)) + 1 / (m t : ℝ) := by
  simp [egyptianSum, Finset.sum_image, hm.injective.eq_iff, Finset.sum_range_succ]

theorem local_pair_obstruction
    (S : Finset ℕ) (t i j a b : ℕ) (z x : ℝ)
    (hS : IsBestNTerm S t z)
    (hi : 2 ≤ i) (hj : 0 < j) (hiS : i ∉ S)
    (ha : i < a) (hb : i < b) (hab : a ≠ b)
    (hpair : (1:ℝ)/i + 1/(j+1:ℕ) < 1/(a:ℝ) + 1/(b:ℝ))
    (hcap : (1:ℝ)/i + 1/(j:ℝ) ≤ 1/((i:ℝ)-1))
    (hlo : egyptianSum S + 1/(a:ℝ) + 1/(b:ℝ) < x)
    (hup : x < egyptianSum S + 1/(i:ℝ) + 1/(j:ℝ))
    (hxz : x ≤ z)
    (m : ℕ → ℕ) (hm : StrictMono m) (hmp : ∀ k, 0 < m k)
    (h0 : IsBestNTerm (image m (range t)) t x)
    (h1 : IsBestNTerm (image m (range (t+1))) (t+1) x)
    (h2 : IsBestNTerm (image m (range (t+2))) (t+2) x) : False := by
  have hip : 0 < (i:ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hjp : 0 < (j:ℝ) := by exact_mod_cast hj
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hSx : IsBestNTerm S t x :=
    IsBestNTerm_of_Ioc S t z x hS (by
      have : 0 < (1:ℝ)/(a:ℝ) := by positivity
      have : 0 < (1:ℝ)/(b:ℝ) := by positivity
      linarith) hxz
  have heq : egyptianSum (image m (range t)) = egyptianSum S :=
    le_antisymm (hSx.2.2 _ h0.1 h0.2.1) (h0.2.2 _ hSx.1 hSx.2.1)
  have hsucc := prefix_sum_succ m hm t
  have hsucc2 := prefix_sum_succ m hm (t+1)
  have hfirst : (1:ℝ)/i < x - egyptianSum S := by
    have : 0 < (1:ℝ)/(j+1:ℕ) := by positivity
    linarith
  have hvalid : IsUnderapprox (insert i S) x := by
    constructor
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · omega
      · exact hS.2.1.1 k hk
    · simp only [egyptianSum, sum_insert hiS]
      change 1/(i:ℝ) + egyptianSum S < x
      linarith
  have hcompetitor := h1.2.2 (insert i S) (by simp [hiS, hS.1]) hvalid
  have hins : egyptianSum (insert i S) = 1/(i:ℝ) + egyptianSum S := by
    simp [egyptianSum, hiS]
  have hinv : (1:ℝ)/i ≤ 1/(m t:ℝ) := by rw [hins, hsucc, heq] at hcompetitor; linarith
  have hmt_le : m t ≤ i := by
    by_contra h
    have hlt : (i:ℝ) < m t := by exact_mod_cast (show i < m t by omega)
    have := one_div_lt_one_div_of_lt hip hlt
    linarith
  have hmt_ge : i ≤ m t := by
    by_contra h
    have hle : (m t:ℝ) ≤ (i:ℝ)-1 := by
      have hnat : m t + 1 ≤ i := by omega
      have hr : (m t:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast hnat
      linarith
    have hmp' : 0 < (m t:ℝ) := by exact_mod_cast hmp t
    have hrec := one_div_le_one_div_of_le hmp' hle
    have hbound := h1.2.1.2
    rw [hsucc, heq] at hbound
    linarith
  have hmti : m t = i := le_antisymm hmt_le hmt_ge
  have hnext : (1:ℝ)/(m (t+1):ℝ) < 1/(j:ℝ) := by
    have hbound := h2.2.1.2
    rw [show t+2 = (t+1)+1 by omega, hsucc2, hsucc, heq, hmti] at hbound
    linarith
  have hjnext : j+1 ≤ m (t+1) := by
    by_contra h
    have hle : (m (t+1):ℝ) ≤ j := by exact_mod_cast (show m (t+1) ≤ j by omega)
    have hpos : 0 < (m (t+1):ℝ) := by exact_mod_cast hmp (t+1)
    have := one_div_le_one_div_of_le hpos hle
    linarith
  have hnext_le : (1:ℝ)/(m (t+1):ℝ) ≤ 1/(j+1:ℕ) := by
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hjnext)
  apply non_greedy_contradiction m hm hmp t x h2 a b ha0 hb0 hab
      (by simpa [hmti] using ha) (by simpa [hmti] using hb)
  · simpa [heq] using hlo
  · rw [hmti]
    linarith

noncomputable def badLower (i : ℕ) : ℝ :=
  1 / (i+1:ℕ) + 1 / (i*(i+1)/2+1:ℕ)

noncomputable def badUpper (i : ℕ) : ℝ :=
  1 / (i:ℝ) + 1 / (i*(i+1)+4:ℕ)

lemma half_product_cast (i : ℕ) :
    ((i*(i+1)/2:ℕ):ℝ) = (i:ℝ)*((i:ℝ)+1)/2 := by
  have h := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one i)
  have hr : ((i*(i+1)/2:ℕ):ℝ)*2 = (i:ℝ)*((i:ℝ)+1) := by
    exact_mod_cast h
  linarith

lemma explicit_pair_bounds (i : ℕ) (hi : 4 ≤ i) :
    i+1 < i*(i+1)/2+1 ∧
    (1:ℝ)/i + 1/(i*(i+1)+5:ℕ) < badLower i ∧
    badLower i < badUpper i ∧
    badUpper i ≤ 1/((i:ℝ)-1) := by
  have hir : (4:ℝ) ≤ i := by exact_mod_cast hi
  have hip : 0 < (i:ℝ) := by linarith
  have him : 0 < (i:ℝ)-1 := by linarith
  have hh := half_product_cast i
  have hT : (20:ℝ) ≤ (i:ℝ)*((i:ℝ)+1) := by nlinarith
  have hn : i+1 < i*(i+1)/2+1 := by
    have : (i:ℝ)+1 < ((i*(i+1)/2:ℕ):ℝ)+1 := by nlinarith
    exact_mod_cast this
  refine ⟨hn, ?_, ?_, ?_⟩
  · unfold badLower
    push_cast
    rw [hh]
    have hd :
        1 / ((i:ℝ)+1) + 1 / ((i:ℝ)*((i:ℝ)+1)/2+1) -
          (1/(i:ℝ) + 1/((i:ℝ)*((i:ℝ)+1)+5)) =
        ((i:ℝ)*((i:ℝ)+1)-10) /
          ((i:ℝ)*((i:ℝ)+1)*((i:ℝ)*((i:ℝ)+1)+2)*((i:ℝ)*((i:ℝ)+1)+5)) := by
      field_simp
      ring
    have hpos : 0 < ((i:ℝ)*((i:ℝ)+1)-10) /
          ((i:ℝ)*((i:ℝ)+1)*((i:ℝ)*((i:ℝ)+1)+2)*((i:ℝ)*((i:ℝ)+1)+5)) := by
      apply div_pos
      · linarith
      · positivity
    linarith
  · unfold badLower badUpper
    push_cast
    rw [hh]
    have hd :
        (1/(i:ℝ) + 1/((i:ℝ)*((i:ℝ)+1)+4)) -
          (1 / ((i:ℝ)+1) + 1 / ((i:ℝ)*((i:ℝ)+1)/2+1)) =
        8 / ((i:ℝ)*((i:ℝ)+1)*((i:ℝ)*((i:ℝ)+1)+2)*((i:ℝ)*((i:ℝ)+1)+4)) := by
      field_simp
      ring
    have hpos : 0 < (8:ℝ) /
        ((i:ℝ)*((i:ℝ)+1)*((i:ℝ)*((i:ℝ)+1)+2)*((i:ℝ)*((i:ℝ)+1)+4)) := by positivity
    linarith
  · unfold badUpper
    push_cast
    have hrec : (1:ℝ)/((i:ℝ)*((i:ℝ)+1)+4) ≤ 1/((i:ℝ)*((i:ℝ)-1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hid : (1:ℝ)/i + 1/((i:ℝ)*((i:ℝ)-1)) = 1/((i:ℝ)-1) := by
      field_simp
      ring
    linarith

theorem explicit_interval_no_chain
    (S : Finset ℕ) (t i : ℕ) (z x : ℝ)
    (hS : IsBestNTerm S t z)
    (hi : 4 ≤ i) (hmax : ∀ a ∈ S, a < i)
    (hlo : egyptianSum S + badLower i < x)
    (hup : x < egyptianSum S + badUpper i)
    (hxz : x ≤ z) :
    ¬ ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ k, 0 < m k) ∧
      IsBestNTerm (image m (range t)) t x ∧
      IsBestNTerm (image m (range (t+1))) (t+1) x ∧
      IsBestNTerm (image m (range (t+2))) (t+2) x := by
  obtain ⟨hn, hpair, _, hcap⟩ := explicit_pair_bounds i hi
  rintro ⟨m, hm, hmp, h0, h1, h2⟩
  apply local_pair_obstruction S t i (i*(i+1)+4) (i+1) (i*(i+1)/2+1)
    z x hS (by omega) (by omega) (by intro h; exact (lt_irrefl i) (hmax i h))
    (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ hxz m hm hmp h0 h1 h2
  · simpa [badLower, Nat.add_assoc] using hpair
  · simpa [badUpper] using hcap
  · simpa [badLower, add_assoc] using hlo
  · simpa [badUpper, add_assoc] using hup

lemma bad_interval_positive_small (i : ℕ) (hi : 4 ≤ i) :
    0 < badLower i ∧ badLower i < badUpper i ∧ badUpper i < 2/(i:ℝ) := by
  have hip : 0 < (i:ℝ) := by exact_mod_cast (show 0 < i by omega)
  refine ⟨?_, (explicit_pair_bounds i hi).2.2.1, ?_⟩
  · unfold badLower
    positivity
  · unfold badUpper
    have hir : (4:ℝ) ≤ i := by exact_mod_cast hi
    have hden : (i:ℝ) < (i*(i+1)+4:ℕ) := by
      push_cast
      nlinarith
    have hrec := one_div_lt_one_div_of_lt hip hden
    have htwo : (2:ℝ)/i = 1/(i:ℝ)+1/(i:ℝ) := by ring
    rw [htwo]
    linarith

theorem not_eventuallyGreedy_of_bad_intervals (x : ℝ)
    (hbad : ∀ N : ℕ, ∃ (S : Finset ℕ) (t i : ℕ) (z : ℝ),
      N ≤ t ∧ IsBestNTerm S t z ∧ 4 ≤ i ∧ (∀ a ∈ S, a < i) ∧
      egyptianSum S + badLower i < x ∧ x < egyptianSum S + badUpper i ∧ x ≤ z) :
    ¬ EventuallyGreedy x := by
  rintro ⟨_, m, hm, hmp, N, hbest⟩
  obtain ⟨S, t, i, z, hNt, hS, hi, hmax, hlo, hup, hxz⟩ := hbad N
  apply explicit_interval_no_chain S t i z x hS hi hmax hlo hup hxz
  exact ⟨m, hm, hmp, hbest t hNt, hbest (t+1) (by omega), hbest (t+2) (by omega)⟩

#print axioms explicit_pair_bounds
#print axioms explicit_interval_no_chain
#print axioms not_eventuallyGreedy_of_bad_intervals

end Erdos206.EgyptianFractions
