import PriorErdos206

namespace ExplicitEgyptian

def qsum (S : Finset ℕ) : ℚ := ∑ a ∈ S, 1 / (a : ℚ)

def base (n L : ℕ) (z : ℚ) : Finset ℕ :=
  (Finset.range n).image (fun k => L + ⌈(n : ℚ) / z⌉₊ + k + 1)

theorem base_card (n L : ℕ) (z : ℚ) : (base n L z).card = n := by
  unfold base
  rw [Finset.card_image_of_injective _ (by
    intro a b h; dsimp at h; omega : Function.Injective (fun k => L + ⌈(n : ℚ) / z⌉₊ + k + 1))]
  exact Finset.card_range n

theorem base_above (n L : ℕ) (z : ℚ) : ∀ a ∈ base n L z, L < a := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  omega

theorem base_sum_lt (n L : ℕ) (z : ℚ) (hz : 0 < z) : qsum (base n L z) < z := by
  by_cases hn : n = 0
  · subst n; simpa [base, qsum] using hz
  have hnR : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hceil : (n : ℚ) / z ≤ (⌈(n : ℚ) / z⌉₊ : ℚ) := Nat.le_ceil _
  have hterm : ∀ k ∈ Finset.range n,
      (1 : ℚ) / (L + ⌈(n : ℚ) / z⌉₊ + k + 1) < z / n := by
    intro k hk
    have hden : (n : ℚ) / z < L + ⌈(n : ℚ) / z⌉₊ + k + 1 := by
      have : (0 : ℚ) ≤ L := Nat.cast_nonneg _
      have : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      linarith
    have hdenpos : (0 : ℚ) < L + ⌈(n : ℚ) / z⌉₊ + k + 1 := by positivity
    apply (div_lt_div_iff₀ hdenpos hnR).2
    have := (div_lt_iff₀ hz).1 hden
    nlinarith
  have h := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range n).Nonempty by simpa using hn) hterm
  have hinj : Function.Injective (fun k => L + ⌈(n : ℚ) / z⌉₊ + k + 1) := by
    intro a b h; dsimp at h; omega
  have hcancel : (n : ℚ) * (z / n) = z := by field_simp
  simpa [qsum, base, Finset.sum_image, Nat.cast_add, Nat.cast_one,
    hinj.injOn, hcancel] using h

def pick (S : Finset ℕ) (xs : List (Finset ℕ)) : Finset ℕ :=
  ((S :: xs).argmax qsum).getD S

theorem pick_mem (S : Finset ℕ) (xs : List (Finset ℕ)) : pick S xs ∈ S :: xs := by
  unfold pick
  cases h : (S :: xs).argmax qsum with
  | none => simp_all
  | some T => exact List.argmax_mem (by simpa using h)

theorem le_pick (S : Finset ℕ) (xs : List (Finset ℕ)) (T : Finset ℕ)
    (hT : T ∈ S :: xs) : qsum T ≤ qsum (pick S xs) := by
  unfold pick
  cases h : (S :: xs).argmax qsum with
  | none => simp_all
  | some U => exact List.le_of_mem_argmax hT (by simpa using h)

def optimize : ℕ → ℕ → ℚ → Finset ℕ
  | 0, _, _ => ∅
  | n + 1, L, z =>
    let S := base (n + 1) L z
    let B := ⌊((n + 1 : ℕ) : ℚ) / qsum S⌋₊
    let candidates := ((List.range (B + 1)).filter
      (fun a => L < a ∧ (1 : ℚ) / a < z)).map
      (fun a => insert a (optimize n a (z - 1 / (a : ℚ))))
    pick S candidates

#eval optimize 2 0 (11/24)

theorem qsum_nonneg (S : Finset ℕ) : 0 ≤ qsum S := by
  apply Finset.sum_nonneg
  intro a ha
  positivity

theorem qsum_pos {S : Finset ℕ} (hS : S.Nonempty)
    (hpos : ∀ a ∈ S, 0 < a) : 0 < qsum S := by
  apply Finset.sum_pos
  · intro a ha
    exact one_div_pos.mpr (Nat.cast_pos.mpr (hpos a ha))
  · exact hS

theorem qsum_insert {S : Finset ℕ} {a : ℕ} (ha : a ∉ S) :
    qsum (insert a S) = 1 / (a : ℚ) + qsum S := by
  exact Finset.sum_insert ha

theorem qsum_erase {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) :
    qsum S = 1 / (a : ℚ) + qsum (S.erase a) := by
  have h := qsum_insert (Finset.notMem_erase a S)
  simpa only [Finset.insert_erase ha] using h

theorem optimize_correct (n L : ℕ) (z : ℚ) (hz : 0 < z) :
    (optimize n L z).card = n ∧
    (∀ a ∈ optimize n L z, L < a) ∧
    qsum (optimize n L z) < z ∧
    ∀ T : Finset ℕ, T.card = n → (∀ a ∈ T, L < a) → qsum T < z →
      qsum T ≤ qsum (optimize n L z) := by
  induction n generalizing L z with
  | zero =>
    simp only [optimize, Finset.card_empty, Finset.notMem_empty, false_implies,
      implies_true, qsum, Finset.sum_empty, true_and]
    refine ⟨hz, ?_⟩
    intro T hT _ _
    simp [Finset.card_eq_zero.mp hT]
  | succ n ih =>
    let S := base (n+1) L z
    let B := ⌊((n+1 : ℕ) : ℚ) / qsum S⌋₊
    let xs := ((List.range (B+1)).filter
      (fun a => L < a ∧ (1 : ℚ)/a < z)).map
      (fun a => insert a (optimize n a (z-1/(a:ℚ))))
    change (pick S xs).card = n+1 ∧ _
    have hScard : S.card = n+1 := base_card _ _ _
    have hSabove : ∀ a ∈ S, L < a := base_above _ _ _
    have hSlt : qsum S < z := base_sum_lt _ _ _ hz
    have hSpos : 0 < qsum S := qsum_pos
      (Finset.card_pos.mp (by omega)) (fun a ha => lt_of_le_of_lt (Nat.zero_le L) (hSabove a ha))
    have hcandidate : ∀ U ∈ S :: xs,
        U.card = n+1 ∧ (∀ a ∈ U, L < a) ∧ qsum U < z := by
      intro U hU
      rcases List.mem_cons.mp hU with rfl | hU
      · exact ⟨hScard, hSabove, hSlt⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hU
        have ha' : L < a ∧ (1:ℚ)/a < z := by simpa using (List.mem_filter.mp ha).2
        have hrec := ih a (z-1/(a:ℚ)) (by linarith)
        have hnot : a ∉ optimize n a (z-1/(a:ℚ)) := by
          intro h
          exact (lt_irrefl a) (hrec.2.1 a h)
        refine ⟨by rw [Finset.card_insert_of_notMem hnot, hrec.1], ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha'.1
          · exact lt_trans ha'.1 (hrec.2.1 b hb)
        · rw [qsum_insert hnot]
          linarith [hrec.2.2.1]
    obtain ⟨hcard, habove, hlt⟩ := hcandidate _ (pick_mem S xs)
    refine ⟨hcard, habove, hlt, ?_⟩
    intro T hT hTabove hTlt
    have hbasepick : qsum S ≤ qsum (pick S xs) := le_pick S xs S (by simp)
    by_cases hsmall : qsum T ≤ qsum S
    · exact le_trans hsmall hbasepick
    have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
    let a := T.min' hTnonempty
    have haT : a ∈ T := Finset.min'_mem T hTnonempty
    have hapos : 0 < a := lt_of_le_of_lt (Nat.zero_le L) (hTabove a haT)
    have halower : ∀ b ∈ T, a ≤ b := fun b hb => Finset.min'_le T b hb
    have hsumupper : qsum T ≤ (n+1 : ℕ)/(a:ℚ) := by
      calc
        qsum T ≤ ∑ _b ∈ T, (1:ℚ)/(a:ℚ) := by
          apply Finset.sum_le_sum
          intro b hb
          exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hapos)
            (Nat.cast_le.mpr (halower b hb))
        _ = (n+1 : ℕ)/(a:ℚ) := by simp [hT, div_eq_mul_inv]
    have habound : a ≤ B := by
      apply Nat.le_floor
      apply (le_div_iff₀ hSpos).mpr
      have hmul := (le_div_iff₀ (Nat.cast_pos.mpr hapos)).mp hsumupper
      nlinarith
    have hsplit := qsum_erase haT
    have haunder : (1:ℚ)/a < z := by linarith [qsum_nonneg (T.erase a)]
    have htailcard : (T.erase a).card = n := by
      rw [Finset.card_erase_of_mem haT, hT]
      omega
    have htailabove : ∀ b ∈ T.erase a, a < b := by
      intro b hb
      obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
      have hle := halower b hb
      omega
    have htailunder : qsum (T.erase a) < z - 1/(a:ℚ) := by linarith
    have hrec := ih a (z-1/(a:ℚ)) (by linarith)
    have htaille := hrec.2.2.2 (T.erase a) htailcard htailabove htailunder
    have hnot : a ∉ optimize n a (z-1/(a:ℚ)) := by
      intro h
      exact (lt_irrefl a) (hrec.2.1 a h)
    have hcandmem : insert a (optimize n a (z-1/(a:ℚ))) ∈ S :: xs := by
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨a, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr (by omega), by simpa using And.intro (hTabove a haT) haunder⟩
    have hcandle := le_pick S xs _ hcandmem
    rw [qsum_insert hnot] at hcandle
    change qsum T ≤ qsum (pick S xs)
    linarith

theorem cast_qsum (S : Finset ℕ) :
    (qsum S : ℝ) = Erdos206.EgyptianFractions.egyptianSum S := by
  simp [qsum, Erdos206.EgyptianFractions.egyptianSum]

theorem optimize_isBestNTerm (n : ℕ) (z : ℚ) (hz : 0 < z) :
    Erdos206.EgyptianFractions.IsBestNTerm (optimize n 0 z) n (z : ℝ) := by
  obtain ⟨hc, ha, hl, hmax⟩ := optimize_correct n 0 z hz
  refine ⟨hc, ⟨ha, ?_⟩, ?_⟩
  · rw [← cast_qsum]
    exact Rat.cast_lt.mpr hl
  · intro T hT hU
    rw [← cast_qsum, ← cast_qsum]
    apply Rat.cast_le.mpr
    apply hmax T hT hU.1
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa [cast_qsum] using hU.2

#print axioms optimize_correct
#print axioms optimize_isBestNTerm

end ExplicitEgyptian
