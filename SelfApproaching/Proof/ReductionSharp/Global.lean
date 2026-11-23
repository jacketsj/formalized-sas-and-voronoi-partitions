import SelfApproaching.Proof.ReductionSharp.Assembly

/-!
# The windowed bound: averaging over points and window offsets
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset Real SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

/-- A geometric tail starting after an arbitrary natural number `s`. -/
lemma geom_bound_nat {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (s : ℕ) :
    (1 - r) * ∑ b : Fin n, (if s < b.val then r ^ (b.val - s - 1) else 0) ≤ 1 := by
  rw [← sum_filter]
  have hinj : Set.InjOn (fun b : Fin n => b.val - s - 1) (univ.filter (fun b : Fin n => s < b.val)) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
    simp only at hab
    ext; omega
  rw [← sum_image (f := fun d => r ^ d) hinj]
  have hsub : (univ.filter (fun b : Fin n => s < b.val)).image (fun b : Fin n => b.val - s - 1)
      ⊆ range n := by
    intro d hd
    simp only [mem_image] at hd
    obtain ⟨b, _, rfl⟩ := hd
    simp only [mem_range]; omega
  calc (1 - r) * ∑ d ∈ (univ.filter (fun b : Fin n => s < b.val)).image
          (fun b : Fin n => b.val - s - 1), r ^ d
      ≤ (1 - r) * ∑ d ∈ range n, r ^ d := by
        have : 0 ≤ 1 - r := by linarith
        gcongr
    _ = 1 - r ^ n := mul_neg_geom_sum r n
    _ ≤ 1 := by linarith [pow_nonneg h0 n]

lemma card_step_le_one (G : ℕ) (c : ℕ) :
    ((range G).filter fun τ => (c + τ) / G ≠ (c + τ + 1) / G).card ≤ 1 := by
  rw [card_le_one]
  intro τ1 h1 τ2 h2
  simp only [mem_filter, mem_range] at h1 h2
  have hd : ∀ τ, (c + τ) / G ≠ (c + τ + 1) / G → G ∣ c + τ + 1 := by
    intro τ h
    rw [Nat.succ_div] at h
    by_contra hn
    rw [if_neg hn] at h
    exact h rfl
  have d1 := hd τ1 h1.2
  have d2 := hd τ2 h2.2
  have hm : c + 1 + τ1 ≡ c + 1 + τ2 [MOD G] := by
    unfold Nat.ModEq
    rw [show c + 1 + τ1 = c + τ1 + 1 by ring, show c + 1 + τ2 = c + τ2 + 1 by ring,
      Nat.mod_eq_zero_of_dvd d1, Nat.mod_eq_zero_of_dvd d2]
  have := Nat.ModEq.add_left_cancel' (c + 1) hm
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1] at this

lemma card_cross_le (G : ℕ) (a d : ℕ) :
    ((range G).filter fun τ => (a + τ) / G ≠ (a + d + τ) / G).card ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hsub : ((range G).filter fun τ => (a + τ) / G ≠ (a + (d + 1) + τ) / G) ⊆
        ((range G).filter fun τ => (a + τ) / G ≠ (a + d + τ) / G) ∪
        ((range G).filter fun τ => (a + d + τ) / G ≠ (a + d + τ + 1) / G) := by
      intro τ hτ
      simp only [mem_filter, mem_union] at hτ ⊢
      by_contra h
      push Not at h
      apply hτ.2
      rw [h.1 hτ.1, h.2 hτ.1]
      ring_nf
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ d + 1 := by have := card_step_le_one G (a + d); omega

/-- Number of window offsets for which `a` and `b` lie in different windows. -/
def cnt (G : ℕ) (a b : Fin n) : ℕ := ((range G).filter fun τ => win G τ a ≠ win G τ b).card

lemma cnt_le_min (G : ℕ) {a b : Fin n} (hab : a < b) :
    (cnt G a b : ℝ) ≤ ∑ j ∈ range G, (if j < b.val - a.val then (1:ℝ) else 0) := by
  rw [sum_boole]
  have h1 : cnt G a b ≤ b.val - a.val := by
    have := card_cross_le G a.val (b.val - a.val)
    have hb : a.val + (b.val - a.val) = b.val := by have := Fin.lt_def.mp hab; omega
    rw [hb] at this
    exact this
  have h2 : cnt G a b ≤ G := by
    unfold cnt
    exact (card_filter_le _ _).trans (card_range G).le
  have h3 : ((range G).filter fun j => j < b.val - a.val).card = min G (b.val - a.val) := by
    have : (range G).filter (fun j => j < b.val - a.val) = range (min G (b.val - a.val)) := by
      ext j; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  rw [h3]
  exact_mod_cast le_min h2 h1

lemma inner_cross {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (G : ℕ) (a : Fin n) :
    ∑ b, (if a < b then (cnt G a b : ℝ) * wgt q a b else 0) ≤ 1 - (1 - q) ^ G := by
  have hr0 : 0 ≤ 1 - q := by linarith
  calc ∑ b, (if a < b then (cnt G a b : ℝ) * wgt q a b else 0)
      ≤ ∑ b : Fin n, ∑ j ∈ range G, (if a.val + j < b.val then
          q ^ 2 * ((1 - q) ^ j * (1 - q) ^ (b.val - (a.val + j) - 1)) else 0) := by
        apply sum_le_sum; intro b _
        split_ifs with hab
        · calc (cnt G a b : ℝ) * wgt q a b
              ≤ (∑ j ∈ range G, (if j < b.val - a.val then (1:ℝ) else 0)) * wgt q a b :=
                mul_le_mul_of_nonneg_right (cnt_le_min G hab) (wgt_nonneg hq1 a b)
            _ = _ := by
                rw [sum_mul]
                apply sum_congr rfl; intro j _
                by_cases hj : j < b.val - a.val
                · rw [if_pos hj, if_pos (by omega), one_mul, ← pow_add]
                  unfold wgt; congr 2; omega
                · rw [if_neg hj, if_neg (by omega), zero_mul]
        · apply sum_nonneg; intro j _
          split_ifs
          · positivity
          · exact le_rfl
    _ = ∑ j ∈ range G, q ^ 2 * (1 - q) ^ j *
          ∑ b : Fin n, (if a.val + j < b.val then (1 - q) ^ (b.val - (a.val + j) - 1) else 0) := by
        rw [sum_comm]
        apply sum_congr rfl; intro j _
        rw [mul_sum]
        apply sum_congr rfl; intro b _
        split_ifs <;> ring
    _ ≤ ∑ j ∈ range G, q * (1 - q) ^ j := by
        apply sum_le_sum; intro j _
        have hg := geom_bound_nat (n := n) hr0 (by linarith) (a.val + j)
        rw [sub_sub_cancel] at hg
        have hp : 0 ≤ q * (1 - q) ^ j := by positivity
        calc q ^ 2 * (1 - q) ^ j * ∑ b : Fin n, (if a.val + j < b.val then
              (1 - q) ^ (b.val - (a.val + j) - 1) else 0)
            = (q * (1 - q) ^ j) * (q * ∑ b : Fin n, (if a.val + j < b.val then
              (1 - q) ^ (b.val - (a.val + j) - 1) else 0)) := by ring
          _ ≤ (q * (1 - q) ^ j) * 1 := mul_le_mul_of_nonneg_left hg hp
          _ = q * (1 - q) ^ j := mul_one _
    _ = 1 - (1 - q) ^ G := by
        rw [← mul_sum]
        have := geom_sum_mul_neg (1 - q) G
        rw [sub_sub_cancel] at this
        linarith [this]

lemma sum_ite_pk_le {M : ℕ} (T : Fin n → Fin n → Finset (Fin n))
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) (a b : Fin n) (x : ℝ) (hx : 0 ≤ x)
    (X : Fin n → Prop) [DecidablePred X] :
    ∑ k, (if Pk T k a b ∧ X k then x else 0) ≤ if a < b then M * x else 0 := by
  split_ifs with hab
  · calc ∑ k, (if Pk T k a b ∧ X k then x else 0)
        ≤ ∑ k, (if k ∈ T a b then x else 0) := by
          apply sum_le_sum; intro k _
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd h1.1.2.1 h2
          · exact hx
          · exact le_rfl
      _ = (T a b).card * x := by rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul]
      _ ≤ M * x := by gcongr; exact_mod_cast hT4 a b hab
  · apply le_of_eq
    apply sum_eq_zero; intro k _
    rw [if_neg]; rintro ⟨h, _⟩; exact hab h.1

lemma sum_μk_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) (T : Fin n → Fin n → Finset (Fin n))
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) :
    ∑ k, μk T q k ≤ n * M * q := by
  unfold μk
  rw [sum_comm]
  have hr0 : 0 ≤ 1 - q := by linarith
  calc ∑ a, ∑ k, ∑ b, (if Pk T k a b then wgt q a b else 0)
      = ∑ a, ∑ b, ∑ k, (if Pk T k a b ∧ True then wgt q a b else 0) := by
        apply sum_congr rfl; intro a _; rw [sum_comm]; simp
    _ ≤ ∑ a, ∑ b, (if a < b then M * wgt q a b else 0) := by
        apply sum_le_sum; intro a _; apply sum_le_sum; intro b _
        exact sum_ite_pk_le T hT4 a b _ (wgt_nonneg hq1 a b) (fun _ => True)
    _ ≤ ∑ _a : Fin n, (M : ℝ) * q := by
        apply sum_le_sum; intro a _
        have hg := geom_bound (r := 1 - q) hr0 a
        rw [sub_sub_cancel] at hg
        calc ∑ b, (if a < b then M * wgt q a b else 0)
            = (M * q) * (q * ∑ b : Fin n, (if a < b then (1 - q) ^ (b.val - a.val - 1) else 0)) := by
              rw [mul_sum, mul_sum]
              apply sum_congr rfl; intro b _
              split_ifs <;> simp [wgt]; ring
          _ ≤ (M * q) * 1 := mul_le_mul_of_nonneg_left hg (by positivity)
          _ = M * q := mul_one _
    _ = n * M * q := by simp; ring

lemma sum_Ck_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) (T : Fin n → Fin n → Finset (Fin n))
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) (G : ℕ) :
    ∑ τ ∈ range G, ∑ k, Ck T q G τ k ≤ n * M * (1 - (1 - q) ^ G) := by
  unfold Ck
  calc ∑ τ ∈ range G, ∑ k, ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
        wgt q a b else 0)
      = ∑ k, ∑ a, ∑ b, ∑ τ ∈ range G, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
          wgt q a b else 0) := by
        rw [sum_comm]; apply sum_congr rfl; intro k _
        rw [sum_comm]; apply sum_congr rfl; intro a _
        rw [sum_comm]
    _ = ∑ a, ∑ b, ∑ k, ∑ τ ∈ range G, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
          wgt q a b else 0) := by
        rw [sum_comm]; apply sum_congr rfl; intro a _
        rw [sum_comm]
    _ = ∑ a, ∑ b, ∑ k, (if Pk T k a b ∧ True then (cnt G a b : ℝ) * wgt q a b else 0) := by
        apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
        apply sum_congr rfl; intro k _
        by_cases hP : Pk T k a b
        · simp only [hP, true_and, and_true, if_true]
          rw [← sum_filter, sum_const, nsmul_eq_mul]; rfl
        · simp [hP]
    _ ≤ ∑ a, ∑ b, (if a < b then M * ((cnt G a b : ℝ) * wgt q a b) else 0) := by
        apply sum_le_sum; intro a _; apply sum_le_sum; intro b _
        exact sum_ite_pk_le T hT4 a b _ (by have := wgt_nonneg hq1 a b; positivity)
          (fun _ => True)
    _ ≤ ∑ _a : Fin n, (M : ℝ) * (1 - (1 - q) ^ G) := by
        apply sum_le_sum; intro a _
        have := inner_cross hq0 hq1 G a
        calc ∑ b, (if a < b then M * ((cnt G a b : ℝ) * wgt q a b) else 0)
            = M * ∑ b, (if a < b then (cnt G a b : ℝ) * wgt q a b else 0) := by
              rw [mul_sum]; apply sum_congr rfl; intro b _; split_ifs <;> simp
          _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    _ = n * M * (1 - (1 - q) ^ G) := by simp; ring

end SelfApproaching.Proof.ReductionSharp
