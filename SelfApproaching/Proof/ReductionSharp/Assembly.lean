import SelfApproaching.Proof.ReductionSharp.PointEst
import SelfApproaching.Proof.ReductionSharp.Numeric

/-!
# Assembling the windowed estimate
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset Real SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

/-- The total union-bound mass of `k`. -/
noncomputable def μk (T : Fin n → Fin n → Finset (Fin n)) (q : ℝ) (k : Fin n) : ℝ :=
  ∑ a, ∑ b, if Pk T k a b then wgt q a b else 0

lemma two_mul_card_lt_le {α : Type*} [LinearOrder α] (W : Finset α) :
    2 * ((W ×ˢ W).filter (fun x => x.1 < x.2)).card ≤ W.card * W.card := by
  set A := (W ×ˢ W).filter (fun x => x.1 < x.2)
  set B := (W ×ˢ W).filter (fun x => x.2 < x.1)
  have hAB : A.card = B.card := by
    apply card_bij (fun x _ => x.swap)
    · intro x hx; simp only [A, B, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x _ y _ h; simpa using h
    · intro y hy
      refine ⟨y.swap, ?_, by simp⟩
      simp only [A, B, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hy ⊢
      exact ⟨⟨hy.1.2, hy.1.1⟩, hy.2⟩
  have hdisj : Disjoint A B := by
    rw [disjoint_left]
    intro x hA hB
    simp only [A, B, mem_filter] at hA hB
    exact lt_asymm hA.2 hB.2
  have hsub : A ∪ B ⊆ W ×ˢ W := union_subset (filter_subset _ _) (filter_subset _ _)
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_product] at this
  omega

lemma card_window_le (G τ p : ℕ) (hG : 0 < G) :
    ((univ : Finset (Fin n)).filter fun i => win G τ i = p).card ≤ G := by
  have : ((univ : Finset (Fin n)).filter fun i => win G τ i = p).card ≤ (range G).card := by
    apply card_le_card_of_injOn (fun i => (i.val + τ) % G)
    · intro i _; simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ hG
    · intro i hi j hj hij
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, win] at hi hj
      simp only at hij
      have h1 := Nat.div_add_mod (i.val + τ) G
      have h2 := Nat.div_add_mod (j.val + τ) G
      rw [hi] at h1; rw [hj] at h2
      ext; omega
  simpa using this

/-- Each window carries little mass. -/
lemma up_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Fin n → Fin n → Finset (Fin n))
    (G τ : ℕ) (hG : 0 < G) (hγ : (G : ℝ) * q ≤ 29 / 100) (k : Fin n) (p : ℕ) :
    up T q G τ k p ≤ 841 / 20000 := by
  set W := (univ : Finset (Fin n)).filter fun i => win G τ i = p
  have hW := card_window_le (n := n) G τ p hG
  have h2 := two_mul_card_lt_le W
  have hle : up T q G τ k p ≤ ∑ x ∈ (W ×ˢ W).filter (fun x => x.1 < x.2), q ^ 2 := by
    unfold up
    rw [← sum_product' (f := fun a b => if Pk T k a b ∧ win G τ a = p ∧ win G τ b = p then
      wgt q a b else 0), sum_filter]
    have hsub : W ×ˢ W ⊆ univ ×ˢ univ := subset_univ _
    rw [← sum_subset hsub]
    · apply sum_le_sum
      intro x _
      split_ifs with h1 h2
      · unfold wgt
        have : (1 - q) ^ (x.2.val - x.1.val - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        nlinarith [sq_nonneg q]
      · exact absurd h1.1.1 h2
      · positivity
      · exact le_rfl
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, h1, h2⟩
      apply hx
      simp [W, mem_product, h1, h2]
  rw [sum_const, nsmul_eq_mul] at hle
  have hc : (2 : ℝ) * ((W ×ˢ W).filter (fun x => x.1 < x.2)).card ≤ (G : ℝ) * G := by
    have : (W.card : ℝ) ≤ G := by exact_mod_cast hW
    have h2r : (2 : ℝ) * ((W ×ˢ W).filter (fun x => x.1 < x.2)).card ≤ W.card * W.card := by
      exact_mod_cast h2
    nlinarith [Nat.cast_nonneg (α := ℝ) W.card]
  have hGq : (0 : ℝ) ≤ G * q := by positivity
  nlinarith [sq_nonneg q]

lemma sum_up (q : ℝ) (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n) :
    ∑ p ∈ wins n G τ, up T q G τ k p = μk T q k - Ck T q G τ k := by
  have h : ∑ p ∈ wins n G τ, up T q G τ k p =
      ∑ a, ∑ b, if Pk T k a b ∧ win G τ a = win G τ b then wgt q a b else 0 := by
    unfold up
    rw [sum_comm]
    apply sum_congr rfl; intro a _
    rw [sum_comm]
    apply sum_congr rfl; intro b _
    by_cases hP : Pk T k a b
    · by_cases hw : win G τ a = win G τ b
      · rw [if_pos ⟨hP, hw⟩]
        rw [sum_eq_single (win G τ a)]
        · rw [if_pos ⟨hP, rfl, hw.symm⟩]
        · intro p _ hp; rw [if_neg]; rintro ⟨_, h1, _⟩; exact hp h1.symm
        · intro h; exact absurd (mem_wins G τ a) h
      · rw [if_neg (fun h => hw h.2)]
        apply sum_eq_zero; intro p _
        rw [if_neg]; rintro ⟨_, h1, h2⟩; exact hw (h1.trans h2.symm)
    · rw [if_neg (fun h => hP h.1)]
      apply sum_eq_zero; intro p _
      rw [if_neg]; rintro ⟨h, _⟩; exact hP h
  rw [h]
  unfold μk Ck
  rw [eq_sub_iff_add_eq, ← sum_add_distrib]
  apply sum_congr rfl; intro a _
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro b _
  by_cases hP : Pk T k a b <;> by_cases hw : win G τ a = win G τ b <;> simp [hP, hw]

/-- The per-point estimate in exponential form. -/
lemma point_exp {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Fin n → Fin n → Finset (Fin n))
    (G τ : ℕ) (hG : 0 < G) (hγ : (G : ℝ) * q ≤ 29 / 100) (k : Fin n) :
    q * (exp (-(1023 / 1000 * (μk T q k - Ck T q G τ k))) - Ck T q G τ k)
      ≤ ∑ g, wt q g * (if k ∈ Good T g then (1:ℝ) else 0) := by
  have hup := fun p => up_le hq0 hq1 T G τ hG hγ k p
  have hprod : exp (-(1023 / 1000 * (μk T q k - Ck T q G τ k)))
      ≤ ∏ p ∈ wins n G τ, (1 - up T q G τ k p) := by
    rw [← sum_up, mul_sum, ← sum_neg_distrib, exp_sum]
    apply prod_le_prod
    · intro p _; exact (exp_pos _).le
    · intro p _
      have h0 : 0 ≤ up T q G τ k p := by
        unfold up
        exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by
          split_ifs
          · exact wgt_nonneg hq1 _ _
          · exact le_refl _))
      exact one_sub_ge_exp h0 (hup p)
  have := point_est hq0 hq1 T G τ k (fun p _ => by linarith [hup p])
  have := mul_le_mul_of_nonneg_left hprod hq0
  linarith

end SelfApproaching.Proof.ReductionSharp
