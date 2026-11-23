import SelfApproaching.Proof.ReductionSharp.Window

/-!
# The survival probability of a single point

`P(k survives) ≥ q · ∏_p (1 - up p) - q · Ck`, where the product runs over the windows.
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

lemma sum_wt_double (q : ℝ) (f : Fin n → Fin n → (Fin n → Bool) → ℝ) :
    ∑ g, wt q g * ∑ a, ∑ b, f a b g = ∑ a, ∑ b, ∑ g, wt q g * f a b g := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_comm]

lemma DW_ind_ge (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n) (p : ℕ)
    (g : Fin n → Bool) :
    1 - ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a = p ∧ win G τ b = p then
        (if Ev2 g a b then (1:ℝ) else 0) else 0)
      ≤ if DW T G τ k p g then 1 else 0 := by
  have hsum : 0 ≤ ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a = p ∧ win G τ b = p then
        (if Ev2 g a b then (1:ℝ) else 0) else 0) :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  by_cases hD : DW T G τ k p g
  · rw [if_pos hD]; linarith
  rw [if_neg hD]
  unfold DW at hD
  push Not at hD
  obtain ⟨a, b, hP, ha, hb, hE⟩ := hD
  have ha' := single_le_sum (f := fun a' => ∑ b, (if Pk T k a' b ∧ win G τ a' = p ∧
      win G τ b = p then (if Ev2 g a' b then (1:ℝ) else 0) else 0))
    (fun a' _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (mem_univ a)
  have hb' := single_le_sum (f := fun b' => (if Pk T k a b' ∧ win G τ a = p ∧
      win G τ b' = p then (if Ev2 g a b' then (1:ℝ) else 0) else 0))
    (fun _ _ => by dsimp only; split_ifs <;> norm_num) (mem_univ b)
  simp only [if_pos (And.intro hP (And.intro ha hb)), if_pos hE] at hb'
  linarith

lemma E_DW_ge {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Fin n → Fin n → Finset (Fin n))
    (G τ : ℕ) (k : Fin n) (p : ℕ) :
    1 - up T q G τ k p ≤ ∑ g, wt q g * (if DW T G τ k p g then (1:ℝ) else 0) := by
  calc 1 - up T q G τ k p
      = ∑ g, wt q g * (1 - ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a = p ∧ win G τ b = p then
          (if Ev2 g a b then (1:ℝ) else 0) else 0)) := by
        simp_rw [mul_sub, mul_one]
        rw [sum_sub_distrib, sum_wt, sum_wt_double]
        congr 1
        unfold up
        apply sum_congr rfl; intro a _
        apply sum_congr rfl; intro b _
        split_ifs with h
        · rw [sum_ev2 q h.1.1]; rfl
        · simp
    _ ≤ ∑ g, wt q g * (if DW T G τ k p g then (1:ℝ) else 0) := by
        apply sum_le_sum; intro g _
        exact mul_le_mul_of_nonneg_left (DW_ind_ge T G τ k p g) (wt_nonneg hq0 hq1 g)

lemma blk_disjoint (G τ : ℕ) (k : Fin n) :
    ((wins n G τ : Finset ℕ) : Set ℕ).PairwiseDisjoint (blk G τ k) := by
  intro p _ p' _ hpp'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [blk, mem_erase, mem_filter, mem_univ, true_and] at hi hi'
  exact hpp' (hi.2.symm.trans hi'.2)

lemma point_est {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Fin n → Fin n → Finset (Fin n))
    (G τ : ℕ) (k : Fin n) (hup : ∀ p ∈ wins n G τ, up T q G τ k p ≤ 1) :
    q * ∏ p ∈ wins n G τ, (1 - up T q G τ k p) - q * Ck T q G τ k
      ≤ ∑ g, wt q g * (if k ∈ Good T g then (1:ℝ) else 0) := by
  have hind : ∑ g, wt q g * ((if g k = true then (1:ℝ) else 0) *
      ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0))
      = q * ∏ p ∈ wins n G τ, ∑ g, wt q g * (if DW T G τ k p g then (1:ℝ) else 0) := by
    rw [indep_two q {k}]
    · rw [sum_wt_coord, indep_prod q (wins n G τ) (blk G τ k) (blk_disjoint G τ k)]
      intro p _ g g' h
      rw [if_congr (DW_dep T G τ k p g g' h) rfl rfl]
    · intro g g' h
      rw [h k (mem_singleton_self k)]
    · intro g g' h
      apply prod_congr rfl; intro p _
      apply if_congr _ rfl rfl
      apply DW_dep
      intro i hi
      apply h
      simp only [blk, mem_erase] at hi
      simpa using hi.1
  have hcross : ∑ g, wt q g * ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
      (if Ev g a b k then (1:ℝ) else 0) else 0) = q * Ck T q G τ k := by
    rw [sum_wt_double]
    unfold Ck
    rw [mul_sum]
    apply sum_congr rfl; intro a _
    rw [mul_sum]
    apply sum_congr rfl; intro b _
    split_ifs with h
    · unfold wt wgt
      rw [sum_ev q h.1.1 (by rcases h.1.2.2 with h' | h' <;> [exact Or.inl h'; exact Or.inr h'])]
      ring
    · simp
  have hprod : ∏ p ∈ wins n G τ, (1 - up T q G τ k p)
      ≤ ∏ p ∈ wins n G τ, ∑ g, wt q g * (if DW T G τ k p g then (1:ℝ) else 0) := by
    apply prod_le_prod
    · intro p hp; linarith [hup p hp]
    · intro p _; exact E_DW_ge hq0 hq1 T G τ k p
  calc q * ∏ p ∈ wins n G τ, (1 - up T q G τ k p) - q * Ck T q G τ k
      ≤ q * ∏ p ∈ wins n G τ, ∑ g, wt q g * (if DW T G τ k p g then (1:ℝ) else 0)
          - q * Ck T q G τ k := by
        have := mul_le_mul_of_nonneg_left hprod hq0
        linarith
    _ = ∑ g, wt q g * ((if g k = true then (1:ℝ) else 0) *
          ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0)
        - ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
          (if Ev g a b k then (1:ℝ) else 0) else 0)) := by
        simp_rw [mul_sub]
        rw [sum_sub_distrib, hind, hcross]
    _ ≤ ∑ g, wt q g * (if k ∈ Good T g then (1:ℝ) else 0) := by
        apply sum_le_sum; intro g _
        exact mul_le_mul_of_nonneg_left (good_ind_ge T G τ k g) (wt_nonneg hq0 hq1 g)

end SelfApproaching.Proof.ReductionSharp
