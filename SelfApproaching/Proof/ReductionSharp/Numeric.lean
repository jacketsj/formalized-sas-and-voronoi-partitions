import Mathlib

/-!
# Real-number estimates for the sharpened reduction
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset Real

/-- Jensen's inequality for `exp`, via the tangent line. -/
lemma card_mul_exp_avg_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (hs : 0 < s.card) :
    (s.card : ℝ) * exp ((∑ i ∈ s, y i) / s.card) ≤ ∑ i ∈ s, exp (y i) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs
  set m := (∑ i ∈ s, y i) / (s.card : ℝ) with hm
  have key : ∀ i, exp m * (1 + (y i - m)) ≤ exp (y i) := by
    intro i
    have h1 := add_one_le_exp (y i - m)
    have h2 : exp (y i) = exp m * exp (y i - m) := by rw [← exp_add]; ring_nf
    rw [h2]
    have := exp_pos m
    nlinarith
  calc (s.card : ℝ) * exp m = ∑ i ∈ s, exp m * (1 + (y i - m)) := by
        rw [← mul_sum, sum_add_distrib, sum_sub_distrib, sum_const, sum_const]
        simp only [nsmul_eq_mul, mul_one]
        have : (s.card : ℝ) * m = ∑ i ∈ s, y i := by
          rw [hm]; field_simp
        rw [this]; ring
    _ ≤ ∑ i ∈ s, exp (y i) := sum_le_sum (fun i _ => key i)

lemma exp_neg_bounds {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    1 - y + y ^ 2 / 2 - 2 / 9 * y ^ 3 ≤ exp (-y) ∧
      exp (-y) ≤ 1 - y + y ^ 2 / 2 + 2 / 9 * y ^ 3 := by
  have hb := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
    (n := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at hb
  rw [abs_neg, abs_of_nonneg h0] at hb
  norm_num at hb
  have h := abs_le.mp hb
  constructor <;> nlinarith [h.1, h.2]

/-- `1 - u ≥ exp (-κ u)` for small `u`, with `κ = 1023/1000`. -/
lemma one_sub_ge_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 841 / 20000) :
    exp (-(1023 / 1000 * u)) ≤ 1 - u := by
  have hy0 : 0 ≤ 1023 / 1000 * u := by positivity
  have hy1 : 1023 / 1000 * u ≤ 1 := by linarith
  have := (exp_neg_bounds hy0 hy1).2
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- Lower Bonferroni bound for powers. -/
lemma pow_ge_bonferroni {q : ℝ} (h1 : q ≤ 1) (G : ℕ) :
    1 - G * q + (G * (G - 1) / 2) * q ^ 2 - (G * (G - 1) * (G - 2) / 6) * q ^ 3 ≤
      (1 - q) ^ G := by
  induction G with
  | zero => simp
  | succ G ih =>
    rw [pow_succ (1 - q) G]
    push_cast
    have h2 : 0 ≤ 1 - q := by linarith
    have := mul_le_mul_of_nonneg_right ih h2
    have hC : (0 : ℝ) ≤ G * (G - 1) * (G - 2) := by
      rcases Nat.lt_or_ge G 2 with h | h
      · interval_cases G <;> norm_num
      · have : (2 : ℝ) ≤ G := by exact_mod_cast h
        have h3 : (0:ℝ) ≤ G - 1 := by linarith
        have h4 : (0:ℝ) ≤ G - 2 := by linarith
        positivity
    have hC4 : 0 ≤ G * (G - 1) * (G - 2) / 6 * q ^ 4 := by positivity
    nlinarith [hC4]

/-- The final numerical inequality. -/
lemma final_numeric {μ C : ℝ} (hμ : μ ≤ 1 / 2) (hC : C ≤ 1087 / 2500) :
    500 / 999 ≤ exp (-(1023 / 1000 * (μ - C))) - C := by
  set E0 := exp (-(1023 / 1000 * (1 / 2 - 1087 / 2500 : ℝ))) with hE0
  have hy := exp_neg_bounds (y := 1023 / 1000 * (1 / 2 - 1087 / 2500 : ℝ)) (by norm_num)
    (by norm_num)
  rw [← hE0] at hy
  have hlo : (9354 / 10000 : ℝ) ≤ E0 := by linarith [hy.1]
  have hhi : E0 ≤ (9356 / 10000 : ℝ) := by linarith [hy.2]
  have htan : E0 * (1 + 1023 / 1000 * (C - 1087 / 2500)) ≤
      exp (-(1023 / 1000 * (1 / 2 - C))) := by
    have h1 := add_one_le_exp (1023 / 1000 * (C - 1087 / 2500))
    have h2 : exp (-(1023 / 1000 * (1 / 2 - C))) =
        E0 * exp (1023 / 1000 * (C - 1087 / 2500)) := by
      rw [hE0, ← exp_add]; ring_nf
    rw [h2]
    have := exp_pos (-(1023 / 1000 * (1 / 2 - 1087 / 2500 : ℝ)))
    rw [← hE0] at this
    nlinarith
  have hmono : exp (-(1023 / 1000 * (1 / 2 - C))) ≤ exp (-(1023 / 1000 * (μ - C))) := by
    apply exp_le_exp.mpr; linarith
  nlinarith

/-- The bound on the averaged straddling mass. -/
lemma cross_numeric (M : ℕ) (hM : 1001 ≤ M) :
    (M : ℝ) * (1 - (1 - 1 / (2 * (M : ℝ))) ^ (29 * M / 50)) / ((29 * M / 50 : ℕ) : ℝ)
      ≤ 1087 / 2500 := by
  set G := 29 * M / 50 with hG
  have hG1 : 50 * G ≤ 29 * M := by rw [hG, mul_comm]; exact Nat.div_mul_le_self _ _
  have hG2 : 29 * M < 50 * G + 50 := by
    have := Nat.lt_div_mul_add (a := 29 * M) (b := 50) (by norm_num)
    rw [hG]; linarith
  have hMr : (1001 : ℝ) ≤ M := by exact_mod_cast hM
  have hG1r : 50 * (G : ℝ) ≤ 29 * M := by exact_mod_cast hG1
  have hG2r : 29 * (M : ℝ) < 50 * G + 50 := by exact_mod_cast hG2
  have hGpos : (0 : ℝ) < G := by nlinarith
  set q : ℝ := 1 / (2 * (M : ℝ)) with hq
  have hMq : (M : ℝ) * q = 1 / 2 := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2002 := by
    rw [hq, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hγ1 : (G : ℝ) * q ≤ 29 / 100 := by
    have : (G : ℝ) * q = G / (2 * M) := by rw [hq]; field_simp
    rw [this, div_le_iff₀ (by positivity)]; linarith
  have hγ2 : 29 / 100 - q < (G : ℝ) * q := by
    have : (G : ℝ) * q + q = (G + 1) / (2 * M) := by rw [hq]; field_simp
    have h3 : (29 / 100 : ℝ) < (G + 1) / (2 * M) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  have hbon := pow_ge_bonferroni (q := q) (by linarith) G
  rw [div_le_iff₀ hGpos]
  -- `1 - (1-q)^G ≤ Gq - G(G-1)q²/2 + G(G-1)(G-2)q³/6`
  have h1 : (M : ℝ) * (1 - (1 - q) ^ G) ≤
      M * ((G : ℝ) * q - (G * (G - 1) / 2) * q ^ 2 + (G * (G - 1) * (G - 2) / 6) * q ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h2 : (M : ℝ) * ((G : ℝ) * q - (G * (G - 1) / 2) * q ^ 2 + (G * (G - 1) * (G - 2) / 6) * q ^ 3)
      = G * ((M * q) * (1 - (G * q - q) / 2 + (G * q - q) * (G * q - 2 * q) / 6)) := by ring
  rw [h2, hMq] at h1
  have h3 : (G * q - q) * (G * q - 2 * q) ≤ (G * q) * (G * q) := by nlinarith
  have h4 : (1 / 2 : ℝ) * (1 - (G * q - q) / 2 + (G * q - q) * (G * q - 2 * q) / 6)
      ≤ 1087 / 2500 := by nlinarith
  nlinarith

end SelfApproaching.Proof.ReductionSharp
