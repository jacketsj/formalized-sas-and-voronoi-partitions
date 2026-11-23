import SelfApproaching.Definitions
import SelfApproaching.Proof.LpLarge.Generic

namespace SelfApproaching.Proof

open Real

namespace LpLarge

open Finset

/-- One block of the code vector: `a` at the codeword symbol, `-1` elsewhere. -/
noncomputable def blk (a : ℝ) (c s : Fin 3) : ℝ := if c = s then a else -1

lemma jf_of_pos {p x : ℝ} (hx : 0 < x) : jf p x = x ^ (p - 1) := by
  simp [jf, Real.sign_of_pos hx, abs_of_pos hx]

lemma jf_neg_one (p : ℝ) : jf p (-1) = -1 := by
  simp [jf, Real.sign_of_neg]

lemma blk_psum {p a : ℝ} (ha : 0 < a) (c : Fin 3) : ∑ s, |blk a c s| ^ p = a ^ p + 2 := by
  fin_cases c <;> simp [blk, Fin.sum_univ_three, abs_of_pos ha] <;> ring

lemma blk_inner {p a : ℝ} (ha : 0 < a) (c c' : Fin 3) :
    ∑ s, jf p (blk a c s) * blk a c' s = if c = c' then a ^ p + 2 else 1 - a ^ (p - 1) - a := by
  have hap : a ^ (p - 1) * a = a ^ p := by
    rw [Real.rpow_sub_one ha.ne', div_mul_cancel₀ _ ha.ne']
  fin_cases c <;> fin_cases c' <;> simp [blk, Fin.sum_univ_three, jf_of_pos ha, jf_neg_one] <;>
    linarith

lemma sum_extend {α β : Type*} [Fintype α] [Fintype β] {e : α → β} (he : Function.Injective e)
    (F : ℝ → ℝ → ℝ) (hF : F 0 0 = 0) (u w : α → ℝ) :
    ∑ r, F (Function.extend e u 0 r) (Function.extend e w 0 r) = ∑ i, F (u i) (w i) := by
  symm
  refine Fintype.sum_of_injective e he _ _ (fun r hr => ?_) (fun i => ?_)
  · have hr' : ¬∃ a, e a = r := fun ⟨a, ha⟩ => hr ⟨a, ha⟩
    rw [Function.extend_apply' _ _ _ hr', Function.extend_apply' _ _ _ hr']
    exact hF
  · rw [he.extend_apply, he.extend_apply]

/-- The code vectors `v_C ∈ ℝ^d` (blocks `(a, -1, -1)` permuted by the codeword symbols, padded
with zeros), with their `p`-th power sums and pairwise `J`-inner products. -/
lemma code_vectors {p : ℝ} (hp : 1 < p) {a : ℝ} (ha : 0 < a) {n d N : ℕ} (hnd : n * 3 ≤ d)
    (C : Fin N → Fin n → Fin 3) :
    ∃ v : Fin N → Fin d → ℝ, (∀ i, psum p (v i) = n * (a ^ p + 2)) ∧
      ∀ i k, ∑ r, jf p (v k r) * v i r =
        n * (1 - a ^ (p - 1) - a) + (a ^ p + 2 - (1 - a ^ (p - 1) - a)) *
          ((Finset.univ.filter fun b => C k b = C i b).card : ℝ) := by
  set e : Fin n × Fin 3 → Fin d := fun x => Fin.castLE hnd (finProdFinEquiv x)
  have he : Function.Injective e := (Fin.castLE_injective hnd).comp finProdFinEquiv.injective
  set w : Fin N → Fin n × Fin 3 → ℝ := fun m x => blk a (C m x.1) x.2
  refine ⟨fun m => Function.extend e (w m) 0, fun i => ?_, fun i k => ?_⟩
  · have := sum_extend he (fun x _ => |x| ^ p)
      (by simp [Real.zero_rpow (by linarith : p ≠ 0)]) (w i) (w i)
    simp only [psum]
    rw [this, Fintype.sum_prod_type]
    simp only [w, blk_psum ha, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have := sum_extend he (fun x y => jf p x * y) (by simp) (w k) (w i)
    simp only at this
    rw [this, Fintype.sum_prod_type]
    simp only [w, blk_inner ha]
    have h : ∀ b, (if C k b = C i b then a ^ p + 2 else 1 - a ^ (p - 1) - a) =
        (1 - a ^ (p - 1) - a) + (a ^ p + 2 - (1 - a ^ (p - 1) - a)) *
          (if C k b = C i b then 1 else 0) := by
      intro b; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Two distinct points form a strict SAS. -/
lemma two_point {p : ℝ} (hp0 : p ≠ 0) {d : ℕ} (hd : 0 < d) :
    IsStrictSAS (lpDist p) (fun (i : Fin 2) (_ : Fin d) => ((i : ℕ) : ℝ)) := by
  intro i j k hij hki
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := by omega
  obtain rfl : k = 1 := by omega
  simp only [lpDist, Fin.isValue, Fin.val_one, Nat.cast_one, sub_self, abs_zero,
    Real.zero_rpow hp0, Finset.sum_const_zero]
  rw [Real.zero_rpow (one_div_ne_zero hp0)]
  simpa using Real.rpow_pos_of_pos (by exact_mod_cast hd : (0:ℝ) < d) _

end LpLarge

/-- The `1 < p < ∞`, `p ≠ 2` case, assuming the code lemma (`Proof.Codes.exists_code`) as a
hypothesis. -/
theorem lp_large_strict_sas_exponential_of_codes
    (hcodes : ∀ q : ℕ, 2 ≤ q → ∀ δ : ℝ, 0 < δ →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ N : ℕ, exp (c * n) ≤ N ∧ ∃ C : Fin N → (Fin n → Fin q),
        ∀ i j, i ≠ j →
          ((Finset.univ.filter fun b => C i b = C j b).card : ℝ) ≤ (1 / q + δ) * n)
    (p : ℝ) (hp1 : 1 < p) (hp2 : p ≠ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, ∃ ℓ : ℕ, exp (c * d) ≤ ℓ ∧
      ∃ x : Fin ℓ → (Fin d → ℝ), IsStrictSAS (lpDist p) x := by
  have hp0 : p ≠ 0 := by linarith
  -- the block parameter `a`, strictly between `2` and `2 ^ (1 / (p - 1))`
  set b : ℝ := (2:ℝ) ^ (p - 1)⁻¹ with hbdef
  set a : ℝ := (2 + b) / 2 with hadef
  have hp1' : 0 < p - 1 := by linarith
  have hb0 : 0 < b := by positivity
  have hbp : b ^ (p - 1) = 2 := Real.rpow_inv_rpow (by norm_num) hp1'.ne'
  have ha0 : 0 < a := by positivity
  have hkey : (a ^ (p - 1) - 2) * (a - 2) < 0 := by
    rcases lt_or_gt_of_ne hp2 with h | h
    · have hb2 : 2 < b := by
        have h1 : (1:ℝ) < (p - 1)⁻¹ := (one_lt_inv₀ hp1').2 (by linarith)
        have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) h1
        rwa [Real.rpow_one] at this
      have h1 : a ^ (p - 1) < b ^ (p - 1) := Real.rpow_lt_rpow ha0.le (by linarith) hp1'
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have hb2 : b < 2 := by
        have h1 : (p - 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) h1
        rwa [Real.rpow_one] at this
      have h1 : b ^ (p - 1) < a ^ (p - 1) := Real.rpow_lt_rpow hb0.le (by linarith) hp1'
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  -- per-block contributions: `A` on agreement, `B` on disagreement
  set A : ℝ := a ^ p + 2 with hAdef
  set B : ℝ := 1 - a ^ (p - 1) - a with hBdef
  have hap : a ^ (p - 1) * a = a ^ p := by
    rw [Real.rpow_sub_one ha0.ne', div_mul_cancel₀ _ ha0.ne']
  have hAB2 : A + 2 * B < 0 := by
    have : A + 2 * B = (a ^ (p - 1) - 2) * (a - 2) := by rw [hAdef, hBdef, ← hap]; ring
    linarith
  have hA : 0 < A := by positivity
  have hAB : 0 < A - B := by
    have h1 : 0 < a ^ (p - 1) := by positivity
    have h2 : 0 < a ^ p := by positivity
    rw [hAdef, hBdef]
    linarith
  set δ : ℝ := -(A + 2 * B) / (6 * (A - B)) with hδdef
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  set κ : ℝ := -(A + 2 * B) / (6 * A) with hκdef
  have hκ : 0 < κ := div_pos (by linarith) (by positivity)
  have hABδ : (A - B) * δ = -(A + 2 * B) / 6 := by
    rw [hδdef]; field_simp
  have hκA : κ * A = -(A + 2 * B) / 6 := by
    rw [hκdef]; field_simp
  obtain ⟨c₀, hc₀, hN⟩ := hcodes 3 (by norm_num) δ hδ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (c₀ / 9) (Real.log 2 / 2), lt_min (by positivity) (by positivity), fun d => ?_⟩
  set c := min (c₀ / 9) (Real.log 2 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c ≤ c₀ / 9 := min_le_left _ _
  have hc2 : c ≤ Real.log 2 / 2 := min_le_right _ _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: a single point
    refine ⟨1, by simp, fun _ _ => 0, fun i j k hij _ => ?_⟩
    exact absurd hij (by omega)
  by_cases hn : d / 3 = 0
  · -- `d ∈ {1, 2}`: two distinct points
    refine ⟨2, ?_, fun i _ => (i : ℝ), fun i j k hij hki => ?_⟩
    · have hd2 : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
      have : c * d ≤ Real.log 2 := by nlinarith
      calc exp (c * d) ≤ exp (Real.log 2) := exp_le_exp.2 this
        _ = 2 := Real.exp_log (by norm_num)
        _ = ((2:ℕ):ℝ) := by norm_num
    · exact LpLarge.two_point hp0 hd i j k hij hki
  -- main case: the code vectors
  set n := d / 3 with hndef
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨N, hNe, C, hC⟩ := hN n
  obtain ⟨v, hv1, hv2⟩ := LpLarge.code_vectors hp1 ha0 (by omega : n * 3 ≤ d) C
  have hS : 0 < (n : ℝ) * A := by positivity
  have hinner : ∀ i k, i ≠ k → ∑ r, LpLarge.jf p (v k r) * v i r ≤ -(κ * (n * A)) := by
    intro i k hik
    rw [hv2]
    have hag := hC k i (Ne.symm hik)
    push_cast at hag
    have h1 := mul_le_mul_of_nonneg_left hag hAB.le
    have h3 : (A - B) * ((1 / 3 + δ) * n) = (A - B) / 3 * n - (A + 2 * B) / 6 * n := by
      rw [show (A - B) * ((1 / 3 + δ) * n) = (A - B) / 3 * n + ((A - B) * δ) * n by ring, hABδ]
      ring
    have h2 : κ * (n * A) = -(A + 2 * B) / 6 * n := by rw [← hκA]; ring
    rw [h2]
    linarith
  obtain ⟨η, -, hη⟩ := LpLarge.strictSAS_of_family hp1 v hS hκ hv1 hinner
  refine ⟨N, ?_, _, hη⟩
  have hd9 : (d : ℝ) ≤ 9 * n := by exact_mod_cast (by omega : d ≤ 9 * n)
  have : c * d ≤ c₀ * n := by nlinarith
  exact le_trans (exp_le_exp.2 this) hNe

end SelfApproaching.Proof
