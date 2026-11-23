import Mathlib

/-!
# Asymptotic expansion of `∫₀³ cos(πnx/3) x^β dx`

For `β > -1` and `n ≠ 0`, the cosine integral `J_β(n) = ∫₀³ cos(πnx/3) x^β dx` equals a finite
sum `∑_{j<m} A_j (-1)^n / n^{2j+2}` up to an error `O(|n|^{-(β+1)})`.

* `osc_base`: for `-1 < γ ≤ 0` and `|ω| ≥ 1`, `|∫₀³ cos(ωx + φ) x^γ dx| ≤ C |ω|^{-(γ+1)}`
  (split the integral at `1/|ω|`, integrate by parts on the far part).
* `ibp_cos`, `ibp_sin`: one integration by parts.
* `cos_integral_rec`: the two-step recursion `J_β = (-1)^n a / n² - b / n² · J_{β-2}`.
* `cos_integral_decomp`: the expansion, by induction on the number of steps.
-/

namespace SelfApproaching.Proof.LpAspectSharp

open Real MeasureTheory intervalIntegral Set

/-- The basic oscillatory estimate for an integrable singularity `x^γ`, `-1 < γ ≤ 0`. -/
lemma osc_base (γ φ ω : ℝ) (hγ1 : -1 < γ) (hγ0 : γ ≤ 0) (hω : 1 ≤ |ω|) :
    |∫ x in (0 : ℝ)..3, Real.cos (ω * x + φ) * x ^ γ| ≤
      (1 / (γ + 1) + 2) * (|ω|⁻¹) ^ (γ + 1) := by
  set δ : ℝ := |ω|⁻¹ with hδ
  have hω0 : 0 < |ω| := by linarith
  have hω0' : ω ≠ 0 := abs_pos.mp hω0
  have hδ0 : 0 < δ := inv_pos.mpr hω0
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hω
  have hγ1' : 0 < γ + 1 := by linarith
  have hint_rpow : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x ^ γ) volume a b :=
    fun a b => intervalIntegral.intervalIntegrable_rpow' hγ1
  have hf : ∀ a b : ℝ, IntervalIntegrable (fun x => Real.cos (ω * x + φ) * x ^ γ) volume a b :=
    fun a b => (hint_rpow a b).continuousOn_mul (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf 0 δ) (hf δ 3)]
  -- the near part
  have hnear : |∫ x in (0 : ℝ)..δ, Real.cos (ω * x + φ) * x ^ γ| ≤ δ ^ (γ + 1) / (γ + 1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hδ0.le
      (f := fun x => Real.cos (ω * x + φ) * x ^ γ) (g := fun x => x ^ γ)
      (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le γ)]
        calc |Real.cos (ω * x + φ)| * x ^ γ ≤ 1 * x ^ γ :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.rpow_nonneg hx.1.le γ)
          _ = x ^ γ := one_mul _) (hint_rpow 0 δ)
    rw [Real.norm_eq_abs, integral_rpow (Or.inl hγ1), Real.zero_rpow hγ1'.ne', sub_zero] at h
    exact h
  -- the far part: integrate by parts on `[δ, 3]`
  have hpos : ∀ x ∈ uIcc δ 3, 0 < x := fun x hx => by
    rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1]
  set Φ : ℝ → ℝ := fun x => x ^ γ * Real.sin (ω * x + φ) / ω with hΦ
  set f2 : ℝ → ℝ := fun x => γ * x ^ (γ - 1) * Real.sin (ω * x + φ) / ω with hf2
  have hderΦ : ∀ x ∈ uIcc δ 3,
      HasDerivAt Φ (Real.cos (ω * x + φ) * x ^ γ + f2 x) x := by
    intro x hx
    have h1 := Real.hasDerivAt_rpow_const (p := γ) (Or.inl (hpos x hx).ne')
    have hs : HasDerivAt (fun x => Real.sin (ω * x + φ)) (Real.cos (ω * x + φ) * ω) x := by
      simpa using (((hasDerivAt_id x).const_mul ω).add_const φ).sin
    convert (h1.mul hs).div_const ω using 1
    simp only [hf2]
    field_simp
    ring
  have hf2c : ContinuousOn f2 (uIcc δ 3) := by
    intro x hx
    have : ContinuousAt (fun x : ℝ => x ^ (γ - 1)) x :=
      Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne')
    exact (((continuousAt_const.mul this).mul (by fun_prop)).div_const _).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderΦ
    ((hf δ 3).add hf2c.intervalIntegrable)
  rw [intervalIntegral.integral_add (hf δ 3) hf2c.intervalIntegrable] at hFTC
  have hΦb : ∀ x, 0 < x → |Φ x| ≤ x ^ γ * δ := fun x hx => by
    simp only [hΦ, hδ]
    rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _), div_eq_mul_inv]
    gcongr
    calc x ^ γ * |Real.sin (ω * x + φ)| ≤ x ^ γ * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.rpow_nonneg hx.le γ)
      _ = x ^ γ := mul_one _
  -- the remaining integral
  set g : ℝ → ℝ := fun x => -γ * x ^ (γ - 1) * δ with hg
  have hderg : ∀ x ∈ uIcc δ 3, HasDerivAt (fun x => -(x ^ γ) * δ) (g x) x := by
    intro x hx
    have h1 := Real.hasDerivAt_rpow_const (p := γ) (Or.inl (hpos x hx).ne')
    convert (h1.neg).mul_const δ using 1
    simp only [hg]; ring
  have hgc : ContinuousOn g (uIcc δ 3) := by
    intro x hx
    have : ContinuousAt (fun x : ℝ => x ^ (γ - 1)) x :=
      Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne')
    exact ((continuousAt_const.mul this).mul continuousAt_const).continuousWithinAt
  have hgint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderg hgc.intervalIntegrable
  have hrest : |∫ x in δ..3, f2 x| ≤ δ ^ γ * δ - 3 ^ γ * δ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (by linarith : δ ≤ 3) (f := f2) (g := g)
      (Filter.Eventually.of_forall fun x hx => by
        have hx0 : 0 < x := by linarith [hx.1]
        simp only [hf2, hg, hδ]
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_nonpos hγ0,
          abs_of_nonneg (Real.rpow_nonneg hx0.le (γ - 1)), div_eq_mul_inv]
        have h0 : 0 ≤ -γ * x ^ (γ - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
        calc -γ * x ^ (γ - 1) * |Real.sin (ω * x + φ)| * |ω|⁻¹
            ≤ -γ * x ^ (γ - 1) * 1 * |ω|⁻¹ := by
              gcongr; exact Real.abs_sin_le_one _
          _ = -γ * x ^ (γ - 1) * |ω|⁻¹ := by ring) (hgc.intervalIntegrable (μ := volume))
    rw [Real.norm_eq_abs, hgint] at h
    linarith
  have hfar : |∫ x in δ..3, Real.cos (ω * x + φ) * x ^ γ| ≤ 2 * (δ ^ γ * δ) := by
    have e : ∫ x in δ..3, Real.cos (ω * x + φ) * x ^ γ = Φ 3 - Φ δ - ∫ x in δ..3, f2 x := by
      linarith
    rw [e]
    have h3 := hΦb 3 (by norm_num)
    have hd := hΦb δ hδ0
    calc |Φ 3 - Φ δ - ∫ x in δ..3, f2 x| ≤ |Φ 3| + |Φ δ| + |∫ x in δ..3, f2 x| := by
          have := abs_sub (Φ 3 - Φ δ) (∫ x in δ..3, f2 x)
          have := abs_sub (Φ 3) (Φ δ)
          linarith
      _ ≤ 3 ^ γ * δ + δ ^ γ * δ + (δ ^ γ * δ - 3 ^ γ * δ) := by gcongr
      _ = 2 * (δ ^ γ * δ) := by ring
  rw [← Real.rpow_add_one hδ0.ne'] at hfar
  calc |(∫ x in (0 : ℝ)..δ, Real.cos (ω * x + φ) * x ^ γ) +
        ∫ x in δ..3, Real.cos (ω * x + φ) * x ^ γ|
      ≤ |∫ x in (0 : ℝ)..δ, Real.cos (ω * x + φ) * x ^ γ| +
        |∫ x in δ..3, Real.cos (ω * x + φ) * x ^ γ| := abs_add_le _ _
    _ ≤ δ ^ (γ + 1) / (γ + 1) + 2 * δ ^ (γ + 1) := add_le_add hnear hfar
    _ = (1 / (γ + 1) + 2) * δ ^ (γ + 1) := by ring

/-- One integration by parts for the cosine integral. -/
lemma ibp_cos (β ω : ℝ) (hβ : 0 < β) (hω : ω ≠ 0) :
    ∫ x in (0 : ℝ)..3, Real.cos (ω * x) * x ^ β =
      3 ^ β * Real.sin (ω * 3) / ω - β / ω * ∫ x in (0 : ℝ)..3, Real.sin (ω * x) * x ^ (β - 1) := by
  set Φ : ℝ → ℝ := fun x => x ^ β * Real.sin (ω * x) / ω with hΦ
  have hder : ∀ x ∈ Ioo (0 : ℝ) 3, HasDerivAt Φ
      (Real.cos (ω * x) * x ^ β + β / ω * (Real.sin (ω * x) * x ^ (β - 1))) x := by
    intro x hx
    have h1 := Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.1.ne')
    have hs : HasDerivAt (fun x => Real.sin (ω * x)) (Real.cos (ω * x) * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).sin
    convert (h1.mul hs).div_const ω using 1
    field_simp
    ring
  have hcont : ContinuousOn Φ (Icc 0 3) :=
    (((Real.continuous_rpow_const hβ.le).mul (by fun_prop)).div_const _).continuousOn
  have hi1 : IntervalIntegrable (fun x => Real.cos (ω * x) * x ^ β) volume 0 3 :=
    ((by fun_prop : Continuous fun x : ℝ => Real.cos (ω * x)).mul
      (Real.continuous_rpow_const hβ.le)).intervalIntegrable _ _
  have hi2' : IntervalIntegrable (fun x => Real.sin (ω * x) * x ^ (β - 1)) volume 0 3 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).continuousOn_mul (by fun_prop)
  have hi2 := hi2'.const_mul (β / ω)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 3)
    hcont hder (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at h
  simp only [hΦ, Real.zero_rpow hβ.ne', zero_mul, zero_div, sub_zero] at h
  linarith

/-- One integration by parts for the sine integral. -/
lemma ibp_sin (β ω : ℝ) (hβ : 0 < β) (hω : ω ≠ 0) :
    ∫ x in (0 : ℝ)..3, Real.sin (ω * x) * x ^ β =
      -(3 ^ β * Real.cos (ω * 3) / ω) +
        β / ω * ∫ x in (0 : ℝ)..3, Real.cos (ω * x) * x ^ (β - 1) := by
  set Φ : ℝ → ℝ := fun x => -(x ^ β * Real.cos (ω * x) / ω) with hΦ
  have hder : ∀ x ∈ Ioo (0 : ℝ) 3, HasDerivAt Φ
      (Real.sin (ω * x) * x ^ β - β / ω * (Real.cos (ω * x) * x ^ (β - 1))) x := by
    intro x hx
    have h1 := Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.1.ne')
    have hc : HasDerivAt (fun x => Real.cos (ω * x)) (-Real.sin (ω * x) * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).cos
    convert ((h1.mul hc).div_const ω).neg using 1
    field_simp
    ring
  have hcont : ContinuousOn Φ (Icc 0 3) :=
    (((Real.continuous_rpow_const hβ.le).mul (by fun_prop)).div_const _).neg.continuousOn
  have hi1 : IntervalIntegrable (fun x => Real.sin (ω * x) * x ^ β) volume 0 3 :=
    ((by fun_prop : Continuous fun x : ℝ => Real.sin (ω * x)).mul
      (Real.continuous_rpow_const hβ.le)).intervalIntegrable _ _
  have hi2' : IntervalIntegrable (fun x => Real.cos (ω * x) * x ^ (β - 1)) volume 0 3 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).continuousOn_mul (by fun_prop)
  have hi2 := hi2'.const_mul (β / ω)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 3)
    hcont hder (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at h
  simp only [hΦ, Real.zero_rpow hβ.ne', zero_mul, zero_div, neg_zero, sub_zero] at h
  linarith

lemma abs_omega_ge (n : ℤ) : |(n : ℝ)| ≤ |π * n / 3| := by
  have h3 : (3 : ℝ) < π := Real.pi_gt_three
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    le_div_iff₀ (by norm_num)]
  have : 0 ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith

lemma one_le_abs_int (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn

lemma inv_omega_rpow_le (n : ℤ) (hn : n ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (|π * n / 3|⁻¹) ^ s ≤ 1 / |(n : ℝ)| ^ s := by
  have h1 := one_le_abs_int n hn
  have h2 := abs_omega_ge n
  rw [one_div, ← Real.inv_rpow (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (inv_anti₀ (by linarith) h2) hs

/-- The base case `-1 < β ≤ 1`. -/
lemma cos_integral_base (β : ℝ) (h1 : -1 < β) (h2 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      |∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ β| ≤ C / |(n : ℝ)| ^ (β + 1) := by
  rcases le_or_gt β 0 with hb | hb
  · have hC : 0 ≤ 1 / (β + 1) + 2 := by
      have : 0 < β + 1 := by linarith
      positivity
    refine ⟨1 / (β + 1) + 2, hC, fun n hn => ?_⟩
    have hω : 1 ≤ |π * n / 3| := (one_le_abs_int n hn).trans (abs_omega_ge n)
    have h := osc_base β 0 (π * n / 3) h1 hb hω
    simp only [add_zero] at h
    calc _ ≤ _ := h
      _ ≤ (1 / (β + 1) + 2) * (1 / |(n : ℝ)| ^ (β + 1)) :=
          mul_le_mul_of_nonneg_left (inv_omega_rpow_le n hn (by linarith)) hC
      _ = _ := by ring
  · have hC : 0 ≤ β * (1 / β + 2) := by positivity
    refine ⟨β * (1 / β + 2), hC, fun n hn => ?_⟩
    set ω : ℝ := π * n / 3 with hωdef
    have hω : 1 ≤ |ω| := (one_le_abs_int n hn).trans (abs_omega_ge n)
    have hω0 : ω ≠ 0 := by intro h; rw [h, abs_zero] at hω; linarith
    rw [ibp_cos β ω hb hω0]
    have hs : Real.sin (ω * 3) = 0 := by
      rw [show ω * 3 = (n : ℝ) * π by rw [hωdef]; ring]
      exact Real.sin_int_mul_pi n
    rw [hs, mul_zero, zero_div, zero_sub, abs_neg, abs_mul]
    have hS : ∫ x in (0 : ℝ)..3, Real.sin (ω * x) * x ^ (β - 1) =
        ∫ x in (0 : ℝ)..3, Real.cos (ω * x + -(π / 2)) * x ^ (β - 1) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [← sub_eq_add_neg, Real.cos_sub_pi_div_two]
    rw [hS]
    have hb' := osc_base (β - 1) (-(π / 2)) ω (by linarith) (by linarith) hω
    rw [show β - 1 + 1 = β by ring] at hb'
    have hωpos : 0 < |ω| := by linarith
    have hβω : |β / ω| = β * |ω|⁻¹ := by
      rw [abs_div, abs_of_pos hb, div_eq_mul_inv]
    rw [hβω]
    have hpow : |ω|⁻¹ * (|ω|⁻¹) ^ β = (|ω|⁻¹) ^ (β + 1) := by
      rw [Real.rpow_add_one (inv_pos.mpr hωpos).ne']; ring
    have hle := inv_omega_rpow_le n hn (s := β + 1) (by linarith)
    rw [← hωdef] at hle
    calc β * |ω|⁻¹ * |∫ x in (0 : ℝ)..3, Real.cos (ω * x + -(π / 2)) * x ^ (β - 1)|
        ≤ β * |ω|⁻¹ * ((1 / β + 2) * (|ω|⁻¹) ^ β) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = β * (1 / β + 2) * (|ω|⁻¹ * (|ω|⁻¹) ^ β) := by ring
      _ ≤ β * (1 / β + 2) * (1 / |(n : ℝ)| ^ (β + 1)) := by
          rw [hpow]; gcongr
      _ = β * (1 / β + 2) / |(n : ℝ)| ^ (β + 1) := by ring

/-- The two-step recursion `J_β = (-1)^n a / n² - b / n² · J_{β-2}` for `β > 1`. -/
lemma cos_integral_rec (β : ℝ) (hβ : 1 < β) (n : ℤ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ β =
      9 * β * 3 ^ (β - 1) / π ^ 2 * (-1 : ℝ) ^ n / (n : ℝ) ^ 2 -
        9 * β * (β - 1) / π ^ 2 / (n : ℝ) ^ 2 *
          ∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ (β - 2) := by
  set ω : ℝ := π * n / 3 with hωdef
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hω0 : ω ≠ 0 := by rw [hωdef]; have := Real.pi_pos; positivity
  rw [ibp_cos β ω (by linarith) hω0, ibp_sin (β - 1) ω (by linarith) hω0,
    show β - 1 - 1 = β - 2 by ring]
  have hs : Real.sin (ω * 3) = 0 := by
    rw [show ω * 3 = (n : ℝ) * π by rw [hωdef]; ring]
    exact Real.sin_int_mul_pi n
  have hc : Real.cos (ω * 3) = (-1 : ℝ) ^ n := by
    rw [show ω * 3 = (n : ℝ) * π by rw [hωdef]; ring]
    exact Real.cos_int_mul_pi n
  rw [hs, hc, hωdef]
  have := Real.pi_pos
  field_simp
  ring

/-- The expansion with a prescribed number `m` of steps. -/
lemma cos_integral_decomp_aux (m : ℕ) :
    ∀ β : ℝ, -1 < β - 2 * m → β - 2 * m ≤ 1 →
      ∃ (A : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
        |(∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ β) -
          ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2)| ≤
            C / |(n : ℝ)| ^ (β + 1) := by
  induction m with
  | zero =>
    intro β h1 h2
    simp only [CharP.cast_eq_zero, mul_zero, sub_zero] at h1 h2
    obtain ⟨C, hC, h⟩ := cos_integral_base β h1 h2
    exact ⟨fun _ => 0, C, hC, fun n hn => by simpa using h n hn⟩
  | succ m ih =>
    intro β h1 h2
    push_cast at h1 h2
    have hβ : 1 < β := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    obtain ⟨A, C, hC, h⟩ := ih (β - 2) (by linarith) (by linarith)
    set a : ℝ := 9 * β * 3 ^ (β - 1) / π ^ 2 with ha
    set b : ℝ := 9 * β * (β - 1) / π ^ 2 with hb
    have hb0 : 0 ≤ b := by
      rw [hb]; have : 0 ≤ β - 1 := by linarith
      have : 0 ≤ β := by linarith
      positivity
    refine ⟨fun j => match j with
      | 0 => a
      | j + 1 => -b * A j, b * C, mul_nonneg hb0 hC, fun n hn => ?_⟩
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [cos_integral_rec β hβ n hn, Finset.sum_range_succ']
    set R := (∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ (β - 2)) -
      ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2) with hR
    have hsum : ∑ j ∈ Finset.range m, -b * A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * (j + 1) + 2) =
        -b / (n : ℝ) ^ 2 *
          ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by ring, pow_add]
      field_simp
    have e : a * (-1 : ℝ) ^ n / (n : ℝ) ^ 2 - b / (n : ℝ) ^ 2 *
        (∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ (β - 2)) -
        (∑ j ∈ Finset.range m, -b * A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * (j + 1) + 2) +
          a * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * 0 + 2)) = -(b / (n : ℝ) ^ 2 * R) := by
      rw [hsum, hR]; ring
    simp only [] at e ⊢
    rw [e, abs_neg, abs_mul, abs_div, abs_of_nonneg hb0, abs_pow]
    have hnpos : 0 < |(n : ℝ)| := abs_pos.mpr hn'
    have hpow : |(n : ℝ)| ^ (β + 1) = |(n : ℝ)| ^ 2 * |(n : ℝ)| ^ (β - 2 + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]; norm_num; ring_nf
    calc b / |(n : ℝ)| ^ 2 * |R| ≤ b / |(n : ℝ)| ^ 2 * (C / |(n : ℝ)| ^ (β - 2 + 1)) := by
          gcongr; exact h n hn
      _ = b * C / |(n : ℝ)| ^ (β + 1) := by
          rw [hpow]
          have : 0 < |(n : ℝ)| ^ (β - 2 + 1) := Real.rpow_pos_of_pos hnpos _
          field_simp

theorem cos_integral_decomp (β : ℝ) (hβ : -1 < β) :
    ∃ (m : ℕ) (A : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      |(∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ β) -
        ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2)| ≤
          C / |(n : ℝ)| ^ (β + 1) := by
  set m := ⌈(β - 1) / 2⌉₊ with hm
  have h1 : -1 < β - 2 * m := by
    rcases le_or_gt ((β - 1) / 2) 0 with h | h
    · rw [hm, Nat.ceil_eq_zero.mpr h]; simpa using hβ
    · have := Nat.ceil_lt_add_one h.le
      rw [← hm] at this
      linarith
  have h2 : β - 2 * m ≤ 1 := by
    have := Nat.le_ceil ((β - 1) / 2)
    rw [← hm] at this
    linarith
  obtain ⟨A, C, hC, h⟩ := cos_integral_decomp_aux m β h1 h2
  exact ⟨m, A, C, hC, h⟩

end SelfApproaching.Proof.LpAspectSharp
