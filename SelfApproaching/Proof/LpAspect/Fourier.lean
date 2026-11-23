import Mathlib

/-!
# A separable approximation of `|a - b|^p`

For `p ≥ 1` we approximate `|t|^p` on `[-2, 2]` by a partial sum of the Fourier series of the
`6`-periodic extension of `|t|^p` from `[-3, 3]`. Two integrations by parts show that the
Fourier coefficients are `O(1/n²)`, so the partial sum over `|n| ≤ K` has error `O(1/K)`.
Since `exp(iω(a - b)) = exp(iωa) exp(-iωb)`, the partial sum evaluated at `a - b` is a sum of
`O(K)` products `φ(a) ψ(b)`.
-/

namespace SelfApproaching.Proof.LpAspect

open Real MeasureTheory intervalIntegral Set

noncomputable section

/-- The cosine integral `∫₀³ cos(πn x/3) x^p dx` is `O(1/n²)`. -/
lemma cos_integral_bound (p : ℝ) (hp : 1 ≤ p) (n : ℤ) (hn : n ≠ 0) :
    |∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p| ≤ (2 * p * 3 ^ (p - 1) + p) / n ^ 2 := by
  set ω : ℝ := π * n / 3 with hω
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hω0 : ω ≠ 0 := by rw [hω]; have := Real.pi_pos; positivity
  have hω2 : (n : ℝ) ^ 2 ≤ ω ^ 2 := by
    rw [hω, div_pow, mul_pow, le_div_iff₀ (by norm_num)]
    have h3 : (3 : ℝ) ^ 2 ≤ π ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    nlinarith [sq_nonneg (n : ℝ)]
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  set g : ℝ → ℝ := fun x => p * (p - 1) * x ^ (p - 2) with hg
  set Φ : ℝ → ℝ := fun x =>
    x ^ p * Real.sin (ω * x) / ω + p * x ^ (p - 1) * Real.cos (ω * x) / ω ^ 2 with hΦ
  set Ψ : ℝ → ℝ := fun x => p * x ^ (p - 1) with hΨ
  have hg_nonneg : ∀ x, 0 ≤ x → 0 ≤ g x := fun x hx => by
    simp only [hg]
    have : 0 ≤ p - 1 := by linarith
    have := Real.rpow_nonneg hx (p - 2)
    positivity
  have hg_int : IntervalIntegrable g volume 0 3 := by
    rcases eq_or_lt_of_le hp with h1 | h1
    · have : g = fun _ => 0 := by
        funext x; simp [hg, ← h1]
      rw [this]; exact _root_.intervalIntegrable_const
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  have hpow : ∀ q : ℝ, 0 ≤ q → ContinuousOn (fun x : ℝ => x ^ q) (Icc 0 3) := fun q hq =>
    (Real.continuous_rpow_const hq).continuousOn
  -- derivatives on `(0, 3)`
  have hderΦ : ∀ x ∈ Ioo (0 : ℝ) 3,
      HasDerivAt Φ (Real.cos (ω * x) * x ^ p + g x * Real.cos (ω * x) / ω ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl hx0)
    have h2 := Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx0)
    have hs : HasDerivAt (fun x => Real.sin (ω * x)) (Real.cos (ω * x) * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).sin
    have hc : HasDerivAt (fun x => Real.cos (ω * x)) (-Real.sin (ω * x) * ω) x := by
      simpa using ((hasDerivAt_id x).const_mul ω).cos
    have := ((h1.mul hs).div_const ω).add (((h2.const_mul p).mul hc).div_const (ω ^ 2))
    convert this using 1
    simp only [hg]
    have e : x ^ (p - 2) = x ^ (p - 1 - 1) := by ring_nf
    rw [e]
    field_simp
    ring
  have hderΨ : ∀ x ∈ Ioo (0 : ℝ) 3, HasDerivAt Ψ (g x) x := by
    intro x hx
    have h2 := (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx.1.ne')).const_mul p
    convert h2 using 1
    simp only [hg]
    have e : x ^ (p - 2) = x ^ (p - 1 - 1) := by ring_nf
    rw [e]; ring
  have hcontΦ : ContinuousOn Φ (Icc 0 3) := by
    simp only [hΦ]
    refine ContinuousOn.add ?_ ?_
    · exact ((hpow p (by linarith)).mul (by fun_prop)).div_const _
    · exact (((hpow (p - 1) (by linarith)).const_smul p).mul (by fun_prop)).div_const _
  have hcontΨ : ContinuousOn Ψ (Icc 0 3) :=
    (hpow (p - 1) (by linarith)).const_smul p
  have hint1 : IntervalIntegrable (fun x => Real.cos (ω * x) * x ^ p) volume 0 3 :=
    (Continuous.intervalIntegrable (by
      exact (by fun_prop : Continuous fun x => Real.cos (ω * x)).mul
        (Real.continuous_rpow_const (by linarith))) _ _)
  have hint2 : IntervalIntegrable (fun x => g x * Real.cos (ω * x) / ω ^ 2) volume 0 3 :=
    (hg_int.mul_continuousOn (by fun_prop)).div_const _
  have hFTC1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 3)
    hcontΦ hderΦ (hint1.add hint2)
  have hFTC2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 3)
    hcontΨ hderΨ hg_int
  rw [intervalIntegral.integral_add hint1 hint2] at hFTC1
  have hmain : ∫ x in (0 : ℝ)..3, Real.cos (ω * x) * x ^ p =
      Φ 3 - Φ 0 - ∫ x in (0 : ℝ)..3, g x * Real.cos (ω * x) / ω ^ 2 := by linarith
  have hω2pos : 0 < ω ^ 2 := by positivity
  have hrest : |∫ x in (0 : ℝ)..3, g x * Real.cos (ω * x) / ω ^ 2| ≤ p * 3 ^ (p - 1) / ω ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 3)
      (f := fun x => g x * Real.cos (ω * x) / ω ^ 2) (g := fun x => g x / ω ^ 2)
      (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (hg_nonneg x hx.1.le),
          abs_of_pos hω2pos]
        apply div_le_div_of_nonneg_right _ hω2pos.le
        calc g x * |Real.cos (ω * x)| ≤ g x * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hg_nonneg x hx.1.le)
          _ = g x := mul_one _) (hg_int.div_const _)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq_of_le (intervalIntegral.integral_div _ _) ?_)
    rw [hFTC2]
    apply div_le_div_of_nonneg_right _ hω2pos.le
    simp only [hΨ]
    have : 0 ≤ p * (0 : ℝ) ^ (p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg le_rfl _)
    linarith
  have hΦ3 : |Φ 3| ≤ p * 3 ^ (p - 1) / ω ^ 2 := by
    have hs : Real.sin (ω * 3) = 0 := by
      rw [show ω * 3 = (n : ℝ) * π by rw [hω]; ring]
      exact Real.sin_int_mul_pi n
    simp only [hΦ, hs, mul_zero, zero_div, zero_add]
    rw [abs_div, abs_of_pos hω2pos]
    gcongr
    have h3 : 0 ≤ p * (3 : ℝ) ^ (p - 1) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    rw [abs_mul, abs_of_nonneg h3]
    calc p * 3 ^ (p - 1) * |Real.cos (ω * 3)| ≤ p * 3 ^ (p - 1) * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hΦ0 : |Φ 0| ≤ p / ω ^ 2 := by
    simp only [hΦ, mul_zero, Real.sin_zero, Real.cos_zero, zero_div, zero_add, mul_one]
    rw [abs_div, abs_of_pos hω2pos]
    gcongr
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p),
      abs_of_nonneg (Real.rpow_nonneg le_rfl _)]
    calc p * (0 : ℝ) ^ (p - 1) ≤ p * 1 := by
          gcongr; exact Real.zero_rpow_le_one _
      _ = p := mul_one _
  have htot : |∫ x in (0 : ℝ)..3, Real.cos (ω * x) * x ^ p| ≤
      (2 * p * 3 ^ (p - 1) + p) / ω ^ 2 := by
    rw [hmain]
    calc |Φ 3 - Φ 0 - ∫ x in (0 : ℝ)..3, g x * Real.cos (ω * x) / ω ^ 2|
        ≤ |Φ 3| + |Φ 0| + |∫ x in (0 : ℝ)..3, g x * Real.cos (ω * x) / ω ^ 2| := by
          have := abs_sub (Φ 3 - Φ 0) (∫ x in (0 : ℝ)..3, g x * Real.cos (ω * x) / ω ^ 2)
          have := abs_sub (Φ 3) (Φ 0)
          linarith
      _ ≤ p * 3 ^ (p - 1) / ω ^ 2 + p / ω ^ 2 + p * 3 ^ (p - 1) / ω ^ 2 := by
          gcongr
      _ = (2 * p * 3 ^ (p - 1) + p) / ω ^ 2 := by ring
  refine htot.trans ?_
  have : 0 ≤ 2 * p * 3 ^ (p - 1) + p := by
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) (p - 1)
    have : 0 ≤ p := by linarith
    positivity
  exact div_le_div_of_nonneg_left this hn2 hω2

/-! ### Tail bounds for `∑ 1/n²` -/

/-- `W K k = 1/k²` for `k > K`, and `0` otherwise. -/
def tailW (K k : ℕ) : ℝ := if k ≤ K then 0 else 1 / (k : ℝ) ^ 2

lemma tailW_nonneg (K k : ℕ) : 0 ≤ tailW K k := by
  unfold tailW; split_ifs <;> positivity

lemma sum_range_tailW (K N : ℕ) : ∑ i ∈ Finset.range N, tailW K i ≤ 2 / (K + 1) := by
  unfold tailW
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  have : (Finset.range N).filter (fun i => ¬ i ≤ K) = Finset.Ioo K N := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega
  rw [this]
  simpa only [one_div] using sum_Ioo_inv_sq_le (α := ℝ) K N

lemma sum_range_tailW_succ (K N : ℕ) : ∑ i ∈ Finset.range N, tailW K (i + 1) ≤ 2 / (K + 1) := by
  have h := sum_range_tailW K (N + 1)
  rw [Finset.sum_range_succ'] at h
  linarith [tailW_nonneg K 0]

lemma tail_bound {f : ℤ → ℂ} {s : ℂ} (hf : HasSum f s) {B : ℝ} (hB : 0 ≤ B) (K : ℕ)
    (hb : ∀ n : ℤ, (K : ℤ) < |n| → ‖f n‖ ≤ B / (n : ℝ) ^ 2) :
    ‖s - ∑ n ∈ Finset.Icc (-(K : ℤ)) K, f n‖ ≤ 4 * B / (K + 1) := by
  set S := Finset.Icc (-(K : ℤ)) K
  have hv : HasSum (fun n => if n ∈ S then f n else 0) (∑ n ∈ S, f n) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := S)
      (f := fun n => if n ∈ S then f n else 0) (fun b hb => if_neg hb)
    rwa [Finset.sum_congr rfl (fun n hn => if_pos hn)] at this
  have hu : HasSum (fun n => if n ∈ S then 0 else f n) (s - ∑ n ∈ S, f n) := by
    convert hf.sub hv using 1
    funext n; split_ifs <;> simp
  have hs1 : Summable (fun k : ℕ => tailW K k) :=
    summable_of_sum_range_le (tailW_nonneg K) (sum_range_tailW K)
  have hs2 : Summable (fun k : ℕ => tailW K (k + 1)) :=
    summable_of_sum_range_le (fun k => tailW_nonneg K _) (sum_range_tailW_succ K)
  have hw : HasSum (fun n : ℤ => B * tailW K n.natAbs)
      (B * ∑' k, tailW K k + B * ∑' k, tailW K (k + 1)) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · simpa using hs1.hasSum.mul_left B
    · convert hs2.hasSum.mul_left B using 2 with k
  refine (hu.norm_le_of_bounded hw ?_).trans ?_
  · intro n
    split_ifs with h
    · rw [norm_zero]; exact mul_nonneg hB (tailW_nonneg _ _)
    · have hK : (K : ℤ) < |n| := by
        simp only [S, Finset.mem_Icc, not_and_or, not_le] at h
        rcases h with h | h
        · rw [abs_of_neg (by omega : n < 0)]; omega
        · rw [abs_of_pos (by omega)]; exact h
      refine (hb n hK).trans (le_of_eq ?_)
      have hK' : ¬ n.natAbs ≤ K := by
        have := Int.natCast_natAbs n
        omega
      simp only [tailW, hK', if_false]
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
      ring
  · have h1 : ∑' k, tailW K k ≤ 2 / (K + 1) :=
      Real.tsum_le_of_sum_range_le (tailW_nonneg K) (sum_range_tailW K)
    have h2 : ∑' k, tailW K (k + 1) ≤ 2 / (K + 1) :=
      Real.tsum_le_of_sum_range_le (fun k => tailW_nonneg K _) (sum_range_tailW_succ K)
    calc B * ∑' k, tailW K k + B * ∑' k, tailW K (k + 1) ≤ B * (2 / (K + 1)) + B * (2 / (K + 1)) := by
          gcongr
      _ = 4 * B / (K + 1) := by ring

/-! ### The periodic extension of `|t|^p` and its Fourier coefficients -/

theorem fact_six : Fact ((0 : ℝ) < 6) := ⟨by norm_num⟩

attribute [local instance] fact_six

/-- `|t|^p` as a complex-valued function. -/
def absPowC (p : ℝ) (t : ℝ) : ℂ := ((|t| ^ p : ℝ) : ℂ)

lemma continuous_absPowC (p : ℝ) (hp : 0 ≤ p) : Continuous (absPowC p) :=
  Complex.continuous_ofReal.comp ((Real.continuous_rpow_const hp).comp continuous_abs)

/-- The `6`-periodic extension of `|t|^p` from `[-3, 3]`. -/
def perAbsPow (p : ℝ) (hp : 0 ≤ p) : C(AddCircle (6 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco 6 (-3) (absPowC p),
    AddCircle.liftIco_continuous (by norm_num [absPowC]) (continuous_absPowC p hp).continuousOn⟩

lemma perAbsPow_apply (p : ℝ) (hp : 0 ≤ p) {t : ℝ} (ht : |t| < 3) :
    perAbsPow p hp (t : AddCircle (6 : ℝ)) = absPowC p t := by
  show AddCircle.liftIco 6 (-3) (absPowC p) (t : AddCircle (6 : ℝ)) = absPowC p t
  rw [AddCircle.liftIco_coe_apply]
  rw [abs_lt] at ht
  constructor <;> linarith [ht.1, ht.2]

lemma integral_exp_absPowC (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    ∫ x in (-3 : ℝ)..3, Complex.exp (-(2 * π * Complex.I * n * x) / 6) * absPowC p x =
      ((2 * ∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun x => Complex.exp (-(2 * π * Complex.I * n * x) / 6) * absPowC p x
    with hh
  have hc : Continuous h := by
    simp only [hh]
    exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-(2 * π * Complex.I * n * x) / 6)).mul (continuous_absPowC p hp)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ x in (-3 : ℝ)..0, h x = ∫ x in (0 : ℝ)..3, h (-x) := by
    rw [intervalIntegral.integral_comp_neg]; norm_num
  rw [hneg, ← intervalIntegral.integral_add (f := fun x => h (-x)) (g := h)
    ((hc.comp continuous_neg).intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  rw [show ((2 * ∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p : ℝ) : ℂ) =
      ∫ x in (0 : ℝ)..3, ((2 * (Real.cos (π * n / 3 * x) * x ^ p) : ℝ) : ℂ) by
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]]
  refine intervalIntegral.integral_congr fun x hx => ?_
  have hx0 : 0 ≤ x := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hx; exact hx.1
  simp only [hh, absPowC, abs_neg, abs_of_nonneg hx0]
  rw [← add_mul]
  have e : Complex.exp (-(2 * π * Complex.I * n * ((-x : ℝ) : ℂ)) / 6) +
      Complex.exp (-(2 * π * Complex.I * n * (x : ℂ)) / 6) =
      2 * Complex.cos ((π * n / 3 * x : ℝ) : ℂ) := by
    rw [Complex.two_cos]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  rw [e]
  push_cast
  ring

lemma fourierCoeff_perAbsPow (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    fourierCoeff (perAbsPow p hp) n =
      (((∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p) / 3 : ℝ) : ℂ) := by
  show fourierCoeff (AddCircle.liftIco 6 (-3) (absPowC p)) n = _
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  norm_num
  rw [integral_exp_absPowC p hp n]
  push_cast
  ring

lemma norm_fourierCoeff_perAbsPow_le (p : ℝ) (hp : 1 ≤ p) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (perAbsPow p (by linarith)) n‖ ≤ (2 * p * 3 ^ (p - 1) + p) / 3 / n ^ 2 := by
  rw [fourierCoeff_perAbsPow, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 3), div_div, mul_comm (3 : ℝ), ← div_div]
  exact div_le_div_of_nonneg_right (cos_integral_bound p hp n hn) (by norm_num)

/-! ### The separable approximation -/

/-- For `p ≥ 1`, `|a - b|^p` (for `|a - b| ≤ 2`) is approximated within `A / K` by a sum of at
most `6K` products `φ(a) ψ(b)`. -/
theorem exists_separable_approx (p : ℝ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ K : ℕ, 1 ≤ K → ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι ≤ 6 * K ∧
      ∃ φ ψ : ι → ℝ → ℝ, ∀ a b : ℝ, |a - b| ≤ 2 →
        |∑ l, φ l a * ψ l b - |a - b| ^ p| ≤ A / K := by
  have hp0 : 0 ≤ p := by linarith
  set B : ℝ := (2 * p * 3 ^ (p - 1) + p) / 3 with hB
  have hBpos : 0 < B := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (p - 1)
    have : 0 < p := by linarith
    positivity
  refine ⟨4 * B, by positivity, fun K hK => ?_⟩
  set f := perAbsPow p hp0
  set c : ℤ → ℂ := fourierCoeff f with hc
  have hcb : ∀ n : ℤ, n ≠ 0 → ‖c n‖ ≤ B / (n : ℝ) ^ 2 := fun n hn =>
    norm_fourierCoeff_perAbsPow_le p hp n hn
  have hsum : Summable c := by
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => B * (1 / (n : ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left B) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [mul_one_div]; exact hcb n hn
  set S := Finset.Icc (-(K : ℤ)) K with hS
  set e : ℤ → ℝ → ℂ := fun n t => fourier n (t : AddCircle (6 : ℝ)) with he
  have he_mul : ∀ n a b, e n a * e n (-b) = e n (a - b) := by
    intro n a b
    simp only [he, fourier_coe_apply, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hnorm_e : ∀ n t, ‖e n t‖ = 1 := fun n t => Circle.norm_coe _
  -- the error bound for the partial sum
  have herr : ∀ t : ℝ, |t| ≤ 2 → ‖absPowC p t - ∑ n ∈ S, c n * e n t‖ ≤ 4 * B / K := by
    intro t ht
    have hpt := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle (6 : ℝ))
    rw [perAbsPow_apply p hp0 (by linarith)] at hpt
    have := tail_bound hpt hBpos.le K (fun n hn => by
      rw [smul_eq_mul, norm_mul, hnorm_e n t, mul_one]
      exact hcb n (by rintro rfl; simp at hn; omega))
    refine this.trans ?_
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    gcongr
    linarith
  refine ⟨S × Bool, inferInstance, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Int.card_Icc]
    omega
  refine ⟨fun l a => if l.2 then (c l.1 * e l.1 a).re else -(c l.1 * e l.1 a).im,
    fun l b => if l.2 then (e l.1 (-b)).re else (e l.1 (-b)).im, fun a b hab => ?_⟩
  have hsep : ∑ l : S × Bool, (if l.2 then (c l.1 * e l.1 a).re else -(c l.1 * e l.1 a).im) *
      (if l.2 then (e l.1 (-b)).re else (e l.1 (-b)).im) = (∑ n ∈ S, c n * e n (a - b)).re := by
    rw [Fintype.sum_prod_type, Complex.re_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_bool, ← he_mul, ← mul_assoc]
    simp only [if_true, Bool.false_eq_true, if_false, Complex.mul_re, Complex.mul_im]
    ring
  rw [hsep]
  have hre : (absPowC p (a - b)).re = |a - b| ^ p := by simp [absPowC]
  rw [← hre, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← norm_neg, neg_sub]
  exact herr (a - b) hab

end

end SelfApproaching.Proof.LpAspect
