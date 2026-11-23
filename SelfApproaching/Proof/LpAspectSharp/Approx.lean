import Mathlib
import SelfApproaching.Proof.LpAspect.Fourier
import SelfApproaching.Proof.LpAspectSharp.Sep

/-!
# A separable approximation of `|a - b|^p` with error `O(K^{-p})`

Let `c_n` be the Fourier coefficients of the `6`-periodic extension of `|t|^p` from `[-3, 3]`.
Given a decomposition `c_n = ∑_{j < m} a_j (-1)^n / n^{2j+2} + ρ_n` with `|ρ_n| = O(|n|^{-(p+1)})`
(see `cos_integral_decomp`), the series `∑_n (-1)^n n^{-2j-2} e_n(t)` sum to Bernoulli polynomials
in `t` (exactly separable in `t = a - b`), while the remaining series `∑ ρ_n e_n(t)` is truncated
to `|n| ≤ K` with error `O(K^{-p})`.
-/

namespace SelfApproaching.Proof.LpAspectSharp

open Real MeasureTheory Set LpAspect

noncomputable section

attribute [local instance] fact_six

/-! ### Tail bounds for `∑ |n|^{-(r+1)}` -/

/-- `tailR r K k = k^{-(r+1)}` for `k > K`, and `0` otherwise. -/
def tailR (r : ℝ) (K k : ℕ) : ℝ := if k ≤ K then 0 else (k : ℝ) ^ (-(r + 1))

lemma tailR_nonneg (r : ℝ) (K k : ℕ) : 0 ≤ tailR r K k := by
  unfold tailR; split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma sum_range_rpow_le {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((K : ℝ) + (i + 1 : ℕ)) ^ (-(r + 1)) ≤ (K : ℝ) ^ (-r) / r := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(r + 1))) (Icc (K : ℝ) (K + N)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (hK0.trans_le hx.1) hxy (by linarith)
  refine hanti.sum_le_integral.trans ?_
  have h0 : (0 : ℝ) ∉ uIcc (K : ℝ) (K + N) := by
    rw [uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    intro h; linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show -(r + 1) + 1 = -r by ring]
  have h1 : 0 ≤ ((K : ℝ) + N) ^ (-r) := Real.rpow_nonneg (by positivity) _
  rw [div_neg, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (by linarith) hr.le

lemma sum_range_tailR {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ i ∈ Finset.range N, tailR r K i ≤ (K : ℝ) ^ (-r) / r := by
  calc ∑ i ∈ Finset.range N, tailR r K i ≤ ∑ i ∈ Finset.range (K + 1 + N), tailR r K i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          fun _ _ _ => tailR_nonneg _ _ _
    _ = ∑ i ∈ Finset.range (K + 1), tailR r K i +
          ∑ i ∈ Finset.Ico (K + 1) (K + 1 + N), tailR r K i :=
        (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    _ = ∑ i ∈ Finset.range N, ((K : ℝ) + (i + 1 : ℕ)) ^ (-(r + 1)) := by
        rw [Finset.sum_eq_zero (fun i hi => by
          rw [tailR, if_pos (by simp at hi; omega)]), zero_add, Finset.sum_Ico_eq_sum_range,
          show K + 1 + N - (K + 1) = N by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tailR, if_neg (by omega)]
        push_cast; ring_nf
    _ ≤ (K : ℝ) ^ (-r) / r := sum_range_rpow_le hr hK N

lemma sum_range_tailR_succ {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ i ∈ Finset.range N, tailR r K (i + 1) ≤ (K : ℝ) ^ (-r) / r := by
  have h := sum_range_tailR hr hK (N + 1)
  rw [Finset.sum_range_succ'] at h
  linarith [tailR_nonneg r K 0]

lemma tail_bound_rpow {f : ℤ → ℂ} {s : ℂ} (hf : HasSum f s) {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    {K : ℕ} (hK : 1 ≤ K) (hb : ∀ n : ℤ, (K : ℤ) < |n| → ‖f n‖ ≤ B / |(n : ℝ)| ^ (r + 1)) :
    ‖s - ∑ n ∈ Finset.Icc (-(K : ℤ)) K, f n‖ ≤ 2 * B * ((K : ℝ) ^ (-r) / r) := by
  set S := Finset.Icc (-(K : ℤ)) K
  have hv : HasSum (fun n => if n ∈ S then f n else 0) (∑ n ∈ S, f n) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := S)
      (f := fun n => if n ∈ S then f n else 0) (fun b hb => if_neg hb)
    rwa [Finset.sum_congr rfl (fun n hn => if_pos hn)] at this
  have hu : HasSum (fun n => if n ∈ S then 0 else f n) (s - ∑ n ∈ S, f n) := by
    convert hf.sub hv using 1
    funext n; split_ifs <;> simp
  have hs1 : Summable (fun k : ℕ => tailR r K k) :=
    summable_of_sum_range_le (tailR_nonneg r K) (sum_range_tailR hr hK)
  have hs2 : Summable (fun k : ℕ => tailR r K (k + 1)) :=
    summable_of_sum_range_le (fun k => tailR_nonneg r K _) (sum_range_tailR_succ hr hK)
  have hw : HasSum (fun n : ℤ => B * tailR r K n.natAbs)
      (B * ∑' k, tailR r K k + B * ∑' k, tailR r K (k + 1)) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · simpa using hs1.hasSum.mul_left B
    · convert hs2.hasSum.mul_left B using 2 with k
  refine (hu.norm_le_of_bounded hw ?_).trans ?_
  · intro n
    split_ifs with h
    · rw [norm_zero]; exact mul_nonneg hB (tailR_nonneg _ _ _)
    · have hK' : (K : ℤ) < |n| := by
        simp only [S, Finset.mem_Icc, not_and_or, not_le] at h
        rcases h with h | h
        · rw [abs_of_neg (by omega : n < 0)]; omega
        · rw [abs_of_pos (by omega)]; exact h
      refine (hb n hK').trans (le_of_eq ?_)
      have hK'' : ¬ n.natAbs ≤ K := by
        have := Int.natCast_natAbs n
        omega
      simp only [tailR, hK'', if_false]
      rw [Nat.cast_natAbs, Int.cast_abs, Real.rpow_neg (abs_nonneg _), div_eq_mul_inv]
  · have h1 : ∑' k, tailR r K k ≤ (K : ℝ) ^ (-r) / r :=
      Real.tsum_le_of_sum_range_le (tailR_nonneg r K) (sum_range_tailR hr hK)
    have h2 : ∑' k, tailR r K (k + 1) ≤ (K : ℝ) ^ (-r) / r :=
      Real.tsum_le_of_sum_range_le (fun k => tailR_nonneg r K _) (sum_range_tailR_succ hr hK)
    calc B * ∑' k, tailR r K k + B * ∑' k, tailR r K (k + 1) ≤
          B * ((K : ℝ) ^ (-r) / r) + B * ((K : ℝ) ^ (-r) / r) := by gcongr
      _ = 2 * B * ((K : ℝ) ^ (-r) / r) := by ring

/-! ### Fourier series of Bernoulli polynomials, in the variable `t ∈ [-3, 3]` -/

lemma hasSum_bernoulli {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : |t| ≤ 3) :
    HasSum (fun n : ℤ => (((-1 : ℝ) ^ n / (n : ℝ) ^ k : ℝ) : ℂ) * fourier n (t : AddCircle (6 : ℝ)))
      (-(2 * π * Complex.I) ^ k / k.factorial * bernoulliFun k ((t + 3) / 6)) := by
  have hx : (t + 3) / 6 ∈ Icc (0 : ℝ) 1 := by
    rw [abs_le] at ht
    constructor <;> linarith [ht.1, ht.2]
  convert hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx using 1
  funext n
  rw [fourier_coe_apply, fourier_coe_apply]
  have he : Complex.exp (2 * π * Complex.I * n * (((t + 3) / 6 : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) =
      (-1 : ℂ) ^ n * Complex.exp (2 * π * Complex.I * n * (t : ℂ) / ((6 : ℝ) : ℂ)) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [he]
  push_cast
  ring

/-! ### The separable approximation -/

/-- If the cosine integrals `∫₀³ cos(πnx/3) x^p dx` admit a decomposition into terms
`A_j (-1)^n / n^{2j+2}` plus an `O(|n|^{-(p+1)})` remainder, then `|a - b|^p` (for `|a - b| ≤ 2`)
is approximated within `A / K^p` by a sum of at most `B K` products `φ(a) ψ(b)`. -/
theorem exists_separable_approx_of_decomp (p : ℝ) (hp : 1 ≤ p)
    (hdec : ∃ (m : ℕ) (A : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      |(∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p) -
        ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2)| ≤
          C / |(n : ℝ)| ^ (p + 1)) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ K : ℕ, 1 ≤ K → ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι ≤ B * K ∧ ∃ φ ψ : ι → ℝ → ℝ, ∀ a b : ℝ, |a - b| ≤ 2 →
        |∑ l, φ l a * ψ l b - |a - b| ^ p| ≤ A / (K : ℝ) ^ p := by
  obtain ⟨m, A, C, hC, hdec⟩ := hdec
  have hp0 : 0 ≤ p := by linarith
  have hp0' : 0 < p := by linarith
  set J : ℤ → ℝ := fun n => ∫ x in (0 : ℝ)..3, Real.cos (π * n / 3 * x) * x ^ p with hJ
  set c : ℤ → ℂ := fourierCoeff (perAbsPow p hp0) with hc
  have hcJ : ∀ n, c n = ((J n / 3 : ℝ) : ℂ) := fun n => fourierCoeff_perAbsPow p hp0 n
  -- summability of the Fourier coefficients (from the `O(1/n²)` bound)
  set B0 : ℝ := (2 * p * 3 ^ (p - 1) + p) / 3 with hB0
  have hsum : Summable c := by
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => B0 * (1 / (n : ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left B0) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [mul_one_div]; exact norm_fourierCoeff_perAbsPow_le p hp n hn
  -- the remainder coefficients
  set w : ℕ → ℤ → ℝ := fun j n => (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2) with hw
  set ρ : ℤ → ℝ := fun n => J n / 3 - ∑ j ∈ Finset.range m, A j / 3 * w j n with hρdef
  have hρ : ∀ n : ℤ, n ≠ 0 → |ρ n| ≤ C / 3 / |(n : ℝ)| ^ (p + 1) := by
    intro n hn
    have e : ρ n = (J n - ∑ j ∈ Finset.range m, A j * (-1 : ℝ) ^ n / (n : ℝ) ^ (2 * j + 2)) / 3 := by
      simp only [hρdef, hw, sub_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_right_comm]
    exact div_le_div_of_nonneg_right (hdec n hn) (by norm_num)
  set e : ℤ → ℝ → ℂ := fun n t => fourier n (t : AddCircle (6 : ℝ)) with he
  set V : ℕ → ℝ → ℂ := fun j t => -(2 * π * Complex.I) ^ (2 * j + 2) / (2 * j + 2).factorial *
    bernoulliFun (2 * j + 2) ((t + 3) / 6) with hV
  -- the remainder series
  have hρsum : ∀ t : ℝ, |t| ≤ 2 → HasSum (fun n => (ρ n : ℂ) * e n t)
      (absPowC p t - ∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * V j t) := by
    intro t ht
    have hfull := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle (6 : ℝ))
    rw [perAbsPow_apply p hp0 (by linarith)] at hfull
    have hpoly : HasSum (fun n => ∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * ((w j n : ℂ) * e n t))
        (∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * V j t) :=
      hasSum_sum fun j _ => (hasSum_bernoulli (by omega) (by linarith)).mul_left _
    convert hfull.sub hpoly using 1
    funext n
    rw [smul_eq_mul, show fourierCoeff (perAbsPow p hp0) n = c n from rfl, hcJ]
    change _ = _ * e n t - _
    simp only [hρdef, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the polynomial part is separable
  set P : ℕ → Polynomial ℝ := fun j => Polynomial.map (algebraMap ℚ ℝ)
    (Polynomial.bernoulli (2 * j + 2)) with hP
  choose N hN using fun j => SepLE.poly (P j) (1 / 6) (1 / 2)
  set N₀ := ∑ j ∈ Finset.range m, 1 * N j with hN₀
  have hpolySep : SepLE (fun a b => ∑ j ∈ Finset.range m,
      (A j / 3 * (-(2 * π * Complex.I) ^ (2 * j + 2) / (2 * j + 2).factorial).re) *
        bernoulliFun (2 * j + 2) ((a - b + 3) / 6)) N₀ := by
    refine (SepLE.sum _ _ _ fun j _ => (SepLE.prod_fun (fun _ =>
      A j / 3 * (-(2 * π * Complex.I) ^ (2 * j + 2) / (2 * j + 2).factorial).re)
        (fun _ => 1)).mul (hN j)).congr fun a b => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hP, bernoulliFun, mul_one]
    congr 2
    ring
  refine ⟨2 * (C / 3) / p + 1, by positivity, N₀ + 6, fun K hK => ?_⟩
  set S := Finset.Icc (-(K : ℤ)) K with hS
  have hSep := hpolySep.add (SepLE.trig S (fun n => (ρ n : ℂ)))
  have hcardS : S.card * 2 ≤ 6 * K := by
    rw [hS, Int.card_Icc]; omega
  obtain ⟨ι, _, hcard, φ, ψ, hφψ⟩ := hSep.mono (show N₀ + S.card * 2 ≤ (N₀ + 6) * K by
    have : N₀ ≤ N₀ * K := Nat.le_mul_of_pos_right _ hK
    nlinarith)
  refine ⟨ι, inferInstance, hcard, φ, ψ, fun a b hab => ?_⟩
  rw [← hφψ]
  have htail := tail_bound_rpow (hρsum (a - b) hab) (B := C / 3) (by positivity) hp0' hK
    (fun n hn => by
      rw [norm_mul, show ‖e n (a - b)‖ = 1 from Circle.norm_coe _, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact hρ n (by rintro rfl; simp at hn; omega))
  have hre : (absPowC p (a - b) - ∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * V j (a - b) -
      ∑ n ∈ S, (ρ n : ℂ) * e n (a - b)).re = |a - b| ^ p -
      ((∑ j ∈ Finset.range m,
        (A j / 3 * (-(2 * π * Complex.I) ^ (2 * j + 2) / (2 * j + 2).factorial).re) *
          bernoulliFun (2 * j + 2) ((a - b + 3) / 6)) +
        (∑ n ∈ S, (ρ n : ℂ) * fourier n ((a - b : ℝ) : AddCircle (6 : ℝ))).re) := by
    simp only [Complex.sub_re, Complex.re_sum, hV, absPowC, Complex.ofReal_re, he,
      Complex.re_ofReal_mul, Complex.re_mul_ofReal, mul_assoc]
    ring
  have hKp : (K : ℝ) ^ (-p) = 1 / (K : ℝ) ^ p := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  calc |(∑ j ∈ Finset.range m,
        (A j / 3 * (-(2 * π * Complex.I) ^ (2 * j + 2) / (2 * j + 2).factorial).re) *
          bernoulliFun (2 * j + 2) ((a - b + 3) / 6)) +
        (∑ n ∈ S, (ρ n : ℂ) * fourier n ((a - b : ℝ) : AddCircle (6 : ℝ))).re - |a - b| ^ p|
        = |(absPowC p (a - b) - ∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * V j (a - b) -
            ∑ n ∈ S, (ρ n : ℂ) * e n (a - b)).re| := by rw [hre, abs_sub_comm]
    _ ≤ ‖absPowC p (a - b) - ∑ j ∈ Finset.range m, ((A j / 3 : ℝ) : ℂ) * V j (a - b) -
            ∑ n ∈ S, (ρ n : ℂ) * e n (a - b)‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * (C / 3) * ((K : ℝ) ^ (-p) / p) := htail
    _ = (2 * (C / 3) / p) / (K : ℝ) ^ p := by rw [hKp]; field_simp
    _ ≤ (2 * (C / 3) / p + 1) / (K : ℝ) ^ p := by
        gcongr
        linarith

end

end SelfApproaching.Proof.LpAspectSharp
