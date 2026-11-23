import Mathlib.Analysis.MeanInequalitiesPow
import SelfApproaching.Definitions
import SelfApproaching.Proof.Codes

namespace SelfApproaching.Proof

open Real Finset

/-- A strict SAS in a lower dimension gives one in any higher dimension (pad with zeros). -/
private lemma lp_sas_pad {p : ℝ} (hp : 0 < p) {d' d ℓ : ℕ} (hd : d' ≤ d)
    (x : Fin ℓ → (Fin d' → ℝ)) (hx : IsStrictSAS (lpDist p) x) :
    ∃ y : Fin ℓ → (Fin d → ℝ), IsStrictSAS (lpDist p) y := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  refine ⟨fun i => Fin.append (x i) (0 : Fin e → ℝ), ?_⟩
  have h : ∀ a b, lpDist p (Fin.append (x a) (0 : Fin e → ℝ)) (Fin.append (x b) 0) =
      lpDist p (x a) (x b) := by
    intro a b
    simp [lpDist, Fin.sum_univ_add, Real.zero_rpow hp.ne']
  intro i j k hij hki
  simp only [h]
  exact hx i j k hij hki

/-- Strictness can be checked on `p`-th power sums. -/
private lemma strictSAS_of_pow {p : ℝ} (hp : 0 < p) {d ℓ : ℕ} (x : Fin ℓ → (Fin d → ℝ))
    (h : ∀ i j k : Fin ℓ, i < j → k ≠ i →
      ∑ t, |x k t - x j t| ^ p < ∑ t, |x k t - x i t| ^ p) :
    IsStrictSAS (lpDist p) x := fun i j k hij hki =>
  Real.rpow_lt_rpow (Finset.sum_nonneg fun _ _ => rpow_nonneg (abs_nonneg _) _)
    (h i j k hij hki) (by positivity)

/-- Two points form a strict SAS. -/
private lemma lp_two_sas {p : ℝ} (hp : 0 < p) :
    ∃ x : Fin 2 → (Fin 1 → ℝ), IsStrictSAS (lpDist p) x := by
  refine ⟨fun i _ => (i : ℝ), strictSAS_of_pow hp _ fun i j k hij hki => ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Real.zero_rpow hp.ne']

private lemma inner_sum {p : ℝ} (hp : 0 < p) (c c' : Fin 8) (α β : ℝ) :
    ∑ a : Fin 8, |(if c = a then α else 0) - (if c' = a then β else 0)| ^ p =
      if c = c' then |α - β| ^ p else |α| ^ p + |β| ^ p := by
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      simp [Ne.symm ha, zero_rpow hp.ne']
    · simp
  · rw [Finset.sum_congr rfl (g := fun a => (if c = a then |α| ^ p else 0) +
        (if c' = a then |β| ^ p else 0)) ?_]
    · rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp
    · intro a _
      by_cases h1 : c = a <;> by_cases h2 : c' = a
      · exact absurd (h1.trans h2.symm) h
      all_goals simp [h1, h2, zero_rpow hp.ne']

private lemma upper_rpow {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) : |α - β| ^ p ≤ α ^ p + β ^ p := by
  calc |α - β| ^ p ≤ (α + β) ^ p := by
        apply rpow_le_rpow (abs_nonneg _) _ hp.le
        rw [abs_le]; constructor <;> linarith
    _ ≤ α ^ p + β ^ p := rpow_add_le_add_rpow hα hβ hp.le hp1

private lemma lower_rpow_aux {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {α β : ℝ}
    (hβ : 0 ≤ β) (hαβ : β ≤ α) :
    α ^ p + β ^ p - 2 * min (α ^ p) (β ^ p) ≤ |α - β| ^ p := by
  have hmin : min (α ^ p) (β ^ p) = β ^ p :=
    min_eq_right (rpow_le_rpow hβ hαβ hp.le)
  have := rpow_add_le_add_rpow (sub_nonneg.mpr hαβ) hβ hp.le hp1
  rw [sub_add_cancel] at this
  rw [hmin, abs_of_nonneg (sub_nonneg.mpr hαβ)]
  linarith

private lemma lower_rpow {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) : α ^ p + β ^ p - 2 * min (α ^ p) (β ^ p) ≤ |α - β| ^ p := by
  rcases le_total β α with h | h
  · exact lower_rpow_aux hp hp1 hβ h
  · have := lower_rpow_aux hp hp1 hα h
    rw [abs_sub_comm, min_comm]
    linarith

/-- The main construction: a code with small agreements gives a strict SAS. -/
private lemma lp_code_sas {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (n N : ℕ) (hn : 1 ≤ n)
    (C : Fin N → (Fin n → Fin 8))
    (hC : ∀ i j, i ≠ j → ((Finset.univ.filter fun b => C i b = C j b).card : ℝ) ≤ n / 4) :
    ∃ x : Fin N → (Fin (n * 8) → ℝ), IsStrictSAS (lpDist p) x := by
  set R : Fin N → ℝ := fun i => (1 / 3 : ℝ) ^ (i : ℕ) with hRdef
  set r : Fin N → ℝ := fun i => R i ^ p⁻¹ with hrdef
  have hRpos : ∀ i, 0 < R i := fun i => by positivity
  have hr0 : ∀ i, 0 ≤ r i := fun i => rpow_nonneg (hRpos i).le _
  have hrR : ∀ i, r i ^ p = R i := fun i => rpow_inv_rpow (hRpos i).le hp.ne'
  have hRdec : ∀ i j, i < j → R j ≤ R i / 3 := by
    intro i j hij
    have : (i : ℕ) + 1 ≤ j := hij
    calc R j ≤ (1 / 3 : ℝ) ^ ((i : ℕ) + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) this
      _ = R i / 3 := by rw [pow_succ]; ring
  let x : Fin N → Fin (n * 8) → ℝ := fun i t =>
    if C i (finProdFinEquiv.symm t).1 = (finProdFinEquiv.symm t).2 then r i else 0
  have hS : ∀ k l, ∑ t, |x k t - x l t| ^ p =
      ∑ b, (if C k b = C l b then |r k - r l| ^ p else |r k| ^ p + |r l| ^ p) := by
    intro k l
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [x, Equiv.symm_apply_apply]
    exact Finset.sum_congr rfl fun b _ => inner_sum hp _ _ _ _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- upper bound
  have hup : ∀ k l, ∑ t, |x k t - x l t| ^ p ≤ n * (R k + R l) := by
    intro k l
    rw [hS]
    calc _ ≤ ∑ _b : Fin n, (R k + R l) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_of_nonneg (hr0 k), abs_of_nonneg (hr0 l), ← hrR, ← hrR]
          split_ifs
          · exact upper_rpow hp hp1 (hr0 k) (hr0 l)
          · exact le_rfl
      _ = n * (R k + R l) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- lower bound
  have hlow : ∀ k l, k ≠ l →
      n * (R k + R l) - min (R k) (R l) * n / 2 ≤ ∑ t, |x k t - x l t| ^ p := by
    intro k l hkl
    rw [hS]
    set m := min (R k) (R l)
    have hm : 0 ≤ m := le_min (hRpos k).le (hRpos l).le
    calc n * (R k + R l) - m * n / 2 ≤ n * (R k + R l) - 2 * m *
          (Finset.univ.filter fun b => C k b = C l b).card := by
          have := hC k l hkl
          nlinarith
      _ = ∑ b : Fin n, ((R k + R l) - if C k b = C l b then 2 * m else 0) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_of_nonneg (hr0 k), abs_of_nonneg (hr0 l)]
          split_ifs
          · have := lower_rpow hp hp1 (hr0 k) (hr0 l)
            rw [hrR, hrR] at this
            linarith
          · rw [hrR, hrR]; linarith
  refine ⟨x, strictSAS_of_pow hp x fun i j k hij hki => ?_⟩
  have hji := hRdec i j hij
  have hmi : min (R k) (R i) ≤ R i := min_le_right _ _
  by_cases hkj : k = j
  · subst hkj
    have := hlow k i hki
    simp only [sub_self, abs_zero, zero_rpow hp.ne', Finset.sum_const_zero]
    nlinarith [hRpos k, hRpos i]
  · refine lt_of_lt_of_le ?_ (hlow k i hki)
    refine lt_of_le_of_lt (hup k j) ?_
    rcases lt_or_gt_of_ne hki with hlt | hlt
    · nlinarith [hRpos j]
    · have := hRdec i k hlt
      have hmk : min (R k) (R i) ≤ R k := min_le_left _ _
      nlinarith [hRpos j]

theorem lp_small_strict_sas_exponential (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, ∃ ℓ : ℕ, exp (c * d) ≤ ℓ ∧
      ∃ x : Fin ℓ → (Fin d → ℝ), IsStrictSAS (lpDist p) x := by
  obtain ⟨c0, hc0, hcode⟩ := exists_code 8 (by norm_num) (1 / 8) (by norm_num)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨min (c0 / 16) (log 2 / 8), lt_min (by positivity) (by positivity), fun d => ?_⟩
  set c := min (c0 / 16) (log 2 / 8) with hc
  have hc1 : c ≤ c0 / 16 := min_le_left _ _
  have hc2 : c ≤ log 2 / 8 := min_le_right _ _
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, by simp, fun _ _ => 0, fun i j _ hij => ?_⟩
    exact absurd hij (by omega)
  by_cases hd8 : 8 ≤ d
  · set n := d / 8 with hn
    have hn1 : 1 ≤ n := by omega
    have h16 : d ≤ 16 * n := by omega
    obtain ⟨N, hN, C, hC⟩ := hcode n
    obtain ⟨x, hx⟩ := lp_code_sas hp hp1 n N hn1 C fun i j hij => by
      have := hC i j hij
      norm_num at this ⊢
      linarith
    obtain ⟨y, hy⟩ := lp_sas_pad hp (Nat.div_mul_le_self d 8) x hx
    refine ⟨N, le_trans ?_ hN, y, hy⟩
    apply exp_le_exp.mpr
    have : (d : ℝ) ≤ 16 * n := by exact_mod_cast h16
    nlinarith
  · obtain ⟨x, hx⟩ := lp_two_sas hp
    obtain ⟨y, hy⟩ := lp_sas_pad hp hd x hx
    refine ⟨2, ?_, y, hy⟩
    have hd' : (d : ℝ) ≤ 8 := by exact_mod_cast (show d ≤ 8 by omega)
    calc exp (c * d) ≤ exp (log 2) := exp_le_exp.mpr (by nlinarith)
      _ = 2 := by rw [exp_log (by norm_num)]

end SelfApproaching.Proof
