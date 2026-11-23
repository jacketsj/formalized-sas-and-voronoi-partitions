import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Real.Sign
import SelfApproaching.Definitions

/-!
# A generic strict-SAS construction for `ℓ_p`, `1 < p < ∞`

If `v 0, …, v (N-1)` all have the same `p`-th power sum `S > 0` and pairwise satisfy
`⟨J(v k), v i⟩ ≤ -κ S` (where `J(u)_r = sign(u_r) |u_r|^(p-1)`), then `x i = η^i v i` is a strict
SAS for the `ℓ_p` distance, for a suitable `η > 0`.
-/

namespace SelfApproaching.Proof.LpLarge

open Real Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The `p`-th power sum `∑ r, |y r| ^ p`. -/
def psum (p : ℝ) (y : ι → ℝ) : ℝ := ∑ r, |y r| ^ p

/-- The `ℓ_p` (quasi)norm `(∑ r, |y r| ^ p) ^ (1 / p)`. -/
def nrm (p : ℝ) (y : ι → ℝ) : ℝ := psum p y ^ (1 / p)

/-- The duality map `x ↦ sign x * |x| ^ (p - 1)` (derivative of `|x| ^ p / p`). -/
def jf (p x : ℝ) : ℝ := Real.sign x * |x| ^ (p - 1)

lemma psum_nonneg (p : ℝ) (y : ι → ℝ) : 0 ≤ psum p y :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

lemma nrm_nonneg (p : ℝ) (y : ι → ℝ) : 0 ≤ nrm p y := Real.rpow_nonneg (psum_nonneg p y) _

lemma nrm_add_le {p : ℝ} (hp : 1 ≤ p) (x y : ι → ℝ) : nrm p (x + y) ≤ nrm p x + nrm p y :=
  Real.Lp_add_le Finset.univ x y hp

lemma psum_smul (p c : ℝ) (y : ι → ℝ) : psum p (c • y) = |c| ^ p * psum p y := by
  unfold psum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

lemma nrm_smul {p : ℝ} (hp : 0 < p) (c : ℝ) (y : ι → ℝ) : nrm p (c • y) = |c| * nrm p y := by
  unfold nrm
  rw [psum_smul, Real.mul_rpow (rpow_nonneg (abs_nonneg _) _) (psum_nonneg _ _),
    ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

lemma nrm_neg {p : ℝ} (hp : 0 < p) (y : ι → ℝ) : nrm p (-y) = nrm p y := by
  simpa using nrm_smul hp (-1) y

lemma nrm_sub_le {p : ℝ} (hp : 1 ≤ p) (x y : ι → ℝ) : nrm p (x - y) ≤ nrm p x + nrm p y := by
  rw [sub_eq_add_neg, ← nrm_neg (by linarith : (0:ℝ) < p) y]
  exact nrm_add_le hp x (-y)

lemma nrm_sub_ge {p : ℝ} (hp : 1 ≤ p) (x y : ι → ℝ) : nrm p x - nrm p y ≤ nrm p (x - y) := by
  have := nrm_add_le hp (x - y) y
  rw [sub_add_cancel] at this
  linarith

lemma nrm_rpow {p : ℝ} (hp : 0 < p) (y : ι → ℝ) : nrm p y ^ p = psum p y := by
  unfold nrm
  rw [one_div, Real.rpow_inv_rpow (psum_nonneg _ _) hp.ne']

/-- Tangent-line inequality for `|·|^p` at a positive point. -/
lemma tangent_pos {p : ℝ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x ^ p + p * x ^ (p - 1) * (y - x) ≤ |y| ^ p := by
  have hxp : x ^ p = x ^ (p - 1) * x := by
    rw [Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne']
  rcases le_or_gt y 0 with hy | hy
  · have h1 : 0 < x ^ (p - 1) := Real.rpow_pos_of_pos hx _
    have e : x ^ p + p * x ^ (p - 1) * (y - x) = x ^ (p - 1) * ((1 - p) * x + p * y) := by
      rw [hxp]; ring
    rw [e]
    have : (1 - p) * x + p * y ≤ 0 := by nlinarith
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos h1.le this) (rpow_nonneg (abs_nonneg _) _)
  · have hb := one_add_mul_self_le_rpow_one_add (s := y / x - 1)
      (by have := div_pos hy hx; linarith) hp
    rw [add_sub_cancel, Real.div_rpow hy.le hx.le] at hb
    rw [abs_of_pos hy]
    have hxp0 : 0 < x ^ p := rpow_pos_of_pos hx p
    rw [le_div_iff₀ hxp0] at hb
    calc x ^ p + p * x ^ (p - 1) * (y - x) = (1 + p * (y / x - 1)) * x ^ p := by
          rw [hxp]; field_simp
      _ ≤ y ^ p := hb

/-- Tangent-line inequality for `|·|^p` (convexity), for all real `x, y`. -/
lemma tangent {p : ℝ} (hp : 1 ≤ p) (x y : ℝ) : |x| ^ p + p * jf p x * (y - x) ≤ |y| ^ p := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := tangent_pos hp (neg_pos.2 hx) (-y)
    simp only [jf, Real.sign_of_neg hx, abs_of_neg hx, abs_neg] at h ⊢
    linarith
  · simp [jf, Real.zero_rpow (by linarith : p ≠ 0)]
    positivity
  · simpa [jf, Real.sign_of_pos hx, abs_of_pos hx] using tangent_pos hp hx y

lemma psum_sub_smul_ge {p : ℝ} (hp : 1 ≤ p) (u w : ι → ℝ) (t : ℝ) :
    psum p u - p * t * ∑ r, jf p (u r) * w r ≤ psum p (u - t • w) := by
  unfold psum
  have h : ∀ r, |u r| ^ p - p * t * (jf p (u r) * w r) ≤ |(u - t • w) r| ^ p := by
    intro r
    have := tangent hp (u r) ((u - t • w) r)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  calc _ = ∑ r, (|u r| ^ p - p * t * (jf p (u r) * w r)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun r _ => h r

/-- Convexity bound `(1 + u)^p ≤ 1 + (2^p - 1) u` on `[0, 1]`. -/
lemma one_add_rpow_le {p : ℝ} (hp : 1 ≤ p) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ p ≤ 1 + (2 ^ p - 1) * u := by
  have h := (convexOn_rpow hp).2 (show (1:ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2:ℝ) ∈ Set.Ici 0 by norm_num) (show 0 ≤ 1 - u by linarith) hu0 (by ring)
  simp only [smul_eq_mul, Real.one_rpow] at h
  have e : (1 - u) * 1 + u * 2 = 1 + u := by ring
  rw [e] at h
  linarith

/-- **Generic construction.** Vectors with equal `p`-th power sums `S > 0` and pairwise
`⟨J(v k), v i⟩ ≤ -κ S` give a strict SAS `i ↦ η^i v i`. -/
theorem strictSAS_of_family {p : ℝ} (hp : 1 < p) {N : ℕ} (v : Fin N → ι → ℝ) {S κ : ℝ}
    (hS : 0 < S) (hκ : 0 < κ) (hpsum : ∀ i, psum p (v i) = S)
    (hinner : ∀ i k, i ≠ k → ∑ r, jf p (v k r) * v i r ≤ -(κ * S)) :
    ∃ η : ℝ, 0 < η ∧
      IsStrictSAS (fun x y : ι → ℝ => nrm p (x - y)) (fun i => η ^ (i : ℕ) • v i) := by
  have hp0 : 0 < p := by linarith
  set M : ℝ := 2 ^ p - 1 with hMdef
  have hM : 0 < M := by
    have : (1:ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp0
    linarith
  set η : ℝ := min (1 / 4) (p * κ / (2 * M)) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hη1 : η ≤ 1 := by linarith
  have hηM : M * η < p * κ := by
    have h1 : η ≤ p * κ / (2 * M) := min_le_right _ _
    have hpk : 0 < p * κ := by positivity
    calc M * η ≤ M * (p * κ / (2 * M)) := by gcongr
      _ = p * κ / 2 := by field_simp
      _ < p * κ := by linarith
  refine ⟨η, hη0, ?_⟩
  set s : ℝ := S ^ (1 / p) with hsdef
  have hs : 0 < s := rpow_pos_of_pos hS _
  have hsp : s ^ p = S := by rw [hsdef, one_div, Real.rpow_inv_rpow hS.le hp0.ne']
  have hnv : ∀ i, nrm p (v i) = s := fun i => by rw [nrm, hpsum]
  have hnx : ∀ (m : ℕ) i, nrm p (η ^ m • v i) = η ^ m * s := by
    intro m i; rw [nrm_smul hp0, abs_of_pos (pow_pos hη0 m), hnv]
  intro i j k hij hki
  show nrm p (η ^ (k:ℕ) • v k - η ^ (j:ℕ) • v j) < nrm p (η ^ (k:ℕ) • v k - η ^ (i:ℕ) • v i)
  have hij' : (i : ℕ) < j := hij
  rcases lt_or_gt_of_ne hki with hk | hk
  · -- `k < i < j`: tangent-line lower bound versus Minkowski upper bound
    have hk' : (k : ℕ) < i := hk
    obtain ⟨a, ha⟩ : ∃ a, (i:ℕ) = k + (a + 1) := ⟨i - k - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, (j:ℕ) = k + (a + 1 + (b + 1)) := ⟨j - i - 1, by omega⟩
    set t := η ^ (a + 1) with htdef
    set t' := η ^ (a + 1 + (b + 1)) with ht'def
    have e1 : η ^ (k:ℕ) • v k - η ^ (i:ℕ) • v i = η ^ (k:ℕ) • (v k - t • v i) := by
      rw [ha, pow_add, smul_sub, mul_smul]
    have e2 : η ^ (k:ℕ) • v k - η ^ (j:ℕ) • v j = η ^ (k:ℕ) • (v k - t' • v j) := by
      rw [hb, pow_add, smul_sub, mul_smul]
    rw [e1, e2, nrm_smul hp0, nrm_smul hp0]
    refine mul_lt_mul_of_pos_left ?_ (abs_pos.2 (pow_pos hη0 _).ne')
    have ht0 : 0 < t := pow_pos hη0 _
    have ht1 : t ≤ 1 := pow_le_one₀ hη0.le hη1
    have ht' : t' ≤ η * t := by
      rw [ht'def, pow_add, mul_comm η]
      gcongr
      exact pow_le_of_le_one hη0.le hη1 (by omega)
    have ht'0 : 0 ≤ t' := by positivity
    have ht'1 : t' ≤ 1 := by nlinarith
    have hupper : nrm p (v k - t' • v j) ≤ (1 + t') * s := by
      calc _ ≤ nrm p (v k) + nrm p (t' • v j) := nrm_sub_le hp.le _ _
        _ = (1 + t') * s := by rw [nrm_smul hp0, abs_of_nonneg ht'0, hnv, hnv]; ring
    have hlower := psum_sub_smul_ge hp.le (v k) (v i) t
    rw [hpsum] at hlower
    have hin := hinner i k (Fin.ne_of_gt hk)
    have hconv := one_add_rpow_le hp.le ht'0 ht'1
    refine lt_of_le_of_lt hupper ?_
    rw [← Real.rpow_lt_rpow_iff (by positivity) (nrm_nonneg _ _) hp0, nrm_rpow hp0,
      Real.mul_rpow (by positivity) hs.le, hsp]
    have h1 : (1 + t') ^ p * S ≤ (1 + M * (η * t)) * S := by
      refine mul_le_mul_of_nonneg_right ?_ hS.le
      have := mul_le_mul_of_nonneg_left ht' hM.le
      linarith
    have h2 : M * η * t * S < p * κ * t * S :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hηM ht0) hS
    have h3 : p * t * ∑ r, jf p (v k r) * v i r ≤ p * t * (-(κ * S)) :=
      mul_le_mul_of_nonneg_left hin (by positivity)
    nlinarith
  · -- `i < k`: triangle inequality only
    have hk' : (i : ℕ) < k := hk
    have hkp : η ^ (k:ℕ) ≤ η ^ ((i:ℕ) + 1) := pow_le_pow_of_le_one hη0.le hη1 (by omega)
    have hjp : η ^ (j:ℕ) ≤ η ^ ((i:ℕ) + 1) := pow_le_pow_of_le_one hη0.le hη1 (by omega)
    have hupper := nrm_sub_le hp.le (η ^ (k:ℕ) • v k) (η ^ (j:ℕ) • v j)
    have hlower := nrm_sub_ge hp.le (η ^ (i:ℕ) • v i) (η ^ (k:ℕ) • v k)
    rw [← neg_sub (η ^ (k:ℕ) • v k), nrm_neg hp0] at hlower
    rw [hnx, hnx] at hupper hlower
    rw [pow_succ] at hkp hjp
    have hP : 0 < η ^ (i:ℕ) * s * (1 - 3 * η) :=
      mul_pos (mul_pos (pow_pos hη0 _) hs) (by linarith)
    have hk2 : η ^ (k:ℕ) * s ≤ η ^ (i:ℕ) * η * s := mul_le_mul_of_nonneg_right hkp hs.le
    have hj2 : η ^ (j:ℕ) * s ≤ η ^ (i:ℕ) * η * s := mul_le_mul_of_nonneg_right hjp hs.le
    nlinarith

end

end SelfApproaching.Proof.LpLarge
