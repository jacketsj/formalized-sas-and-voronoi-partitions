import SelfApproaching.Proof.EuclideanLower.Core

/-!
# The `⌈9d/4⌉` construction in `ℝ^d`

Coordinate vectors `ee d a` (zero when `a ≥ d`), the invariant `Inv`, the initial sequence,
the five-point step (Lemma 1) and the negative-axis completion (Lemma 2).
-/

namespace SelfApproaching.Proof.EuclideanLowerAux

open Filter Topology

variable {d : ℕ}

/-- The `a`-th coordinate vector of `ℝ^d` (zero if `a ≥ d`). -/
noncomputable def ee (d a : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : a < d then EuclideanSpace.single ⟨a, h⟩ 1 else 0

lemma inner_ee_left (a : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (ee d a) v = if h : a < d then v ⟨a, h⟩ else 0 := by
  unfold ee
  split_ifs <;> simp [EuclideanSpace.inner_single_left]

lemma inner_ee_self {a : ℕ} (ha : a < d) : inner ℝ (ee d a) (ee d a) = 1 := by
  rw [inner_ee_left]
  simp [ha, ee]

lemma inner_ee_ne {a b : ℕ} (hab : a ≠ b) : inner ℝ (ee d a) (ee d b) = 0 := by
  rw [inner_ee_left]
  split_ifs with h
  · unfold ee
    split_ifs with h'
    · simp only [PiLp.single_apply, Fin.mk.injEq, hab, if_false]
    · simp
  · rfl

lemma norm_ee {a : ℕ} (ha : a < d) : ‖ee d a‖ = 1 := by
  simp [ee, ha]

lemma inner_ee_mem (a b : ℕ) :
    0 ≤ inner ℝ (ee d a) (ee d b) ∧ inner ℝ (ee d a) (ee d b) ≤ 1 := by
  by_cases hab : a = b
  · subst hab
    by_cases ha : a < d
    · rw [inner_ee_self ha]
      norm_num
    · simp [ee, ha]
  · rw [inner_ee_ne hab]
    norm_num

lemma tend0 {E : Type*} [TopologicalSpace E] [Zero E] {f : ℝ → E} (hf : Continuous f)
    (h0 : f 0 = 0) : Tendsto f (𝓝[>] 0) (𝓝 0) := by
  simpa [h0] using (hf.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Invariant of the construction: `x 0, …, x N` is a strict SAS ending at the origin, all
coordinates lie in `[0, 1]`, and coordinates `≥ D` vanish. -/
structure Inv (d : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (N D : ℕ) : Prop where
  sas : NSAS x (N + 1)
  last : x N = 0
  nonneg : ∀ i ≤ N, ∀ m, 0 ≤ inner ℝ (ee d m) (x i)
  le_one : ∀ i ≤ N, ∀ m, inner ℝ (ee d m) (x i) ≤ 1
  zero : ∀ i ≤ N, ∀ m, D ≤ m → inner ℝ (ee d m) (x i) = 0

/-! ## The initial sequence `(e_0, e_1/2, …, e_{r-1}/2^{r-1}, 0)` -/

/-- The initial sequence. -/
noncomputable def initSeq (d r : ℕ) : ℕ → EuclideanSpace ℝ (Fin d) :=
  fun a => if a < r then ((1 : ℝ) / 2) ^ a • ee d a else 0

lemma init_inv (r : ℕ) (hr : r ≤ d) : Inv d (initSeq d r) r r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply orth_sas
    · intro a _ b _ hab
      unfold initSeq
      split_ifs <;> simp [real_inner_smul_left, real_inner_smul_right, inner_ee_ne hab]
    · intro a b hab hb
      have ha : a < r := by omega
      have hna : ‖initSeq d r a‖ = ((1 : ℝ) / 2) ^ a := by
        simp only [initSeq, ha, if_true, norm_smul, norm_ee (show a < d by omega), mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hna]
      by_cases hbr : b < r
      · simp only [initSeq, hbr, if_true, norm_smul, norm_ee (show b < d by omega), mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hab
      · simp only [initSeq, hbr, if_false, norm_zero]
        positivity
  · simp [initSeq]
  · intro i _ m
    unfold initSeq
    split_ifs
    · rw [real_inner_smul_right]
      exact mul_nonneg (by positivity) (inner_ee_mem m i).1
    · simp
  · intro i _ m
    unfold initSeq
    split_ifs
    · rw [real_inner_smul_right]
      exact mul_le_one₀ (pow_le_one₀ (by norm_num) (by norm_num)) (inner_ee_mem m i).1
        (inner_ee_mem m i).2
    · simp
  · intro i _ m hm
    unfold initSeq
    split_ifs with hi
    · rw [real_inner_smul_right, inner_ee_ne (by omega), mul_zero]
    · simp

/-! ## Lemma 2: negative-axis completion -/

/-- Radii `t_0 = t`, `t_{n+1} = t_n² / 16`. -/
noncomputable def tseq (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => tseq t n ^ 2 / 16

lemma tseq_pos_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    0 < tseq t n ∧ tseq t n ≤ 1 := by
  induction n with
  | zero => exact ⟨ht0, ht1⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by simp only [tseq]; positivity, ?_⟩
    simp only [tseq]
    nlinarith

lemma tseq_strictAnti {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : StrictAnti (tseq t) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  obtain ⟨h0, h1⟩ := tseq_pos_le ht0 ht1 n
  simp only [tseq]
  nlinarith

lemma tseq_continuous (n : ℕ) : Continuous fun t => tseq t n := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => simp only [tseq]; fun_prop

lemma tseq_zero (n : ℕ) : tseq 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tseq, ih]

/-- The negative-axis points `-t_a e_a` (`a < d`), followed by the origin. -/
noncomputable def negSeq (d : ℕ) (t : ℝ) : ℕ → EuclideanSpace ℝ (Fin d) :=
  fun a => if a < d then (-tseq t a) • ee d a else 0

lemma final {x : ℕ → EuclideanSpace ℝ (Fin d)} {N D : ℕ} (h : Inv d x N D) :
    ∃ y : ℕ → EuclideanSpace ℝ (Fin d), NSAS y (N + d + 1) := by
  have hnorm : ∀ t, 0 < t → t ≤ 1 → ∀ a < d, ‖negSeq d t a‖ = tseq t a := by
    intro t ht0 ht1 a ha
    simp only [negSeq, ha, if_true, norm_smul, norm_neg, norm_ee ha, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (tseq_pos_le ht0 ht1 a).1
  have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), NSAS (negSeq d t) (d + 1) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    apply orth_sas
    · intro a _ b _ hab
      unfold negSeq
      split_ifs <;> simp [real_inner_smul_left, real_inner_smul_right, inner_ee_ne hab]
    · intro a b hab hb
      have ha : a < d := by omega
      rw [hnorm t ht.1 ht.2.le a ha]
      by_cases hbd : b < d
      · rw [hnorm t ht.1 ht.2.le b hbd]
        exact tseq_strictAnti ht.1 ht.2.le hab
      · simp only [negSeq, hbd, if_false, norm_zero]
        exact (tseq_pos_le ht.1 ht.2.le a).1
  have hobs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a < N, ∀ i j, i < j → j ≤ d →
      dist (x a) (negSeq d t j) < dist (x a) (negSeq d t i) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    intro a ha
    apply chain (f := fun j => dist (x a) (negSeq d t j))
    intro j hj
    have hinner : inner ℝ (x a) (negSeq d t j) = -tseq t j * inner ℝ (ee d j) (x a) := by
      simp only [negSeq, hj, if_true, real_inner_smul_right, real_inner_comm]
    have hn := hnorm t ht.1 ht.2.le j hj
    have hp0 := h.nonneg a ha.le j
    obtain ⟨tj0, tj1⟩ := tseq_pos_le ht.1 ht.2.le j
    rw [← pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero, dist_eq_norm, dist_eq_norm,
      norm_sub_sq_real, norm_sub_sq_real, hinner, hn]
    by_cases hj1 : j + 1 < d
    · have hinner' : inner ℝ (x a) (negSeq d t (j + 1)) =
          -tseq t (j + 1) * inner ℝ (ee d (j + 1)) (x a) := by
        simp only [negSeq, hj1, if_true, real_inner_smul_right, real_inner_comm]
      rw [hinner', hnorm t ht.1 ht.2.le (j + 1) hj1]
      have hq0 := h.nonneg a ha.le (j + 1)
      have hq1 := h.le_one a ha.le (j + 1)
      obtain ⟨tk0, tk1⟩ := tseq_pos_le ht.1 ht.2.le (j + 1)
      have htk : tseq t (j + 1) = tseq t j ^ 2 / 16 := rfl
      have hA : tseq t (j + 1) * inner ℝ (ee d (j + 1)) (x a) ≤ tseq t (j + 1) :=
        mul_le_of_le_one_right tk0.le hq1
      have hB : tseq t (j + 1) ^ 2 ≤ tseq t (j + 1) := by nlinarith
      have hC : 0 ≤ tseq t j * inner ℝ (ee d j) (x a) := mul_nonneg tj0.le hp0
      have hD : 0 < tseq t j ^ 2 := by positivity
      nlinarith
    · have : negSeq d t (j + 1) = 0 := by simp [negSeq, hj1]
      rw [this]
      simp only [inner_zero_right, norm_zero]
      have hC : 0 ≤ tseq t j * inner ℝ (ee d j) (x a) := mul_nonneg tj0.le hp0
      have hD : 0 < tseq t j ^ 2 := by positivity
      nlinarith
  have hlim : ∀ m < d, Tendsto (fun t => negSeq d t m) (𝓝[>] 0) (𝓝 0) := by
    intro m hm
    apply tend0
    · simp only [negSeq, hm, if_true]
      have := tseq_continuous m
      fun_prop
    · simp [negSeq, tseq_zero]
  have hev := extend x N d h.sas h.last (negSeq d) (fun t => by simp [negSeq]) hlim hint hobs
  obtain ⟨t, ht⟩ := hev.exists
  exact ⟨_, ht⟩

/-! ## Lemma 1: five points in four new coordinates -/

/-- The radii `R_a = t (1 - a ε² / 16)` with `ε = t² / 64`. -/
noncomputable def RR (a : ℕ) (t : ℝ) : ℝ := t * (1 - a * (t ^ 2 / 64) ^ 2 / 16)

/-- The coefficient `s = t² / 8` of the reused coordinate. -/
noncomputable def ss (t : ℝ) : ℝ := t ^ 2 / 8

/-- The coefficient `c = t (1 - ε) / 2` of the new coordinates. -/
noncomputable def cc (t : ℝ) : ℝ := t * (1 - t ^ 2 / 64) / 2

/-- The point `b_a = R_a e_{D+a}`. -/
noncomputable def bb (d D a : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) := RR a t • ee d (D + a)

/-- The point `z = s e_0 + c (e_D + e_{D+1} + e_{D+2} + e_{D+3})`. -/
noncomputable def zz (d D : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  ss t • ee d 0 + cc t • (ee d D + ee d (D + 1) + ee d (D + 2) + ee d (D + 3))

/-- The six new points `(b_0, b_1, b_2, b_3, z, 0)`. -/
noncomputable def qq (d D : ℕ) (t : ℝ) : ℕ → EuclideanSpace ℝ (Fin d) :=
  five (bb d D 0 t) (bb d D 1 t) (bb d D 2 t) (bb d D 3 t) (zz d D t)

lemma num_facts {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    RR 1 t < RR 0 t ∧ RR 2 t < RR 1 t ∧ RR 3 t < RR 2 t ∧ 0 < RR 3 t ∧ RR 0 t ≤ 1 ∧
    ss t ^ 2 + 4 * cc t ^ 2 < RR 3 t ^ 2 ∧ 2 * cc t * RR 0 t < ss t ^ 2 + 4 * cc t ^ 2 ∧
    0 ≤ cc t ∧ cc t ≤ 1 ∧ 0 ≤ ss t ∧ ss t ≤ 1 ∧ 2 * ss t < ss t ^ 2 + 4 * cc t ^ 2 := by
  have he0 : 0 < t ^ 2 / 64 := by positivity
  have he1 : t ^ 2 / 64 < 1 / 64 := by nlinarith
  have hee : 0 < (t ^ 2 / 64) ^ 2 := by positivity
  have hee1 : (t ^ 2 / 64) ^ 2 < 1 := by nlinarith
  have hR : ∀ a : ℕ, RR (a + 1) t = RR a t - t * (t ^ 2 / 64) ^ 2 / 16 := by
    intro a
    simp only [RR]
    push_cast
    ring
  have hR0 : RR 0 t = t := by simp [RR]
  have htee : 0 < t * (t ^ 2 / 64) ^ 2 / 16 := by positivity
  have htee1 : t * (t ^ 2 / 64) ^ 2 / 16 < t / 16 := by nlinarith
  have hR1 := hR 0
  have hR2 := hR 1
  have hR3 := hR 2
  norm_num at hR1 hR2 hR3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have e : RR 3 t ^ 2 - (ss t ^ 2 + 4 * cc t ^ 2) =
        t ^ 2 * (t ^ 2 / 64) * (1 - 11 * (t ^ 2 / 64) / 8 + 9 * (t ^ 2 / 64) ^ 3 / 256) := by
      simp only [RR, ss, cc]
      push_cast
      ring
    have : 0 < 1 - 11 * (t ^ 2 / 64) / 8 + 9 * (t ^ 2 / 64) ^ 3 / 256 := by
      have : 0 ≤ (t ^ 2 / 64) ^ 3 := by positivity
      nlinarith
    have : 0 < t ^ 2 * (t ^ 2 / 64) * (1 - 11 * (t ^ 2 / 64) / 8 + 9 * (t ^ 2 / 64) ^ 3 / 256) :=
      by positivity
    linarith
  · have e : ss t ^ 2 + 4 * cc t ^ 2 - 2 * cc t * RR 0 t = t ^ 2 * (t ^ 2 / 64) ^ 2 := by
      simp only [RR, ss, cc]
      push_cast
      ring
    have : 0 < t ^ 2 * (t ^ 2 / 64) ^ 2 := by positivity
    linarith
  · simp only [cc]
    nlinarith
  · simp only [cc]
    nlinarith
  · simp only [ss]
    positivity
  · simp only [ss]
    nlinarith
  · have e : ss t ^ 2 + 4 * cc t ^ 2 - 2 * ss t =
        t ^ 2 * (3 / 4 - t ^ 2 / 64 + (t ^ 2 / 64) ^ 2) := by
      simp only [ss, cc]
      ring
    have : 0 < t ^ 2 * (3 / 4 - t ^ 2 / 64 + (t ^ 2 / 64) ^ 2) := by
      have : 0 < 3 / 4 - t ^ 2 / 64 + (t ^ 2 / 64) ^ 2 := by nlinarith
      positivity
    linarith

lemma inner_bb_bb {D a a' : ℕ} (h : a ≠ a') (t : ℝ) :
    inner ℝ (bb d D a t) (bb d D a' t) = 0 := by
  simp [bb, real_inner_smul_left, real_inner_smul_right, inner_ee_ne (show D + a ≠ D + a' by omega)]

lemma norm_bb {D a : ℕ} (hDd : D + 4 ≤ d) (ha : a < 4) {t : ℝ} (h0 : 0 ≤ RR a t) :
    ‖bb d D a t‖ = RR a t := by
  simp only [bb, norm_smul, norm_ee (show D + a < d by omega), mul_one, Real.norm_eq_abs]
  exact abs_of_nonneg h0

section Geometry

variable {D : ℕ} (hD : 1 ≤ D) (hDd : D + 4 ≤ d)
include hD hDd

omit hD in
lemma inner_ee_sum {a : ℕ} (ha : a < 4) :
    inner ℝ (ee d (D + a)) (ee d D + ee d (D + 1) + ee d (D + 2) + ee d (D + 3)) = 1 := by
  interval_cases a <;>
    simp (disch := omega) only [add_zero, inner_add_right, inner_ee_self, inner_ee_ne] <;> norm_num

lemma inner_bb_zz {a : ℕ} (ha : a < 4) (t : ℝ) :
    inner ℝ (bb d D a t) (zz d D t) = cc t * RR a t := by
  rw [bb, zz, real_inner_smul_left, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_ee_sum hDd ha, inner_ee_ne (show D + a ≠ 0 by omega)]
  ring

lemma norm_zz_sq (t : ℝ) : ‖zz d D t‖ ^ 2 = ss t ^ 2 + 4 * cc t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp (disch := omega) only [zz, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_ee_self, inner_ee_ne]
  ring

lemma inner_ee_zz_mem (m : ℕ) {t : ℝ} (hs0 : 0 ≤ ss t) (hs1 : ss t ≤ 1) (hc0 : 0 ≤ cc t)
    (hc1 : cc t ≤ 1) :
    0 ≤ inner ℝ (ee d m) (zz d D t) ∧ inner ℝ (ee d m) (zz d D t) ≤ 1 := by
  rcases (show m = 0 ∨ m = D ∨ m = D + 1 ∨ m = D + 2 ∨ m = D + 3 ∨
      (m ≠ 0 ∧ m ≠ D ∧ m ≠ D + 1 ∧ m ≠ D + 2 ∧ m ≠ D + 3) by omega) with h | h | h | h | h | h <;>
  · try subst h
    simp (disch := omega) only [zz, inner_add_right, real_inner_smul_right, inner_ee_self,
      inner_ee_ne]
    constructor <;> linarith

end Geometry

lemma inner_ee_zz_zero {D m : ℕ} (hD : 1 ≤ D) (hm : D + 4 ≤ m) (t : ℝ) : inner ℝ (ee d m) (zz d D t) = 0 := by
  simp (disch := omega) only [zz, inner_add_right, real_inner_smul_right, inner_ee_ne]
  ring

lemma step {x : ℕ → EuclideanSpace ℝ (Fin d)} {N D : ℕ} (hD : 1 ≤ D) (hDd : D + 4 ≤ d)
    (h : Inv d x N D) : ∃ x' : ℕ → EuclideanSpace ℝ (Fin d), Inv d x' (N + 5) (D + 4) := by
  have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), NSAS (qq d D t) (5 + 1) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    obtain ⟨r10, r21, r32, r3, -, hC, hcC, hc0, -⟩ := num_facts ht.1 ht.2
    exact five_sas _ _ _ _ _ (RR 0 t) (RR 1 t) (RR 2 t) (RR 3 t) (cc t) _
      (inner_bb_bb (by norm_num) t) (inner_bb_bb (by norm_num) t) (inner_bb_bb (by norm_num) t)
      (inner_bb_bb (by norm_num) t) (inner_bb_bb (by norm_num) t) (inner_bb_bb (by norm_num) t)
      (norm_bb hDd (by norm_num) (by linarith)) (norm_bb hDd (by norm_num) (by linarith))
      (norm_bb hDd (by norm_num) (by linarith)) (norm_bb hDd (by norm_num) (by linarith))
      (inner_bb_zz hD hDd (by norm_num) t) (inner_bb_zz hD hDd (by norm_num) t)
      (inner_bb_zz hD hDd (by norm_num) t) (inner_bb_zz hD hDd (by norm_num) t)
      (norm_zz_sq hD hDd t) r10 r21 r32 r3 hC hcC hc0
  have hobs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a < N, ∀ i j, i < j → j ≤ 5 →
      dist (x a) (qq d D t j) < dist (x a) (qq d D t i) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    obtain ⟨r10, r21, r32, r3, -, hC, -, -, -, hs0, -, hsC⟩ := num_facts ht.1 ht.2
    intro a ha
    have hpb : ∀ b < 4, inner ℝ (x a) (bb d D b t) = 0 := by
      intro b _
      rw [bb, real_inner_smul_right, real_inner_comm, h.zero a ha.le _ (by omega), mul_zero]
    have hpz : inner ℝ (x a) (zz d D t) = ss t * inner ℝ (ee d 0) (x a) := by
      rw [zz, inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_add_right,
        inner_add_right, inner_add_right, real_inner_comm (ee d 0), real_inner_comm (ee d D),
        real_inner_comm (ee d (D + 1)), real_inner_comm (ee d (D + 2)),
        real_inner_comm (ee d (D + 3)), h.zero a ha.le D le_rfl,
        h.zero a ha.le (D + 1) (by omega), h.zero a ha.le (D + 2) (by omega),
        h.zero a ha.le (D + 3) (by omega)]
      ring
    have hp0 := h.nonneg a ha.le 0
    have hp1 := h.le_one a ha.le 0
    have hsp : ss t * inner ℝ (ee d 0) (x a) ≤ ss t := mul_le_of_le_one_right hs0 hp1
    apply chain (f := fun j => dist (x a) (qq d D t j))
    intro j hj
    rw [← pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero, dist_eq_norm, dist_eq_norm,
      norm_sub_sq_real, norm_sub_sq_real]
    interval_cases j <;>
    · simp only [qq, five, hpb 0 (by norm_num), hpb 1 (by norm_num), hpb 2 (by norm_num),
        hpb 3 (by norm_num), hpz, norm_zz_sq hD hDd t, inner_zero_right, norm_zero,
        norm_bb hDd (show 0 < 4 by norm_num) (show 0 ≤ RR 0 t by linarith),
        norm_bb hDd (show 1 < 4 by norm_num) (show 0 ≤ RR 1 t by linarith),
        norm_bb hDd (show 2 < 4 by norm_num) (show 0 ≤ RR 2 t by linarith),
        norm_bb hDd (show 3 < 4 by norm_num) (show 0 ≤ RR 3 t by linarith)]
      nlinarith
  have hlim : ∀ m < 5, Tendsto (fun t => qq d D t m) (𝓝[>] 0) (𝓝 0) := by
    intro m hm
    interval_cases m <;>
    · apply tend0
      · simp only [qq, five, bb, zz, RR, ss, cc]
        fun_prop
      · simp [qq, five, bb, zz, RR, ss, cc]
  have hev := extend x N 5 h.sas h.last (qq d D) (fun _ => rfl) hlim hint hobs
  obtain ⟨t, ht, ht01⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  obtain ⟨-, -, -, r3, r0, -, -, hc0, hc1, hs0, hs1, -⟩ := num_facts ht01.1 ht01.2
  have hRmem : ∀ b < 4, 0 ≤ RR b t ∧ RR b t ≤ 1 := by
    intro b hb
    have h1 : ∀ b' : ℕ, RR (b' + 1) t ≤ RR b' t := by
      intro b'
      simp only [RR]
      push_cast
      have : 0 ≤ t * (t ^ 2 / 64) ^ 2 / 16 := by have := ht01.1; positivity
      nlinarith
    interval_cases b
    · exact ⟨by linarith [h1 0, h1 1, h1 2], r0⟩
    · exact ⟨by linarith [h1 1, h1 2], by linarith [h1 0]⟩
    · exact ⟨by linarith [h1 2], by linarith [h1 0, h1 1]⟩
    · exact ⟨r3.le, by linarith [h1 0, h1 1, h1 2]⟩
  have hnew : ∀ i ≤ 5, ∀ m, (0 ≤ inner ℝ (ee d m) (qq d D t i) ∧
      inner ℝ (ee d m) (qq d D t i) ≤ 1) ∧ (D + 4 ≤ m → inner ℝ (ee d m) (qq d D t i) = 0) := by
    intro i hi m
    have hb : ∀ b < 4, (0 ≤ inner ℝ (ee d m) (bb d D b t) ∧
        inner ℝ (ee d m) (bb d D b t) ≤ 1) ∧ (D + 4 ≤ m → inner ℝ (ee d m) (bb d D b t) = 0) := by
      intro b hb
      obtain ⟨h0, h1⟩ := hRmem b hb
      rw [bb, real_inner_smul_right]
      refine ⟨⟨mul_nonneg h0 (inner_ee_mem _ _).1,
        mul_le_one₀ h1 (inner_ee_mem _ _).1 (inner_ee_mem _ _).2⟩, fun hm => ?_⟩
      rw [inner_ee_ne (by omega), mul_zero]
    interval_cases i
    · exact hb 0 (by norm_num)
    · exact hb 1 (by norm_num)
    · exact hb 2 (by norm_num)
    · exact hb 3 (by norm_num)
    · exact ⟨inner_ee_zz_mem hD hDd m hs0 hs1 hc0 hc1, fun hm => inner_ee_zz_zero hD hm t⟩
    · simp [qq, five]
  refine ⟨ins x N (qq d D t), ht, by simp [ins, qq, five], ?_, ?_, ?_⟩
  · intro i hi m
    unfold ins
    split_ifs with hiN
    · exact h.nonneg i hiN.le m
    · exact (hnew (i - N) (by omega) m).1.1
  · intro i hi m
    unfold ins
    split_ifs with hiN
    · exact h.le_one i hiN.le m
    · exact (hnew (i - N) (by omega) m).1.2
  · intro i hi m hm
    unfold ins
    split_ifs with hiN
    · exact h.zero i hiN.le m (by omega)
    · exact (hnew (i - N) (by omega) m).2 hm

end SelfApproaching.Proof.EuclideanLowerAux
