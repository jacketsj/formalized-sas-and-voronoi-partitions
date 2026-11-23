import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import SelfApproaching.Definitions

/-!
# Navigable graphs with out-degree `3^d` in `ℝ^d` (Lemma 10, Arya–Mount)
-/

namespace SelfApproaching.Proof.Exponential

open MeasureTheory Metric

section Cover

variable {E : Type*} [MetricSpace E] {n : ℕ}

/-- The greedy out-neighbourhood of `i`, organised as an induction on the points sorted by
distance from `x i`: a set `S ⊆ T` in which no point is strictly closer to an earlier
(not farther) point of `S` than to `x i`, and such that every point of `T` is in `S` or is
strictly closer to some point of `S` than to `x i`. -/
lemma exists_cover (x : Fin n → E) (i : Fin n) (T : Finset (Fin n)) :
    ∃ S ⊆ T,
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → dist (x y) (x i) ≤ dist (x z) (x i) →
        dist (x z) (x i) ≤ dist (x z) (x y)) ∧
      (∀ q ∈ T, q ∈ S ∨ ∃ y ∈ S, dist (x q) (x y) < dist (x q) (x i)) := by
  induction T using Finset.induction_on_max_value (fun j => dist (x j) (x i)) with
  | empty => exact ⟨∅, subset_rfl, by simp, by simp⟩
  | insert a s _ hmax ih =>
    obtain ⟨S, hSs, hpair, hcov⟩ := ih
    by_cases ha : ∃ y ∈ S, dist (x a) (x y) < dist (x a) (x i)
    · refine ⟨S, hSs.trans (Finset.subset_insert _ _), hpair, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Or.inr ha
      · exact hcov q hq
    · push Not at ha
      refine ⟨insert a S, Finset.insert_subset_insert _ hSs, ?_, ?_⟩
      · intro y hy z hz hyz hle
        rcases Finset.mem_insert.mp hy with rfl | hy' <;>
          rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact absurd rfl hyz
        · have := hmax z (hSs hz')
          have heq : dist (x z) (x i) = dist (x y) (x i) := le_antisymm this hle
          rw [heq, dist_comm (x z)]
          exact ha z hz'
        · exact ha y hy'
        · exact hpair y hy' z hz' hyz hle
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact Or.inl (Finset.mem_insert_self _ _)
        · rcases hcov q hq with h | ⟨y, hy, h⟩
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr ⟨y, Finset.mem_insert_of_mem hy, h⟩

end Cover

section Angle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- If `0 < ‖p‖ ≤ ‖q‖ ≤ ‖q - p‖`, the unit directions of `p` and `q` are at distance `≥ 1`. -/
lemma one_le_norm_sub_unit {p q : F} (hp : 0 < ‖p‖) (hpq : ‖p‖ ≤ ‖q‖) (hq : ‖q‖ ≤ ‖q - p‖) :
    1 ≤ ‖‖p‖⁻¹ • p - ‖q‖⁻¹ • q‖ := by
  have hq0 : 0 < ‖q‖ := hp.trans_le hpq
  set a := ‖p‖
  set b := ‖q‖
  have h1 := norm_sub_sq_real q p
  have h2 := norm_sub_sq_real (a⁻¹ • p) (b⁻¹ • q)
  rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), abs_of_pos (inv_pos.mpr hq0),
    inv_mul_cancel₀ hp.ne', inv_mul_cancel₀ hq0.ne', real_inner_comm] at h2
  have hs : 2 * inner ℝ q p ≤ a ^ 2 := by
    have : b ^ 2 ≤ ‖q - p‖ ^ 2 := pow_le_pow_left₀ hq0.le hq 2
    linarith
  have hab : 0 < a * b := mul_pos hp hq0
  have h3 : a⁻¹ * (b⁻¹ * inner ℝ q p) * (a * b) = inner ℝ q p := by
    field_simp
  have h4 : 1 ≤ ‖a⁻¹ • p - b⁻¹ • q‖ ^ 2 := by
    rw [h2]
    have h5 : 2 * (a⁻¹ * (b⁻¹ * inner ℝ q p)) * (a * b) ≤ 1 * (a * b) := by
      nlinarith
    have h6 := le_of_mul_le_mul_right h5 hab
    linarith
  nlinarith [norm_nonneg (a⁻¹ • p - b⁻¹ • q)]

end Angle

section Packing

variable {d : ℕ}

/-- At most `3^d` unit vectors in `ℝ^d` are pairwise at distance `≥ 1`. -/
lemma card_le_of_unit_sep {ι : Type*} (S : Finset ι) (u : ι → EuclideanSpace ℝ (Fin d))
    (hu : ∀ y ∈ S, ‖u y‖ = 1) (hsep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ dist (u y) (u z)) :
    S.card ≤ 3 ^ d := by
  set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hball : ∀ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      volume (ball c r) = ENNReal.ofReal (r ^ d) * V := by
    intro c r hr
    rw [Measure.addHaar_ball_of_pos volume c hr, finrank_euclideanSpace_fin]
  have hdisj : (S : Set ι).PairwiseDisjoint (fun y => ball (u y) (1 / 2)) := by
    intro y hy z hz hyz
    exact ball_disjoint_ball (by norm_num; exact hsep y hy z hz hyz)
  have hsub : (⋃ y ∈ S, ball (u y) (1 / 2)) ⊆ ball 0 (3 / 2) := by
    intro p hp
    simp only [Set.mem_iUnion, mem_ball] at hp
    obtain ⟨y, hy, hpy⟩ := hp
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' p (u y)
    rw [hu y hy, ← dist_eq_norm] at this
    linarith
  have hmeas := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hmeas
  simp only [hball _ _ (by norm_num : (0 : ℝ) < 1 / 2), hball _ _ (by norm_num : (0 : ℝ) < 3 / 2),
    Finset.sum_const, nsmul_eq_mul] at hmeas
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hV0 hVt, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmeas
  have h3 : ((3 : ℝ) / 2) ^ d = 3 ^ d * (1 / 2) ^ d := by
    rw [← mul_pow]; norm_num
  rw [h3] at hmeas
  have := le_of_mul_le_mul_right hmeas (by positivity)
  exact_mod_cast this

end Packing

/-- Lemma 10: every finite point set in `ℝ^d` has a navigable graph of out-degree `≤ 3^d`. -/
theorem exists_navigable {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hx : Function.Injective x) :
    ∃ N : Fin n → Finset (Fin n), (∀ i, (N i).card ≤ 3 ^ d) ∧
      ∀ i q, q ≠ i → ∃ y ∈ N i, dist (x q) (x y) < dist (x q) (x i) := by
  have h : ∀ i, ∃ S : Finset (Fin n), S.card ≤ 3 ^ d ∧
      ∀ q, q ≠ i → ∃ y ∈ S, dist (x q) (x y) < dist (x q) (x i) := by
    intro i
    obtain ⟨S, hST, hpair, hcov⟩ := exists_cover x i (Finset.univ.erase i)
    have hSi : ∀ y ∈ S, 0 < ‖x y - x i‖ := by
      intro y hy
      have : y ≠ i := Finset.ne_of_mem_erase (hST hy)
      rw [norm_pos_iff, sub_ne_zero]
      exact hx.ne this
    refine ⟨S, ?_, ?_⟩
    · apply card_le_of_unit_sep S (fun y => ‖x y - x i‖⁻¹ • (x y - x i))
      · intro y hy
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hSi y hy)),
          inv_mul_cancel₀ (hSi y hy).ne']
      · have key : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → dist (x y) (x i) ≤ dist (x z) (x i) →
            1 ≤ dist (‖x y - x i‖⁻¹ • (x y - x i)) (‖x z - x i‖⁻¹ • (x z - x i)) := by
          intro y hy z hz hyz hle
          rw [dist_eq_norm]
          apply one_le_norm_sub_unit (hSi y hy)
          · rwa [← dist_eq_norm, ← dist_eq_norm]
          · rw [sub_sub_sub_cancel_right, ← dist_eq_norm, ← dist_eq_norm]
            exact hpair y hy z hz hyz hle
        intro y hy z hz hyz
        rcases le_total (dist (x y) (x i)) (dist (x z) (x i)) with h | h
        · exact key y hy z hz hyz h
        · rw [dist_comm]
          exact key z hz y hy (Ne.symm hyz) h
    · intro q hq
      rcases hcov q (Finset.mem_erase.mpr ⟨hq, Finset.mem_univ _⟩) with h | h
      · refine ⟨q, h, ?_⟩
        rw [dist_self]
        exact dist_pos.mpr (hx.ne hq)
      · exact h
  choose N hN1 hN2 using h
  exact ⟨N, hN1, hN2⟩

end SelfApproaching.Proof.Exponential
