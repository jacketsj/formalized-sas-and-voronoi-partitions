import Mathlib

/-!
# Rank bounds for real matrices

* `trace_sq_le_rank_mul_sum_sq`: for a real symmetric matrix `A`,
  `(tr A)² ≤ rank A · ∑ᵢⱼ Aᵢⱼ²`.
* `rank_le_of_separable`: a matrix of the form `Aᵢⱼ = ∑_{l ∈ ι} φₗ(i) ψₗ(j)` has rank `≤ |ι|`.
-/

namespace SelfApproaching.Proof.LpAspect

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real symmetric matrix, `∑ᵢⱼ Aᵢⱼ² = ∑ᵢ λᵢ²`. -/
lemma sum_sq_eq_sum_eigenvalues_sq {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∑ i, ∑ j, A i j ^ 2 = ∑ i, hA.eigenvalues i ^ 2 := by
  have h1 : (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [trace, diag, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : A j i = A i j := by
      have := congrFun (congrFun hA i) j
      simpa using this
    rw [this, sq]
  have h2 : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
    set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
    set D : Matrix n n ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
    have hspec : A = U * D * star U := by
      conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
    have : A * A = U * (D * D) * star U := by
      rw [hspec]
      calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
            simp only [Matrix.mul_assoc]
        _ = U * (D * D) * star U := by rw [hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, trace_mul_cycle, hUU, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal]
    simp [sq]
  rw [← h1, h2]

/-- `(tr A)² ≤ rank A · ‖A‖_F²` for real symmetric `A`. -/
theorem trace_sq_le_rank_mul_sum_sq (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ A.rank * ∑ i, ∑ j, A i j ^ 2 := by
  rw [sum_sq_eq_sum_eigenvalues_sq hA, hA.rank_eq_card_non_zero_eigs]
  have htr : A.trace = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]; simp
  set S := Finset.univ.filter fun i => hA.eigenvalues i ≠ 0
  have hS : (∑ i, hA.eigenvalues i) = ∑ i ∈ S, hA.eigenvalues i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact not_not.mp h
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} = S.card := by
    rw [Fintype.card_subtype]
  rw [htr, hS, hcard]
  calc (∑ i ∈ S, hA.eigenvalues i) ^ 2 ≤ S.card * ∑ i ∈ S, hA.eigenvalues i ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ S.card * ∑ i, hA.eigenvalues i ^ 2 := by
        gcongr
        exact Finset.subset_univ S

/-- A matrix `Aᵢⱼ = ∑_{l} φₗ(i) ψₗ(j)` has rank at most the number of terms. -/
theorem rank_le_of_separable {m ι : Type*} [Fintype m] [Fintype ι] (A : Matrix m m ℝ)
    (φ ψ : ι → m → ℝ) (hA : ∀ i j, A i j = ∑ l, φ l i * ψ l j) :
    A.rank ≤ Fintype.card ι := by
  have : A = (Matrix.of fun i l => φ l i) * (Matrix.of fun l j => ψ l j) := by
    ext i j
    simp [hA, mul_apply]
  rw [this]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width _)

end SelfApproaching.Proof.LpAspect
