import SelfApproaching.Definitions
import SelfApproaching.Proof.Exponential.Partition
import SelfApproaching.Proof.Exponential.Navigable

/-!
# Theorem 12: exponential balanced partition bound via navigable graphs

Combines Lemma 10 (`Exponential.exists_navigable`: navigable graphs of out-degree `≤ 3^d` in
`ℝ^d`) with Lemma 11 (`Exponential.balanced_of_navigable`).
-/

namespace SelfApproaching.Proof

open Real

theorem euclidean_balanced_exp (d : ℕ) (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x) :
    HasBalancedVoronoiPartition dist x (1 / (2 * 3 ^ d)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `ℝ^0` is a single point, so two distinct points are impossible
    exfalso
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    exact h01 (hx (Subsingleton.elim _ _))
  obtain ⟨N, hN, hnav⟩ := Exponential.exists_navigable x hx
  apply Exponential.balanced_of_navigable x hn ((3 : ℝ) ^ d) _ N
  · intro i
    exact_mod_cast hN i
  · intro i q hq
    obtain ⟨y, hy, h⟩ := hnav i q hq
    exact ⟨y, hy, Exponential.mem_voronoiSide.mpr (Or.inl h)⟩
  · calc (3 / 2 : ℝ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) hd

end SelfApproaching.Proof
