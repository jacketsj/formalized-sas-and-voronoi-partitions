import SelfApproaching.Definitions
import SelfApproaching.Proof.EuclideanUpper.Rows

/-!
# Weak SASs in `ℝ^d` have length `< 11d/2`

Proof outline (see `Proof/EuclideanUpper/Bisector.lean` and `Proof/EuclideanUpper/Rows.lean`):
with `N = ℓ - 1` unit step directions `u i`, the bisector distance bound gives the row bound
`∑_{j>i} ⟪u i, u j⟫² ≤ 9/4`, hence `∑_{i,j} ⟪u i, u j⟫² ≤ 11N/2 - 7`; on the other hand
`∑_{i,j} ⟪u i, u j⟫² ≥ N²/d` for any `N` unit vectors in `ℝ^d`.
-/

namespace SelfApproaching.Proof

open Real

namespace EuclideanUpper

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `∑_{i,j<N} ⟪u i, u j⟫² ≥ N²/d` for unit vectors in `ℝ^d`. -/
theorem gram_lower (d N : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i < N, ‖v i‖ = 1) :
    (N : ℝ) ^ 2 ≤ d * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ⟪v i, v j⟫ ^ 2 := by
  have hinner : ∀ i j, ⟪v i, v j⟫ = ∑ a, v i a * v j a := fun i j => by
    simp [PiLp.inner_apply, mul_comm]
  set M : Fin d → Fin d → ℝ := fun a b => ∑ i ∈ Finset.range N, v i a * v i b
  have hexp : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ⟪v i, v j⟫ ^ 2 =
      ∑ a, ∑ b, M a b ^ 2 := by
    simp only [hinner, M, sq, Finset.sum_mul_sum]
    calc _ = ∑ i ∈ Finset.range N, ∑ a, ∑ b, ∑ j ∈ Finset.range N,
          (v i).ofLp a * (v j).ofLp a * ((v i).ofLp b * (v j).ofLp b) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  have hdiag : ∑ a, M a a ^ 2 ≤ ∑ a, ∑ b, M a b ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => M a b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  have htr : ∑ a, M a a = N := by
    simp only [M]
    rw [Finset.sum_comm]
    have : ∀ i ∈ Finset.range N, ∑ a, v i a * v i a = 1 := fun i hi => by
      rw [← hinner, real_inner_self_eq_norm_sq, hv i (Finset.mem_range.1 hi)]
      norm_num
    rw [Finset.sum_congr rfl this]
    simp
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => M a a)
  simp only [Finset.card_univ, Fintype.card_fin, htr] at hcs
  rw [hexp]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hdiag hd]

end EuclideanUpper

open EuclideanUpper in
theorem euclidean_sas_length_lt (d : ℕ) (hd : 1 ≤ d) (ℓ : ℕ)
    (x : Fin ℓ → EuclideanSpace ℝ (Fin d)) (hx : IsSAS dist x) :
    2 * ℓ < 11 * d := by
  by_cases hsmall : ℓ ≤ 5
  · omega
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 3 := ⟨ℓ - 3, by omega⟩
  set y : ℕ → EuclideanSpace ℝ (Fin d) := fun m => if h : m < n + 3 then x ⟨m, h⟩ else 0
    with hy
  have hS : SASn y (n + 3) := by
    constructor
    · intro a b ha hb e
      simp only [hy, dif_pos ha, dif_pos hb] at e
      exact congrArg Fin.val (hx.1 e)
    · intro a b k hab hb hk hka
      simp only [hy, dif_pos hb, dif_pos hk, dif_pos (hab.trans hb)]
      have := hx.2 ⟨a, hab.trans hb⟩ ⟨b, hb⟩ ⟨k, hk⟩ (Fin.mk_lt_mk.2 hab)
        (fun h => hka (congrArg Fin.val h))
      simpa only [dist_eq_norm] using this
  have hup := gram_upper n hS
  have hlow := gram_lower d (n + 2) (u y) (fun i hi => u_norm hS i (by omega))
  push_cast at hlow
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_contra hcon
  have h11 : (11 * d : ℝ) ≤ 2 * (n + 3) := by exact_mod_cast not_lt.1 hcon
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ d),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (n + 3) - 11 * d) (by linarith : (0 : ℝ) ≤ 11 * n + 8)]

end SelfApproaching.Proof
