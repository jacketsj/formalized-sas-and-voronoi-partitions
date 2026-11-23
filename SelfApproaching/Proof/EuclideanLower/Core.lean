import Mathlib

/-!
# Generic tools for the `⌈9d/4⌉` construction

Sequences are represented as `ℕ → E` together with a length.
-/

namespace SelfApproaching.Proof.EuclideanLowerAux

open Filter Topology

/-- Strict SAS for the first `n` terms of a `ℕ`-indexed sequence. -/
def NSAS {E : Type*} [MetricSpace E] (x : ℕ → E) (n : ℕ) : Prop :=
  ∀ i j k, i < j → j < n → k < n → k ≠ i → dist (x k) (x j) < dist (x k) (x i)

/-- Keep the first `N` terms of `p`, then continue with `q`. -/
def ins {E : Type*} (p : ℕ → E) (N : ℕ) (q : ℕ → E) : ℕ → E :=
  fun i => if i < N then p i else q (i - N)

/-- Inserting a family of new points (depending on a parameter `t` and tending to `0`) before
the final origin of a strict SAS gives eventually a strict SAS, provided the new points form a
strict SAS ending at the origin and every old point sees them get strictly closer. -/
theorem extend {α E : Type*} [NormedAddCommGroup E] {l : Filter α}
    (p : ℕ → E) (N M : ℕ) (hp : NSAS p (N + 1)) (hpN : p N = 0)
    (q : α → ℕ → E) (hq0 : ∀ t, q t M = 0)
    (hlim : ∀ m < M, Tendsto (fun t => q t m) l (𝓝 0))
    (hint : ∀ᶠ t in l, NSAS (q t) (M + 1))
    (hobs : ∀ᶠ t in l, ∀ a < N, ∀ i j, i < j → j ≤ M →
      dist (p a) (q t j) < dist (p a) (q t i)) :
    ∀ᶠ t in l, NSAS (ins p N (q t)) (N + M + 1) := by
  have key : ∀ i j k, i < j → j < N + M + 1 → k < N + M + 1 → k ≠ i →
      ∀ᶠ t in l, dist (ins p N (q t) k) (ins p N (q t) j) <
        dist (ins p N (q t) k) (ins p N (q t) i) := by
    intro i j k hij hj hk hki
    by_cases hiN : N ≤ i
    · have hjN : ¬ j < N := by omega
      have hiN' : ¬ i < N := by omega
      by_cases hkN : k < N
      · filter_upwards [hobs] with t ht
        simp only [ins, hjN, hiN', hkN, if_true, if_false]
        exact ht k hkN (i - N) (j - N) (by omega) (by omega)
      · filter_upwards [hint] with t ht
        simp only [ins, hjN, hiN', hkN, if_false]
        exact ht (i - N) (j - N) (k - N) (by omega) (by omega) (by omega) (by omega)
    · replace hiN : i < N := not_le.mp hiN
      have hlimy : ∀ m, m < N + M + 1 →
          Tendsto (fun t => ins p N (q t) m) l (𝓝 (p (min m N))) := by
        intro m hm
        by_cases hmN : m < N
        · simp only [ins, hmN, if_true, min_eq_left hmN.le]
          exact tendsto_const_nhds
        · simp only [ins, hmN, if_false, min_eq_right (not_lt.mp hmN), hpN]
          rcases lt_or_eq_of_le (show m - N ≤ M by omega) with h | h
          · exact hlim _ h
          · simp only [h, hq0]
            exact tendsto_const_nhds
      have hlt : dist (p (min k N)) (p (min j N)) < dist (p (min k N)) (p (min i N)) := by
        apply hp <;> omega
      exact ((hlimy k hk).dist (hlimy j hj)).eventually_lt
        ((hlimy k hk).dist (hlimy i (by omega))) hlt
  have h3 : ∀ᶠ t in l, ∀ i j k : Fin (N + M + 1), i.val < j.val → k.val ≠ i.val →
      dist (ins p N (q t) k) (ins p N (q t) j) < dist (ins p N (q t) k) (ins p N (q t) i) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k => ?_
    by_cases h1 : i.val < j.val
    · by_cases h2 : k.val ≠ i.val
      · filter_upwards [key i j k h1 j.2 k.2 h2] with t ht _ _ using ht
      · exact Eventually.of_forall fun _ _ h => absurd h h2
    · exact Eventually.of_forall fun _ h => absurd h h1
  filter_upwards [h3] with t ht
  intro i j k hij hj hk hki
  exact ht ⟨i, by omega⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hki

/-- Mutually orthogonal vectors with strictly decreasing norms form a strict SAS. -/
theorem orth_sas {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E) (M : ℕ)
    (horth : ∀ a ≤ M, ∀ b ≤ M, a ≠ b → inner ℝ (v a) (v b) = 0)
    (hanti : ∀ a b, a < b → b ≤ M → ‖v b‖ < ‖v a‖) : NSAS v (M + 1) := by
  have hd : ∀ a ≤ M, ∀ b ≤ M, a ≠ b → dist (v a) (v b) ^ 2 = ‖v a‖ ^ 2 + ‖v b‖ ^ 2 := by
    intro a ha b hb hab
    rw [dist_eq_norm, norm_sub_sq_real, horth a ha b hb hab]
    ring
  intro i j k hij hj hk hki
  rw [← pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero]
  have h1 := hanti i j hij (by omega)
  have h0 : 0 ≤ ‖v j‖ := norm_nonneg _
  rw [hd k (by omega) i (by omega) hki]
  by_cases hkj : k = j
  · subst hkj
    simp only [dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    nlinarith
  · rw [hd k (by omega) j (by omega) hkj]
    nlinarith

/-- A strictly decreasing chain, from consecutive comparisons. -/
theorem chain {f : ℕ → ℝ} {M : ℕ} (h : ∀ a < M, f (a + 1) < f a) :
    ∀ i j, i < j → j ≤ M → f j < f i := by
  intro i j hij hjM
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h' | h'
    · exact (h j (by omega)).trans (ih h' (by omega))
    · subst h'
      exact h i (by omega)

/-- The six-term sequence `(b0, b1, b2, b3, z, 0)`. -/
def five {E : Type*} [Zero E] (b0 b1 b2 b3 z : E) : ℕ → E
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => z
  | _ => 0

theorem five_sas {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b0 b1 b2 b3 z : E) (R0 R1 R2 R3 c C : ℝ)
    (h01 : inner ℝ b0 b1 = 0) (h02 : inner ℝ b0 b2 = 0) (h03 : inner ℝ b0 b3 = 0)
    (h12 : inner ℝ b1 b2 = 0) (h13 : inner ℝ b1 b3 = 0) (h23 : inner ℝ b2 b3 = 0)
    (n0 : ‖b0‖ = R0) (n1 : ‖b1‖ = R1) (n2 : ‖b2‖ = R2) (n3 : ‖b3‖ = R3)
    (z0 : inner ℝ b0 z = c * R0) (z1 : inner ℝ b1 z = c * R1)
    (z2 : inner ℝ b2 z = c * R2) (z3 : inner ℝ b3 z = c * R3) (hz : ‖z‖ ^ 2 = C)
    (hR10 : R1 < R0) (hR21 : R2 < R1) (hR32 : R3 < R2) (hR3 : 0 < R3) (hC : C < R3 ^ 2)
    (hcC : 2 * c * R0 < C) (hc : 0 ≤ c) : NSAS (five b0 b1 b2 b3 z) 6 := by
  have h10 : inner ℝ b1 b0 = 0 := by rw [real_inner_comm]; exact h01
  have h20 : inner ℝ b2 b0 = 0 := by rw [real_inner_comm]; exact h02
  have h30 : inner ℝ b3 b0 = 0 := by rw [real_inner_comm]; exact h03
  have h21 : inner ℝ b2 b1 = 0 := by rw [real_inner_comm]; exact h12
  have h31 : inner ℝ b3 b1 = 0 := by rw [real_inner_comm]; exact h13
  have h32 : inner ℝ b3 b2 = 0 := by rw [real_inner_comm]; exact h23
  have z0' : inner ℝ z b0 = c * R0 := by rw [real_inner_comm]; exact z0
  have z1' : inner ℝ z b1 = c * R1 := by rw [real_inner_comm]; exact z1
  have z2' : inner ℝ z b2 = c * R2 := by rw [real_inner_comm]; exact z2
  have z3' : inner ℝ z b3 = c * R3 := by rw [real_inner_comm]; exact z3
  have s10 : R1 ^ 2 < R0 ^ 2 := pow_lt_pow_left₀ hR10 (by linarith) two_ne_zero
  have s21 : R2 ^ 2 < R1 ^ 2 := pow_lt_pow_left₀ hR21 (by linarith) two_ne_zero
  have s32 : R3 ^ 2 < R2 ^ 2 := pow_lt_pow_left₀ hR32 hR3.le two_ne_zero
  have c1 : c * R1 ≤ c * R0 := mul_le_mul_of_nonneg_left hR10.le hc
  have c2 : c * R2 ≤ c * R1 := mul_le_mul_of_nonneg_left hR21.le hc
  have c3 : c * R3 ≤ c * R2 := mul_le_mul_of_nonneg_left hR32.le hc
  have c3' : 0 ≤ c * R3 := mul_nonneg hc hR3.le
  have hR3c : 2 * c < R3 := by
    have h : 2 * c * R3 < R3 * R3 := by
      have e1 : 2 * c * R3 = 2 * (c * R3) := by ring
      have e2 : R3 * R3 = R3 ^ 2 := by ring
      have e3 : 2 * c * R0 = 2 * (c * R0) := by ring
      linarith
    exact lt_of_mul_lt_mul_right h hR3.le
  have g : ∀ a b : ℝ, b < a → 2 * c < b →
      b ^ 2 - 2 * (c * b) < a ^ 2 - 2 * (c * a) := by
    intro a b hab hb
    have h := mul_pos (sub_pos.2 hab) (show 0 < a + b - 2 * c by linarith)
    have e : (a - b) * (a + b - 2 * c) = (a ^ 2 - 2 * (c * a)) - (b ^ 2 - 2 * (c * b)) := by ring
    linarith
  have g10 := g R0 R1 hR10 (by linarith)
  have g21 := g R1 R2 hR21 (by linarith)
  have g32 := g R2 R3 hR32 hR3c
  have g3 : 0 < R3 ^ 2 - 2 * (c * R3) := by
    have h := mul_pos hR3 (show 0 < R3 - 2 * c by linarith)
    have e : R3 * (R3 - 2 * c) = R3 ^ 2 - 2 * (c * R3) := by ring
    linarith
  intro i j k hij hj hk hki
  rw [← pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero, dist_eq_norm, dist_eq_norm,
    norm_sub_sq_real, norm_sub_sq_real]
  have hi : i < 5 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    first
    | omega
    | (simp only [five, real_inner_self_eq_norm_sq, inner_zero_left, inner_zero_right, norm_zero,
        h01, h02, h03, h12, h13, h23, h10, h20, h30, h21, h31, h32, z0, z1, z2, z3,
        z0', z1', z2', z3', n0, n1, n2, n3, hz]
       linarith only [s10, s21, s32, c1, c2, c3, c3', g10, g21, g32, g3, hC, hcC, hR3, hR10,
         hR21, hR32, hR3c])

end SelfApproaching.Proof.EuclideanLowerAux
