import SelfApproaching.Proof.EuclideanUpper.Bisector

/-!
# Row bound and the upper bound on the Frobenius norm of the step Gram matrix

For a (weak) SAS `y 0, …, y (ℓ-1)` in a real inner product space with unit steps `u j`, every row
`∑_{j > i} ⟪u i, u j⟫²` with `i + 2 < ℓ` is at most `9/4`; hence for `N = ℓ - 1 ≥ 2` steps,
`∑_{i,j < N} ⟪u i, u j⟫² ≤ 11 N / 2 - 7`.
-/

namespace SelfApproaching.Proof.EuclideanUpper

open List

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `y 0, …, y (ℓ-1)` is a (weak) SAS for the norm distance. -/
def SASn (y : ℕ → E) (ℓ : ℕ) : Prop :=
  (∀ a b, a < ℓ → b < ℓ → y a = y b → a = b) ∧
    ∀ a b k, a < b → b < ℓ → k < ℓ → k ≠ a → ‖y k - y b‖ ≤ ‖y k - y a‖

/-- Unit step directions. -/
noncomputable def u (y : ℕ → E) (j : ℕ) : E := ‖y (j + 1) - y j‖⁻¹ • (y (j + 1) - y j)

omit [InnerProductSpace ℝ E] in
lemma bsum_range' (y : ℕ → E) (a : E) : ∀ k m : ℕ,
    bsum a ((range' m (k + 1)).map y) = ∑ r ∈ Finset.range k, phi (y (m + r)) (y (m + r + 1)) a ^ 2
  | 0, m => by simp
  | k + 1, m => by
    rw [range'_succ, map_cons, range'_succ, map_cons, bsum_cons_cons, ← map_cons, ← range'_succ,
      bsum_range' y a k (m + 1), Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show m + (r + 1) = m + 1 + r by omega]

omit [InnerProductSpace ℝ E] in
lemma fwdSAS_range' {y : ℕ → E} {ℓ : ℕ} (hS : SASn y ℓ) (m n : ℕ) (h : m + n ≤ ℓ) :
    FwdSAS ((range' m n).map y) := by
  have hlt : ∀ a ∈ range' m n, a < ℓ := fun a ha => by
    obtain ⟨i, hi, rfl⟩ := mem_range'.1 ha
    omega
  refine ⟨Nodup.map_on (fun a ha b hb e => hS.1 a b (hlt a ha) (hlt b hb) e) nodup_range', ?_⟩
  intro o p q hsub
  obtain ⟨l', hl', e⟩ := sublist_map_iff.1 hsub
  have hlen := congrArg length e
  simp only [length_cons, length_nil, length_map] at hlen
  match l', hl', e with
  | [a, b, c], hl', e =>
    simp only [map_cons, map_nil, cons.injEq] at e
    obtain ⟨rfl, rfl, rfl, -⟩ := e
    have hp := (pairwise_lt_range' (s := m) (n := n)).sublist hl'
    simp only [pairwise_cons, mem_cons, forall_eq_or_imp,
      not_mem_nil, false_imp_iff, implies_true, and_true, Pairwise.nil] at hp
    have hb : b ∈ range' m n := hl'.subset (by simp)
    have hc : c ∈ range' m n := hl'.subset (by simp)
    have ha : a ∈ range' m n := hl'.subset (by simp)
    have := hS.2 b c a hp.2 (hlt c hc) (hlt a ha) hp.1.1.ne
    rw [norm_sub_rev (y c), norm_sub_rev (y b)]
    exact this

omit [InnerProductSpace ℝ E] in
lemma approach_range' {y : ℕ → E} {ℓ : ℕ} (hS : SASn y ℓ) (i m n : ℕ) (hi : i < m)
    (h : m + n ≤ ℓ) : Approach (y i) ((range' m n).map y) := by
  unfold Approach
  rw [pairwise_map]
  refine (pairwise_lt_range' (s := m) (n := n)).imp_of_mem fun ha hb hab => ?_
  obtain ⟨r, hr, rfl⟩ := mem_range'.1 ha
  obtain ⟨r', hr', rfl⟩ := mem_range'.1 hb
  exact pow_le_pow_left₀ (norm_nonneg _) (hS.2 _ _ i hab (by omega) (by omega) (by omega)) 2

lemma near_term (A B C : E) (hAB : A ≠ B) (hBC : B ≠ C) (h1 : ‖A - C‖ ≤ ‖A - B‖)
    (h2 : ‖C - B‖ ≤ ‖C - A‖) :
    ⟪B - A, ‖C - B‖⁻¹ • (C - B)⟫ ^ 2 + ‖B - C‖ ^ 2 ≤ 5 / 4 * ‖B - A‖ ^ 2 := by
  set s := B - A
  set w := C - B
  set L := ‖s‖
  set M := ‖w‖
  set c := ⟪s, w⟫
  have hL : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hAB))
  have hM : 0 < M := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hBC))
  have eCA : C - A = s + w := by simp [s, w]
  have hBC' : ‖B - C‖ = M := norm_sub_rev _ _
  have hAB' : ‖A - B‖ = L := norm_sub_rev _ _
  have hAC' : ‖A - C‖ = ‖C - A‖ := norm_sub_rev _ _
  rw [hAC', hAB'] at h1
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [eCA, norm_add_sq_real] at h1' h2'
  have hcs : |c| ≤ L * M := abs_real_inner_le_norm s w
  have hc2 : c ^ 2 ≤ L ^ 2 * M ^ 2 := by
    have := sq_le_sq' (abs_le.1 hcs).1 (abs_le.1 hcs).2
    nlinarith
  rw [real_inner_smul_right, hBC']
  have hMM : M ^ 2 ≤ L ^ 2 := by linarith
  have hc4 : c ^ 2 ≤ L ^ 4 / 4 := by nlinarith
  have k1 : L ^ 2 * (c ^ 2 + M ^ 4) ≤ 5 / 4 * L ^ 4 * M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hMM) (sub_nonneg.2 hc2),
      mul_nonneg (sub_nonneg.2 hc4) (sq_nonneg M)]
  have k2 : c ^ 2 + M ^ 4 ≤ 5 / 4 * L ^ 2 * M ^ 2 := by
    have hL2 : 0 < L ^ 2 := by positivity
    nlinarith
  rw [mul_pow, inv_pow]
  have hM2 : 0 < M ^ 2 := by positivity
  rw [show (M ^ 2)⁻¹ * c ^ 2 = c ^ 2 / M ^ 2 by ring, div_add' _ _ _ hM2.ne', div_le_iff₀ hM2]
  nlinarith

/-- **Row bound.** -/
theorem row_bound {y : ℕ → E} {ℓ : ℕ} (hS : SASn y ℓ) (i k : ℕ) (hℓ : ℓ = i + 3 + k) :
    ∑ j ∈ Finset.Ico (i + 1) (ℓ - 1), ⟪u y i, u y j⟫ ^ 2 ≤ 9 / 4 := by
  set A := y i
  set B := y (i + 1)
  set C := y (i + 2)
  set s := B - A
  have hAB : A ≠ B := fun h => by have := hS.1 _ _ (by omega) (by omega) h; omega
  have hBC : B ≠ C := fun h => by have := hS.1 _ _ (by omega) (by omega) h; omega
  have hL : 0 < ‖s‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hAB))
  have hterm : ∀ j, ⟪u y i, u y j⟫ ^ 2 = ⟪s, u y j⟫ ^ 2 / ‖s‖ ^ 2 := fun j => by
    show ⟪‖s‖⁻¹ • s, u y j⟫ ^ 2 = _
    rw [real_inner_smul_left, mul_pow, inv_pow]
    field_simp
  simp only [hterm, ← Finset.sum_div]
  rw [div_le_iff₀ (by positivity), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  -- far terms
  have hfar : ∑ j ∈ Finset.Ico (i + 1 + 1) (ℓ - 1), ⟪s, u y j⟫ ^ 2 ≤
      ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 := by
    have hsub : ∀ j ∈ Finset.Ico (i + 1 + 1) (ℓ - 1), ⟪s, u y j⟫ ^ 2 ≤
        phi (y j) (y (j + 1)) A ^ 2 + phi (y j) (y (j + 1)) B ^ 2 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have e : ⟪s, u y j⟫ = phi (y j) (y (j + 1)) B - phi (y j) (y (j + 1)) A := by
        have := phi_line A s (y j) (y (j + 1)) 1
        rw [one_smul, show A + s = B by simp [s], one_mul] at this
        rw [this, u, real_inner_smul_right]
        ring
      have hA : 0 ≤ phi (y j) (y (j + 1)) A := phi_nonneg
        (pow_le_pow_left₀ (norm_nonneg _) (hS.2 _ _ i (by omega) (by omega) (by omega)
          (by omega)) 2)
      have hB : 0 ≤ phi (y j) (y (j + 1)) B := phi_nonneg
        (pow_le_pow_left₀ (norm_nonneg _) (hS.2 _ _ (i + 1) (by omega) (by omega) (by omega)
          (by omega)) 2)
      rw [e]
      nlinarith [mul_nonneg hA hB]
    refine (Finset.sum_le_sum hsub).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show ℓ - 1 - (i + 1 + 1) = k by omega]
    have hbA := bisector_bound _ ((range' (i + 3) k).map y) rfl C A
      (by
        have := fwdSAS_range' hS (i + 2) (k + 1) (by omega)
        rwa [range'_succ, map_cons] at this)
      (by
        have := approach_range' hS i (i + 2) (k + 1) (by omega) (by omega)
        rwa [range'_succ, map_cons] at this)
    have hbB := bisector_bound _ ((range' (i + 3) k).map y) rfl C B
      (by
        have := fwdSAS_range' hS (i + 2) (k + 1) (by omega)
        rwa [range'_succ, map_cons] at this)
      (by
        have := approach_range' hS (i + 1) (i + 2) (k + 1) (by omega) (by omega)
        rwa [range'_succ, map_cons] at this)
    have eA := bsum_range' y A k (i + 2)
    have eB := bsum_range' y B k (i + 2)
    rw [range'_succ, map_cons] at eA eB
    rw [eA] at hbA
    rw [eB] at hbB
    simp only [show i + 1 + 1 = i + 2 by omega]
    exact add_le_add hbA hbB
  have hnear := near_term A B C hAB hBC (hS.2 _ _ i (by omega) (by omega) (by omega) (by omega))
    (hS.2 _ _ (i + 2) (by omega) (by omega) (by omega) (by omega))
  have h1 : ‖A - C‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    have := hS.2 (i + 1) (i + 2) i (by omega) (by omega) (by omega) (by omega)
    rw [show ‖s‖ = ‖A - B‖ from norm_sub_rev _ _]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hu : u y (i + 1) = ‖C - B‖⁻¹ • (C - B) := rfl
  rw [hu]
  linarith

/-- Splitting a symmetric double sum into the diagonal and twice the upper triangle. -/
lemma sum_sym (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = f j i) : ∀ n : ℕ,
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f i j =
      ∑ i ∈ Finset.range n, f i i + 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico (i + 1) n, f i j
  | 0 => by simp
  | n + 1 => by
    have ih := sum_sym f hf n
    have h1 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico (i + 1) (n + 1), f i j =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico (i + 1) n, f i j +
          ∑ i ∈ Finset.range n, f i n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact Finset.sum_Ico_succ_top (by omega) _
    have h2 : ∑ j ∈ Finset.range n, f n j = ∑ i ∈ Finset.range n, f i n :=
      Finset.sum_congr rfl fun j _ => hf n j
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, Finset.Ico_self,
      Finset.sum_empty, add_zero, h1, h2, ih]
    ring

lemma u_norm {y : ℕ → E} {ℓ : ℕ} (hS : SASn y ℓ) (i : ℕ) (hi : i + 1 < ℓ) : ‖u y i‖ = 1 := by
  have hne : y (i + 1) - y i ≠ 0 :=
    sub_ne_zero.2 fun h => by have := hS.1 _ _ hi (by omega) h; omega
  rw [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]

/-- Upper bound on `∑_{i,j<N} ⟪u i, u j⟫²` for an SAS with `N + 1` points, `N ≥ 2`. -/
theorem gram_upper {y : ℕ → E} (n : ℕ) (hS : SASn y (n + 3)) :
    ∑ i ∈ Finset.range (n + 2), ∑ j ∈ Finset.range (n + 2), ⟪u y i, u y j⟫ ^ 2 ≤
      11 / 2 * (n + 2 : ℝ) - 7 := by
  rw [sum_sym _ (fun i j => by rw [real_inner_comm])]
  have hdiag : ∑ i ∈ Finset.range (n + 2), ⟪u y i, u y i⟫ ^ 2 = n + 2 := by
    have h1 : ∀ i ∈ Finset.range (n + 2), ⟪u y i, u y i⟫ ^ 2 = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [real_inner_self_eq_norm_sq, u_norm hS i (by omega)]
      norm_num
    rw [Finset.sum_congr rfl h1]
    simp
  have hrow : ∀ i ∈ Finset.range n,
      ∑ j ∈ Finset.Ico (i + 1) (n + 2), ⟪u y i, u y j⟫ ^ 2 ≤ 9 / 4 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have := row_bound hS i (n - i) (by omega)
    rwa [show n + 3 - 1 = n + 2 by omega] at this
  have hlast : ⟪u y n, u y (n + 1)⟫ ^ 2 ≤ 1 := by
    have := abs_real_inner_le_norm (u y n) (u y (n + 1))
    rw [u_norm hS n (by omega), u_norm hS (n + 1) (by omega), one_mul] at this
    have h0 := abs_nonneg ⟪u y n, u y (n + 1)⟫
    rw [← sq_abs]
    nlinarith
  rw [hdiag, Finset.sum_range_succ, Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty,
    add_zero, show n + 1 + 1 = n + 2 by omega, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self,
    Finset.sum_empty, zero_add]
  have := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  linarith

end SelfApproaching.Proof.EuclideanUpper
