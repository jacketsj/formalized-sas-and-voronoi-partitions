import SelfApproaching.Definitions
import SelfApproaching.Proof.Codes

namespace SelfApproaching.Proof

open Real Finset

/-! ## Combinatorial core

Index the points by `Fin (N + N)`: `Fin.castAdd N i` is the `i`-th point of the first copy `X₁`
and `Fin.natAdd N i` the `i`-th point of the (half-scaled) second copy `X₂`. Larger indices have
smaller scalings. Only three distance comparisons are needed. -/

private lemma kcenter_core {N : ℕ} (hN : 1 ≤ N) (D : Fin (N + N) → Fin (N + N) → ℝ)
    (ha : ∀ i j k : Fin N, j ≠ k →
      D (Fin.castAdd N j) (Fin.natAdd N i) < D (Fin.castAdd N j) (Fin.castAdd N k))
    (hb : ∀ i j k : Fin N, k < i →
      D (Fin.castAdd N j) (Fin.natAdd N i) < D (Fin.castAdd N j) (Fin.natAdd N k))
    (hc : ∀ i j k : Fin N, k < i →
      D (Fin.natAdd N j) (Fin.castAdd N i) < D (Fin.natAdd N j) (Fin.castAdd N k))
    (P : Finset (Fin (N + N))) (hP : P.Nonempty) (hPc : 4 * P.card ≤ N + N) :
    ∃ p ∈ P, N + N < 4 * (univ.filter fun k => ∀ q ∈ P, q ≠ p → D k p < D k q).card := by
  classical
  have hne : ∀ i j : Fin N, Fin.castAdd N i ≠ Fin.natAdd N j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  by_cases h2 : ∃ i, Fin.natAdd N i ∈ P
  · -- some center lies in `X₂`: take the one with the smallest scaling
    set Q := univ.filter fun i : Fin N => Fin.natAdd N i ∈ P with hQdef
    have hQ : Q.Nonempty := by
      obtain ⟨i, hi⟩ := h2
      exact ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    set i := Q.max' hQ
    have hi : Fin.natAdd N i ∈ P := (Finset.mem_filter.mp (Q.max'_mem hQ)).2
    refine ⟨Fin.natAdd N i, hi, ?_⟩
    set T := univ.filter fun j : Fin N => Fin.castAdd N j ∈ P with hTdef
    set T' := univ.filter fun j : Fin N => Fin.castAdd N j ∉ P with hT'def
    have hsub : T'.map (Fin.castAddEmb N) ⊆
        univ.filter fun k => ∀ q ∈ P, q ≠ Fin.natAdd N i → D k (Fin.natAdd N i) < D k q := by
      intro k hk
      simp only [T', mem_map, mem_filter, mem_univ, true_and] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      simp only [mem_filter, mem_univ, true_and]
      intro q hq hqp
      induction q using Fin.addCases with
      | left k => exact ha i j k (by rintro rfl; exact hj hq)
      | right k =>
        have hk : k ∈ Q := Finset.mem_filter.mpr ⟨mem_univ _, hq⟩
        have hki : k ≤ i := Q.le_max' k hk
        have hki' : k ≠ i := by rintro rfl; exact hqp rfl
        exact hb i j k (lt_of_le_of_ne hki hki')
    have hcard1 := card_le_card hsub
    rw [card_map] at hcard1
    have hT : T.map (Fin.castAddEmb N) ⊆ P.erase (Fin.natAdd N i) := by
      intro k hk
      simp only [T, mem_map, mem_filter, mem_univ, true_and] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact mem_erase.mpr ⟨hne _ _, hj⟩
    have hcard2 := card_le_card hT
    rw [card_map, card_erase_of_mem hi] at hcard2
    have hcard3 : T.card + T'.card = N := by
      rw [hTdef, hT'def, card_filter_add_card_filter_not]
      simp
    have := hP.card_pos
    omega
  · -- all centers lie in `X₁`: the one with the smallest scaling gets all of `X₂`
    simp only [not_exists] at h2
    set Q := univ.filter fun i : Fin N => Fin.castAdd N i ∈ P with hQdef
    have hQ : Q.Nonempty := by
      obtain ⟨q, hq⟩ := hP
      induction q using Fin.addCases with
      | left k => exact ⟨k, Finset.mem_filter.mpr ⟨mem_univ _, hq⟩⟩
      | right k => exact absurd hq (h2 k)
    set i := Q.max' hQ
    have hi : Fin.castAdd N i ∈ P := (Finset.mem_filter.mp (Q.max'_mem hQ)).2
    refine ⟨Fin.castAdd N i, hi, ?_⟩
    have hsub : (univ : Finset (Fin N)).map (Fin.natAddEmb N) ⊆
        univ.filter fun k => ∀ q ∈ P, q ≠ Fin.castAdd N i → D k (Fin.castAdd N i) < D k q := by
      intro k hk
      obtain ⟨j, -, rfl⟩ := mem_map.mp hk
      simp only [mem_filter, mem_univ, true_and]
      intro q hq hqp
      induction q using Fin.addCases with
      | left k =>
        have hk : k ∈ Q := Finset.mem_filter.mpr ⟨mem_univ _, hq⟩
        have hki : k ≤ i := Q.le_max' k hk
        have hki' : k ≠ i := by rintro rfl; exact hqp rfl
        exact hc i j k (lt_of_le_of_ne hki hki')
      | right k => exact absurd hq (h2 k)
    have := card_le_card hsub
    rw [card_map, card_univ, Fintype.card_fin] at this
    omega

/-! ## Geometry -/

/-- The indicator vector of the word `C i`, as a vector in `ℝ^(m × 8)`. -/
private noncomputable def wv {m N : ℕ} (C : Fin N → (Fin m → Fin 8)) (i : Fin N)
    (t : Fin (m * 8)) : ℝ :=
  if C i (finProdFinEquiv.symm t).1 = (finProdFinEquiv.symm t).2 then 1 else 0

private lemma inner_sum_sq (c c' : Fin 8) (α β : ℝ) :
    ∑ a : Fin 8, (α * (if c = a then 1 else 0) - β * (if c' = a then 1 else 0)) ^ 2 =
      α ^ 2 + β ^ 2 - (if c' = c then 2 * α * β else 0) := by
  rw [Finset.sum_congr rfl (g := fun a => (if c = a then α ^ 2 else 0) +
      (if c' = a then β ^ 2 else 0) - (if c = a then (if c' = a then 2 * α * β else 0) else 0))
      (fun a _ => by
        by_cases h1 : c = a <;> by_cases h2 : c' = a
        · simp only [if_pos h1, if_pos h2]; ring
        · simp only [if_pos h1, if_neg h2]; ring
        · simp only [if_neg h1, if_pos h2]; ring
        · simp only [if_neg h1, if_neg h2]; ring)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  simp

private lemma sum_sq_wv {m N : ℕ} (C : Fin N → (Fin m → Fin 8)) (α β : ℝ) (j k : Fin N) :
    ∑ t, (α * wv C j t - β * wv C k t) ^ 2 =
      m * (α ^ 2 + β ^ 2) - 2 * α * β * (univ.filter fun b => C j b = C k b).card := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [wv, Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun b _ => inner_sum_sq (C j b) (C k b) α β, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  simp only [eq_comm (a := C k _)]
  ring

/-- Realize a family of vectors in `ℝ^D` inside `EuclideanSpace ℝ (Fin d)` for `D ≤ d`. -/
private lemma euclid_embed {n D d : ℕ} (hD : D ≤ d) (g : Fin n → Fin D → ℝ) :
    ∃ x : Fin n → EuclideanSpace ℝ (Fin d),
      ∀ a b, dist (x a) (x b) = √(∑ t, (g a t - g b t) ^ 2) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hD
  refine ⟨fun a => WithLp.toLp 2 (Fin.append (g a) (0 : Fin e → ℝ)), fun a b => ?_⟩
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_add, Real.dist_eq, sq_abs]

/-- Transfer the combinatorial core to points of Euclidean space. -/
private lemma kcenter_of_sq {N d : ℕ} (hN : 1 ≤ N) (x : Fin (N + N) → EuclideanSpace ℝ (Fin d))
    (S : Fin (N + N) → Fin (N + N) → ℝ) (hS0 : ∀ a b, 0 ≤ S a b)
    (hx : ∀ a b, dist (x a) (x b) = √(S a b)) (hpos : ∀ a b, a ≠ b → 0 < S a b)
    (ha : ∀ i j k : Fin N, j ≠ k →
      S (Fin.castAdd N j) (Fin.natAdd N i) < S (Fin.castAdd N j) (Fin.castAdd N k))
    (hb : ∀ i j k : Fin N, k < i →
      S (Fin.castAdd N j) (Fin.natAdd N i) < S (Fin.castAdd N j) (Fin.natAdd N k))
    (hc : ∀ i j k : Fin N, k < i →
      S (Fin.natAdd N j) (Fin.castAdd N i) < S (Fin.natAdd N j) (Fin.castAdd N k)) :
    Function.Injective x ∧
      ∀ P : Finset (Fin (N + N)), P.Nonempty → 4 * P.card ≤ N + N →
        ∃ p ∈ P, N + N < 4 * (voronoiCell dist x P p).card := by
  refine ⟨fun a b hab => ?_, fun P hP hPc => ?_⟩
  · by_contra hne
    have h := hpos a b hne
    have h0 : dist (x a) (x b) = 0 := by rw [hab, dist_self]
    rw [hx, Real.sqrt_eq_zero (hS0 a b)] at h0
    linarith
  · obtain ⟨p, hp, hcard⟩ := kcenter_core hN S ha hb hc P hP hPc
    refine ⟨p, hp, lt_of_lt_of_le hcard ?_⟩
    apply Nat.mul_le_mul_left
    apply le_of_eq
    unfold voronoiCell
    congr 1
    ext k
    simp only [hx, Real.sqrt_lt_sqrt_iff (hS0 _ _)]

/-- The main construction from a code. -/
private lemma kcenter_from_code {m N d : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (hd : m * 8 + m * 8 ≤ d)
    (C : Fin N → (Fin m → Fin 8))
    (hC : ∀ i j, i ≠ j → ((univ.filter fun b => C i b = C j b).card : ℝ) ≤ m / 4) :
    ∃ x : Fin (N + N) → EuclideanSpace ℝ (Fin d), Function.Injective x ∧
      ∀ P : Finset (Fin (N + N)), P.Nonempty → 4 * P.card ≤ N + N →
        ∃ p ∈ P, N + N < 4 * (voronoiCell dist x P p).card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  -- scalings `r i = 1 - i / (10 N) ∈ (9/10, 1]`, strictly decreasing
  set r : Fin N → ℝ := fun i => 1 - (i : ℝ) / (10 * N) with hrdef
  have hr_lo : ∀ i, 9 / 10 < r i := by
    intro i
    have : (i : ℝ) < N := by exact_mod_cast i.2
    have : (i : ℝ) / (10 * N) < 1 / 10 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    simp only [r]; linarith
  have hr_hi : ∀ i, r i ≤ 1 := by
    intro i
    simp only [r]
    have : 0 ≤ (i : ℝ) / (10 * N) := by positivity
    linarith
  have hr_anti : ∀ i k : Fin N, k < i → r i < r k := by
    intro i k hki
    have : (k : ℝ) < i := by exact_mod_cast hki
    simp only [r]
    have : (k : ℝ) / (10 * N) < i / (10 * N) := div_lt_div_of_pos_right this (by positivity)
    linarith
  set A : Fin N → Fin N → ℝ := fun j k => ((univ.filter fun b => C j b = C k b).card : ℝ)
    with hAdef
  have hA0 : ∀ j k, 0 ≤ A j k := fun _ _ => Nat.cast_nonneg _
  -- coefficients of each point in the two blocks
  let idx : Fin (N + N) → Fin N := Fin.addCases (fun i => i) (fun i => i)
  let c1 : Fin (N + N) → ℝ := Fin.addCases (fun i => r i) (fun _ => 0)
  let c2 : Fin (N + N) → ℝ := Fin.addCases (fun _ => 0) (fun i => r i / 2)
  let g : Fin (N + N) → Fin (m * 8 + m * 8) → ℝ := fun a =>
    Fin.append (fun t => c1 a * wv C (idx a) t) (fun t => c2 a * wv C (idx a) t)
  set S : Fin (N + N) → Fin (N + N) → ℝ := fun a b => ∑ t, (g a t - g b t) ^ 2 with hSdef
  have hSf : ∀ a b, S a b = (m * (c1 a ^ 2 + c1 b ^ 2) - 2 * c1 a * c1 b * A (idx a) (idx b)) +
      (m * (c2 a ^ 2 + c2 b ^ 2) - 2 * c2 a * c2 b * A (idx a) (idx b)) := by
    intro a b
    simp only [S, g, Fin.sum_univ_add, Fin.append_left, Fin.append_right, sum_sq_wv, A]
  have hLL : ∀ j k, S (Fin.castAdd N j) (Fin.castAdd N k) =
      m * (r j ^ 2 + r k ^ 2) - 2 * r j * r k * A j k := by
    intro j k
    rw [hSf]; simp only [c1, c2, idx, Fin.addCases_left]; ring
  have hLR : ∀ j i, S (Fin.castAdd N j) (Fin.natAdd N i) = m * (r j ^ 2 + (r i / 2) ^ 2) := by
    intro j i
    rw [hSf]; simp only [c1, c2, idx, Fin.addCases_left, Fin.addCases_right]; ring
  have hRL : ∀ j i, S (Fin.natAdd N j) (Fin.castAdd N i) = m * ((r j / 2) ^ 2 + r i ^ 2) := by
    intro j i
    rw [hSf]; simp only [c1, c2, idx, Fin.addCases_left, Fin.addCases_right]; ring
  have hRR : ∀ j k, S (Fin.natAdd N j) (Fin.natAdd N k) =
      m * ((r j / 2) ^ 2 + (r k / 2) ^ 2) - 2 * (r j / 2) * (r k / 2) * A j k := by
    intro j k
    rw [hSf]; simp only [c1, c2, idx, Fin.addCases_right]; ring
  obtain ⟨x, hx⟩ := euclid_embed hd g
  have hr0 : ∀ i, 0 < r i := fun i => by linarith [hr_lo i]
  have hlow : ∀ j k, j ≠ k →
      m * (r j ^ 2 + r k ^ 2 - r j * r k / 2) ≤ m * (r j ^ 2 + r k ^ 2) - 2 * r j * r k * A j k := by
    intro j k hjk
    have h1 : r j * r k * A j k ≤ r j * r k * (m / 4) :=
      mul_le_mul_of_nonneg_left (hC j k hjk) (mul_pos (hr0 j) (hr0 k)).le
    nlinarith
  have hsq : ∀ i k : Fin N, k < i → m * r i ^ 2 < m * r k ^ 2 := by
    intro i k hki
    have := hr_anti i k hki
    have : r i ^ 2 < r k ^ 2 := by nlinarith [hr0 i]
    exact mul_lt_mul_of_pos_left this hmr
  have hquad : ∀ j k, 0 < r j ^ 2 + r k ^ 2 - r j * r k / 2 := by
    intro j k
    nlinarith [hr0 j, hr0 k, hr_hi j, hr_hi k, mul_pos (hr0 j) (hr0 k)]
  refine ⟨x, kcenter_of_sq hN x S (fun a b => Finset.sum_nonneg fun _ _ => sq_nonneg _) hx
    ?_ ?_ ?_ ?_⟩
  · intro a b hab
    induction a using Fin.addCases with
    | left j =>
      induction b using Fin.addCases with
      | left k =>
        have hjk : j ≠ k := fun h => hab (h ▸ rfl)
        rw [hLL]
        nlinarith [hlow j k hjk, mul_pos hmr (hquad j k)]
      | right k =>
        rw [hLR]
        have := hr0 j
        positivity
    | right j =>
      induction b using Fin.addCases with
      | left k =>
        rw [hRL]
        have := hr0 k
        positivity
      | right k =>
        have hjk : j ≠ k := fun h => hab (h ▸ rfl)
        rw [hRR]
        nlinarith [hlow j k hjk, mul_pos hmr (hquad j k)]
  · intro i j k hjk
    rw [hLR, hLL]
    have h1 : 0 < r k ^ 2 - r j * r k / 2 - r i ^ 2 / 4 := by
      have : r j * r k ≤ 1 * r k := mul_le_mul_of_nonneg_right (hr_hi j) (hr0 k).le
      have : r i ^ 2 ≤ 1 := by nlinarith [hr0 i, hr_hi i]
      nlinarith [mul_nonneg (by linarith [hr_lo k] : (0 : ℝ) ≤ r k - 9 / 10)
        (by linarith [hr_lo k] : (0 : ℝ) ≤ r k + 4 / 10)]
    nlinarith [hlow j k hjk, mul_pos hmr h1]
  · intro i j k hki
    rw [hLR, hLR]
    nlinarith [hsq i k hki]
  · intro i j k hki
    rw [hRL, hRL]
    nlinarith [hsq i k hki]

theorem kcenter_unbalanced :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, ∃ n : ℕ, (2 : ℝ) ^ (c * d) ≤ n ∧
      ∃ x : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective x ∧
        ∀ P : Finset (Fin n), P.Nonempty → 4 * P.card ≤ n →
          ∃ p ∈ P, n < 4 * (voronoiCell dist x P p).card := by
  obtain ⟨c0, hc0, hcode⟩ := exists_code 8 (by norm_num) (1 / 8) (by norm_num)
  refine ⟨min (c0 / 32) (1 / 16), lt_min (by positivity) (by norm_num), fun d => ?_⟩
  set c := min (c0 / 32) (1 / 16) with hc
  have hc1 : c ≤ c0 / 32 := min_le_left _ _
  have hc2 : c ≤ 1 / 16 := min_le_right _ _
  have hcpos : 0 < c := lt_min (by positivity) (by norm_num)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, by simp, fun _ => 0, fun a b _ => Subsingleton.elim a b, fun P hP hPc => ?_⟩
    have := hP.card_pos
    omega
  by_cases hd16 : 16 ≤ d
  · set m := d / 16 with hm
    have hm1 : 1 ≤ m := by omega
    have h32 : d ≤ 32 * m := by omega
    obtain ⟨N, hN, C, hC⟩ := hcode m
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ N := le_trans (one_le_exp (by positivity)) hN
      exact_mod_cast this
    obtain ⟨x, hx⟩ := kcenter_from_code (d := d) hm1 hN1 (by omega) C fun i j hij => by
      have := hC i j hij
      norm_num at this ⊢
      linarith
    refine ⟨N + N, ?_, x, hx⟩
    have hcd : 0 ≤ c * d := by positivity
    have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ (c * d) ≤ exp 1 ^ (c * d) := rpow_le_rpow (by norm_num) h2e hcd
      _ = exp (c * d) := exp_one_rpow _
      _ ≤ exp (c0 * m) := by
        apply exp_le_exp.mpr
        have : (d : ℝ) ≤ 32 * m := by exact_mod_cast h32
        nlinarith
      _ ≤ N := hN
      _ ≤ ((N + N : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · obtain ⟨x, hx⟩ := euclid_embed (n := 2) hd (fun a _ => (a : ℝ))
    refine ⟨2, ?_, x, ?_, fun P hP hPc => ?_⟩
    · have hd' : (d : ℝ) ≤ 16 := by exact_mod_cast (show d ≤ 16 by omega)
      calc (2 : ℝ) ^ (c * d) ≤ 2 ^ (1 : ℝ) :=
            rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
        _ = ((2 : ℕ) : ℝ) := by norm_num
    · intro a b hab
      have h0 : dist (x a) (x b) = 0 := by rw [hab, dist_self]
      rw [hx] at h0
      fin_cases a <;> fin_cases b <;> simp_all
    · have := hP.card_pos
      omega

end SelfApproaching.Proof
