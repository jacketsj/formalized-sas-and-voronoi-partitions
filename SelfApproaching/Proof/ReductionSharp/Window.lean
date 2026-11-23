import SelfApproaching.Proof.ReductionSharp.Indep

/-!
# The windowed estimate for a single point

Split `Fin n` into windows of `G` consecutive indices (with offset `τ`). A selected point `k`
survives the deletion of violators as soon as no consecutive pair inside a window and no
consecutive pair straddling two windows is violated by `k`. The window events are independent,
which gives a product (instead of a union bound) for the pairs inside windows.
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

/-- The window of index `i`. -/
def win (G τ : ℕ) (i : Fin n) : ℕ := (i.val + τ) / G

/-- The (indices of the) nonempty windows. -/
def wins (n G τ : ℕ) : Finset ℕ := (univ : Finset (Fin n)).image (win G τ)

lemma mem_wins (G τ : ℕ) (i : Fin n) : win G τ i ∈ wins n G τ := mem_image_of_mem _ (mem_univ i)

/-- `(a, b)` is a pair that `k` can violate. -/
def Pk (T : Fin n → Fin n → Finset (Fin n)) (k a b : Fin n) : Prop :=
  a < b ∧ k ∈ T a b ∧ (k < a ∨ b < k)

instance (T : Fin n → Fin n → Finset (Fin n)) (k a b : Fin n) : Decidable (Pk T k a b) := by
  unfold Pk; infer_instance

/-- No pair inside window `p` is consecutive in `g` and violated by `k`. -/
def DW (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n) (p : ℕ)
    (g : Fin n → Bool) : Prop :=
  ∀ a b, Pk T k a b → win G τ a = p → win G τ b = p → ¬ Ev2 g a b

instance (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n) (p : ℕ)
    (g : Fin n → Bool) : Decidable (DW T G τ k p g) := by
  unfold DW; infer_instance

/-- Probability that `a < b` are consecutive. -/
noncomputable def wgt (q : ℝ) (a b : Fin n) : ℝ := q ^ 2 * (1 - q) ^ (b.val - a.val - 1)

/-- Union-bound mass of the pairs inside window `p`. -/
noncomputable def up (T : Fin n → Fin n → Finset (Fin n)) (q : ℝ) (G τ : ℕ) (k : Fin n)
    (p : ℕ) : ℝ :=
  ∑ a, ∑ b, if Pk T k a b ∧ win G τ a = p ∧ win G τ b = p then wgt q a b else 0

/-- Union-bound mass of the pairs straddling two windows. -/
noncomputable def Ck (T : Fin n → Fin n → Finset (Fin n)) (q : ℝ) (G τ : ℕ) (k : Fin n) : ℝ :=
  ∑ a, ∑ b, if Pk T k a b ∧ win G τ a ≠ win G τ b then wgt q a b else 0

lemma wt_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : Fin n → Bool) : 0 ≤ wt q g := by
  unfold wt
  apply prod_nonneg
  intro c _
  unfold bw
  split_ifs <;> linarith [hq0]

lemma wgt_nonneg {q : ℝ} (hq1 : q ≤ 1) (a b : Fin n) : 0 ≤ wgt q a b := by
  unfold wgt
  have : 0 ≤ 1 - q := by linarith
  positivity

lemma win_mono {G τ : ℕ} {a c : Fin n} (h : a ≤ c) : win G τ a ≤ win G τ c := by
  unfold win
  apply Nat.div_le_div_right
  have := Fin.le_def.mp h
  omega

/-- The block of coordinates that `DW … p` depends on. -/
def blk (G τ : ℕ) (k : Fin n) (p : ℕ) : Finset (Fin n) :=
  (univ.filter fun i => win G τ i = p).erase k

lemma DW_dep (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n) (p : ℕ)
    (g g' : Fin n → Bool) (h : ∀ i ∈ blk G τ k p, g i = g' i) :
    DW T G τ k p g ↔ DW T G τ k p g' := by
  have key : ∀ a b, Pk T k a b → win G τ a = p → win G τ b = p → (Ev2 g a b ↔ Ev2 g' a b) := by
    intro a b hP ha hb
    obtain ⟨hab, _, hk⟩ := hP
    have hin : ∀ c, a ≤ c → c ≤ b → g c = g' c := by
      intro c h1 h2
      apply h
      simp only [blk, mem_erase, mem_filter, mem_univ, true_and]
      have w1 := win_mono (G := G) (τ := τ) h1
      have w2 := win_mono (G := G) (τ := τ) h2
      refine ⟨?_, by omega⟩
      rintro rfl
      rcases hk with hk | hk
      · exact absurd h1 (not_le.mpr hk)
      · exact absurd h2 (not_le.mpr hk)
    unfold Ev2
    rw [hin a le_rfl hab.le, hin b hab.le le_rfl]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun c hc1 hc2 => (hin c hc1.le hc2.le) ▸ h3 c hc1 hc2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun c hc1 hc2 => (hin c hc1.le hc2.le).symm ▸ h3 c hc1 hc2⟩
  unfold DW
  constructor
  · intro hD a b hP ha hb hE
    exact hD a b hP ha hb ((key a b hP ha hb).mpr hE)
  · intro hD a b hP ha hb hE
    exact hD a b hP ha hb ((key a b hP ha hb).mp hE)

lemma mem_viol_iff (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) (a b k : Fin n) :
    (a, b, k) ∈ Viol T g ↔ Pk T k a b ∧ Ev g a b k := by
  simp [Viol, Pk]

lemma mem_good_iff (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) (k : Fin n) :
    k ∈ Good T g ↔ g k = true ∧ ¬ ∃ a b, Pk T k a b ∧ Ev g a b k := by
  unfold Good Rset
  rw [mem_sdiff, mem_filter, mem_image]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨a, b, hP, hE⟩
    exact h2 ⟨(a, b, k), (mem_viol_iff T g a b k).mpr ⟨hP, hE⟩, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨⟨a, b, c⟩, hm, rfl⟩
    exact h2 ⟨a, b, (mem_viol_iff T g a b c).mp hm⟩

lemma ev_ev2 {g : Fin n → Bool} {a b k : Fin n} (h : Ev g a b k) : Ev2 g a b := by
  unfold Ev at h
  exact ⟨(h a).1 (Or.inl rfl), (h b).1 (Or.inr (Or.inl rfl)), fun c h1 h2 => (h c).2 ⟨h1, h2⟩⟩

/-- The pointwise inequality behind the estimate. -/
lemma good_ind_ge (T : Fin n → Fin n → Finset (Fin n)) (G τ : ℕ) (k : Fin n)
    (g : Fin n → Bool) :
    (if g k = true then (1:ℝ) else 0) *
        ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0)
      - ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
          (if Ev g a b k then (1:ℝ) else 0) else 0)
      ≤ if k ∈ Good T g then 1 else 0 := by
  have hprod : ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0) ≤ 1 :=
    prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)
  have hprod0 : 0 ≤ ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0) :=
    prod_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hsum : 0 ≤ ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
      (if Ev g a b k then (1:ℝ) else 0) else 0) :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  by_cases hk : k ∈ Good T g
  · rw [if_pos hk]
    have : (if g k = true then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    nlinarith
  rw [if_neg hk]
  rw [mem_good_iff] at hk
  by_cases hgk : g k = true
  · have hv : ∃ a b, Pk T k a b ∧ Ev g a b k := by
      by_contra h; exact hk ⟨hgk, h⟩
    obtain ⟨a, b, hP, hE⟩ := hv
    by_cases hw : win G τ a = win G τ b
    · have h0 : ∏ p ∈ wins n G τ, (if DW T G τ k p g then (1:ℝ) else 0) = 0 := by
        apply prod_eq_zero (mem_wins G τ a)
        rw [if_neg]
        intro hD
        exact hD a b hP rfl hw.symm (ev_ev2 hE)
      rw [h0]; linarith
    · have h1 : (1:ℝ) ≤ ∑ a, ∑ b, (if Pk T k a b ∧ win G τ a ≠ win G τ b then
          (if Ev g a b k then (1:ℝ) else 0) else 0) := by
        have ha := single_le_sum (f := fun a' => ∑ b, (if Pk T k a' b ∧ win G τ a' ≠ win G τ b then
          (if Ev g a' b k then (1:ℝ) else 0) else 0))
          (fun a' _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (mem_univ a)
        have hb := single_le_sum (f := fun b' => (if Pk T k a b' ∧ win G τ a ≠ win G τ b' then
          (if Ev g a b' k then (1:ℝ) else 0) else 0))
          (fun _ _ => by dsimp only; split_ifs <;> norm_num) (mem_univ b)
        simp only [if_pos (And.intro hP hw), if_pos hE] at hb
        linarith
      have : (if g k = true then (1:ℝ) else 0) ≤ 1 := by rw [if_pos hgk]
      nlinarith
  · rw [if_neg hgk]; linarith

end SelfApproaching.Proof.ReductionSharp
