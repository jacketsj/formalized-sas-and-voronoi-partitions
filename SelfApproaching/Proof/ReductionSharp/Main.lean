import SelfApproaching.Proof.ReductionSharp.Global

/-!
# The sharpened combinatorial core

For `M ≥ 1001` the windowed estimate gives an SAS-like set with `n ≤ (999/250) M |R|`; for
`M ≤ 1000` the plain union bound with the `M - 1` genuine violators per pair suffices.
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset Real SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

lemma card_good_eq (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) :
    ((Good T g).card : ℝ) = ∑ k, (if k ∈ Good T g then (1:ℝ) else 0) := by
  rw [sum_boole]
  congr 2
  ext k; simp

lemma exists_good_of_avg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (T : Fin n → Fin n → Finset (Fin n))
    (c : ℝ) (h : c ≤ ∑ g, wt q g * ((Good T g).card : ℝ)) :
    ∃ g : Fin n → Bool, c ≤ (Good T g).card := by
  have hw : ∀ g : Fin n → Bool, 0 < wt q g := by
    intro g; unfold wt
    apply prod_pos; intro i _; unfold bw; split_ifs <;> linarith
  have hsum : ∑ g : Fin n → Bool, wt q g * c ≤ ∑ g, wt q g * ((Good T g).card : ℝ) := by
    rw [← sum_mul, sum_wt, one_mul]; exact h
  obtain ⟨g, _, hg⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨g, le_of_mul_le_mul_left hg (hw g)⟩

theorem window_core (M : ℕ) (hM : 1001 ≤ M) (T : Fin n → Fin n → Finset (Fin n))
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) (hn : 0 < n) :
    ∃ g : Fin n → Bool, (n : ℝ) ≤ 999 / 250 * M * (Good T g).card := by
  set q : ℝ := 1 / (2 * (M : ℝ)) with hq
  set G : ℕ := 29 * M / 50 with hGdef
  have hMr : (1001 : ℝ) ≤ M := by exact_mod_cast hM
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  have hMq : (M : ℝ) * q = 1 / 2 := by rw [hq]; field_simp
  have hG : 0 < G := by rw [hGdef]; omega
  have hγ : (G : ℝ) * q ≤ 29 / 100 := by
    have hG1 : 50 * G ≤ 29 * M := by rw [hGdef, mul_comm]; exact Nat.div_mul_le_self _ _
    have hG1r : 50 * (G : ℝ) ≤ 29 * M := by exact_mod_cast hG1
    have : (G : ℝ) * q = G / (2 * M) := by rw [hq]; field_simp
    rw [this, div_le_iff₀ (by positivity)]; linarith
  set E := ∑ g, wt q g * ((Good T g).card : ℝ) with hE
  have hEk : E = ∑ k, ∑ g, wt q g * (if k ∈ Good T g then (1:ℝ) else 0) := by
    rw [hE, sum_comm]
    apply sum_congr rfl; intro g _
    rw [card_good_eq, mul_sum]
  set y : ℕ × Fin n → ℝ := fun x => -(1023 / 1000 * (μk T q x.2 - Ck T q G x.1 x.2)) with hy
  set A := ∑ k, μk T q k with hA
  set B := ∑ τ ∈ range G, ∑ k, Ck T q G τ k with hB
  have hstep : q * (∑ x ∈ range G ×ˢ univ, exp (y x) - B) ≤ G * E := by
    have : ∀ τ, q * ∑ k, (exp (y (τ, k)) - Ck T q G τ k) ≤ E := by
      intro τ
      rw [hEk, mul_sum]
      apply sum_le_sum; intro k _
      exact point_exp hq0.le hq1.le T G τ hG hγ k
    calc q * (∑ x ∈ range G ×ˢ univ, exp (y x) - B)
        = ∑ τ ∈ range G, q * ∑ k, (exp (y (τ, k)) - Ck T q G τ k) := by
          rw [sum_product, hB, ← sum_sub_distrib, mul_sum]
          apply sum_congr rfl; intro τ _
          rw [sum_sub_distrib]
      _ ≤ ∑ _τ ∈ range G, E := sum_le_sum (fun τ _ => this τ)
      _ = G * E := by simp
  have hcard : 0 < (range G ×ˢ (univ : Finset (Fin n))).card := by
    rw [card_product, card_range, card_univ, Fintype.card_fin]; positivity
  have hjen := card_mul_exp_avg_le (range G ×ˢ (univ : Finset (Fin n))) y hcard
  have hsumy : ∑ x ∈ range G ×ˢ (univ : Finset (Fin n)), y x =
      -(1023 / 1000 * (G * A - B)) := by
    rw [sum_product]
    simp only [hy]
    have h1 : ∀ τ ∈ range G, ∑ k, -(1023 / 1000 * (μk T q k - Ck T q G τ k)) =
        -(1023 / 1000) * A + 1023 / 1000 * ∑ k, Ck T q G τ k := by
      intro τ _
      rw [hA, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro k _; ring
    rw [sum_congr rfl h1, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, ← hB]
    ring
  have hcardr : ((range G ×ˢ (univ : Finset (Fin n))).card : ℝ) = G * n := by
    rw [card_product, card_range, card_univ, Fintype.card_fin]; push_cast; ring
  rw [hsumy, hcardr] at hjen
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  -- averaged quantities
  have hμ : A / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hnr]
    have := sum_μk_le hq0.le hq1.le M T hT4
    nlinarith
  have hC : B / (G * n) ≤ 1087 / 2500 := by
    have h1 := sum_Ck_le hq0.le hq1.le M T hT4 G
    have h2 := cross_numeric M hM
    rw [← hq, ← hGdef] at h2
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hGr] at h2
    nlinarith
  have hfin := final_numeric hμ hC
  have havg : -(1023 / 1000 * (G * A - B)) / (G * n) = -(1023 / 1000 * (A / n - B / (G * n))) := by
    field_simp
  rw [havg] at hjen
  -- conclude `E ≥ q n · 500/999`
  have hEbound : q * n * (500 / 999) ≤ E := by
    have h1 : q * (G * n * (exp (-(1023 / 1000 * (A / n - B / (G * n)))) - B / (G * n)))
        ≤ G * E := by
      have : G * n * (B / (G * n)) = B := by field_simp
      nlinarith
    have h2 : q * (G * n * (500 / 999)) ≤ G * E := by
      have : q * (G * n * (500 / 999)) ≤
          q * (G * n * (exp (-(1023 / 1000 * (A / n - B / (G * n)))) - B / (G * n))) := by
        apply mul_le_mul_of_nonneg_left _ hq0.le
        apply mul_le_mul_of_nonneg_left hfin (by positivity)
      linarith
    nlinarith
  obtain ⟨g, hg⟩ := exists_good_of_avg hq0 hq1 T _ hEbound
  refine ⟨g, ?_⟩
  have : q * n * (500 / 999) = n / ((999 / 250) * M) := by rw [hq]; field_simp; ring
  rw [this, div_le_iff₀ (by positivity)] at hg
  linarith

lemma viol_erase (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) :
    Viol T g = Viol (fun i j => (T i j).erase i) g := by
  ext ⟨a, b, k⟩
  simp only [Viol, mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨h1, ⟨?_, h2⟩, h3⟩, h4⟩
    rintro rfl; rcases h3 with h | h
    · exact lt_irrefl _ h
    · exact lt_irrefl _ (h1.trans h)
  · rintro ⟨⟨h1, ⟨_, h2⟩, h3⟩, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩

/-- The union bound, using that `i` itself never violates the pair `(i, j)`. -/
theorem union_core (M : ℕ) (hM : 2 ≤ M) (T : Fin n → Fin n → Finset (Fin n))
    (hT1 : ∀ i j, i < j → i ∈ T i j) (hT4 : ∀ i j, i < j → (T i j).card ≤ M) :
    ∃ g : Fin n → Bool, (n : ℝ) ≤ 4 * (M - 1 : ℕ) * (Good T g).card := by
  set m := M - 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; exact_mod_cast (by omega : 1 ≤ M - 1)
  set q : ℝ := 1 / (2 * m) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  have hT4' : ∀ i j, i < j → ((fun i j => (T i j).erase i) i j).card ≤ m := by
    intro i j hij
    simp only
    rw [card_erase_of_mem (hT1 i j hij)]
    have := hT4 i j hij; omega
  have hE := expected_viol hq0.le hq1.le m (fun i j => (T i j).erase i) hT4'
  have hR := sum_weight_card (n := n) q
  have hc : ∀ g : Fin n → Bool, ((Rset g).card : ℝ) - (Viol T g).card ≤ (Good T g).card := by
    intro g
    have hc1 : (Rset g).card ≤ (Good T g).card + ((Viol T g).image (fun p => p.2.2)).card :=
      card_le_card_sdiff_add_card
    have hc2 : ((Viol T g).image (fun p => p.2.2)).card ≤ (Viol T g).card := card_image_le
    have : ((Rset g).card : ℝ) ≤ (Good T g).card + (Viol T g).card := by exact_mod_cast (by omega)
    linarith
  have hEb : n * q - n * m * q ^ 2 ≤ ∑ g, wt q g * ((Good T g).card : ℝ) := by
    calc n * q - n * m * q ^ 2
        ≤ ∑ g, wt q g * (((Rset g).card : ℝ) - (Viol T g).card) := by
          simp only [mul_sub, sum_sub_distrib]
          have e1 : ∑ g : Fin n → Bool, wt q g * ((Rset g).card : ℝ) = n * q := hR
          have e2 : ∑ g : Fin n → Bool, wt q g * ((Viol T g).card : ℝ) ≤ n * m * q ^ 2 := by
            simp_rw [viol_erase T]; exact hE
          linarith
      _ ≤ ∑ g, wt q g * ((Good T g).card : ℝ) := by
          apply sum_le_sum; intro g _
          exact mul_le_mul_of_nonneg_left (hc g) (wt_nonneg hq0.le hq1.le g)
  obtain ⟨g, hg⟩ := exists_good_of_avg hq0 hq1 T _ hEb
  refine ⟨g, ?_⟩
  have : (n : ℝ) * q - n * m * q ^ 2 = n / (4 * m) := by rw [hq]; field_simp; ring
  rw [this, div_le_iff₀ (by positivity)] at hg
  linarith

/-- The sharpened combinatorial core of the reduction, with constant `999/250 = 3.996`. -/
theorem core_sharp (M : ℕ) (hM : 1 ≤ M) (T : Fin n → Fin n → Finset (Fin n))
    (hT1 : ∀ i j, i < j → i ∈ T i j)
    (hT3 : ∀ i c v, i < c → c < v → T i v ⊆ T i c ∪ T c v)
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) :
    ∃ R : Finset (Fin n), (∀ s ∈ R, ∀ t ∈ R, ∀ r ∈ R, s < t → r ∈ T s t → s ≤ r ∧ r ≤ t) ∧
      (n : ℝ) ≤ 999 / 250 * M * R.card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨∅, by simp, ?_⟩
    subst hn; simp
  rcases Nat.lt_or_ge M 1001 with hM' | hM'
  · rcases Nat.lt_or_ge M 2 with hM2 | hM2
    · -- `M = 1`: nobody violates anything, so everything is kept
      have hM1 : M = 1 := by omega
      refine ⟨Good T (fun _ => true), good_prop T hT3 _, ?_⟩
      have hV : Viol T (fun _ => true) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        rintro ⟨a, b, k⟩ hp
        simp only [Viol, mem_filter, mem_univ, true_and] at hp
        obtain ⟨⟨hab, hk, hout⟩, _⟩ := hp
        have h1 := hT1 a b hab
        have h2 := hT4 a b hab
        rw [hM1] at h2
        have : k = a := (card_le_one.mp h2) k hk a h1
        subst this
        rcases hout with h | h
        · exact lt_irrefl _ h
        · exact lt_irrefl _ (hab.trans h)
      have hG : Good T (fun _ => true) = univ := by
        simp [Good, Rset, hV]
      rw [hG, card_univ, Fintype.card_fin, hM1]
      have : (0 : ℝ) ≤ n := by positivity
      push_cast; linarith
    · obtain ⟨g, hg⟩ := union_core M hM2 T hT1 hT4
      refine ⟨Good T g, good_prop T hT3 g, ?_⟩
      have hMr : ((M - 1 : ℕ) : ℝ) = M - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ M)]; ring
      rw [hMr] at hg
      have hM1000 : (M : ℝ) ≤ 1000 := by exact_mod_cast (by omega : M ≤ 1000)
      have hc : (0 : ℝ) ≤ (Good T g).card := by positivity
      nlinarith
  · obtain ⟨g, hg⟩ := window_core M hM' T hT4 hn
    exact ⟨Good T g, good_prop T hT3 g, hg⟩

end SelfApproaching.Proof.ReductionSharp
