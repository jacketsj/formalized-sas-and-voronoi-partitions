import Mathlib

namespace SelfApproaching.Proof.ReductionCore

open Finset

variable {n : ℕ}

/-- Bernoulli weight of a single coordinate. -/
noncomputable def bw (q : ℝ) : Bool → ℝ := fun b => if b then q else 1 - q

lemma sum_weight_mul_prod (p : Bool → ℝ) (h : Fin n → Bool → ℝ) :
    ∑ g : Fin n → Bool, (∏ i, p (g i)) * ∏ i, h i (g i) = ∏ i, ∑ b, p b * h i b := by
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma sum_weight (q : ℝ) : ∑ g : Fin n → Bool, ∏ i, bw q (g i) = 1 := by
  have := sum_weight_mul_prod (n := n) (bw q) (fun _ _ => 1)
  simpa [bw] using this

lemma sum_weight_card (q : ℝ) :
    ∑ g : Fin n → Bool, (∏ i, bw q (g i)) * ((univ.filter fun i => g i = true).card : ℝ)
      = n * q := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  have key : ∀ i : Fin n, ∑ g : Fin n → Bool, (∏ c, bw q (g c)) * (if g i = true then (1:ℝ) else 0)
      = q := by
    intro i
    have := sum_weight_mul_prod (n := n) (bw q)
      (fun c b => if c = i then (if b = true then (1:ℝ) else 0) else 1)
    simp only [Fintype.prod_ite_eq'] at this
    rw [this]
    have h2 : ∀ c : Fin n, ∑ b, bw q b * (if c = i then (if b = true then (1:ℝ) else 0) else 1)
        = if c = i then q else 1 := by
      intro c
      by_cases hc : c = i <;> simp [hc, bw]
    simp_rw [h2]
    rw [Fintype.prod_ite_eq']
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  simp


/-- The event that `i < j` are consecutive in `g`, and `k` is also in `g`. -/
def Ev (g : Fin n → Bool) (i j k : Fin n) : Prop :=
  ∀ c, ((c = i ∨ c = j ∨ c = k) → g c = true) ∧ (i < c ∧ c < j → g c = false)

instance (g : Fin n → Bool) (i j k : Fin n) : Decidable (Ev g i j k) := by
  unfold Ev; infer_instance

/-- Factor of the indicator of `Ev`. -/
noncomputable def hfun (i j k c : Fin n) (b : Bool) : ℝ :=
  if ((c = i ∨ c = j ∨ c = k) → b = true) ∧ (i < c ∧ c < j → b = false) then 1 else 0

lemma ev_indicator (g : Fin n → Bool) (i j k : Fin n) :
    (if Ev g i j k then (1:ℝ) else 0) = ∏ c, hfun i j k c (g c) := by
  unfold hfun
  by_cases h : Ev g i j k
  · rw [if_pos h, Fintype.prod_boole]; exact (if_pos h).symm
  · rw [if_neg h, Fintype.prod_boole]; exact (if_neg h).symm

lemma sum_ev (q : ℝ) {i j k : Fin n} (hij : i < j) (hk : k < i ∨ j < k) :
    ∑ g : Fin n → Bool, (∏ c, bw q (g c)) * (if Ev g i j k then (1:ℝ) else 0)
      = q ^ 3 * (1 - q) ^ (j.val - i.val - 1) := by
  simp_rw [ev_indicator]
  rw [sum_weight_mul_prod]
  have h2 : ∀ c : Fin n, ∑ b, bw q b * hfun i j k c b
      = (if c ∈ ({i, j, k} : Finset (Fin n)) then q else 1) *
        (if c ∈ Ioo i j then 1 - q else 1) := by
    intro c
    have hne : ¬ (c ∈ ({i, j, k} : Finset (Fin n)) ∧ c ∈ Ioo i j) := by
      simp only [mem_insert, mem_singleton, mem_Ioo]
      rintro ⟨h | h | h, h1, h2⟩ <;> subst h
      · exact lt_irrefl _ h1
      · exact lt_irrefl _ h2
      · rcases hk with hk | hk
        · exact lt_asymm hk h1
        · exact lt_asymm hk h2
    by_cases h1 : c ∈ ({i, j, k} : Finset (Fin n))
    · have h1' : c ∉ Ioo i j := fun h => hne ⟨h1, h⟩
      simp only [mem_insert, mem_singleton] at h1
      simp only [mem_Ioo] at h1'
      simp [hfun, bw, h1, h1']
    · by_cases h3 : c ∈ Ioo i j
      · simp only [mem_insert, mem_singleton] at h1
        simp only [mem_Ioo] at h3
        simp [hfun, bw, h1, h3]
      · simp only [mem_insert, mem_singleton] at h1
        simp only [mem_Ioo] at h3
        simp [hfun, bw, h1, h3]
  simp_rw [h2]
  rw [prod_mul_distrib, Fintype.prod_ite_mem, Fintype.prod_ite_mem, prod_const, prod_const,
    Fin.card_Ioo]
  have hc : ({i, j, k} : Finset (Fin n)).card = 3 := by
    rw [card_eq_three]
    refine ⟨i, j, k, hij.ne, ?_, ?_, rfl⟩
    · rcases hk with hk | hk
      · exact hk.ne'
      · exact (hij.trans hk).ne
    · rcases hk with hk | hk
      · exact (hk.trans hij).ne'
      · exact hk.ne
  rw [hc]

lemma geom_bound {r : ℝ} (h0 : 0 ≤ r) (i : Fin n) :
    (1 - r) * ∑ j : Fin n, (if i < j then r ^ (j.val - i.val - 1) else 0) ≤ 1 := by
  rcases le_or_gt r 1 with hr | hr
  · rw [← sum_filter]
    have hinj : Set.InjOn (fun j : Fin n => j.val - i.val - 1) (univ.filter (fun j => i < j)) := by
      intro a ha b hb hab
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      simp only at hab
      ext
      have := Fin.lt_def.mp ha
      have := Fin.lt_def.mp hb
      omega
    rw [← sum_image (f := fun d => r ^ d) hinj]
    have hsub : (univ.filter (fun j => i < j)).image (fun j : Fin n => j.val - i.val - 1)
        ⊆ range n := by
      intro d hd
      simp only [mem_image] at hd
      obtain ⟨j, _, rfl⟩ := hd
      simp only [mem_range]
      omega
    calc (1 - r) * ∑ d ∈ (univ.filter (fun j => i < j)).image (fun j : Fin n => j.val - i.val - 1),
          r ^ d ≤ (1 - r) * ∑ d ∈ range n, r ^ d := by
          gcongr
      _ = 1 - r ^ n := mul_neg_geom_sum r n
      _ ≤ 1 := by linarith [pow_nonneg h0 n]
  · have : 0 ≤ ∑ j : Fin n, (if i < j then r ^ (j.val - i.val - 1) else 0) :=
      sum_nonneg (fun j _ => by split_ifs <;> positivity)
    nlinarith


/-- The violating triples `(i, j, k)` of the subset `g`: `i < j` are consecutive in `g`,
`k ∈ g` lies outside `[i, j]`, and `k ∈ T i j`. -/
def Viol (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) :
    Finset (Fin n × Fin n × Fin n) :=
  univ.filter fun p => (p.1 < p.2.1 ∧ p.2.2 ∈ T p.1 p.2.1 ∧ (p.2.2 < p.1 ∨ p.2.1 < p.2.2)) ∧
    Ev g p.1 p.2.1 p.2.2

lemma expected_viol {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ)
    (T : Fin n → Fin n → Finset (Fin n)) (hT4 : ∀ i j, i < j → (T i j).card ≤ M) :
    ∑ g : Fin n → Bool, (∏ c, bw q (g c)) * ((Viol T g).card : ℝ) ≤ n * M * q ^ 2 := by
  simp only [Viol, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [sum_comm]
  have key : ∀ p : Fin n × Fin n × Fin n,
      ∑ g : Fin n → Bool, (∏ c, bw q (g c)) *
        (if (p.1 < p.2.1 ∧ p.2.2 ∈ T p.1 p.2.1 ∧ (p.2.2 < p.1 ∨ p.2.1 < p.2.2)) ∧
          Ev g p.1 p.2.1 p.2.2 then (1:ℝ) else 0)
      = if p.1 < p.2.1 ∧ p.2.2 ∈ T p.1 p.2.1 ∧ (p.2.2 < p.1 ∨ p.2.1 < p.2.2) then
          q ^ 3 * (1 - q) ^ (p.2.1.val - p.1.val - 1) else 0 := by
    intro p
    by_cases h : p.1 < p.2.1 ∧ p.2.2 ∈ T p.1 p.2.1 ∧ (p.2.2 < p.1 ∨ p.2.1 < p.2.2)
    · simp only [h, true_and, if_true]
      exact sum_ev q h.1 h.2.2
    · simp [h]
  rw [sum_congr rfl (fun p _ => key p)]
  simp only [Fintype.sum_prod_type]
  have hgeom := fun i : Fin n => geom_bound (r := 1 - q) (by linarith) i
  calc ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (if i < j ∧ k ∈ T i j ∧ (k < i ∨ j < k) then q ^ 3 * (1 - q) ^ (j.val - i.val - 1) else 0)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
        (if i < j then (M : ℝ) * (q ^ 3 * (1 - q) ^ (j.val - i.val - 1)) else 0) := by
        gcongr with i _ j _
        split_ifs with hij
        · calc ∑ k : Fin n, (if i < j ∧ k ∈ T i j ∧ (k < i ∨ j < k) then
                q ^ 3 * (1 - q) ^ (j.val - i.val - 1) else 0)
              ≤ ∑ k : Fin n, (if k ∈ T i j then q ^ 3 * (1 - q) ^ (j.val - i.val - 1) else 0) := by
                gcongr with k _
                split_ifs with h1 h2 h2
                · exact le_rfl
                · exact absurd h1.2.1 h2
                · have : 0 ≤ 1 - q := by linarith
                  positivity
                · exact le_rfl
            _ = (T i j).card * (q ^ 3 * (1 - q) ^ (j.val - i.val - 1)) := by
                rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul]
            _ ≤ M * (q ^ 3 * (1 - q) ^ (j.val - i.val - 1)) := by
                have : 0 ≤ 1 - q := by linarith
                gcongr
                exact_mod_cast hT4 i j hij
        · apply le_of_eq
          apply sum_eq_zero
          intro k _
          rw [if_neg]
          exact fun h => hij h.1
    _ = ∑ i : Fin n, (M : ℝ) * q ^ 2 *
          (q * ∑ j : Fin n, (if i < j then (1 - q) ^ (j.val - i.val - 1) else 0)) := by
        congr 1
        ext i
        rw [mul_sum, mul_sum]
        congr 1
        ext j
        split_ifs <;> ring
    _ ≤ ∑ _i : Fin n, (M : ℝ) * q ^ 2 * 1 := by
        gcongr with i _
        have := hgeom i
        simp only [sub_sub_cancel] at this
        exact this
    _ = n * M * q ^ 2 := by simp; ring


/-- The subset selected by `g`. -/
def Rset (g : Fin n → Bool) : Finset (Fin n) := univ.filter fun i => g i = true

/-- The subset selected by `g`, with every violator deleted. -/
def Good (T : Fin n → Fin n → Finset (Fin n)) (g : Fin n → Bool) : Finset (Fin n) :=
  Rset g \ (Viol T g).image (fun p => p.2.2)

lemma good_prop (T : Fin n → Fin n → Finset (Fin n))
    (hT3 : ∀ i c v, i < c → c < v → T i v ⊆ T i c ∪ T c v) (g : Fin n → Bool) :
    ∀ s ∈ Good T g, ∀ t ∈ Good T g, ∀ r ∈ Good T g, s < t → r ∈ T s t → s ≤ r ∧ r ≤ t := by
  have claim : ∀ d : ℕ, ∀ u v : Fin n, v.val - u.val = d → u < v → g u = true → g v = true →
      ∀ w, g w = true → w ∉ (Viol T g).image (fun p => p.2.2) → w ∈ T u v → u ≤ w ∧ w ≤ v := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro u v hd huv hu hv w hw hdel hwT
      by_cases hc : ∃ c, u < c ∧ c < v ∧ g c = true
      · obtain ⟨c, h1, h2, hgc⟩ := hc
        have h1' := Fin.lt_def.mp h1
        have h2' := Fin.lt_def.mp h2
        rcases mem_union.mp (hT3 u c v h1 h2 hwT) with h | h
        · have := ih (c.val - u.val) (by omega) u c rfl h1 hu hgc w hw hdel h
          exact ⟨this.1, this.2.trans h2.le⟩
        · have := ih (v.val - c.val) (by omega) c v rfl h2 hgc hv w hw hdel h
          exact ⟨h1.le.trans this.1, this.2⟩
      · push Not at hc
        by_contra hcon
        apply hdel
        rw [mem_image]
        refine ⟨(u, v, w), ?_, rfl⟩
        simp only [Viol, mem_filter, mem_univ, true_and]
        refine ⟨⟨huv, hwT, ?_⟩, ?_⟩
        · by_contra h
          push Not at h
          exact hcon h
        · intro c
          refine ⟨?_, ?_⟩
          · rintro (rfl | rfl | rfl) <;> assumption
          · rintro ⟨h1, h2⟩
            simpa using hc c h1 h2
  intro s hs t ht r hr hst hrT
  simp only [Good, Rset, mem_sdiff, mem_filter, mem_univ, true_and] at hs ht hr
  exact claim _ s t rfl hst hs.1 ht.1 r hr.1 hr.2 hrT

/-- The combinatorial core of the reduction. -/
theorem core (M : ℕ) (hM : 1 ≤ M) (T : Fin n → Fin n → Finset (Fin n))
    (hT3 : ∀ i c v, i < c → c < v → T i v ⊆ T i c ∪ T c v)
    (hT4 : ∀ i j, i < j → (T i j).card ≤ M) :
    ∃ R : Finset (Fin n), (∀ s ∈ R, ∀ t ∈ R, ∀ r ∈ R, s < t → r ∈ T s t → s ≤ r ∧ r ≤ t) ∧
      (n : ℝ) ≤ 4 * M * R.card := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set q : ℝ := 1 / (2 * M) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    rw [hq]; gcongr; linarith
  have hw : ∀ g : Fin n → Bool, 0 < ∏ c, bw q (g c) := by
    intro g
    apply prod_pos
    intro c _
    unfold bw
    split_ifs <;> linarith
  have hE := expected_viol hq0.le (by linarith) M T hT4
  have hR := sum_weight_card (n := n) q
  have h1 := sum_weight (n := n) q
  have hsum : ∑ g : Fin n → Bool, (∏ c, bw q (g c)) * (n / (4 * M))
      ≤ ∑ g : Fin n → Bool, (∏ c, bw q (g c)) *
        (((Rset g).card : ℝ) - (Viol T g).card) := by
    rw [← sum_mul, h1]
    simp only [mul_sub, sum_sub_distrib]
    rw [show (∑ g : Fin n → Bool, (∏ c, bw q (g c)) * ((Rset g).card : ℝ)) = n * q from hR]
    have : (n : ℝ) / (4 * M) = n * q - n * M * q ^ 2 := by
      rw [hq]; field_simp; ring
    linarith
  obtain ⟨g, _, hg⟩ := exists_le_of_sum_le univ_nonempty hsum
  have hg' : (n : ℝ) / (4 * M) ≤ ((Rset g).card : ℝ) - (Viol T g).card :=
    le_of_mul_le_mul_left hg (hw g)
  refine ⟨Good T g, good_prop T hT3 g, ?_⟩
  have hc1 : (Rset g).card ≤ (Good T g).card + ((Viol T g).image (fun p => p.2.2)).card :=
    card_le_card_sdiff_add_card
  have hc2 : ((Viol T g).image (fun p => p.2.2)).card ≤ (Viol T g).card := card_image_le
  have hc : ((Rset g).card : ℝ) - (Viol T g).card ≤ (Good T g).card := by
    have : (Rset g).card ≤ (Good T g).card + (Viol T g).card := by omega
    have : ((Rset g).card : ℝ) ≤ (Good T g).card + (Viol T g).card := by exact_mod_cast this
    linarith
  have := hg'.trans hc
  rw [div_le_iff₀ (by positivity)] at this
  linarith

end SelfApproaching.Proof.ReductionCore
