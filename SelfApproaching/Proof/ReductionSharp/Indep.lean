import SelfApproaching.Proof.Reduction.Core

/-!
# Independence for the Bernoulli product weight

Functions of the random subset `g : Fin n → Bool` that depend on disjoint sets of coordinates
are independent under the product weight `∏ i, bw q (g i)`.
-/

namespace SelfApproaching.Proof.ReductionSharp

open Finset SelfApproaching.Proof.ReductionCore

variable {n : ℕ}

/-- The Bernoulli product weight of a subset. -/
noncomputable def wt (q : ℝ) (g : Fin n → Bool) : ℝ := ∏ i, bw q (g i)

lemma sum_wt (q : ℝ) : ∑ g : Fin n → Bool, wt q g = 1 := sum_weight q

lemma sum_wt_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) :
    ∑ g : ι → Bool, ∏ i, bw q (g i) = 1 := by
  rw [← Fintype.prod_sum (fun _ b => bw q b)]
  simp [bw]

/-- Two functions depending on complementary coordinate sets are independent. -/
lemma indep_two (q : ℝ) (A : Finset (Fin n)) (F H : (Fin n → Bool) → ℝ)
    (hF : ∀ g g' : Fin n → Bool, (∀ i ∈ A, g i = g' i) → F g = F g')
    (hH : ∀ g g' : Fin n → Bool, (∀ i, i ∉ A → g i = g' i) → H g = H g') :
    ∑ g, wt q g * (F g * H g) = (∑ g, wt q g * F g) * (∑ g, wt q g * H g) := by
  classical
  set e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ A) (fun _ => Bool) with he
  have hsymm : ∀ (g1 : {i // i ∈ A} → Bool) (g2 : {i // i ∉ A} → Bool) (i : Fin n),
      e.symm (g1, g2) i = if h : i ∈ A then g1 ⟨i, h⟩ else g2 ⟨i, h⟩ := by
    intro g1 g2 i; rfl
  have hw : ∀ g1 g2, wt q (e.symm (g1, g2)) =
      (∏ i : {i // i ∈ A}, bw q (g1 i)) * ∏ i : {i // i ∉ A}, bw q (g2 i) := by
    intro g1 g2
    unfold wt
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ A)]
    congr 1
    · exact Finset.prod_congr (by congr; exact Subsingleton.elim _ _) (fun i _ => by rw [hsymm, dif_pos i.2])
    · exact Finset.prod_congr (by congr) (fun i _ => by rw [hsymm, dif_neg i.2])
  set F1 : ({i // i ∈ A} → Bool) → ℝ := fun g1 => F (e.symm (g1, fun _ => false))
  set H2 : ({i // i ∉ A} → Bool) → ℝ := fun g2 => H (e.symm (fun _ => false, g2))
  have hF1 : ∀ g1 g2, F (e.symm (g1, g2)) = F1 g1 := by
    intro g1 g2; apply hF; intro i hi; rw [hsymm, hsymm, dif_pos hi, dif_pos hi]
  have hH2 : ∀ g1 g2, H (e.symm (g1, g2)) = H2 g2 := by
    intro g1 g2; apply hH; intro i hi; rw [hsymm, hsymm, dif_neg hi, dif_neg hi]
  have hsum : ∀ Φ : (Fin n → Bool) → ℝ, ∑ g, Φ g = ∑ g1, ∑ g2, Φ (e.symm (g1, g2)) := by
    intro Φ
    rw [← Fintype.sum_prod_type', ← e.symm.sum_comp]
  have h1 := sum_wt_subtype (ι := {i // i ∈ A}) q
  have h2 := sum_wt_subtype (ι := {i // i ∉ A}) q
  rw [hsum, hsum, hsum]
  simp_rw [hw, hF1, hH2]
  have eF : ∑ g1 : {i // i ∈ A} → Bool, ∑ g2 : {i // i ∉ A} → Bool, (∏ i : {i // i ∈ A}, bw q (g1 i)) * (∏ i : {i // i ∉ A}, bw q (g2 i)) *
      F1 g1 = ∑ g1, (∏ i : {i // i ∈ A}, bw q (g1 i)) * F1 g1 := by
    apply Fintype.sum_congr; intro g1
    rw [← Finset.sum_mul, ← Finset.mul_sum, h2]; ring
  have eH : ∑ g1 : {i // i ∈ A} → Bool, ∑ g2 : {i // i ∉ A} → Bool, (∏ i : {i // i ∈ A}, bw q (g1 i)) * (∏ i : {i // i ∉ A}, bw q (g2 i)) *
      H2 g2 = ∑ g2, (∏ i : {i // i ∉ A}, bw q (g2 i)) * H2 g2 := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr; intro g2
    rw [← Finset.sum_mul, ← Finset.sum_mul, h1]; ring
  rw [eF, eH, Finset.sum_mul_sum]
  apply Fintype.sum_congr; intro g1
  apply Fintype.sum_congr; intro g2
  ring

/-- Functions depending on pairwise disjoint coordinate sets are independent. -/
lemma indep_prod (q : ℝ) {κ : Type*} [DecidableEq κ] (s : Finset κ) (B : κ → Finset (Fin n))
    (hB : (s : Set κ).PairwiseDisjoint B) (f : κ → (Fin n → Bool) → ℝ)
    (hf : ∀ j ∈ s, ∀ g g' : Fin n → Bool, (∀ i ∈ B j, g i = g' i) → f j g = f j g') :
    ∑ g, wt q g * ∏ j ∈ s, f j g = ∏ j ∈ s, ∑ g, wt q g * f j g := by
  induction s using Finset.induction_on with
  | empty => simp [sum_wt]
  | insert j s hj ih =>
    rw [prod_insert hj]
    have hB' : (s : Set κ).PairwiseDisjoint B := hB.subset (by simp)
    have hf' : ∀ j ∈ s, ∀ g g' : Fin n → Bool, (∀ i ∈ B j, g i = g' i) → f j g = f j g' :=
      fun j' hj' => hf j' (mem_insert_of_mem hj')
    simp_rw [prod_insert hj]
    rw [indep_two q (B j) (f j) (fun g => ∏ j ∈ s, f j g) (hf j (mem_insert_self j s)), ih hB' hf']
    intro g g' hgg'
    apply prod_congr rfl
    intro j' hj'
    apply hf' j' hj'
    intro i hi
    apply hgg'
    intro hiB
    have hne : j ≠ j' := fun h => hj (h ▸ hj')
    have := hB (mem_insert_self j s) (mem_insert_of_mem hj') hne
    exact Finset.disjoint_left.mp this hiB hi

/-- The probability that a fixed coordinate is selected. -/
lemma sum_wt_coord (q : ℝ) (k : Fin n) :
    ∑ g, wt q g * (if g k = true then (1 : ℝ) else 0) = q := by
  unfold wt
  have := sum_weight_mul_prod (n := n) (bw q)
    (fun c b => if c = k then (if b = true then (1:ℝ) else 0) else 1)
  simp only [Fintype.prod_ite_eq'] at this
  rw [this]
  have h2 : ∀ c : Fin n, ∑ b, bw q b * (if c = k then (if b = true then (1:ℝ) else 0) else 1)
      = if c = k then q else 1 := by
    intro c
    by_cases hc : c = k <;> simp [hc, bw]
  simp_rw [h2]
  rw [Fintype.prod_ite_eq']

/-- `a < b` are both selected and consecutive in `g`. -/
def Ev2 (g : Fin n → Bool) (a b : Fin n) : Prop :=
  g a = true ∧ g b = true ∧ ∀ c, a < c → c < b → g c = false

instance (g : Fin n → Bool) (a b : Fin n) : Decidable (Ev2 g a b) := by
  unfold Ev2; infer_instance

/-- Factor of the indicator of `Ev2`. -/
noncomputable def hfun2 (a b c : Fin n) (x : Bool) : ℝ :=
  if ((c = a ∨ c = b) → x = true) ∧ (a < c ∧ c < b → x = false) then 1 else 0

lemma sum_ev2 (q : ℝ) {a b : Fin n} (hab : a < b) :
    ∑ g, wt q g * (if Ev2 g a b then (1:ℝ) else 0) = q ^ 2 * (1 - q) ^ (b.val - a.val - 1) := by
  have hind : ∀ g : Fin n → Bool, (if Ev2 g a b then (1:ℝ) else 0) = ∏ c, hfun2 a b c (g c) := by
    intro g
    unfold hfun2
    rw [Fintype.prod_boole]
    congr 1
    apply propext
    unfold Ev2
    constructor
    · rintro ⟨ha, hb, hc⟩ c
      refine ⟨?_, fun h => hc c h.1 h.2⟩
      rintro (rfl | rfl) <;> assumption
    · intro h
      exact ⟨(h a).1 (Or.inl rfl), (h b).1 (Or.inr rfl), fun c h1 h2 => (h c).2 ⟨h1, h2⟩⟩
  unfold wt
  simp_rw [hind]
  rw [sum_weight_mul_prod]
  have h2 : ∀ c : Fin n, ∑ x, bw q x * hfun2 a b c x
      = (if c ∈ ({a, b} : Finset (Fin n)) then q else 1) *
        (if c ∈ Ioo a b then 1 - q else 1) := by
    intro c
    have hne : ¬ (c ∈ ({a, b} : Finset (Fin n)) ∧ c ∈ Ioo a b) := by
      simp only [mem_insert, mem_singleton, mem_Ioo]
      rintro ⟨h | h, h1, h2⟩ <;> subst h
      · exact lt_irrefl _ h1
      · exact lt_irrefl _ h2
    by_cases h1 : c ∈ ({a, b} : Finset (Fin n))
    · have h1' : c ∉ Ioo a b := fun h => hne ⟨h1, h⟩
      simp only [mem_insert, mem_singleton] at h1
      simp only [mem_Ioo] at h1'
      simp [hfun2, bw, h1, h1']
    · by_cases h3 : c ∈ Ioo a b
      · simp only [mem_insert, mem_singleton] at h1
        simp only [mem_Ioo] at h3
        simp [hfun2, bw, h1, h3]
      · simp only [mem_insert, mem_singleton] at h1
        simp only [mem_Ioo] at h3
        simp [hfun2, bw, h1, h3]
  simp_rw [h2]
  rw [prod_mul_distrib, Fintype.prod_ite_mem, Fintype.prod_ite_mem, prod_const, prod_const,
    Fin.card_Ioo]
  have hc : ({a, b} : Finset (Fin n)).card = 2 := card_pair hab.ne
  rw [hc]

end SelfApproaching.Proof.ReductionSharp
