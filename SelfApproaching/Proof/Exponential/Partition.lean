import SelfApproaching.Definitions

/-!
# Navigability with bounded out-degree implies a balanced Voronoi partition

This is Lemma 11 of the paper (Appendix D), for an arbitrary "distance" `D : α → α → ℝ`.
The key observation is that `k ∈ voronoiSide D x a b` iff `(D (x k) (x a), a)` is
lexicographically smaller than `(D (x k) (x b), b)`, which is a strict total order on sites.
-/

namespace SelfApproaching.Proof.Exponential

variable {α : Type*} {D : α → α → ℝ} {n : ℕ} {x : Fin n → α} {a b c k : Fin n}

lemma mem_voronoiSide :
    k ∈ voronoiSide D x a b ↔
      D (x k) (x a) < D (x k) (x b) ∨ (D (x k) (x a) = D (x k) (x b) ∧ a < b) := by
  simp [voronoiSide]

lemma voronoiSide_total (hab : a ≠ b) :
    k ∈ voronoiSide D x a b ∨ k ∈ voronoiSide D x b a := by
  simp only [mem_voronoiSide]
  rcases lt_trichotomy (D (x k) (x a)) (D (x k) (x b)) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_or_gt_of_ne hab with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

lemma voronoiSide_not_both (h : k ∈ voronoiSide D x a b) : k ∉ voronoiSide D x b a := by
  simp only [mem_voronoiSide] at *
  rintro (g | ⟨g, g'⟩) <;> rcases h with h | ⟨h, h'⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h' g'

lemma voronoiSide_trans (h1 : k ∈ voronoiSide D x a b) (h2 : k ∈ voronoiSide D x b c) :
    k ∈ voronoiSide D x a c := by
  simp only [mem_voronoiSide] at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

lemma voronoiSide_card_add (hab : a ≠ b) :
    (voronoiSide D x a b).card + (voronoiSide D x b a).card = n := by
  rw [← Finset.card_union_of_disjoint]
  · have : voronoiSide D x a b ∪ voronoiSide D x b a = Finset.univ := by
      ext k
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      exact voronoiSide_total hab
    rw [this, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.disjoint_left]
    intro k h1 h2
    exact voronoiSide_not_both h1 h2

lemma voronoiSide_self_eq_empty : voronoiSide D x a a = ∅ := by
  ext k
  simp [mem_voronoiSide]

/-- If every site `i` has another site `y` that a `β` fraction of the points prefer to `i`,
and `3β ≤ 1`, then there is a `β`-balanced Voronoi partition. -/
theorem balanced_of_forall_exists (x : Fin n → α) (β : ℝ) (hβ : 3 * β ≤ 1) (hn : 0 < n)
    (H : ∀ i, ∃ y, y ≠ i ∧ β * n ≤ (voronoiSide D x y i).card) :
    HasBalancedVoronoiPartition D x β := by
  by_contra hno
  have hnb : ∀ a b : Fin n, a ≠ b → β * n ≤ (voronoiSide D x a b).card →
      ((voronoiSide D x b a).card : ℝ) < β * n := by
    intro a b hab h1
    by_contra h2
    push Not at h2
    exact hno ⟨a, b, hab, h1, h2⟩
  choose f hf1 hf2 using H
  have hsmall : ∀ i, ((voronoiSide D x i (f i)).card : ℝ) < β * n :=
    fun i => hnb _ _ (hf1 i) (hf2 i)
  -- a periodic point of `f`
  obtain ⟨c, p, hp, hc⟩ : ∃ c p, 0 < p ∧ f^[p] c = c := by
    obtain ⟨i, j, hij, heq⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] (⟨0, hn⟩ : Fin n))
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨f^[i] ⟨0, hn⟩, j - i, Nat.sub_pos_of_lt h, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq.symm
    · refine ⟨f^[j] ⟨0, hn⟩, i - j, Nat.sub_pos_of_lt h, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      exact heq
  have key : ∀ k, 1 ≤ k → f^[k] c ≠ c ∧
      ((voronoiSide D x c (f^[k] c)).card : ℝ) < β * n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨hf1 c, hsmall c⟩
    | succ k _ ih =>
      rw [Function.iterate_succ_apply']
      set b := f^[k] c
      obtain ⟨hbc, hb⟩ := ih
      have hsum : ((voronoiSide D x b c).card : ℝ) + (voronoiSide D x c b).card = n := by
        exact_mod_cast voronoiSide_card_add hbc
      have hfb := hsmall b
      by_cases hfbc : f b = c
      · exfalso
        rw [hfbc] at hfb
        have : 0 ≤ (1 - 2 * β) * (n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
        nlinarith
      · refine ⟨hfbc, hnb (f b) c hfbc ?_⟩
        have hsub : voronoiSide D x b c ⊆
            voronoiSide D x b (f b) ∪ voronoiSide D x (f b) c := by
          intro k hk
          rw [Finset.mem_union]
          by_cases h : k ∈ voronoiSide D x b (f b)
          · exact Or.inl h
          · right
            rcases voronoiSide_total (k := k) (x := x) (D := D) (hf1 b).symm with h' | h'
            · exact absurd h' h
            · exact voronoiSide_trans h' hk
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (voronoiSide D x b (f b)) (voronoiSide D x (f b) c)
        have h3 : ((voronoiSide D x b c).card : ℝ) ≤
            (voronoiSide D x b (f b)).card + (voronoiSide D x (f b) c).card := by
          exact_mod_cast h1.trans h2
        have : 0 ≤ (1 - 3 * β) * (n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
        nlinarith
  exact (key p hp).1 hc

/-- Lemma 11: a navigable graph with out-degree at most `M` (given by out-neighbour sets `N`)
yields a `1/(2M)`-balanced Voronoi partition, provided `M ≥ 3/2` (in the paper `M ≥ 2`). -/
theorem balanced_of_navigable (x : Fin n → α) (hn : 2 ≤ n) (M : ℝ) (hM : 3 / 2 ≤ M)
    (N : Fin n → Finset (Fin n)) (hN : ∀ i, ((N i).card : ℝ) ≤ M)
    (hnav : ∀ i q, q ≠ i → ∃ y ∈ N i, q ∈ voronoiSide D x y i) :
    HasBalancedVoronoiPartition D x (1 / (2 * M)) := by
  have hM0 : 0 < M := by linarith
  apply balanced_of_forall_exists x _ _ (by omega)
  · intro i
    by_contra h
    push Not at h
    have hlt : ∀ y ∈ N i, ((voronoiSide D x y i).card : ℝ) < 1 / (2 * M) * n := by
      intro y _
      by_cases hy : y = i
      · subst hy
        rw [voronoiSide_self_eq_empty, Finset.card_empty, Nat.cast_zero]
        have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        positivity
      · exact h y hy
    obtain ⟨q, hq⟩ : ∃ q : Fin n, q ≠ i := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      exact exists_ne i
    have hne : (N i).Nonempty := by
      obtain ⟨y, hy, _⟩ := hnav i q hq
      exact ⟨y, hy⟩
    have hsub : Finset.univ.erase i ⊆ (N i).biUnion (fun y => voronoiSide D x y i) := by
      intro q hq
      rw [Finset.mem_erase] at hq
      obtain ⟨y, hy, hqy⟩ := hnav i q hq.1
      exact Finset.mem_biUnion.mpr ⟨y, hy, hqy⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ((n - 1 : ℕ) : ℝ) ≤ ∑ y ∈ N i, ((voronoiSide D x y i).card : ℝ) := by
      exact_mod_cast h1
    have h3 := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : ((N i).card : ℝ) * (1 / (2 * M) * n) ≤ M * (1 / (2 * M) * n) :=
      mul_le_mul_of_nonneg_right (hN i) (by positivity)
    have h5 : M * (1 / (2 * M) * n) = n / 2 := by field_simp
    rw [Nat.cast_sub (by omega), Nat.cast_one] at h2
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith

end SelfApproaching.Proof.Exponential
