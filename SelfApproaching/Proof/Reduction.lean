import SelfApproaching.Definitions
import SelfApproaching.Proof.Reduction.Core

namespace SelfApproaching.Proof

open Real Finset

section Helpers

variable {P : Type*} [MetricSpace P]

/-- A sequence is an SAS as soon as the SAS condition holds for base points outside the
interval of the pair (the remaining case follows by symmetry of the distance). -/
lemma isSAS_of_outside {m : ℕ} (f : Fin m → P) (hf : Function.Injective f)
    (hQ : ∀ s t r : Fin m, s ≤ t → (r < s ∨ t ≤ r) → dist (f r) (f t) ≤ dist (f r) (f s)) :
    IsSAS dist f := by
  refine ⟨hf, fun s t r hst hrs => ?_⟩
  rcases lt_or_gt_of_ne hrs with h | h
  · exact hQ s t r hst.le (Or.inl h)
  · by_cases htr : t ≤ r
    · exact hQ s t r hst.le (Or.inr htr)
    · push Not at htr
      have hs := Fin.lt_def.mp h
      have ht := Fin.lt_def.mp htr
      let r1 : Fin m := ⟨r.val + 1, by omega⟩
      let r0 : Fin m := ⟨r.val - 1, by omega⟩
      have a1 : dist (f r) (f t) ≤ dist (f r) (f r1) :=
        hQ r1 t r (Fin.le_def.mpr (by simp only [r1]; omega))
          (Or.inl (Fin.lt_def.mpr (by simp only [r1]; omega)))
      have a2 : dist (f r) (f r0) ≤ dist (f r) (f s) :=
        hQ s r0 r (Fin.le_def.mpr (by simp only [r0]; omega))
          (Or.inr (Fin.le_def.mpr (by simp only [r0]; omega)))
      have a3 : dist (f r1) (f r) ≤ dist (f r1) (f r0) :=
        hQ r0 r r1 (Fin.le_def.mpr (by simp only [r0]; omega))
          (Or.inr (Fin.le_def.mpr (by simp only [r1]; omega)))
      have a4 : dist (f r0) (f r1) ≤ dist (f r0) (f r) :=
        hQ r r1 r0 (Fin.le_def.mpr (by simp only [r1]; omega))
          (Or.inl (Fin.lt_def.mpr (by simp only [r0]; omega)))
      rw [dist_comm (f r1) (f r), dist_comm (f r1) (f r0)] at a3
      rw [dist_comm (f r0) (f r)] at a4
      linarith

variable {n : ℕ} (x : Fin n → P)

lemma mem_vs {a b k : Fin n} :
    k ∈ voronoiSide dist x a b ↔
      dist (x k) (x a) < dist (x k) (x b) ∨ (dist (x k) (x a) = dist (x k) (x b) ∧ a < b) := by
  simp [voronoiSide]

lemma vs_trans {a b c k : Fin n} (h1 : k ∈ voronoiSide dist x a b)
    (h2 : k ∈ voronoiSide dist x b c) : k ∈ voronoiSide dist x a c := by
  rw [mem_vs] at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

lemma vs_compl {a b k : Fin n} (hab : a ≠ b) :
    k ∈ voronoiSide dist x b a ↔ k ∉ voronoiSide dist x a b := by
  rw [mem_vs, mem_vs]
  constructor
  · rintro (h | ⟨h, h'⟩) (h2 | ⟨h2, h2'⟩)
    · linarith
    · linarith
    · linarith
    · exact lt_asymm h' h2'
  · intro h
    push Not at h
    rcases h.1.lt_or_eq with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      rcases lt_or_gt_of_ne hab with h3 | h3
      · exact absurd h3 (not_lt.mpr (h.2 h1.symm))
      · exact h3

lemma le_of_not_mem_vs {a b k : Fin n} (h : k ∉ voronoiSide dist x a b) :
    dist (x k) (x b) ≤ dist (x k) (x a) := by
  rw [mem_vs] at h
  push Not at h
  exact h.1

lemma card_vs_add {a b : Fin n} (hab : a ≠ b) :
    (voronoiSide dist x a b).card + (voronoiSide dist x b a).card = n := by
  have : voronoiSide dist x b a = (voronoiSide dist x a b)ᶜ := by
    ext k
    rw [vs_compl x hab, mem_compl]
  rw [this, card_add_card_compl, Fintype.card_fin]

lemma self_mem_vs (hx : Function.Injective x) {a b : Fin n} (hab : a ≠ b) :
    a ∈ voronoiSide dist x a b := by
  rw [mem_vs, dist_self]
  exact Or.inl (dist_pos.mpr (hx.ne hab))

end Helpers

theorem balanced_of_sas_bound {P : Type*} [MetricSpace P] (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → P) (hx : Function.Injective x) (L : ℕ)
    (hL : ∀ (ℓ : ℕ) (y : Fin ℓ → P), IsSAS dist y → (∀ i, y i ∈ Set.range x) → ℓ ≤ L) :
    HasBalancedVoronoiPartition dist x (1 / (4 * L)) := by
  set S := voronoiSide dist x with hS
  -- `L ≥ 1`, since a single point is an SAS.
  have hL1 : 1 ≤ L := by
    refine hL 1 (fun _ => x ⟨0, by omega⟩) ⟨fun i j _ => Subsingleton.elim i j, ?_⟩
      (fun _ => ⟨_, rfl⟩)
    intro i j _ hij
    exact absurd (Subsingleton.elim i j) hij.ne
  -- A pair maximizing the smaller side.
  have hne : (univ.offDiag : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := exists_max_image univ.offDiag
    (fun p : Fin n × Fin n => min (S p.1 p.2).card (S p.2 p.1).card) hne
  simp only [mem_offDiag, mem_univ, true_and] at hab
  set M := min (S a b).card (S b a).card with hMdef
  have hbound : ∀ c d : Fin n, c ≠ d → min (S c d).card (S d c).card ≤ M := by
    intro c d hcd
    exact hmax (c, d) (by simp [hcd])
  have hM1 : 1 ≤ M := by
    have h1 : 0 < (S a b).card := card_pos.mpr ⟨a, self_mem_vs x hx hab⟩
    have h2 : 0 < (S b a).card := card_pos.mpr ⟨b, self_mem_vs x hx (Ne.symm hab)⟩
    omega
  -- Main claim: `n ≤ 4 L M`.
  have hmain : n ≤ 4 * L * M := by
    by_cases h3 : n ≤ 3 * M
    · nlinarith
    push Not at h3
    -- the tournament
    let arc : Fin n → Fin n → Prop := fun c d => c ≠ d ∧ (S c d).card ≤ M
    have arc_total : ∀ c d, c ≠ d → arc c d ∨ arc d c := by
      intro c d hcd
      rcases le_total (S c d).card (S d c).card with h | h
      · exact Or.inl ⟨hcd, by have := hbound c d hcd; rw [min_eq_left h] at this; exact this⟩
      · exact Or.inr ⟨hcd.symm, by have := hbound c d hcd; rw [min_eq_right h] at this; exact this⟩
    have arc_anti : ∀ c d, arc c d → ¬ arc d c := by
      intro c d h1 h2
      have : (S c d).card + (S d c).card = n := card_vs_add x h1.1
      have := h1.2
      have := h2.2
      omega
    have arc_trans : ∀ c d e, arc c d → arc d e → c ≠ e → arc c e := by
      intro c d e h1 h2 hce
      by_contra hcon
      have h3' : arc e c := (arc_total c e hce).resolve_left hcon
      have hcov : (univ : Finset (Fin n)) ⊆ S c d ∪ S d e ∪ S e c := by
        intro k _
        by_contra hk
        simp only [mem_union, not_or] at hk
        have k1 : k ∈ S d c := (vs_compl x h1.1).mpr hk.1.1
        have k2 : k ∈ S e d := (vs_compl x h2.1).mpr hk.1.2
        exact hk.2 (vs_trans x k2 k1)
      have := card_le_card hcov
      have := card_union_le (S c d ∪ S d e) (S e c)
      have := card_union_le (S c d) (S d e)
      have := h1.2
      have := h2.2
      have := h3'.2
      simp only [card_univ, Fintype.card_fin] at *
      omega
    classical
    let rank : Fin n → ℕ := fun c => (univ.filter fun d => arc d c).card
    have rank_lt : ∀ c d, arc c d → rank c < rank d := by
      intro c d hcd
      apply card_lt_card
      rw [ssubset_iff_of_subset]
      · exact ⟨c, by simp [hcd], by simp [arc]⟩
      · intro e he
        simp only [mem_filter, mem_univ, true_and] at he ⊢
        refine arc_trans e c d he hcd ?_
        rintro rfl
        exact arc_anti _ _ he hcd
    have rank_lt_n : ∀ c, rank c < n := by
      intro c
      have : (univ.filter fun d => arc d c).card < (univ : Finset (Fin n)).card := by
        apply card_lt_card
        exact filter_ssubset.mpr ⟨c, mem_univ _, by simp [arc]⟩
      simpa using this
    let rk : Fin n → Fin n := fun c => ⟨rank c, rank_lt_n c⟩
    have rk_inj : Function.Injective rk := by
      intro c d h
      by_contra hcd
      have h' : rank c = rank d := congrArg Fin.val h
      rcases arc_total c d hcd with h1 | h1
      · exact absurd h' (rank_lt c d h1).ne
      · exact absurd h' (rank_lt d c h1).ne'
    let e := Equiv.ofBijective rk (Finite.injective_iff_bijective.mp rk_inj)
    let y := e.symm
    have hy : ∀ i j, i < j → arc (y i) (y j) := by
      intro i j hij
      have hne : y i ≠ y j := fun h => hij.ne (y.injective h)
      refine (arc_total _ _ hne).resolve_right fun h => ?_
      have := rank_lt _ _ h
      have hi : rk (y i) = i := e.apply_symm_apply i
      have hj : rk (y j) = j := e.apply_symm_apply j
      have hi' : rank (y i) = i.val := congrArg Fin.val hi
      have hj' : rank (y j) = j.val := congrArg Fin.val hj
      have := Fin.lt_def.mp hij
      omega
    -- the pulled-back Voronoi sides
    let T : Fin n → Fin n → Finset (Fin n) := fun i j => univ.filter fun k => y k ∈ S (y i) (y j)
    have hT3 : ∀ i c v, i < c → c < v → T i v ⊆ T i c ∪ T c v := by
      intro i c v hic hcv k hk
      simp only [T, mem_union, mem_filter, mem_univ, true_and] at hk ⊢
      by_contra hcon
      push Not at hcon
      have hic' : y i ≠ y c := fun h => hic.ne (y.injective h)
      have hcv' : y c ≠ y v := fun h => hcv.ne (y.injective h)
      have hiv' : y i ≠ y v := fun h => (hic.trans hcv).ne (y.injective h)
      have k1 : y k ∈ S (y c) (y i) := (vs_compl x hic').mpr hcon.1
      have k2 : y k ∈ S (y v) (y c) := (vs_compl x hcv').mpr hcon.2
      exact (vs_compl x hiv').mp (vs_trans x k2 k1) hk
    have hT4 : ∀ i j, i < j → (T i j).card ≤ M := by
      intro i j hij
      refine le_trans ?_ (hy i j hij).2
      refine card_le_card_of_injOn y ?_ y.injective.injOn
      intro k hk
      simp only [T, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk
      exact hk
    obtain ⟨R, hRgood, hRcard⟩ := ReductionCore.core M hM1 T hT3 hT4
    -- the SAS
    let emb := R.orderEmbOfFin rfl
    let f : Fin R.card → P := fun t => x (y (emb t))
    have hf : IsSAS dist f := by
      refine isSAS_of_outside f (hx.comp (y.injective.comp emb.injective)) ?_
      intro s t r hst hr
      rcases hst.lt_or_eq with hst | rfl
      · have hst' : emb s < emb t := emb.strictMono hst
        by_cases hT : emb r ∈ T (emb s) (emb t)
        · have := hRgood _ (R.orderEmbOfFin_mem rfl s) _ (R.orderEmbOfFin_mem rfl t) _
            (R.orderEmbOfFin_mem rfl r) hst' hT
          have h1 : s ≤ r := emb.le_iff_le.mp this.1
          have h2 : r ≤ t := emb.le_iff_le.mp this.2
          have hrt : r = t := by
            rcases hr with hr | hr
            · exact absurd hr (not_lt.mpr h1)
            · exact le_antisymm h2 hr
          subst hrt
          simp only [f, dist_self]
          exact dist_nonneg
        · simp only [T, mem_filter, mem_univ, true_and] at hT
          exact le_of_not_mem_vs x hT
      · exact le_rfl
    have hlen := hL R.card f hf (fun i => ⟨y (emb i), rfl⟩)
    have : (n : ℝ) ≤ 4 * M * L := by
      refine hRcard.trans ?_
      gcongr
    have : n ≤ 4 * M * L := by exact_mod_cast this
    nlinarith
  refine ⟨a, b, hab, ?_, ?_⟩
  · have hle : (M : ℝ) ≤ (S a b).card := by exact_mod_cast min_le_left _ _
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    have : (n : ℝ) ≤ 4 * L * M := by exact_mod_cast hmain
    have hL0 : (0 : ℝ) ≤ 4 * L := by positivity
    nlinarith
  · have hle : (M : ℝ) ≤ (S b a).card := by exact_mod_cast min_le_right _ _
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    have : (n : ℝ) ≤ 4 * L * M := by exact_mod_cast hmain
    have hL0 : (0 : ℝ) ≤ 4 * L := by positivity
    nlinarith

end SelfApproaching.Proof
