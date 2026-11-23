import SelfApproaching.Proof.Reduction
import SelfApproaching.Proof.ReductionSharp.Main

/-!
# A sharper reduction from balanced Voronoi partitions to bounded SASs

`balanced_of_sas_bound` gives balance `1 / (4 L)`. Here we improve the constant `4` to
`999/250 = 3.996`. The combinatorial core (`ReductionSharp.core_sharp`) keeps the random-sampling
argument, but replaces the union bound by a product over windows of `≈ 0.58 M` consecutive points:
the events "no violated consecutive pair inside window `p`" are independent, and only the pairs
straddling two windows are union-bounded. Averaging over the window offset and applying Jensen's
inequality to `exp` gives a small but strict gain over `n / (4 M)` once `M ≥ 1001`; for
`M ≤ 1000` the union bound with the `M - 1` genuine violators of each pair already suffices.
-/

namespace SelfApproaching.Proof

open Real Finset

theorem balanced_of_sas_bound_sharp {P : Type*} [MetricSpace P] (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → P) (hx : Function.Injective x) (L : ℕ)
    (hL : ∀ (ℓ : ℕ) (y : Fin ℓ → P), IsSAS dist y → (∀ i, y i ∈ Set.range x) → ℓ ≤ L) :
    HasBalancedVoronoiPartition dist x (1 / (999 / 250 * L)) := by
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
  -- Main claim: `n ≤ (999/250) L M`.
  have hmain : (n : ℝ) ≤ 999 / 250 * L * M := by
    by_cases h3 : n ≤ 3 * M
    · have h3r : (n : ℝ) ≤ 3 * M := by exact_mod_cast h3
      have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith
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
    have hT1 : ∀ i j, i < j → i ∈ T i j := by
      intro i j hij
      simp only [T, mem_filter, mem_univ, true_and]
      exact self_mem_vs x hx (fun h => hij.ne (y.injective h))
    obtain ⟨R, hRgood, hRcard⟩ := ReductionSharp.core_sharp M hM1 T hT1 hT3 hT4
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
    have hlen' : (R.card : ℝ) ≤ L := by exact_mod_cast hlen
    have hM0 : (0 : ℝ) ≤ 999 / 250 * M := by positivity
    have h := mul_le_mul_of_nonneg_left hlen' hM0
    linarith
  have hL0 : (0 : ℝ) < 999 / 250 * L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  refine ⟨a, b, hab, ?_, ?_⟩
  · have hle : (M : ℝ) ≤ (S a b).card := by exact_mod_cast min_le_left _ _
    rw [one_div, inv_mul_le_iff₀ hL0]
    nlinarith
  · have hle : (M : ℝ) ≤ (S b a).card := by exact_mod_cast min_le_right _ _
    rw [one_div, inv_mul_le_iff₀ hL0]
    nlinarith

end SelfApproaching.Proof
