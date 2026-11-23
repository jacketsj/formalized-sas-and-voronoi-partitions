import SelfApproaching.Definitions

/-!
# SASs with bounded aspect ratio (Theorem 6 of the paper)

Write `L i = dist (x i) (x (i+1))` (and `L (ℓ-1) = L (ℓ-2)`). The SAS condition makes `L`
non-increasing and gives `L j ≤ dist (x i) (x j) ≤ L i` for `i < j`. Bucketing the indices by
`⌊log_{1+ε} (L i / m)⌋` gives at most `⌈log_{1+ε} b⌉` buckets, each of aspect ratio `≤ 1 + ε`.
-/

namespace SelfApproaching.Proof

open Real

variable {P : Type*} [MetricSpace P]

/-- The consecutive gaps of a sequence, extended to the last index by repeating the last gap. -/
private noncomputable def gap {ℓ : ℕ} (X : ℕ → P) (i : ℕ) : ℝ :=
  if i + 1 < ℓ then dist (X i) (X (i + 1)) else dist (X (i - 1)) (X i)

private lemma gap_bounds {ℓ : ℕ} (X : ℕ → P)
    (hX : ∀ i j k, i < ℓ → j < ℓ → k < ℓ → i < j → k ≠ i → dist (X k) (X j) ≤ dist (X k) (X i))
    {i j : ℕ} (hij : i < j) (hj : j < ℓ) :
    gap (ℓ := ℓ) X j ≤ dist (X i) (X j) ∧ dist (X i) (X j) ≤ gap (ℓ := ℓ) X i := by
  -- `dist (x j) (x (j-1)) ≤ dist (x j) (x i)`
  have hlow : dist (X (j - 1)) (X j) ≤ dist (X i) (X j) := by
    rcases Nat.lt_or_ge i (j - 1) with h | h
    · rw [dist_comm (X (j - 1)), dist_comm (X i)]
      exact hX i (j - 1) j (by omega) (by omega) hj h (by omega)
    · have : i = j - 1 := by omega
      rw [this]
  refine ⟨?_, ?_⟩
  · unfold gap
    split_ifs with h
    · refine le_trans ?_ hlow
      rw [dist_comm (X (j - 1))]
      exact hX (j - 1) (j + 1) j (by omega) h hj (by omega) (by omega)
    · exact hlow
  · unfold gap
    rw [if_pos (by omega)]
    rcases Nat.lt_or_ge (i + 1) j with h | h
    · exact hX (i + 1) j i (by omega) hj (by omega) h (by omega)
    · have : j = i + 1 := by omega
      rw [this]

theorem sas_length_le_of_aspect (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : ∀ (m : ℕ) (y : Fin m → P), Function.Injective y → AspectRatioLE dist y (1 + ε) →
      m ≤ N)
    (b : ℝ) (hb : 1 < b) (ℓ : ℕ) (x : Fin ℓ → P) (hx : IsSAS dist x)
    (hxb : AspectRatioLT dist x b) :
    ℓ ≤ N * ⌈Real.logb (1 + ε) b⌉₊ := by
  have hε1 : 1 < 1 + ε := by linarith
  set K := ⌈Real.logb (1 + ε) b⌉₊ with hK
  have hlogb : 0 < Real.logb (1 + ε) b := Real.logb_pos hε1 hb
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by
    rw [hK]; exact (Nat.ceil_pos.mpr hlogb).ne')
  rcases Nat.eq_zero_or_pos ℓ with h0 | hℓ0
  · rw [h0]; exact Nat.zero_le _
  -- a single point is a family of aspect ratio `≤ 1 + ε`, so `1 ≤ N`
  have hN1 : 1 ≤ N := hN 1 (fun _ => x ⟨0, hℓ0⟩) (fun a b _ => Subsingleton.elim a b)
    ⟨1, one_pos, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  rcases Nat.lt_or_ge ℓ 2 with hℓ | hℓ
  · calc ℓ ≤ 1 := by omega
      _ ≤ N * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨m, hm, hmb⟩ := hxb
  -- ℕ-indexed version of the sequence
  let X : ℕ → P := fun i => if h : i < ℓ then x ⟨i, h⟩ else x ⟨0, by omega⟩
  have hXx : ∀ i : Fin ℓ, X i = x i := fun i => by simp [X, i.isLt]
  have hX : ∀ i j k, i < ℓ → j < ℓ → k < ℓ → i < j → k ≠ i →
      dist (X k) (X j) ≤ dist (X k) (X i) := by
    intro i j k hi hj hk hij hki
    have := hx.2 ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij (fun h => hki (congrArg Fin.val h))
    simpa [X, hi, hj, hk] using this
  have hXd : ∀ i j, i < ℓ → j < ℓ → i ≠ j → m ≤ dist (X i) (X j) ∧ dist (X i) (X j) < b * m :=
    fun i j hi hj hij => by
      have := hmb ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))
      simpa [X, hi, hj] using this
  -- the gaps lie in `[m, b m)`
  have hgap : ∀ i, i < ℓ → m ≤ gap (ℓ := ℓ) X i ∧ gap (ℓ := ℓ) X i < b * m := by
    intro i hi
    unfold gap
    split_ifs with h
    · exact hXd i (i + 1) hi h (by omega)
    · exact hXd (i - 1) i (by omega) hi (by omega)
  -- the bucket of an index
  let κ : Fin ℓ → ℕ := fun i => ⌊Real.logb (1 + ε) (gap (ℓ := ℓ) X i / m)⌋₊
  have hκ : ∀ i : Fin ℓ, (1 + ε) ^ κ i * m ≤ gap (ℓ := ℓ) X i ∧
      gap (ℓ := ℓ) X i < (1 + ε) ^ κ i * m * (1 + ε) ∧ κ i < K := by
    intro i
    obtain ⟨h1, h2⟩ := hgap i i.isLt
    have hq : 1 ≤ gap (ℓ := ℓ) X i / m := by rw [le_div_iff₀ hm]; linarith
    have hq0 : 0 < gap (ℓ := ℓ) X i / m := by linarith
    have hl0 : 0 ≤ Real.logb (1 + ε) (gap (ℓ := ℓ) X i / m) :=
      Real.logb_nonneg hε1 hq
    refine ⟨?_, ?_, ?_⟩
    · have := Nat.floor_le hl0
      rw [Real.le_logb_iff_rpow_le hε1 hq0, Real.rpow_natCast] at this
      rwa [le_div_iff₀ hm] at this
    · have := Nat.lt_floor_add_one (Real.logb (1 + ε) (gap (ℓ := ℓ) X i / m))
      rw [← Nat.cast_add_one, Real.logb_lt_iff_lt_rpow hε1 hq0, Real.rpow_natCast,
        div_lt_iff₀ hm, pow_succ] at this
      linarith
    · have hlt : Real.logb (1 + ε) (gap (ℓ := ℓ) X i / m) < Real.logb (1 + ε) b :=
        Real.logb_lt_logb hε1 hq0 (by rw [div_lt_iff₀ hm]; linarith)
      have : (κ i : ℝ) < K :=
        lt_of_le_of_lt (Nat.floor_le hl0) (lt_of_lt_of_le hlt (Nat.le_ceil _))
      exact_mod_cast this
  -- each bucket has at most `N` points
  have hfib : ∀ k ∈ (Finset.univ : Finset (Fin ℓ)).image κ,
      ((Finset.univ : Finset (Fin ℓ)).filter fun i => κ i = k).card ≤ N := by
    intro k _
    set F := (Finset.univ : Finset (Fin ℓ)).filter fun i => κ i = k with hF
    let e := F.orderEmbOfFin rfl
    refine hN F.card (fun t => x (e t)) (fun t t' h => e.injective (hx.1 h)) ?_
    refine ⟨(1 + ε) ^ k * m, by positivity, fun t t' htt' => ?_⟩
    have hmem : ∀ t, κ (e t) = k := fun t => by
      have := F.orderEmbOfFin_mem rfl t
      exact (Finset.mem_filter.mp this).2
    have key : ∀ i j : Fin ℓ, κ i = k → κ j = k → i < j →
        (1 + ε) ^ k * m ≤ dist (x i) (x j) ∧ dist (x i) (x j) ≤ (1 + ε) * ((1 + ε) ^ k * m) := by
      intro i j hi hj hij
      obtain ⟨hlo, hhi⟩ := gap_bounds X hX (Fin.lt_def.mp hij) j.isLt
      rw [hXx, hXx] at hlo hhi
      obtain ⟨a1, _, _⟩ := hκ j
      obtain ⟨_, b2, _⟩ := hκ i
      rw [hi] at b2; rw [hj] at a1
      constructor <;> nlinarith
    have hne : e t ≠ e t' := fun h => htt' (e.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key _ _ (hmem t) (hmem t') h
    · rw [dist_comm]; exact key _ _ (hmem t') (hmem t) h
  calc ℓ = (Finset.univ : Finset (Fin ℓ)).card := by simp
    _ ≤ N * ((Finset.univ : Finset (Fin ℓ)).image κ).card :=
        Finset.card_le_mul_card_image _ _ hfib
    _ ≤ N * K := by
        apply Nat.mul_le_mul_left
        calc ((Finset.univ : Finset (Fin ℓ)).image κ).card ≤ (Finset.range K).card :=
              Finset.card_le_card (fun k hk => by
                obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
                exact Finset.mem_range.mpr (hκ i).2.2)
          _ = K := Finset.card_range K

end SelfApproaching.Proof
