import SelfApproaching.Definitions

namespace SelfApproaching.Proof

open Real

namespace NavCore

variable {P : Type*} [MetricSpace P] {n : ℕ} (x : Fin n → P)

/-- `GPath x O q s e t`: greedy search for the target `q` on the graph `O` goes from `s` to `e` in
exactly `t` moves. -/
inductive GPath (O : Fin n → Finset (Fin n)) (q : Fin n) : Fin n → Fin n → ℕ → Prop
  | nil (s : Fin n) : GPath O q s s 0
  | cons {s m e : Fin n} {t : ℕ} : IsGreedyMove dist x O q s m → GPath O q m e t →
      GPath O q s e (t + 1)

variable {x}

theorem GPath.trans {O : Fin n → Finset (Fin n)} {q s m e : Fin n} {t₁ t₂ : ℕ}
    (h₁ : GPath x O q s m t₁) (h₂ : GPath x O q m e t₂) : GPath x O q s e (t₁ + t₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hm _ ih =>
    have := GPath.cons hm (ih h₂)
    rwa [Nat.add_right_comm] at this

theorem GPath.exists_fun {O : Fin n → Finset (Fin n)} {q s e : Fin n} {t : ℕ}
    (h : GPath x O q s e t) :
    ∃ v : Fin (t + 1) → Fin n, v 0 = s ∧ v (Fin.last t) = e ∧
      ∀ i : Fin t, IsGreedyMove dist x O q (v i.castSucc) (v i.succ) := by
  induction h with
  | nil s => exact ⟨fun _ => s, rfl, rfl, fun i => i.elim0⟩
  | @cons s m e t hm _ ih =>
    obtain ⟨v, h0, hl, hv⟩ := ih
    refine ⟨Fin.cons s v, rfl, ?_, ?_⟩
    · rw [← Fin.succ_last, Fin.cons_succ, hl]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h0] using hm
      · simpa [← Fin.succ_castSucc] using hv j

variable (x)

/-- `x q` prefers site `x c` to site `x c'` (closer, ties broken by ID). -/
def Pref (q c c' : Fin n) : Prop :=
  dist (x q) (x c) < dist (x q) (x c') ∨ (dist (x q) (x c) = dist (x q) (x c') ∧ c < c')

/-- The routing guarantees of a subtree rooted at `v` with descendants `Y`, of depth `k`, whose
leaves point to `r`. -/
def Good (r : Fin n) (k : ℕ) (v : Fin n) (Y : Finset (Fin n)) (O : Fin n → Finset (Fin n)) :
    Prop :=
  (∀ q ∈ insert v Y, ∃ t ≤ k, GPath x O q v q t) ∧
  ∀ w ∈ insert v Y, ∀ q, (∃ t ≤ k, GPath x O q w q t) ∨ (∃ t ≤ k + 1, GPath x O q w r t)

/-- There is an out-degree-`≤ 2` assignment on `insert v Y` realizing `Good`. -/
def Built (r : Fin n) (k : ℕ) (v : Fin n) (Y : Finset (Fin n)) : Prop :=
  ∃ o : Fin n → Finset (Fin n), (∀ u, (o u).card ≤ 2) ∧
    ∀ O : Fin n → Finset (Fin n), (∀ u ∈ insert v Y, O u = o u) → Good x r k v Y O

theorem built_leaf (r : Fin n) (k : ℕ) (v : Fin n) : Built x r k v ∅ := by
  refine ⟨fun _ => {r}, fun _ => by simp, fun O hO => ⟨?_, ?_⟩⟩
  · intro q hq
    have hq' : q = v := by simpa using hq
    subst hq'
    exact ⟨0, Nat.zero_le _, GPath.nil _⟩
  · intro w hw q
    replace hw : w = v := by simpa using hw
    have hOw : O w = {r} := hO w (by simp [hw])
    by_cases hqw : q = w
    · subst hqw
      exact Or.inl ⟨0, Nat.zero_le _, GPath.nil _⟩
    · refine Or.inr ⟨1, by omega, GPath.cons ⟨Ne.symm hqw, by simp [hOw], ?_⟩ (GPath.nil _)⟩
      intro w' hw' hne
      simp [hOw] at hw'
      exact absurd hw' hne

theorem exists_pref (C : Finset (Fin n)) (hC : C.Nonempty) (q : Fin n) :
    ∃ c ∈ C, ∀ c' ∈ C, c' ≠ c → Pref x q c c' := by
  obtain ⟨c, hc, hmin⟩ := C.exists_min_image (fun c => toLex (dist (x q) (x c), c)) hC
  refine ⟨c, hc, fun c' hc' hne => ?_⟩
  have h1 := hmin c' hc'
  have h2 : toLex (dist (x q) (x c), c) ≠ toLex (dist (x q) (x c'), c') := by
    intro h
    apply hne
    have := congrArg (fun p => (ofLex p).2) h
    exact this.symm
  have := lt_of_le_of_ne h1 h2
  rw [Prod.Lex.toLex_lt_toLex] at this
  exact this

theorem built_step (r : Fin n) (k : ℕ) (v : Fin n) (Y C : Finset (Fin n))
    (Z : Fin n → Finset (Fin n)) (hvY : v ∉ Y) (hC2 : C.card ≤ 2)
    (hsub : ∀ c ∈ C, Built x r k c (Z c))
    (hdisj : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Disjoint (insert c (Z c)) (insert c' (Z c')))
    (hcover : Y = C.biUnion fun c => insert c (Z c))
    (hpref : ∀ c ∈ C, ∀ q ∈ insert c (Z c), ∀ c' ∈ C, c' ≠ c → Pref x q c c')
    (hmove : ∀ q, ∃ c ∈ C, ∀ c' ∈ C, c' ≠ c → Pref x q c c') :
    Built x r (k + 1) v Y := by
  classical
  choose! oc hoc_card hoc using hsub
  let o : Fin n → Finset (Fin n) := fun u =>
    if u = v then C else if h : ∃ c ∈ C, u ∈ insert c (Z c) then oc h.choose u else ∅
  refine ⟨o, ?_, ?_⟩
  · intro u
    simp only [o]
    split_ifs with h1 h2
    · exact hC2
    · exact hoc_card _ h2.choose_spec.1 u
    · simp
  · intro O hO
    have hYc : ∀ c ∈ C, insert c (Z c) ⊆ Y := fun c hc => by
      rw [hcover]; exact Finset.subset_biUnion_of_mem (fun c => insert c (Z c)) hc
    have hOv : O v = C := by rw [hO v (Finset.mem_insert_self _ _)]; simp [o]
    have hsubO : ∀ c ∈ C, Good x r k c (Z c) O := by
      intro c hc
      apply hoc c hc
      intro u hu
      have huY : u ∈ Y := hYc c hc hu
      have huv : u ≠ v := fun h => hvY (h ▸ huY)
      have hex : ∃ c ∈ C, u ∈ insert c (Z c) := ⟨c, hc, hu⟩
      rw [hO u (Finset.mem_insert_of_mem huY)]
      simp only [o, if_neg huv, dif_pos hex]
      have : hex.choose = c := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj _ hex.choose_spec.1 c hc hne) hex.choose_spec.2 hu
      rw [this]
    have hmem : ∀ u ∈ Y, ∃ c ∈ C, u ∈ insert c (Z c) := by
      intro u hu
      rw [hcover, Finset.mem_biUnion] at hu
      exact hu
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqv | hqY
      · rw [hqv]
        exact ⟨0, Nat.zero_le _, GPath.nil _⟩
      · obtain ⟨c, hc, hqc⟩ := hmem q hqY
        obtain ⟨t, ht, hp⟩ := (hsubO c hc).1 q hqc
        refine ⟨t + 1, by omega, GPath.cons ⟨fun h => hvY (h ▸ hqY), hOv ▸ hc, ?_⟩ hp⟩
        intro w' hw' hne
        exact hpref c hc q hqc w' (hOv ▸ hw') hne
    · intro w hw q
      rcases Finset.mem_insert.mp hw with hwv | hwY
      · rw [hwv]
        by_cases hqv : q = v
        · rw [hqv]
          exact Or.inl ⟨0, Nat.zero_le _, GPath.nil _⟩
        · obtain ⟨c, hc, hcp⟩ := hmove q
          have hm : IsGreedyMove dist x O q v c :=
            ⟨Ne.symm hqv, hOv ▸ hc, fun w' hw' hne => hcp w' (hOv ▸ hw') hne⟩
          rcases (hsubO c hc).2 c (Finset.mem_insert_self _ _) q with ⟨t, ht, hp⟩ | ⟨t, ht, hp⟩
          · exact Or.inl ⟨t + 1, by omega, GPath.cons hm hp⟩
          · exact Or.inr ⟨t + 1, by omega, GPath.cons hm hp⟩
      · obtain ⟨c, hc, hwc⟩ := hmem w hwY
        rcases (hsubO c hc).2 w hwc q with ⟨t, ht, hp⟩ | ⟨t, ht, hp⟩
        · exact Or.inl ⟨t, by omega, hp⟩
        · exact Or.inr ⟨t, by omega, hp⟩

theorem mem_side_iff (q a b : Fin n) : q ∈ voronoiSide dist x a b ↔ Pref x q a b := by
  simp [voronoiSide, Pref]

theorem mem_side_self (hx : Function.Injective x) {a b : Fin n} (hab : a ≠ b) :
    a ∈ voronoiSide dist x a b := by
  rw [mem_side_iff]
  left
  rw [dist_self]
  exact dist_pos.mpr (hx.ne hab)

theorem side_disjoint (a b : Fin n) :
    Disjoint (voronoiSide dist x a b) (voronoiSide dist x b a) := by
  rw [Finset.disjoint_left]
  intro k h1 h2
  rw [mem_side_iff] at h1 h2
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact absurd (h1'.trans h2') (lt_irrefl _)

theorem side_cover {a b : Fin n} (hab : a ≠ b) (k : Fin n) (h : k ∉ voronoiSide dist x a b) :
    k ∈ voronoiSide dist x b a := by
  rw [mem_side_iff] at h ⊢
  unfold Pref at h ⊢
  push Not at h
  rcases lt_trichotomy (dist (x k) (x a)) (dist (x k) (x b)) with h1 | h1 | h1
  · exact absurd h1 h.1.not_gt
  · exact Or.inr ⟨h1.symm, lt_of_le_of_ne (not_lt.mp (fun h' => (h.2 h1).not_gt h')) hab.symm⟩
  · exact Or.inl h1

theorem built_all (hx : Function.Injective x) (β : ℝ)
    (hbal : ∀ Y : Finset (Fin n), 2 ≤ Y.card → ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x a b).card ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x b a).card) (r : Fin n) :
    ∀ k : ℕ, ∀ v Y, v ∉ Y → (Y.card : ℝ) < exp (β * k) → Built x r k v Y := by
  classical
  intro k
  induction k with
  | zero =>
    intro v Y _ hY
    have : Y = ∅ := by
      rw [Nat.cast_zero, mul_zero, exp_zero] at hY
      have : Y.card < 1 := by exact_mod_cast hY
      exact Finset.card_eq_zero.mp (by omega)
    subst this
    exact built_leaf x r 0 v
  | succ k ih =>
    intro v Y hvY hY
    rcases Nat.lt_or_ge Y.card 2 with h2 | h2
    · rcases Nat.lt_or_ge Y.card 1 with h1 | h1
      · have : Y = ∅ := Finset.card_eq_zero.mp (by omega)
        subst this
        exact built_leaf x r _ v
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (by omega : Y.card = 1)
        apply built_step x r k v {a} {a} (fun _ => ∅) hvY (by simp)
        · intro c _
          exact built_leaf x r k c
        · intro c hc c' hc' hne
          simp only [Finset.mem_singleton] at hc hc'
          exact absurd (hc.trans hc'.symm) hne
        · simp
        · intro c hc q _ c' hc' hne
          simp only [Finset.mem_singleton] at hc hc'
          exact absurd (hc'.trans hc.symm) hne
        · exact exists_pref x _ (Finset.singleton_nonempty a)
    · obtain ⟨a, ha, b, hb, hab, hA, hB⟩ := hbal Y h2
      set Ya := (Y ∩ voronoiSide dist x a b).erase a with hYa
      set Yb := (Y ∩ voronoiSide dist x b a).erase b with hYb
      have hZa : (if a = a then Ya else Yb) = Ya := if_pos rfl
      have hZb : (if b = a then Ya else Yb) = Yb := if_neg hab.symm
      have hsA : insert a Ya ⊆ voronoiSide dist x a b := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact mem_side_self x hx hab
        · exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hy)).2
      have hsB : insert b Yb ⊆ voronoiSide dist x b a := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact mem_side_self x hx hab.symm
        · exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hy)).2
      have hdisjAB : Disjoint (insert a Ya) (insert b Yb) :=
        Finset.disjoint_of_subset_left hsA (Finset.disjoint_of_subset_right hsB
          (side_disjoint x a b))
      have hsum : ((Y ∩ voronoiSide dist x a b).card : ℝ) +
          ((Y ∩ voronoiSide dist x b a).card : ℝ) ≤ Y.card := by
        have hd : Disjoint (Y ∩ voronoiSide dist x a b) (Y ∩ voronoiSide dist x b a) :=
          Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right (side_disjoint x a b))
        have := Finset.card_union_of_disjoint hd
        have h3 : (Y ∩ voronoiSide dist x a b ∪ Y ∩ voronoiSide dist x b a).card ≤ Y.card :=
          Finset.card_le_card (Finset.union_subset Finset.inter_subset_left
            Finset.inter_subset_left)
        exact_mod_cast this ▸ h3
      have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
      have hshrink : ∀ m : ℕ, (m : ℝ) ≤ (1 - β) * Y.card → (m : ℝ) < exp (β * k) := by
        intro m hm
        have he : (1 - β) ≤ exp (-β) := by linarith [add_one_le_exp (-β)]
        calc (m : ℝ) ≤ (1 - β) * Y.card := hm
          _ ≤ exp (-β) * Y.card := mul_le_mul_of_nonneg_right he hY0
          _ < exp (-β) * exp (β * ↑(k + 1)) := mul_lt_mul_of_pos_left hY (exp_pos _)
          _ = exp (β * k) := by rw [← exp_add]; congr 1; push_cast; ring
      apply built_step x r k v Y {a, b} (fun c => if c = a then Ya else Yb) hvY
        Finset.card_le_two
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · rw [hZa]
          refine ih _ _ (Finset.notMem_erase _ _) (hshrink _ ?_)
          have := Finset.card_erase_le (a := c) (s := Y ∩ voronoiSide dist x c b)
          have : (Ya.card : ℝ) ≤ (Y ∩ voronoiSide dist x c b).card := by exact_mod_cast this
          linarith
        · rw [Finset.mem_singleton.mp hc, hZb]
          refine ih _ _ (Finset.notMem_erase _ _) (hshrink _ ?_)
          have := Finset.card_erase_le (a := b) (s := Y ∩ voronoiSide dist x b a)
          have : (Yb.card : ℝ) ≤ (Y ∩ voronoiSide dist x b a).card := by exact_mod_cast this
          linarith
      · intro c hc c' hc' hne
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hc'
        rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
        · exact absurd rfl hne
        · rw [hZa, hZb]; exact hdisjAB
        · rw [hZa, hZb]; exact hdisjAB.symm
        · exact absurd rfl hne
      · rw [Finset.biUnion_insert, Finset.singleton_biUnion, hZa, hZb]
        ext y
        constructor
        · intro hy
          by_cases hya : y ∈ voronoiSide dist x a b
          · by_cases hy' : y = a
            · simp [hy']
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨hy', Finset.mem_inter.mpr ⟨hy, hya⟩⟩))
          · have hyb := side_cover x hab y hya
            by_cases hy' : y = b
            · simp [hy']
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨hy', Finset.mem_inter.mpr ⟨hy, hyb⟩⟩))
        · intro hy
          rcases Finset.mem_union.mp hy with hy | hy <;>
            rcases Finset.mem_insert.mp hy with rfl | hy
          · exact ha
          · exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hy)).1
          · exact hb
          · exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hy)).1
      · intro c hc q hq c' hc' hne
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hc'
        rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
        · exact absurd rfl hne
        · rw [hZa] at hq; exact (mem_side_iff x _ _ _).mp (hsA hq)
        · rw [hZb] at hq; exact (mem_side_iff x _ _ _).mp (hsB hq)
        · exact absurd rfl hne
      · exact exists_pref x _ (Finset.insert_nonempty _ _)

end NavCore

/-- Lemmas 6 and 7 of the paper: if every set `Y` of at least two of the points contains two sites
whose Voronoi partition of `Y` is `β`-balanced, then the Voronoi routing tree (with an edge from
every leaf back to the root) has out-degree at most two and opportunistic greedy search reaches
every target from every start within `2 ⌈ln n / β⌉ + 1` moves. -/
theorem navigable_of_balanced {P : Type*} [MetricSpace P] (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → P) (hx : Function.Injective x) (β : ℝ) (hβ : 0 < β)
    (hbal : ∀ Y : Finset (Fin n), 2 ≤ Y.card → ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x a b).card ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x b a).card) :
    ∃ out : Fin n → Finset (Fin n), (∀ v, (out v).card ≤ 2) ∧
      ∀ s q, GreedyReachesWithin dist x out s q (2 * ⌈log n / β⌉₊ + 1) := by
  classical
  set K := ⌈log n / β⌉₊ with hK
  let r : Fin n := ⟨0, hn⟩
  have hcard : (((Finset.univ.erase r).card : ℕ) : ℝ) < exp (β * K) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc ((n - 1 : ℕ) : ℝ) < n := by rw [Nat.cast_sub hn]; simp
      _ = exp (log n) := (exp_log hnpos).symm
      _ ≤ exp (β * K) := by
        apply exp_le_exp.mpr
        have := Nat.le_ceil (log n / β)
        rw [div_le_iff₀ hβ] at this
        linarith
  obtain ⟨o, hcard2, ho⟩ :=
    NavCore.built_all x hx β hbal r K r _ (Finset.notMem_erase r _) hcard
  have hg := ho o (fun _ _ => rfl)
  refine ⟨o, hcard2, fun s q => ?_⟩
  have hs : s ∈ insert r (Finset.univ.erase r) := by simp
  have hq : q ∈ insert r (Finset.univ.erase r) := by simp
  rcases hg.2 s hs q with ⟨t, ht, hp⟩ | ⟨t, ht, hp⟩
  · obtain ⟨v, h0, hl, hv⟩ := hp.exists_fun
    exact ⟨t, by omega, v, h0, hl, hv⟩
  · obtain ⟨t', ht', hp'⟩ := hg.1 q hq
    obtain ⟨v, h0, hl, hv⟩ := (hp.trans hp').exists_fun
    exact ⟨t + t', by omega, v, h0, hl, hv⟩

end SelfApproaching.Proof
