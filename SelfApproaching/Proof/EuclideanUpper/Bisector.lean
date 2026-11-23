import Mathlib

/-!
# Bisector distance bound

For distinct points `p, q` in a real inner product space and a point `y`, `phi p q y` is the
signed distance from `y` to the perpendicular bisector of `p` and `q` (positive on `q`'s side).

The main result `bisector_bound` states: if `x₁, …, x_m` (a list) is "forward self-approaching"
(distinct, and `‖x_k - x_i‖ ≤ ‖x_j - x_i‖` for `i < j < k`) and `a` gets weakly closer along the
list, then `∑_j phi x_j x_{j+1} a ^ 2 ≤ ‖a - x₁‖ ^ 2`.
-/

namespace SelfApproaching.Proof.EuclideanUpper

open List

variable {E : Type*} [NormedAddCommGroup E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Signed distance from `y` to the bisector of `p` and `q`. -/
noncomputable def phi (p q y : E) : ℝ :=
  (‖y - p‖ ^ 2 - ‖y - q‖ ^ 2) / (2 * ‖q - p‖)

/-- Sum of `phi² ` over consecutive pairs of a list. -/
noncomputable def bsum (a : E) : List E → ℝ
  | p :: q :: t => phi p q a ^ 2 + bsum a (q :: t)
  | _ => 0

@[simp] lemma bsum_nil (a : E) : bsum a [] = 0 := rfl
@[simp] lemma bsum_single (a p : E) : bsum a [p] = 0 := rfl
@[simp] lemma bsum_cons_cons (a p q : E) (t : List E) :
    bsum a (p :: q :: t) = phi p q a ^ 2 + bsum a (q :: t) := rfl

/-- Forward self-approaching list. -/
def FwdSAS (l : List E) : Prop :=
  l.Nodup ∧ ∀ o p q, [o, p, q] <+ l → ‖q - o‖ ≤ ‖p - o‖

/-- `b` gets weakly closer along the list. -/
def Approach (b : E) (l : List E) : Prop :=
  l.Pairwise (fun p q => ‖b - q‖ ^ 2 ≤ ‖b - p‖ ^ 2)

lemma FwdSAS.sublist {l₁ l₂ : List E} (h : l₁ <+ l₂) (hl : FwdSAS l₂) : FwdSAS l₁ :=
  ⟨hl.1.sublist h, fun o p q h' => hl.2 o p q (h'.trans h)⟩

lemma Approach.sublist {b : E} {l₁ l₂ : List E} (h : l₁ <+ l₂) (hl : Approach b l₂) :
    Approach b l₁ :=
  Pairwise.sublist h hl

lemma phi_nonneg {p q y : E} (h : ‖y - q‖ ^ 2 ≤ ‖y - p‖ ^ 2) : 0 ≤ phi p q y :=
  div_nonneg (by linarith) (by positivity)

/-- Deleting the first point of a tie only increases the bisector sum. -/
lemma tie_step (b o p q : E) (hoq : o ≠ q) (hd : ‖q - o‖ ≤ ‖p - o‖)
    (hpo : ‖b - p‖ ^ 2 ≤ ‖b - o‖ ^ 2) (hpq : ‖b - p‖ ^ 2 = ‖b - q‖ ^ 2) :
    phi o p b ^ 2 + phi p q b ^ 2 ≤ phi o q b ^ 2 := by
  have h0 : phi p q b = 0 := by simp [phi, hpq]
  have hq : 0 < ‖q - o‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hoq))
  have h1 : phi o p b ≤ phi o q b := by
    unfold phi
    rw [← hpq]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  rw [h0]
  have := pow_le_pow_left₀ (phi_nonneg hpo) h1 2
  linarith [sq_nonneg (0 : ℝ)]

lemma del_le (b p q : E) (l₂ : List E) (hpq : ‖b - p‖ ^ 2 = ‖b - q‖ ^ 2) :
    ∀ l₁ : List E, l₁ ≠ [] → FwdSAS (l₁ ++ p :: q :: l₂) → Approach b (l₁ ++ p :: q :: l₂) →
      bsum b (l₁ ++ p :: q :: l₂) ≤ bsum b (l₁ ++ q :: l₂)
  | [], h, _, _ => absurd rfl h
  | [o], _, hS, hA => by
    simp only [cons_append, nil_append, bsum_cons_cons] at *
    have hsub : [o, p, q] <+ o :: p :: q :: l₂ := by simp
    have hnd := hS.1.sublist hsub
    simp only [nodup_cons, mem_cons, not_or] at hnd
    have hpo : ‖b - p‖ ^ 2 ≤ ‖b - o‖ ^ 2 := by
      simp only [Approach, pairwise_cons] at hA
      exact hA.1 p (by simp)
    have := tie_step b o p q hnd.1.2.1 (hS.2 o p q hsub) hpo hpq
    linarith
  | o :: o' :: m, _, hS, hA => by
    have ih := del_le b p q l₂ hpq (o' :: m) (by simp)
      (hS.sublist (sublist_cons_self _ _)) (hA.sublist (sublist_cons_self _ _))
    simp only [cons_append, bsum_cons_cons] at ih ⊢
    linarith

/-- Consecutive pairs of a list. -/
def adj : List E → List (E × E)
  | p :: q :: t => (p, q) :: adj (q :: t)
  | _ => []

lemma mem_adj : ∀ (l : List E) (p q : E),
    (p, q) ∈ adj l ↔ ∃ l₁ l₂, l = l₁ ++ p :: q :: l₂
  | [], p, q => by simp [adj]
  | [x], p, q => by
    simp only [adj, not_mem_nil, false_iff, not_exists]
    intro l₁ l₂ h
    have := congrArg List.length h
    simp at this; omega
  | x :: y :: t, p, q => by
    simp only [adj, mem_cons, Prod.mk.injEq]
    rw [mem_adj (y :: t) p q]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨l₁, l₂, h⟩)
      · exact ⟨[], t, rfl⟩
      · exact ⟨x :: l₁, l₂, by simp [h]⟩
    · rintro ⟨l₁, l₂, h⟩
      rcases l₁ with _ | ⟨z, l₁⟩
      · simp at h; left; exact ⟨h.1.symm, h.2.1.symm⟩
      · simp only [cons_append, cons.injEq] at h
        right; exact ⟨l₁, l₂, h.2⟩

lemma approach_of_adj (b : E) (l : List E)
    (h : ∀ pq ∈ adj l, ‖b - pq.2‖ ^ 2 ≤ ‖b - pq.1‖ ^ 2) : Approach b l := by
  unfold Approach
  have : Trans (fun p q : E => ‖b - q‖ ^ 2 ≤ ‖b - p‖ ^ 2)
      (fun p q : E => ‖b - q‖ ^ 2 ≤ ‖b - p‖ ^ 2) (fun p q : E => ‖b - q‖ ^ 2 ≤ ‖b - p‖ ^ 2) :=
    ⟨fun h1 h2 => h2.trans h1⟩
  rw [← isChain_iff_pairwise, isChain_iff_forall_rel_of_append_cons_cons]
  intro p q l₁ l₂ e
  exact h (p, q) ((mem_adj l p q).2 ⟨l₁, l₂, e⟩)

lemma adj_of_approach (b : E) (l : List E) (h : Approach b l) :
    ∀ pq ∈ adj l, ‖b - pq.2‖ ^ 2 ≤ ‖b - pq.1‖ ^ 2 := by
  rintro ⟨p, q⟩ hpq
  obtain ⟨l₁, l₂, rfl⟩ := (mem_adj _ p q).1 hpq
  unfold Approach at h
  rw [pairwise_append] at h
  have := h.2.1
  rw [pairwise_cons] at this
  exact this.1 q (by simp)

/-- Finitely many affine constraints `c i + s i * t ≥ 0`, all holding at `0`, one with negative
slope: there is a largest feasible `t ≥ 0`, at which some constraint is tight. -/
lemma exists_tight {ι : Type*} (P : Finset ι) (c s : ι → ℝ) (hc : ∀ i ∈ P, 0 ≤ c i)
    (hs : ∃ i ∈ P, s i < 0) :
    ∃ t, 0 ≤ t ∧ (∀ i ∈ P, 0 ≤ c i + s i * t) ∧ ∃ i ∈ P, c i + s i * t = 0 := by
  classical
  obtain ⟨i₀, hi₀P, hi₀s⟩ := hs
  set Q := P.filter (fun i => s i < 0)
  have hQ : Q.Nonempty := ⟨i₀, by simp [Q, hi₀P, hi₀s]⟩
  obtain ⟨j, hjQ, hmin⟩ := Q.exists_min_image (fun i => c i / (-s i)) hQ
  simp only [Q, Finset.mem_filter] at hjQ
  refine ⟨c j / (-s j), div_nonneg (hc j hjQ.1) (by linarith), ?_, j, hjQ.1, ?_⟩
  · intro i hi
    by_cases hsi : s i < 0
    · have := hmin i (by simp [Q, hi, hsi])
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · have : 0 ≤ c j / -s j := div_nonneg (hc j hjQ.1) (by linarith)
      nlinarith [hc i hi]
  · have : s j ≠ 0 := hjQ.2.ne
    field_simp
    ring

variable [InnerProductSpace ℝ E]

/-- Difference of squared distances along a line. -/
lemma sqdiff_line (a w p q : E) (t : ℝ) :
    ‖a + t • w - p‖ ^ 2 - ‖a + t • w - q‖ ^ 2 =
      (‖a - p‖ ^ 2 - ‖a - q‖ ^ 2) + 2 * ⟪w, q - p⟫ * t := by
  have h1 : a + t • w - p = (a - p) + t • w := by abel
  have h2 : a + t • w - q = (a - q) + t • w := by abel
  rw [h1, h2, norm_add_sq_real, norm_add_sq_real, real_inner_smul_right, real_inner_smul_right]
  have : ⟪w, q - p⟫ = ⟪a - p, w⟫ - ⟪a - q, w⟫ := by
    rw [← inner_sub_left, real_inner_comm]; congr 1; abel
  rw [this]; ring

lemma phi_line (a w p q : E) (t : ℝ) :
    phi p q (a + t • w) = phi p q a + t * (⟪w, q - p⟫ / ‖q - p‖) := by
  unfold phi
  rw [sqdiff_line]
  rcases eq_or_ne ‖q - p‖ 0 with h | h
  · simp [h]
  · field_simp

lemma phi_le_norm (p q y : E) (h : p ≠ q) : phi p q y ≤ ‖y - p‖ := by
  have hL : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
  unfold phi
  rw [div_le_iff₀ (by positivity)]
  have e : y - q = (y - p) - (q - p) := by abel
  rw [e, norm_sub_sq_real (y - p) (q - p)]
  have := real_inner_le_norm (y - p) (q - p)
  nlinarith [sq_nonneg ‖q - p‖]

/-- Base case. -/
lemma bsum_two_le (b x y : E) (hxy : x ≠ y) (h : ‖b - y‖ ^ 2 ≤ ‖b - x‖ ^ 2) :
    phi x y b ^ 2 ≤ ‖b - x‖ ^ 2 :=
  pow_le_pow_left₀ (phi_nonneg h) (phi_le_norm x y b hxy) 2

/-- The bisector sum along a line is a quadratic with nonnegative leading coefficient. -/
lemma bsum_line (a w : E) : ∀ l : List E,
    ∃ α β : ℝ, 0 ≤ α ∧ ∀ t : ℝ, bsum (a + t • w) l = bsum a l + β * t + α * t ^ 2
  | [] => ⟨0, 0, le_rfl, fun t => by simp⟩
  | [_] => ⟨0, 0, le_rfl, fun t => by simp⟩
  | p :: q :: l => by
    obtain ⟨α, β, hα, h⟩ := bsum_line a w (q :: l)
    set c := ⟪w, q - p⟫ / ‖q - p‖
    refine ⟨α + c ^ 2, β + 2 * phi p q a * c, by positivity, fun t => ?_⟩
    simp only [bsum_cons_cons, h, phi_line]
    ring

/-- **Bisector distance bound.** -/
theorem bisector_bound (n : ℕ) : ∀ (l : List E), l.length = n → ∀ (x b : E),
    FwdSAS (x :: l) → Approach b (x :: l) → bsum b (x :: l) ≤ ‖b - x‖ ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro l hl x
  have tie : ∀ b, FwdSAS (x :: l) → Approach b (x :: l) →
      (∃ l₁ p q l₂, x :: l = l₁ ++ p :: q :: l₂ ∧ ‖b - p‖ ^ 2 = ‖b - q‖ ^ 2) →
      bsum b (x :: l) ≤ ‖b - x‖ ^ 2 := by
    rintro b hS hA ⟨l₁, p, q, l₂, e, hpq⟩
    rcases l₁ with _ | ⟨o, m⟩
    · simp only [nil_append, cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hlen : l₂.length < n := by simp at hl; omega
      have := IH _ hlen l₂ rfl q b (hS.sublist (sublist_cons_self _ _))
        (hA.sublist (sublist_cons_self _ _))
      have h0 : phi x q b = 0 := by simp [phi, hpq]
      rw [bsum_cons_cons, h0, hpq]
      linarith
    · simp only [cons_append, cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hsub : x :: (m ++ q :: l₂) <+ x :: (m ++ p :: q :: l₂) :=
        ((sublist_cons_self p (q :: l₂)).append_left m).cons_cons x
      have hlen : (m ++ q :: l₂).length < n := by simp at hl ⊢; omega
      have h1 := del_le b p q l₂ hpq (x :: m) (by simp) hS hA
      have h2 := IH _ hlen (m ++ q :: l₂) rfl x b (hS.sublist hsub) (hA.sublist hsub)
      simp only [cons_append] at h1
      linarith
  rcases l with _ | ⟨y, _ | ⟨z, rest⟩⟩
  · intro b _ _
    simp only [bsum_single]
    positivity
  · intro b hS hA
    simp only [bsum_cons_cons, bsum_single, add_zero]
    have hxy : x ≠ y := by
      have := hS.1
      simpa using this
    exact bsum_two_le b x y hxy (by simpa [Approach] using hA)
  · intro a hS hA
    classical
    set X := x :: y :: z :: rest with hX
    set v := y - x with hv
    set P := (adj X).toFinset with hP
    have hc : ∀ pq ∈ P, 0 ≤ ‖a - pq.1‖ ^ 2 - ‖a - pq.2‖ ^ 2 := fun pq h => by
      have := adj_of_approach a X hA pq (List.mem_toFinset.1 h)
      linarith
    have key : ∀ w : E, (∃ pq ∈ P, 2 * ⟪w, pq.2 - pq.1⟫ < 0) →
        ∃ t : ℝ, 0 ≤ t ∧ bsum (a + t • w) X ≤ ‖a + t • w - x‖ ^ 2 := by
      intro w hw
      obtain ⟨t, ht0, hall, pq, hpq, htight⟩ := exists_tight P _ _ hc hw
      refine ⟨t, ht0, tie _ hS ?_ ?_⟩
      · apply approach_of_adj
        intro pq' h'
        have := hall pq' (List.mem_toFinset.2 h')
        rw [← sqdiff_line] at this
        linarith
      · obtain ⟨l₁, l₂, e⟩ := (mem_adj X pq.1 pq.2).1 (List.mem_toFinset.1 hpq)
        refine ⟨l₁, pq.1, pq.2, l₂, e, ?_⟩
        rw [← sqdiff_line] at htight
        linarith
    have hnd := hS.1
    simp only [hX, nodup_cons, mem_cons, not_or] at hnd
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hnd.1.1))
    have hw : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hnd.2.1.1))
    have h12 : (x, y) ∈ P := by simp [hP, hX, adj]
    have h23 : (y, z) ∈ P := by simp [hP, hX, adj]
    have s12 : 2 * ⟪-v, y - x⟫ < 0 := by
      rw [inner_neg_left, ← hv, real_inner_self_eq_norm_sq]
      nlinarith
    have s23 : 2 * ⟪v, z - y⟫ < 0 := by
      have htri := hS.2 x y z (by simp [hX])
      have e : z - x = v + (z - y) := by rw [hv]; abel
      rw [e, ← hv] at htri
      have := pow_le_pow_left₀ (norm_nonneg _) htri 2
      rw [norm_add_sq_real] at this
      nlinarith
    obtain ⟨t1, ht1, hb1⟩ := key v ⟨_, h23, s23⟩
    obtain ⟨t2, ht2, hb2⟩ := key (-v) ⟨_, h12, s12⟩
    obtain ⟨α, β, hα, hq⟩ := bsum_line a v (y :: z :: rest)
    have hvv : ⟪v, y - x⟫ / ‖y - x‖ = ‖v‖ := by
      rw [← hv, real_inner_self_eq_norm_sq]
      field_simp
    have G : ∀ t : ℝ, bsum (a + t • v) X - ‖a + t • v - x‖ ^ 2 =
        (bsum a X - ‖a - x‖ ^ 2) + (β + 2 * phi x y a * ‖v‖ - 2 * ⟪a - x, v⟫) * t +
          α * t ^ 2 := by
      intro t
      have e : a + t • v - x = (a - x) + t • v := by abel
      simp only [hX, bsum_cons_cons, hq t, phi_line, hvv]
      rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs]
      ring
    have g1 := G t1
    have g2 := G (-t2)
    rw [neg_smul, ← smul_neg] at g2
    by_cases hB : 0 ≤ β + 2 * phi x y a * ‖v‖ - 2 * ⟪a - x, v⟫
    · nlinarith [mul_nonneg hB ht1, mul_nonneg hα (sq_nonneg t1)]
    · nlinarith [mul_nonneg (neg_nonneg.2 (le_of_lt (not_le.1 hB))) ht2, mul_nonneg hα (sq_nonneg t2)]

end SelfApproaching.Proof.EuclideanUpper
