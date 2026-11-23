import SelfApproaching.Definitions
import SelfApproaching.Proof.Reduction
import SelfApproaching.Proof.ReductionSharp
import SelfApproaching.Proof.EuclideanUpper
import SelfApproaching.Proof.EuclideanLower

/-!
# Euclidean balanced Voronoi partitions, and their tightness

The positive result combines the reduction with the `11d/2` SAS bound. The negative result uses
a strict SAS: every two-site Voronoi partition of it has a single point on one side.
-/

namespace SelfApproaching.Proof

open Real

/-- The reduction with the constant `3.996`. -/
theorem balanced_of_sas_bound' {P : Type*} [MetricSpace P] (n : ℕ) (hn : 2 ≤ n) (x : Fin n → P)
    (hx : Function.Injective x) (L : ℕ) (hL : SASLengthLE dist x L) :
    HasBalancedVoronoiPartition dist x (1 / (3.996 * L)) := by
  have h := balanced_of_sas_bound_sharp n hn x hx L hL
  norm_num at h ⊢
  exact h

theorem euclidean_balanced (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x) :
    HasBalancedVoronoiPartition dist x (1 / (21.978 * d - 1.998)) := by
  set L := (11 * d - 1) / 2 with hL
  have hbound : SASLengthLE dist x L := by
    intro ℓ y hy _
    have := euclidean_sas_length_lt d hd ℓ y hy
    omega
  obtain ⟨a, b, hab, h1, h2⟩ := balanced_of_sas_bound' n hn x hx L hbound
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  -- `2 L ≤ 11 d - 1`
  have hLd : (2 * L : ℝ) ≤ 11 * d - 1 := by
    have : 2 * L + 1 ≤ 11 * d := by omega
    have : (2 * L + 1 : ℝ) ≤ 11 * d := by exact_mod_cast this
    linarith
  have hle : 1 / (21.978 * d - 1.998 : ℝ) * n ≤ 1 / (3.996 * L) * n := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  exact ⟨a, b, hab, hle.trans h1, hle.trans h2⟩

/-- For a strict SAS and indices `a < b`, the side of `a` is exactly `{a}`. -/
private lemma voronoiSide_of_strict {E : Type*} [MetricSpace E] {m : ℕ} {x : Fin m → E}
    (hx : IsStrictSAS dist x) {a b : Fin m} (hab : a < b) :
    voronoiSide dist x a b = {a} := by
  ext k
  simp only [voronoiSide, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hka
    have := hx a b k hab hka
    rcases h with h | ⟨h, _⟩ <;> linarith
  · intro hk
    rw [hk]
    left
    have := hx a b b hab (ne_of_gt hab)
    rw [dist_self] at this
    rw [dist_self, dist_comm]
    exact this

private lemma mem_voronoiSide_self {E : Type*} [MetricSpace E] {m : ℕ} {x : Fin m → E}
    (hx : Function.Injective x) {a b : Fin m} (hab : a ≠ b) : a ∈ voronoiSide dist x a b := by
  simp only [voronoiSide, Prefers, Finset.mem_filter, Finset.mem_univ, true_and, dist_self]
  exact Or.inl (dist_pos.mpr (fun h => hab (hx h)))

theorem euclidean_balance_tight (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : Fin ⌈(9 * d : ℝ) / 4⌉₊ → EuclideanSpace ℝ (Fin d), Function.Injective x ∧
      ∀ a b, a ≠ b → min (voronoiSide dist x a b).card (voronoiSide dist x b a).card = 1 := by
  obtain ⟨x, hx⟩ := euclidean_strict_sas_exists d hd
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hx i j j h (ne_of_gt h)
      rw [hij, dist_self] at this
      exact lt_irrefl _ this
    · have := hx j i i h (ne_of_gt h)
      rw [hij, dist_self] at this
      exact lt_irrefl _ this
  refine ⟨x, hinj, fun a b hab => ?_⟩
  have key : ∀ a b, a < b →
      min (voronoiSide dist x a b).card (voronoiSide dist x b a).card = 1 := by
    intro a b h
    rw [voronoiSide_of_strict hx h, Finset.card_singleton]
    exact min_eq_left (Finset.card_pos.mpr ⟨b, mem_voronoiSide_self hinj (ne_of_gt h)⟩)
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [min_comm]; exact key b a h

end SelfApproaching.Proof
