import SelfApproaching.Definitions
import SelfApproaching.Proof.NavigationCore
import SelfApproaching.Proof.Reduction
import SelfApproaching.Proof.EuclideanUpper
import SelfApproaching.Proof.Balanced

/-!
# Navigation: applying the routing-tree theorem

`navigable_of_balanced` needs a balanced pair inside every subset `Y` of the points. We get it by
applying the balanced-partition theorems to `Y`, re-indexed in increasing order of ID (so that
ties are still broken by ID).
-/

namespace SelfApproaching.Proof

open Real

variable {P : Type*} [MetricSpace P]

/-- A balanced partition of the subfamily indexed (in increasing order) by `Y` is a balanced
pair inside `Y`. -/
private lemma balanced_in_subset {n : ℕ} (x : Fin n → P) (Y : Finset (Fin n)) (β : ℝ)
    (h : HasBalancedVoronoiPartition dist (fun i => x (Y.orderEmbOfFin rfl i)) β) :
    ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x a b).card ∧
      β * Y.card ≤ (Y ∩ voronoiSide dist x b a).card := by
  set e := Y.orderEmbOfFin rfl
  have hside : ∀ a b : Fin Y.card,
      (voronoiSide dist (fun i => x (e i)) a b).map e.toEmbedding =
        Y ∩ voronoiSide dist x (e a) (e b) := by
    intro a b
    ext k
    simp only [Finset.mem_map, voronoiSide, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, RelEmbedding.coe_toEmbedding, Prefers]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Y.orderEmbOfFin_mem rfl i, ?_⟩
      simpa [e.lt_iff_lt] using hi
    · rintro ⟨hk, hk'⟩
      have hrange : k ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨i, rfl⟩ := hrange
      exact ⟨i, by simpa [e.lt_iff_lt] using hk', rfl⟩
  obtain ⟨a, b, hab, h1, h2⟩ := h
  refine ⟨e a, Y.orderEmbOfFin_mem rfl a, e b, Y.orderEmbOfFin_mem rfl b,
    fun h => hab (e.injective h), ?_, ?_⟩
  · rw [← hside, Finset.card_map]; simpa using h1
  · rw [← hside, Finset.card_map]; simpa using h2

theorem navigable_of_sas_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → P) (hx : Function.Injective x) (L : ℕ)
    (hL : ∀ (ℓ : ℕ) (y : Fin ℓ → P), IsSAS dist y → (∀ i, y i ∈ Set.range x) → ℓ ≤ L) :
    ∃ out : Fin n → Finset (Fin n), (∀ v, (out v).card ≤ 2) ∧
      ∀ s q, GreedyReachesWithin dist x out s q (2 * ⌈3.996 * L * log n⌉₊ + 1) := by
  -- a single point is an SAS, so `1 ≤ L`
  have hL1 : 1 ≤ L := hL 1 (fun _ => x ⟨0, hn⟩)
    ⟨fun a b _ => Subsingleton.elim a b, fun i j _ h _ => absurd h (by
      rw [Subsingleton.elim i j]; exact lt_irrefl _)⟩ (fun _ => ⟨_, rfl⟩)
  have hβ : (0 : ℝ) < 1 / (3.996 * L) := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  obtain ⟨out, hout, hreach⟩ := navigable_of_balanced n hn x hx (1 / (3.996 * L)) hβ (by
    intro Y hY
    apply balanced_in_subset x Y
    refine balanced_of_sas_bound' Y.card hY _ (fun i j h => (Y.orderEmbOfFin rfl).injective
      (hx h)) L (fun ℓ y hy hyr => hL ℓ y hy (fun i => ?_))
    obtain ⟨j, hj⟩ := hyr i
    exact ⟨_, hj⟩)
  refine ⟨out, hout, fun s q => ?_⟩
  have : log n / (1 / (3.996 * L)) = 3.996 * L * log n := by field_simp
  have h := hreach s q
  rwa [this] at h

theorem euclidean_navigable (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x) :
    ∃ out : Fin n → Finset (Fin n), (∀ v, (out v).card ≤ 2) ∧
      ∀ s q, GreedyReachesWithin dist x out s q (2 * ⌈(21.978 * d - 1.998) * log n⌉₊ + 1) := by
  have hβ : (0 : ℝ) < 1 / (21.978 * d - 1.998) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    apply one_div_pos.mpr
    linarith
  obtain ⟨out, hout, hreach⟩ := navigable_of_balanced n hn x hx (1 / (21.978 * d - 1.998)) hβ (by
    intro Y hY
    apply balanced_in_subset x Y
    exact euclidean_balanced d hd Y.card hY _
      (fun i j h => (Y.orderEmbOfFin rfl).injective (hx h)))
  refine ⟨out, hout, fun s q => ?_⟩
  have : log n / (1 / (21.978 * d - 1.998)) = (21.978 * d - 1.998) * log n := by
    rw [div_div_eq_mul_div, div_one, mul_comm]
  have h := hreach s q
  rwa [this] at h

end SelfApproaching.Proof
