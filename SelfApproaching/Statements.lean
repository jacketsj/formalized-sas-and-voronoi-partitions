import SelfApproaching.Definitions
import SelfApproaching.Proof.Reduction
import SelfApproaching.Proof.ReductionSharp
import SelfApproaching.Proof.EuclideanUpper
import SelfApproaching.Proof.EuclideanLower
import SelfApproaching.Proof.Balanced
import SelfApproaching.Proof.Exponential
import SelfApproaching.Proof.AspectRatio
import SelfApproaching.Proof.Linf
import SelfApproaching.Proof.LpLower
import SelfApproaching.Proof.LpAspectSharp
import SelfApproaching.Proof.Navigation
import SelfApproaching.Proof.KCenter

/-!
# Statements

The main results. To audit them, read this file and `Definitions.lean`.
-/

namespace SelfApproaching

open Real

/-! ## Euclidean space `ℝ^d` -/

/-- Every SAS in `ℝ^d` has fewer than `11d/2` points. -/
theorem sas_length_lt (d : ℕ) (hd : 1 ≤ d) (ℓ : ℕ) (x : Fin ℓ → ℝ^d)
    (hx : IsSAS dist x) :
    2 * ℓ < 11 * d :=
  Proof.euclidean_sas_length_lt d hd ℓ x hx

/-- `ℝ^d` contains a strict SAS with `⌈9d/4⌉` points. -/
theorem strict_sas (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : Fin ⌈(9 * d : ℝ) / 4⌉₊ → ℝ^d, IsStrictSAS dist x :=
  Proof.euclidean_strict_sas_exists d hd

/-- Any `n ≥ 2` distinct points in `ℝ^d` have a `1/(21.978d - 1.998)`-balanced Voronoi partition. -/
theorem balanced (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ^d)
    (hx : Function.Injective x) :
    HasBalancedVoronoiPartition dist x (1 / (21.978 * d - 1.998)) :=
  Proof.euclidean_balanced d hd n hn x hx

/-- Any `n ≥ 2` distinct points in `ℝ^d` have a `1/(2·3^d)`-balanced Voronoi partition
(better than the previous bound for `d ≤ 3`). -/
theorem balanced_exp (d : ℕ) (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ^d)
    (hx : Function.Injective x) :
    HasBalancedVoronoiPartition dist x (1 / (2 * 3 ^ d)) :=
  Proof.euclidean_balanced_exp d n hn x hx

/-- Some `⌈9d/4⌉` distinct points in `ℝ^d` have only one point on the smaller side of every
two-site Voronoi partition. -/
theorem balance_tight (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : Fin ⌈(9 * d : ℝ) / 4⌉₊ → ℝ^d, Function.Injective x ∧
      ∀ a b, a ≠ b → min (voronoiSide dist x a b).card (voronoiSide dist x b a).card = 1 :=
  Proof.euclidean_balance_tight d hd

/-- Any `n ≥ 1` distinct points in `ℝ^d` carry a directed graph of out-degree at most two on which
opportunistic greedy search gets from any point to any point within
`2⌈(21.978d - 1.998) ln n⌉ + 1` moves. -/
theorem navigable (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ^d)
    (hx : Function.Injective x) :
    ∃ out : Fin n → Finset (Fin n), (∀ v, (out v).card ≤ 2) ∧
      ∀ s q, GreedyReachesWithin dist x out s q (2 * ⌈(21.978 * d - 1.998) * log n⌉₊ + 1) :=
  Proof.euclidean_navigable d hd n hn x hx

/-- For some `c > 0`, every `ℝ^d` contains `n ≥ 2^{cd}` distinct points such that, for every
nonempty set `P` of at most `n/4` of them used as centers, some Voronoi cell has more than `n/4`
points. -/
theorem kcenter :
    ∃ c > (0 : ℝ), ∀ d : ℕ, ∃ n : ℕ, (2 : ℝ) ^ (c * d) ≤ n ∧ ∃ x : Fin n → ℝ^d, Function.Injective x ∧
      ∀ P : Finset (Fin n), P.Nonempty → 4 * P.card ≤ n →
        ∃ p ∈ P, n < 4 * (voronoiCell dist x P p).card :=
  Proof.kcenter_unbalanced

/-! ## Any metric space -/

/-- If every SAS among the `n ≥ 2` distinct points `x` has at most `L` points, then `x` has a
`1/(3.996 L)`-balanced Voronoi partition. -/
theorem metric_balanced {P : Type*} [MetricSpace P] (n : ℕ) (hn : 2 ≤ n) (x : Fin n → P)
    (hx : Function.Injective x) (L : ℕ) (hL : SASLengthLE dist x L) :
    HasBalancedVoronoiPartition dist x (1 / (3.996 * L)) :=
  Proof.balanced_of_sas_bound' n hn x hx L hL

/-- If every SAS among the `n ≥ 1` distinct points `x` has at most `L` points, then they carry a
directed graph of out-degree at most two on which opportunistic greedy search gets from any point
to any point within `2⌈3.996 L ln n⌉ + 1` moves. -/
theorem metric_navigable {P : Type*} [MetricSpace P] (n : ℕ) (hn : 1 ≤ n) (x : Fin n → P)
    (hx : Function.Injective x) (L : ℕ) (hL : SASLengthLE dist x L) :
    ∃ out : Fin n → Finset (Fin n), (∀ v, (out v).card ≤ 2) ∧
      ∀ s q, GreedyReachesWithin dist x out s q (2 * ⌈3.996 * L * log n⌉₊ + 1) :=
  Proof.navigable_of_sas_bound n hn x hx L hL

/-- If every subset of distinct points with aspect ratio at most `1 + ε` has at most `N` points,
then every SAS over subsets with aspect ratio less than `b` must have at most `N ⌈log_{1+ε} b⌉` points. -/
theorem metric_aspect {P : Type*} [MetricSpace P] (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : ∀ (m : ℕ) (y : Fin m → P), Function.Injective y → AspectRatioLE dist y (1 + ε) → m ≤ N)
    (b : ℝ) (hb : 1 < b) (ℓ : ℕ) (x : Fin ℓ → P) (hx : IsSAS dist x)
    (hxb : AspectRatioLT dist x b) :
    ℓ ≤ N * ⌈logb (1 + ε) b⌉₊ :=
  Proof.sas_length_le_of_aspect ε hε N hN b hb ℓ x hx hxb

/-! ## `ℓ_p` distances on `Fin d → ℝ` -/

/-- With the `ℓ_∞` distance there is a strict SAS with `2^d` points. -/
theorem linf_strict_sas (d : ℕ) :
    ∃ x : Fin (2 ^ d) → (Fin d → ℝ), IsStrictSAS linfDist x :=
  Proof.linf_strict_sas_exists d

/-- For `0 < p < ∞`, `p ≠ 2`, there is `c > 0` such that for every `d` there is a strict SAS with at
least `e^{cd}` points for the `ℓ_p` distance. -/
theorem lp_strict_sas (p : ℝ) (hp : 0 < p) (hp2 : p ≠ 2) :
    ∃ c > 0, ∀ d : ℕ, ∃ ℓ : ℕ, exp (c * d) ≤ ℓ ∧
      ∃ x : Fin ℓ → (Fin d → ℝ), IsStrictSAS (lpDist p) x :=
  Proof.lp_strict_sas_exponential p hp hp2

/-- For `1 ≤ p < ∞` there is `C` such that for the `ℓ_p` distance every SAS with aspect ratio less
than `b` has at most `C d^{3q/2} ⌈ln b⌉` points, where `q = (2p+2)/(2p-1)`.
Note that this doesn't state the second half of Theorem 5 from the paper (although the needed part is formalized above). -/
theorem lp_aspect (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ d : ℕ, 1 ≤ d → ∀ b : ℝ, 1 < b → ∀ (ℓ : ℕ) (x : Fin ℓ → (Fin d → ℝ)),
      IsSAS (lpDist p) x → AspectRatioLT (lpDist p) x b →
        ℓ ≤ C * (d : ℝ) ^ (3 / 2 * ((2 * p + 2) / (2 * p - 1))) * ⌈log b⌉₊ :=
  Proof.lp_sas_length_le_of_aspect_sharp p hp

end SelfApproaching

#print axioms SelfApproaching.sas_length_lt
#print axioms SelfApproaching.strict_sas
#print axioms SelfApproaching.balanced
#print axioms SelfApproaching.balanced_exp
#print axioms SelfApproaching.balance_tight
#print axioms SelfApproaching.navigable
#print axioms SelfApproaching.kcenter
#print axioms SelfApproaching.metric_balanced
#print axioms SelfApproaching.metric_navigable
#print axioms SelfApproaching.metric_aspect
#print axioms SelfApproaching.linf_strict_sas
#print axioms SelfApproaching.lp_strict_sas
#print axioms SelfApproaching.lp_aspect
