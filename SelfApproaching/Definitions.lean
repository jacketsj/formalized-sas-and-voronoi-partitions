import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Definitions

Everything that `Statements.lean` uses beyond Mathlib.

* Point sets are families `x : Fin n → α`; the index `k` of the point `x k` is its *ID*.
* A distance is any function `D : α → α → ℝ`. The statements use `dist` of a metric space
  (in particular `ℝ^d`, Euclidean space) and the `ℓ_p` distances `lpDist`, `linfDist` on
  `Fin d → ℝ`.
-/

namespace SelfApproaching

noncomputable section

variable {α : Type*} {n : ℕ}

/-- `ℝ^d` is `d`-dimensional Euclidean space (its `dist` is the Euclidean distance). -/
scoped notation "ℝ^" d:max => EuclideanSpace ℝ (Fin d)

/-! ## Self-approaching sequences -/

/-- `x 0, …, x (ℓ-1)` is a *self-approaching sequence* (SAS): the points are distinct, and seen
from any point `x k` the other points get closer along the sequence. -/
def IsSAS (D : α → α → ℝ) {ℓ : ℕ} (x : Fin ℓ → α) : Prop :=
  Function.Injective x ∧ ∀ i j k : Fin ℓ, i < j → k ≠ i → D (x k) (x j) ≤ D (x k) (x i)

/-- A *strict* SAS: as `IsSAS`, with `<` in place of `≤`. Distinctness is automatic in this case. -/
def IsStrictSAS (D : α → α → ℝ) {ℓ : ℕ} (x : Fin ℓ → α) : Prop :=
  ∀ i j k : Fin ℓ, i < j → k ≠ i → D (x k) (x j) < D (x k) (x i)

/-- L_X definition: Every SAS whose points are among the points of `x` has at most `L` points. -/
def SASLengthLE (D : α → α → ℝ) (x : Fin n → α) (L : ℕ) : Prop :=
  ∀ (ℓ : ℕ) (y : Fin ℓ → α), IsSAS D y → (∀ i, y i ∈ Set.range x) → ℓ ≤ L /-! Set.range gets the range of a function -/

/-! ## Voronoi partitions -/

/-- The point `y` *prefers* the site `x a` to the site `x b`: it is closer to `x a`, with ties
broken by ID. (Note that α and a are different characters, but can look similar in some fonts.) -/
abbrev Prefers (D : α → α → ℝ) (x : Fin n → α) (y : α) (a b : Fin n) : Prop :=
  D y (x a) < D y (x b) ∨ (D y (x a) = D y (x b) ∧ a < b)

/-- The two-site Voronoi cell `S(a, b)`: the IDs of the points preferring `x a` to `x b`.
For `a ≠ b`, `voronoiSide D x a b` and `voronoiSide D x b a` partition all IDs. -/
def voronoiSide (D : α → α → ℝ) (x : Fin n → α) (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => Prefers D x (x k) a b

/-- Some two distinct sites each get at least a `β` fraction of the `n` points. -/
def HasBalancedVoronoiPartition (D : α → α → ℝ) (x : Fin n → α) (β : ℝ) : Prop :=
  ∃ a b, a ≠ b ∧ β * n ≤ (voronoiSide D x a b).card ∧ β * n ≤ (voronoiSide D x b a).card

/-- The (strict) Voronoi cell of the center `p` among the centers `P`: the IDs of the points strictly
closer to `x p` than to every other center. This can be strict since it is only used to state a lower bound. -/
def voronoiCell (D : α → α → ℝ) (x : Fin n → α) (P : Finset (Fin n)) (p : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun k => ∀ q ∈ P, q ≠ p → D (x k) (x p) < D (x k) (x q)

/-! ## Opportunistic greedy search -/

/-- One move of opportunistic greedy search for the target `q` in the directed graph with
out-neighbour sets `out`: from `v ≠ q`, move to the out-neighbour `w` that `x q` prefers to all
other out-neighbours (even if `w` is farther from `x q` than `v`). This move is unique due to tiebreaking. -/
def IsGreedyMove (D : α → α → ℝ) (x : Fin n → α) (out : Fin n → Finset (Fin n))
    (q v w : Fin n) : Prop :=
  v ≠ q ∧ w ∈ out v ∧ ∀ w' ∈ out v, w' ≠ w → Prefers D x (x q) w w'

/-- Greedy search from `s` reaches the target `q` within `T` moves. -/
def GreedyReachesWithin (D : α → α → ℝ) (x : Fin n → α) (out : Fin n → Finset (Fin n))
    (s q : Fin n) (T : ℕ) : Prop :=
  ∃ t ≤ T, ∃ v : Fin (t + 1) → Fin n, v 0 = s ∧ v (Fin.last t) = q ∧
    ∀ i : Fin t, IsGreedyMove D x out q (v i.castSucc) (v i.succ) /-! castSucc does not change the value, only the proof of the upper bound allowing it to be a Fin k type -/

/-! ## Aspect ratio -/

/-- All pairwise distances lie in `[m, b m)` for some `m > 0` (aspect ratio less than `b`). -/
def AspectRatioLT (D : α → α → ℝ) {ℓ : ℕ} (x : Fin ℓ → α) (b : ℝ) : Prop :=
  ∃ m > 0, ∀ i j : Fin ℓ, i ≠ j → m ≤ D (x i) (x j) ∧ D (x i) (x j) < b * m

/-- All pairwise distances lie in `[m, b m]` for some `m > 0` (aspect ratio at most `b`).
Only change compared to above is closed vs half-open interval. -/
def AspectRatioLE (D : α → α → ℝ) {ℓ : ℕ} (x : Fin ℓ → α) (b : ℝ) : Prop :=
  ∃ m > 0, ∀ i j : Fin ℓ, i ≠ j → m ≤ D (x i) (x j) ∧ D (x i) (x j) ≤ b * m 

/-! ## `ℓ_p` distances on `Fin d → ℝ` -/

/-- The `ℓ_p` distance `(∑ᵢ |xᵢ - yᵢ|^p)^(1/p)`. -/
def lpDist (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ i, |x i - y i| ^ p) ^ (1 / p)

/-- The `ℓ_∞` distance `maxᵢ |xᵢ - yᵢ|`. -/
def linfDist {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ⨆ i, |x i - y i|

end

end SelfApproaching
