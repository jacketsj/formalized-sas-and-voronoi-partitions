import Mathlib
import SelfApproaching.Definitions
import SelfApproaching.Proof.LpAspect.Rank
import SelfApproaching.Proof.LpAspect.Fourier

/-!
# Nearly equilateral point sets in `ℓ_p` (Lemma 2 of the paper, with a weaker exponent)

Let `y₀, …, y_{m-1} ∈ ℝ^d` have all pairwise `ℓ_p` distances in `[m₀, (1 + ε) m₀]`. Put
`aᵢ = yᵢ / m₀` and `Mᵢⱼ = 1 - ∑_r |aᵢ[r] - aⱼ[r]|^p`, so `Mᵢᵢ = 1` and `|Mᵢⱼ| ≤ (1 + ε)^p - 1`
for `i ≠ j`. Replacing `|s - t|^p` by a separable approximation `∑_l φ_l(s) ψ_l(t)` (symmetrized)
gives a symmetric matrix `M̂` close to `M` entrywise, of rank `≤ 1 + 2 d |ι|`. The bound
`(tr M̂)² ≤ rank M̂ · ‖M̂‖_F²` then bounds `m`.
-/

namespace SelfApproaching.Proof.LpAspect

open Real Matrix

lemma lpDist_rpow {d : ℕ} {p : ℝ} (hp : 0 < p) (x y : Fin d → ℝ) :
    lpDist p x y ^ p = ∑ i, |x i - y i| ^ p := by
  unfold lpDist
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _),
    one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

lemma lpDist_nonneg {d : ℕ} (p : ℝ) (x y : Fin d → ℝ) : 0 ≤ lpDist p x y :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _

lemma lpDist_symm {d : ℕ} (p : ℝ) (x y : Fin d → ℝ) : lpDist p x y = lpDist p y x := by
  unfold lpDist
  simp_rw [abs_sub_comm (x _)]

/-- The core counting bound for nearly equilateral sets. -/
theorem nearly_equilateral_core {d m : ℕ} {p : ℝ} (hp : 1 ≤ p) (y : Fin m → Fin d → ℝ)
    {m₀ ε : ℝ} (hm₀ : 0 < m₀) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hy : ∀ i j, i ≠ j → m₀ ≤ lpDist p (y i) (y j) ∧ lpDist p (y i) (y j) ≤ (1 + ε) * m₀)
    {ι : Type} [Fintype ι] (φ ψ : ι → ℝ → ℝ) {E : ℝ}
    (hφψ : ∀ a b : ℝ, |a - b| ≤ 2 → |∑ l, φ l a * ψ l b - |a - b| ^ p| ≤ E)
    (hE : d * E ≤ 1 / 4) (hm : (m : ℝ) * ((1 + ε) ^ p - 1 + d * E) ^ 2 ≤ 1) :
    9 * (m : ℝ) ≤ 41 * (1 + d * Fintype.card ι * 2) := by
  have hp0 : 0 < p := by linarith
  set a : Fin m → Fin d → ℝ := fun i r => y i r / m₀ with ha
  -- the normalized `p`-th powers of distances
  have hsum_eq : ∀ i j, ∑ r, |a i r - a j r| ^ p = (lpDist p (y i) (y j) / m₀) ^ p := by
    intro i j
    rw [Real.div_rpow (lpDist_nonneg _ _ _) hm₀.le, lpDist_rpow hp0, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ha, ← sub_div, abs_div, abs_of_pos hm₀, Real.div_rpow (abs_nonneg _) hm₀.le]
  have hsum_off : ∀ i j, i ≠ j →
      1 ≤ ∑ r, |a i r - a j r| ^ p ∧ ∑ r, |a i r - a j r| ^ p ≤ (1 + ε) ^ p := by
    intro i j hij
    obtain ⟨h1, h2⟩ := hy i j hij
    rw [hsum_eq]
    constructor
    · exact Real.one_le_rpow (by rw [le_div_iff₀ hm₀]; linarith) hp0.le
    · exact Real.rpow_le_rpow (div_nonneg (lpDist_nonneg _ _ _) hm₀.le)
        (by rw [div_le_iff₀ hm₀]; linarith) hp0.le
  have hcoord : ∀ i j r, |a i r - a j r| ≤ 2 := by
    intro i j r
    by_cases hij : i = j
    · subst hij; simp
    have h1 : |a i r - a j r| ^ p ≤ (1 + ε) ^ p :=
      le_trans (Finset.single_le_sum (f := fun r => |a i r - a j r| ^ p)
        (fun r _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ r)) (hsum_off i j hij).2
    rw [Real.rpow_le_rpow_iff (abs_nonneg _) (by linarith) hp0] at h1
    linarith
  set H : Fin d → Fin m → Fin m → ℝ := fun r i j => ∑ l, φ l (a i r) * ψ l (a j r) with hH
  have hHb : ∀ r i j, |H r i j - |a i r - a j r| ^ p| ≤ E := fun r i j => hφψ _ _ (hcoord i j r)
  set Mh : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => 1 - ∑ r, (H r i j + H r j i) / 2
    with hMh
  set η : ℝ := (1 + ε) ^ p - 1 with hη
  have hdiff : ∀ i j, |Mh i j - (1 - ∑ r, |a i r - a j r| ^ p)| ≤ d * E := by
    intro i j
    have : Mh i j - (1 - ∑ r, |a i r - a j r| ^ p) =
        ∑ r, ((|a i r - a j r| ^ p - H r i j) + (|a j r - a i r| ^ p - H r j i)) / 2 := by
      simp only [hMh, Matrix.of_apply, abs_sub_comm (a j _) (a i _)]
      rw [show (1 - ∑ r, (H r i j + H r j i) / 2 - (1 - ∑ r, |a i r - a j r| ^ p)) =
        ∑ r, |a i r - a j r| ^ p - ∑ r, (H r i j + H r j i) / 2 by ring, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this]
    calc |∑ r, ((|a i r - a j r| ^ p - H r i j) + (|a j r - a i r| ^ p - H r j i)) / 2|
        ≤ ∑ r : Fin d, |((|a i r - a j r| ^ p - H r i j) + (|a j r - a i r| ^ p - H r j i)) / 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin d, E := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
          have h1 := hHb r i j
          have h2 := hHb r j i
          rw [abs_sub_comm] at h1 h2
          calc _ ≤ |(|a i r - a j r| ^ p - H r i j)| + |(|a j r - a i r| ^ p - H r j i)| :=
                abs_add_le _ _
            _ ≤ E + E := add_le_add h1 h2
            _ = E * 2 := by ring
      _ = d * E := by simp
  have hdiag : ∀ i, 1 - d * E ≤ Mh i i ∧ Mh i i ≤ 1 + d * E := by
    intro i
    have h := hdiff i i
    simp only [sub_self, abs_zero, Real.zero_rpow hp0.ne', Finset.sum_const_zero, sub_zero] at h
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hoff : ∀ i j, i ≠ j → |Mh i j| ≤ η + d * E := by
    intro i j hij
    have h := hdiff i j
    obtain ⟨h1, h2⟩ := hsum_off i j hij
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have hEnn : 0 ≤ E := le_trans (abs_nonneg _) (hφψ 0 0 (by simp))
  have hηnn : 0 ≤ η := by
    rw [hη, sub_nonneg]; exact Real.one_le_rpow (by linarith) hp0.le
  -- symmetric
  have hsymm : Mh.IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial, hMh, Matrix.of_apply]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  -- trace
  have htr : 3 / 4 * (m : ℝ) ≤ Mh.trace := by
    rw [Matrix.trace]
    calc 3 / 4 * (m : ℝ) = ∑ _i : Fin m, (3 / 4 : ℝ) := by simp; ring
      _ ≤ ∑ i, Mh.diag i := Finset.sum_le_sum fun i _ => by
          simp only [Matrix.diag]; linarith [(hdiag i).1]
  -- Frobenius norm
  have hfrob : ∑ i, ∑ j, Mh i j ^ 2 ≤ 41 / 16 * (m : ℝ) := by
    have hent : ∀ i j, Mh i j ^ 2 ≤ (if i = j then 25 / 16 else 0) + (η + d * E) ^ 2 := by
      intro i j
      split_ifs with hij
      · subst hij
        obtain ⟨h1, h2⟩ := hdiag i
        have : Mh i i ^ 2 ≤ 25 / 16 := by nlinarith
        nlinarith [sq_nonneg (η + d * E)]
      · rw [zero_add, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hoff i j hij) 2
    calc ∑ i, ∑ j, Mh i j ^ 2 ≤ ∑ i : Fin m, ∑ j : Fin m,
          ((if i = j then 25 / 16 else 0) + (η + d * E) ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
      _ = 25 / 16 * m + m * (m * (η + d * E) ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
          ring
      _ ≤ 25 / 16 * m + m * 1 := by gcongr
      _ = 41 / 16 * (m : ℝ) := by ring
  -- rank
  have hrank : (Mh.rank : ℝ) ≤ 1 + d * Fintype.card ι * 2 := by
    let Φ : Unit ⊕ (Fin d × ι × Bool) → Fin m → ℝ := fun k i =>
      match k with
      | Sum.inl _ => 1
      | Sum.inr (r, l, true) => -(φ l (a i r) / 2)
      | Sum.inr (r, l, false) => -(ψ l (a i r) / 2)
    let Ψ : Unit ⊕ (Fin d × ι × Bool) → Fin m → ℝ := fun k j =>
      match k with
      | Sum.inl _ => 1
      | Sum.inr (r, l, true) => ψ l (a j r)
      | Sum.inr (r, l, false) => φ l (a j r)
    have h := rank_le_of_separable Mh Φ Ψ (fun i j => by
      simp only [hMh, Matrix.of_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton, Φ, Ψ, hH]
      rw [sub_eq_add_neg, one_mul, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring)
    have hc : Fintype.card (Unit ⊕ (Fin d × ι × Bool)) = 1 + d * Fintype.card ι * 2 := by
      simp [Fintype.card_sum, Fintype.card_prod, mul_assoc]
    rw [hc] at h
    exact_mod_cast h
  have key := trace_sq_le_rank_mul_sum_sq Mh hsymm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (3 / 4 * (m : ℝ)) ^ 2 ≤ Mh.trace ^ 2 := pow_le_pow_left₀ (by positivity) htr 2
  have h2 : Mh.trace ^ 2 ≤ (1 + d * Fintype.card ι * 2) * (41 / 16 * (m : ℝ)) :=
    key.trans (mul_le_mul hrank hfrob (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity))
  rcases eq_or_lt_of_le hm0 with h0 | h0
  · rw [← h0]
    have : (0 : ℝ) ≤ d * Fintype.card ι * 2 := by positivity
    linarith
  · nlinarith

/-- `(1 + 1/(4 p s))^p - 1 ≤ 1/(2s)`. -/
lemma one_add_rpow_sub_one_le {p s : ℝ} (hp : 0 < p) (hs : 1 ≤ s) :
    (1 + 1 / (4 * p * s)) ^ p - 1 ≤ 1 / (2 * s) := by
  have hs0 : 0 < s := by linarith
  have hε : 0 ≤ 1 / (4 * p * s) := by positivity
  have h1 : (1 + 1 / (4 * p * s)) ^ p ≤ Real.exp (1 / (4 * p * s) * p) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp (1 / (4 * p * s))])
      hp.le
  have he : 1 / (4 * p * s) * p = 1 / (4 * s) := by field_simp
  rw [he] at h1
  have h2 : |Real.exp (1 / (4 * s)) - 1| ≤ 2 * |1 / (4 * s)| :=
    Real.abs_exp_sub_one_le (by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith)
  rw [abs_le] at h2
  rw [abs_of_nonneg (by positivity)] at h2
  have : 2 * (1 / (4 * s)) = 1 / (2 * s) := by field_simp; ring
  linarith [h2.2]

/-- **Nearly equilateral sets in `ℓ_p`.** There is `A` such that in `(ℝ^d, ℓ_p)`, with
`s = 170 A d²`, every family with aspect ratio at most `1 + 1/(4ps)` has at most `s²` points. -/
theorem nearly_equilateral_card (p : ℝ) (hp : 1 ≤ p) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ d : ℕ, 1 ≤ d → ∀ (m : ℕ) (y : Fin m → (Fin d → ℝ)),
      AspectRatioLE (lpDist p) y (1 + 1 / (4 * p * ((170 * A * d ^ 2 : ℕ) : ℝ))) →
        m ≤ (170 * A * d ^ 2) ^ 2 := by
  obtain ⟨A₀, hA₀, happrox⟩ := exists_separable_approx p hp
  have hp0 : 0 < p := by linarith
  refine ⟨⌈A₀⌉₊, Nat.ceil_pos.mpr hA₀, fun d hd m y hy => ?_⟩
  set A := ⌈A₀⌉₊ with hAdef
  have hA : 1 ≤ A := Nat.ceil_pos.mpr hA₀
  set s := 170 * A * d ^ 2 with hsdef
  have hs : 1 ≤ s := by
    have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
    rw [hsdef]; nlinarith
  obtain ⟨m₀, hm₀, hy⟩ := hy
  by_contra hlt
  push Not at hlt
  set K := 2 * d * A * s with hKdef
  have hK : 1 ≤ K := by
    rw [hKdef]
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hd) hA) hs
    omega
  obtain ⟨ι, _, hcard, φ, ψ, hφψ⟩ := happrox K hK
  set ε : ℝ := 1 / (4 * p * (s : ℝ)) with hε
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hKR : (K : ℝ) = 2 * d * A * s := by rw [hKdef]; push_cast; ring
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  let y' : Fin (s ^ 2) → Fin d → ℝ := fun i => y (Fin.castLE hlt.le i)
  have hy' : ∀ i j, i ≠ j → m₀ ≤ lpDist p (y' i) (y' j) ∧
      lpDist p (y' i) (y' j) ≤ (1 + ε) * m₀ := by
    intro i j hij
    have := hy (Fin.castLE hlt.le i) (Fin.castLE hlt.le j)
      (fun h => hij (Fin.castLE_injective _ h))
    refine ⟨this.1, ?_⟩
    exact this.2
  have hdE : (d : ℝ) * (A₀ / K) ≤ 1 / (2 * s) := by
    rw [hKR, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : A₀ ≤ A := Nat.le_ceil A₀
    have h0 : (0 : ℝ) ≤ d := by positivity
    have : (d : ℝ) * A₀ * (2 * s) ≤ d * A * (2 * s) := by gcongr
    nlinarith
  have hη := one_add_rpow_sub_one_le hp0 hsR
  have hE : (d : ℝ) * (A₀ / K) ≤ 1 / 4 := by
    refine hdE.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (170 : ℝ) ≤ s := by
      rw [hsdef]; push_cast
      have : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hm : ((s ^ 2 : ℕ) : ℝ) * ((1 + ε) ^ p - 1 + d * (A₀ / K)) ^ 2 ≤ 1 := by
    have hηnn : 0 ≤ (1 + ε) ^ p - 1 := by
      rw [sub_nonneg]; exact Real.one_le_rpow (by linarith) hp0.le
    have hsum : (1 + ε) ^ p - 1 + d * (A₀ / K) ≤ 1 / s := by
      have : 1 / (2 * (s : ℝ)) + 1 / (2 * s) = 1 / s := by field_simp; ring
      linarith
    have hnn : 0 ≤ (1 + ε) ^ p - 1 + d * (A₀ / K) := by
      have : 0 ≤ (d : ℝ) * (A₀ / K) := by positivity
      linarith
    calc ((s ^ 2 : ℕ) : ℝ) * ((1 + ε) ^ p - 1 + d * (A₀ / K)) ^ 2
        ≤ (s : ℝ) ^ 2 * (1 / s) ^ 2 := by
          push_cast
          gcongr
      _ = 1 := by field_simp
  have key := nearly_equilateral_core hp y' hm₀ hε0 hε1 hy' φ ψ (E := A₀ / K)
    (fun a b hab => by simpa using hφψ a b hab) hE hm
  have hcR : (Fintype.card ι : ℝ) ≤ 6 * K := by exact_mod_cast hcard
  rw [hKR] at hcR
  have hX : (1 : ℝ) ≤ (d : ℝ) ^ 2 * A * s := by
    have : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ (d : ℝ) ^ 2 * A := by nlinarith
    nlinarith
  have hs2 : ((s ^ 2 : ℕ) : ℝ) = 170 * ((d : ℝ) ^ 2 * A * s) := by
    rw [hsdef]; push_cast; ring
  rw [hs2] at key
  have : (d : ℝ) * Fintype.card ι * 2 ≤ 24 * ((d : ℝ) ^ 2 * A * s) := by
    have h0 : (0 : ℝ) ≤ d := by positivity
    calc (d : ℝ) * Fintype.card ι * 2 ≤ d * (6 * (2 * d * A * s)) * 2 := by gcongr
      _ = 24 * ((d : ℝ) ^ 2 * A * s) := by ring
  nlinarith

end SelfApproaching.Proof.LpAspect
