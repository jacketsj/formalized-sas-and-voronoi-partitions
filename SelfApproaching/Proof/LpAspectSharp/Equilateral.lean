import SelfApproaching.Definitions
import SelfApproaching.Proof.LpAspect.Bucket
import SelfApproaching.Proof.LpAspect.Equilateral

/-!
# From a separable approximation with rate `K^{-p}` to the exponent `3q/2`

Suppose `|a - b|^p` (for `|a - b| ≤ 2`) can be approximated within `A / K^p` by a sum of at most
`B K` products `φ(a) ψ(b)`. Then (Lemma 2 of the paper) a family in `(ℝ^d, ℓ_p)` with aspect
ratio at most `1 + 1/(4ps)`, `s = ⌈A₁ d^{q/2}⌉`, `q = (2p+2)/(2p-1)`, has at most `s²` points,
and by bucketing (Theorem 6) an SAS of aspect ratio `< b` has length `O(d^{3q/2} ⌈ln b⌉)`.
-/

namespace SelfApproaching.Proof.LpAspectSharp

open Real

/-- `(q/2) (2 - 1/p) = 1 + 1/p`. -/
lemma exponent_identity {p : ℝ} (hp : 1 ≤ p) :
    (p + 1) / (2 * p - 1) * (2 - 1 / p) = 1 + 1 / p := by
  have h1 : 2 * p - 1 ≠ 0 := by linarith
  have h2 : p ≠ 0 := by linarith
  rw [div_mul_eq_mul_div, div_eq_iff h1]
  field_simp

/-- Choice of the number of Fourier modes: `K = ⌈X^{1/p}⌉`. -/
lemma ceil_rpow_inv_bounds {p X : ℝ} (hp : 1 ≤ p) (hX : 1 ≤ X) :
    1 ≤ ⌈X ^ (1 / p)⌉₊ ∧ X ≤ (⌈X ^ (1 / p)⌉₊ : ℝ) ^ p ∧
      (⌈X ^ (1 / p)⌉₊ : ℝ) ≤ 2 * X ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 ≤ X ^ (1 / p) := Real.one_le_rpow hX (by positivity)
  refine ⟨Nat.ceil_pos.mpr (by linarith), ?_, ?_⟩
  · calc X = (X ^ (1 / p)) ^ p := by
          rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hp0.ne', Real.rpow_one]
      _ ≤ (⌈X ^ (1 / p)⌉₊ : ℝ) ^ p :=
          Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) hp0.le
  · have := Nat.ceil_lt_add_one (show 0 ≤ X ^ (1 / p) by positivity)
    linarith

/-- The numerical contradiction: if `s ≥ (L + 1) d^{q/2}` and `c ≤ 2 B (2 d A₀ s)^{1/p}`, then
`41 (1 + 2 d c) < 9 s²`. -/
lemma core_ineq {p : ℝ} (hp : 1 ≤ p) {A₀ : ℝ} (hA₀ : 1 ≤ A₀) (B : ℕ) {d s c : ℝ}
    (hd : 1 ≤ d) (hs : (42 + 328 * B * A₀) * d ^ ((p + 1) / (2 * p - 1)) ≤ s)
    (hc : c ≤ 2 * B * (2 * d * A₀ * s) ^ (1 / p)) :
    41 * (1 + d * c * 2) < 9 * s ^ 2 := by
  have hp0 : 0 < p := by linarith
  set e := (p + 1) / (2 * p - 1) with he
  set L : ℝ := 41 + 328 * B * A₀ with hL
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hL1 : 1 ≤ L := by
    have : 0 ≤ (B : ℝ) * A₀ := by positivity
    rw [hL]; linarith
  have hde : 1 ≤ d ^ e := Real.one_le_rpow hd (by
    rw [he]; exact div_nonneg (by linarith) (by linarith))
  have hs' : (L + 1) * d ^ e ≤ s := by rw [hL]; convert hs using 2; ring
  have hs1 : 1 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  set a := s ^ (1 / p) with ha
  set w := d ^ (1 / p) with hw
  have ha1 : 1 ≤ a := Real.one_le_rpow hs1 (by positivity)
  have hw1 : 1 ≤ w := Real.one_le_rpow hd (by positivity)
  have hc₀ : (2 * A₀) ^ (1 / p) ≤ 2 * A₀ := by
    calc (2 * A₀) ^ (1 / p) ≤ (2 * A₀) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith)
            (by rw [div_le_one hp0]; exact hp)
      _ = 2 * A₀ := Real.rpow_one _
  have hX : (2 * d * A₀ * s) ^ (1 / p) = (2 * A₀) ^ (1 / p) * w * a := by
    rw [show 2 * d * A₀ * s = (2 * A₀) * d * s by ring,
      Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow (by positivity) (by linarith)]
  set S := s ^ (2 - 1 / p) with hS
  have hSa : S * a = s ^ 2 := by
    rw [hS, ha, ← Real.rpow_add hs0, show 2 - 1 / p + 1 / p = ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hS2 : (L + 1) * (d * w) ≤ S := by
    have h2p : 1 ≤ 2 - 1 / p := by
      have : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp
      linarith
    calc (L + 1) * (d * w) ≤ (L + 1) ^ (2 - 1 / p) * (d * w) := by
          gcongr
          calc L + 1 = (L + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (L + 1) ^ (2 - 1 / p) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) h2p
      _ = ((L + 1) * d ^ e) ^ (2 - 1 / p) := by
          rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul (by linarith), he,
            exponent_identity hp, Real.rpow_add (by linarith), Real.rpow_one]
      _ ≤ S := Real.rpow_le_rpow (by positivity) hs' (by linarith)
  have hdwa : 1 ≤ d * w * a := by
    have : 1 ≤ d * w := by nlinarith
    nlinarith
  have hc' : c ≤ 2 * B * (2 * A₀ * w * a) := by
    refine hc.trans ?_
    rw [hX]
    have : 0 ≤ w * a := by positivity
    have : (2 * A₀) ^ (1 / p) * w * a ≤ 2 * A₀ * w * a := by
      rw [mul_assoc, mul_assoc (2 * A₀)]; gcongr
    gcongr
  have h1 : 41 * (1 + d * c * 2) ≤ L * (d * w * a) := by
    have : d * c ≤ d * (2 * B * (2 * A₀ * w * a)) := by gcongr
    rw [hL]
    nlinarith
  have h2 : L * (d * w * a) < (L + 1) * (d * w) * a := by nlinarith
  have h3 : (L + 1) * (d * w) * a ≤ S * a := by gcongr
  nlinarith

/-- **Nearly equilateral sets in `ℓ_p`, sharp exponent.** Given a separable approximation of
`|a - b|^p` with rate `K^{-p}`, with `s = ⌈A₁ d^{q/2}⌉`, every family with aspect ratio at most
`1 + 1/(4ps)` has at most `s²` points. -/
theorem nearly_equilateral_card_of_approx (p : ℝ) (hp : 1 ≤ p) (A : ℝ) (hA : 0 < A) (B : ℕ)
    (happrox : ∀ K : ℕ, 1 ≤ K → ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι ≤ B * K ∧ ∃ φ ψ : ι → ℝ → ℝ, ∀ a b : ℝ, |a - b| ≤ 2 →
        |∑ l, φ l a * ψ l b - |a - b| ^ p| ≤ A / (K : ℝ) ^ p)
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (y : Fin m → (Fin d → ℝ))
    (hy : AspectRatioLE (lpDist p) y (1 + 1 / (4 * p *
      (⌈(42 + 328 * B * (A + 1)) * (d : ℝ) ^ ((p + 1) / (2 * p - 1))⌉₊ : ℝ)))) :
    m ≤ ⌈(42 + 328 * B * (A + 1)) * (d : ℝ) ^ ((p + 1) / (2 * p - 1))⌉₊ ^ 2 := by
  have hp0 : 0 < p := by linarith
  set A₀ := A + 1 with hA₀
  have hA₀1 : 1 ≤ A₀ := by linarith
  set e := (p + 1) / (2 * p - 1) with he
  set s := ⌈(42 + 328 * B * A₀) * (d : ℝ) ^ e⌉₊ with hsdef
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hde : 1 ≤ (d : ℝ) ^ e := Real.one_le_rpow hdR (by
    rw [he]; exact div_nonneg (by linarith) (by linarith))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hsge : (42 + 328 * B * A₀) * (d : ℝ) ^ e ≤ s := Nat.le_ceil _
  have hs42 : (42 : ℝ) ≤ s := by
    have : 0 ≤ (B : ℝ) * A₀ := by positivity
    nlinarith
  have hsR : (1 : ℝ) ≤ s := by linarith
  obtain ⟨m₀, hm₀, hy⟩ := hy
  by_contra hlt
  push Not at hlt
  set X : ℝ := 2 * d * A₀ * s with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    have : 1 ≤ (d : ℝ) * A₀ := by nlinarith
    nlinarith
  obtain ⟨hK1, hKp, hK2⟩ := ceil_rpow_inv_bounds hp hX1
  set K := ⌈X ^ (1 / p)⌉₊ with hKdef
  obtain ⟨ι, _, hcard, φ, ψ, hφψ⟩ := happrox K hK1
  set ε : ℝ := 1 / (4 * p * (s : ℝ)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  let y' : Fin (s ^ 2) → Fin d → ℝ := fun i => y (Fin.castLE hlt.le i)
  have hy' : ∀ i j, i ≠ j → m₀ ≤ lpDist p (y' i) (y' j) ∧
      lpDist p (y' i) (y' j) ≤ (1 + ε) * m₀ := fun i j hij =>
    hy (Fin.castLE hlt.le i) (Fin.castLE hlt.le j) (fun h => hij (Fin.castLE_injective _ h))
  have hKp0 : 0 < (K : ℝ) ^ p := by linarith
  have hdE : (d : ℝ) * (A₀ / (K : ℝ) ^ p) ≤ 1 / (2 * s) := by
    calc (d : ℝ) * (A₀ / (K : ℝ) ^ p) = d * A₀ / (K : ℝ) ^ p := by ring
      _ ≤ d * A₀ / X := div_le_div_of_nonneg_left (by positivity) (by linarith) hKp
      _ = 1 / (2 * s) := by
          rw [hXdef]; field_simp
  have hη := LpAspect.one_add_rpow_sub_one_le hp0 hsR
  have hE : (d : ℝ) * (A₀ / (K : ℝ) ^ p) ≤ 1 / 4 := by
    refine hdE.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hm : ((s ^ 2 : ℕ) : ℝ) * ((1 + ε) ^ p - 1 + d * (A₀ / (K : ℝ) ^ p)) ^ 2 ≤ 1 := by
    have hηnn : 0 ≤ (1 + ε) ^ p - 1 := by
      rw [sub_nonneg]; exact Real.one_le_rpow (by linarith) hp0.le
    have hsum : (1 + ε) ^ p - 1 + d * (A₀ / (K : ℝ) ^ p) ≤ 1 / s := by
      have : 1 / (2 * (s : ℝ)) + 1 / (2 * s) = 1 / s := by field_simp; ring
      linarith
    have hnn : 0 ≤ (1 + ε) ^ p - 1 + d * (A₀ / (K : ℝ) ^ p) := by
      have : 0 ≤ (d : ℝ) * (A₀ / (K : ℝ) ^ p) := by positivity
      linarith
    calc ((s ^ 2 : ℕ) : ℝ) * ((1 + ε) ^ p - 1 + d * (A₀ / (K : ℝ) ^ p)) ^ 2
        ≤ (s : ℝ) ^ 2 * (1 / s) ^ 2 := by
          push_cast
          gcongr
      _ = 1 := by field_simp
  have key := LpAspect.nearly_equilateral_core hp y' hm₀ hε0 hε1 hy' φ ψ
    (E := A₀ / (K : ℝ) ^ p)
    (fun a b hab => (hφψ a b hab).trans (div_le_div_of_nonneg_right (by linarith) hKp0.le))
    hE hm
  have hc : (Fintype.card ι : ℝ) ≤ 2 * B * (2 * d * A₀ * s) ^ (1 / p) := by
    have h : (Fintype.card ι : ℝ) ≤ B * K := by exact_mod_cast hcard
    calc (Fintype.card ι : ℝ) ≤ B * K := h
      _ ≤ B * (2 * X ^ (1 / p)) := by gcongr
      _ = 2 * B * (2 * d * A₀ * s) ^ (1 / p) := by rw [hXdef]; ring
  have := core_ineq hp hA₀1 B hdR hsge hc
  push_cast at key
  linarith

/-- **Theorem 5 of the paper from a rate-`p` separable approximation.** -/
theorem lp_sas_length_le_of_aspect_of_approx (p : ℝ) (hp : 1 ≤ p)
    (happrox : ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ K : ℕ, 1 ≤ K → ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι ≤ B * K ∧ ∃ φ ψ : ι → ℝ → ℝ, ∀ a b : ℝ, |a - b| ≤ 2 →
        |∑ l, φ l a * ψ l b - |a - b| ^ p| ≤ A / (K : ℝ) ^ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (b : ℝ), 1 < b → ∀ (ℓ : ℕ) (x : Fin ℓ → (Fin d → ℝ)),
      IsSAS (lpDist p) x → AspectRatioLT (lpDist p) x b →
        (ℓ : ℝ) ≤ C * (d : ℝ) ^ (3 / 2 * ((2 * p + 2) / (2 * p - 1))) * ⌈Real.log b⌉₊ := by
  obtain ⟨A, hA, B, happ⟩ := happrox
  have hp0 : 0 < p := by linarith
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set A₁ : ℝ := 42 + 328 * B * (A + 1) with hA₁
  have hA₁1 : 1 ≤ A₁ := by rw [hA₁]; nlinarith
  refine ⟨(8 * p + 1) * (A₁ + 1) ^ 3, by positivity, fun d hd b hb ℓ x hx hxb => ?_⟩
  set e := (p + 1) / (2 * p - 1) with he
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hde : 1 ≤ (d : ℝ) ^ e := Real.one_le_rpow hdR (by
    rw [he]; exact div_nonneg (by linarith) (by linarith))
  set s := ⌈A₁ * (d : ℝ) ^ e⌉₊ with hsdef
  have hsge : A₁ * (d : ℝ) ^ e ≤ s := Nat.le_ceil _
  have hsR : (1 : ℝ) ≤ s := by nlinarith
  have hsle : (s : ℝ) ≤ (A₁ + 1) * (d : ℝ) ^ e := by
    have := Nat.ceil_lt_add_one (show 0 ≤ A₁ * (d : ℝ) ^ e by positivity)
    nlinarith
  set ε : ℝ := 1 / (4 * p * (s : ℝ)) with hε
  have hε0 : 0 < ε := by positivity
  have hℓ := LpAspect.sas_length_le_of_aspect_symm (lpDist p) (LpAspect.lpDist_symm p) ε hε0
    (s ^ 2) (fun m y _ hy => nearly_equilateral_card_of_approx p hp A hA B happ d hd m y hy)
    b hb ℓ x hx hxb
  -- `log (1 + ε) ≥ ε / 2`
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  have hlog : ε / 2 ≤ Real.log (1 + ε) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h2 : |Real.exp (ε / 2) - 1| ≤ 2 * |ε / 2| :=
      Real.abs_exp_sub_one_le (by rw [abs_of_nonneg (by positivity)]; linarith)
    rw [abs_le, abs_of_nonneg (by positivity)] at h2
    linarith [h2.2]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg hb.le
  have hceil : ⌈Real.logb (1 + ε) b⌉₊ ≤ ⌈8 * p * (s : ℝ)⌉₊ * ⌈Real.log b⌉₊ := by
    apply Nat.ceil_le.mpr
    have hpos : 0 < Real.log (1 + ε) := lt_of_lt_of_le (by positivity) hlog
    calc Real.logb (1 + ε) b = Real.log b / Real.log (1 + ε) := rfl
      _ ≤ Real.log b / (ε / 2) := div_le_div_of_nonneg_left hlogb0 (by positivity) hlog
      _ = 8 * p * s * Real.log b := by rw [hε]; field_simp; ring
      _ ≤ (⌈8 * p * (s : ℝ)⌉₊ : ℝ) * ⌈Real.log b⌉₊ :=
          mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) hlogb0 (by positivity)
      _ = ((⌈8 * p * (s : ℝ)⌉₊ * ⌈Real.log b⌉₊ : ℕ) : ℝ) := by push_cast; ring
  have hℓ' : ℓ ≤ s ^ 2 * (⌈8 * p * (s : ℝ)⌉₊ * ⌈Real.log b⌉₊) :=
    hℓ.trans (Nat.mul_le_mul_left _ hceil)
  have hℓR : (ℓ : ℝ) ≤ (s : ℝ) ^ 2 * ((⌈8 * p * (s : ℝ)⌉₊ : ℝ) * ⌈Real.log b⌉₊) := by
    exact_mod_cast hℓ'
  have hc8 : (⌈8 * p * (s : ℝ)⌉₊ : ℝ) ≤ (8 * p + 1) * s := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 8 * p * (s : ℝ) by positivity)
    nlinarith
  have hexp : (d : ℝ) ^ (3 / 2 * ((2 * p + 2) / (2 * p - 1))) = ((d : ℝ) ^ e) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), he]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hL : (0 : ℝ) ≤ ⌈Real.log b⌉₊ := Nat.cast_nonneg _
  calc (ℓ : ℝ) ≤ (s : ℝ) ^ 2 * ((⌈8 * p * (s : ℝ)⌉₊ : ℝ) * ⌈Real.log b⌉₊) := hℓR
    _ ≤ (s : ℝ) ^ 2 * (((8 * p + 1) * s) * ⌈Real.log b⌉₊) := by gcongr
    _ = (8 * p + 1) * (s : ℝ) ^ 3 * ⌈Real.log b⌉₊ := by ring
    _ ≤ (8 * p + 1) * ((A₁ + 1) * (d : ℝ) ^ e) ^ 3 * ⌈Real.log b⌉₊ := by gcongr
    _ = (8 * p + 1) * (A₁ + 1) ^ 3 * ((d : ℝ) ^ e) ^ (3 : ℕ) * ⌈Real.log b⌉₊ := by ring

end SelfApproaching.Proof.LpAspectSharp
