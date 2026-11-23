import SelfApproaching.Definitions

namespace SelfApproaching.Proof

open Real Finset

/-- The number of positions in which two words agree. -/
private def agree {n q : ℕ} (u v : Fin n → Fin q) : ℕ :=
  (Finset.univ.filter fun b => u b = v b).card

private lemma agree_self {n q : ℕ} (u : Fin n → Fin q) : agree u u = n := by
  simp [agree]

private lemma agree_comm {n q : ℕ} (u v : Fin n → Fin q) : agree u v = agree v u := by
  simp only [agree, eq_comm]

/-- Exponential moment of the number of agreements with a fixed word. -/
private lemma sum_exp_agree (n q : ℕ) (hq : 1 ≤ q) (σ : ℝ) (s : Fin n → Fin q) :
    ∑ w : Fin n → Fin q, exp (σ * agree w s) = (exp σ + ((q : ℝ) - 1)) ^ n := by
  have h1 : ∀ w : Fin n → Fin q,
      exp (σ * agree w s) = ∏ b, (fun b a => if a = s b then exp σ else 1) b (w b) := by
    intro w
    rw [agree, Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun b _ => ?_
    by_cases h : w b = s b <;> simp [h]
  have h2 : ∀ c : Fin q, ∑ a : Fin q, (if a = c then exp σ else 1) = exp σ + ((q : ℝ) - 1) := by
    intro c
    rw [Fintype.sum_eq_add_sum_compl c, if_pos rfl]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun a ha => by
      rw [if_neg (by simpa using ha)])]
    simp [Finset.card_compl, Nat.cast_sub hq]
  simp_rw [h1]
  rw [show (∑ w : Fin n → Fin q, ∏ b, if w b = s b then exp σ else 1) =
      ∏ b, ∑ a : Fin q, (if a = s b then exp σ else 1) from
      (Fintype.prod_sum (fun b a => if a = s b then exp σ else 1)).symm]
  simp [h2]

private lemma exists_code_aux (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ : 0 < δ) (hδ1 : 1 / q + δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ N : ℕ, exp (c * n) ≤ N ∧ ∃ C : Fin N → (Fin n → Fin q),
      ∀ i j, i ≠ j →
        ((Finset.univ.filter fun b => C i b = C j b).card : ℝ) ≤ (1 / q + δ) * n := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  set θ : ℝ := 1 / q + δ with hθ
  set σ : ℝ := min (q * δ / 2) 1 with hσdef
  have hσ : 0 < σ := lt_min (by positivity) one_pos
  have hσ1 : σ ≤ 1 := min_le_right _ _
  have hσ2 : σ ≤ q * δ / 2 := min_le_left _ _
  set E : ℝ := exp σ + ((q : ℝ) - 1) with hE
  have hEpos : 0 < E := by have := exp_pos σ; linarith
  set ρ : ℝ := q * exp (σ * θ) / E with hρdef
  have hρ : 1 < ρ := by
    rw [hρdef, lt_div_iff₀ hEpos, one_mul]
    have h1 : 1 + σ * θ ≤ exp (σ * θ) := by linarith [add_one_le_exp (σ * θ)]
    have h2 : exp σ ≤ 1 + σ + σ ^ 2 := by
      have := abs_exp_sub_one_sub_id_le (x := σ) (by rw [abs_of_pos hσ]; exact hσ1)
      linarith [le_abs_self (exp σ - 1 - σ)]
    have h3 : (q : ℝ) * θ = 1 + q * δ := by rw [hθ]; field_simp
    have h4 : σ ^ 2 < σ * (q * δ) := by nlinarith
    nlinarith
  refine ⟨log ρ, log_pos hρ, fun n => ?_⟩
  set t : ℝ := θ * n with ht
  have htn : t ≤ n := by rw [ht]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let good : Finset (Fin n → Fin q) → Prop :=
    fun S => ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (agree u v : ℝ) ≤ t
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset (Fin n → Fin q))).filter good) Finset.card
    ⟨∅, by simp [good]⟩
  have hSgood : good S := (Finset.mem_filter.mp hS).2
  -- every word is close to some codeword
  have hcov : ∀ w, ∃ s ∈ S, t ≤ agree w s := by
    intro w
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hw : w ∉ S := fun hw => by
      have := hcon w hw
      rw [agree_self] at this
      linarith
    have hgood : good (insert w S) := by
      intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with hu' | hu' <;>
        rcases Finset.mem_insert.mp hv with hv' | hv'
      · exact absurd (hu'.trans hv'.symm) huv
      · rw [hu']; exact (hcon v hv').le
      · rw [hv', agree_comm]; exact (hcon u hu').le
      · exact hSgood u hu' v hv' huv
    have := hmax (insert w S) (by simp [hgood])
    rw [Finset.card_insert_of_notMem hw] at this
    omega
  -- counting
  have key : (q : ℝ) ^ n ≤ S.card * (exp (-(σ * t)) * E ^ n) := by
    calc (q : ℝ) ^ n = ∑ _w : Fin n → Fin q, (1 : ℝ) := by simp
      _ ≤ ∑ w : Fin n → Fin q, ∑ s ∈ S, exp (σ * (agree w s - t)) := by
        refine Finset.sum_le_sum fun w _ => ?_
        obtain ⟨s, hs, hts⟩ := hcov w
        calc (1 : ℝ) ≤ exp (σ * (agree w s - t)) :=
              one_le_exp (mul_nonneg hσ.le (by linarith))
          _ ≤ _ := Finset.single_le_sum (f := fun s => exp (σ * (agree w s - t)))
              (fun _ _ => (exp_pos _).le) hs
      _ = ∑ s ∈ S, exp (-(σ * t)) * ∑ w : Fin n → Fin q, exp (σ * agree w s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← exp_add]; ring_nf
      _ = S.card * (exp (-(σ * t)) * E ^ n) := by
        simp [sum_exp_agree n q (by omega), hE]
  refine ⟨S.card, ?_, fun i => (S.equivFin.symm i : Fin n → Fin q), fun i j hij => ?_⟩
  · rw [mul_comm, exp_nat_mul, exp_log (by linarith), hρdef, div_pow, mul_pow,
      div_le_iff₀ (pow_pos hEpos n), ← exp_nat_mul]
    have h5 : exp (n * (σ * θ)) = exp (σ * t) := by rw [ht]; ring_nf
    rw [h5]
    have h6 : exp (-(σ * t)) * exp (σ * t) = 1 := by rw [← exp_add]; simp
    calc (q : ℝ) ^ n * exp (σ * t) ≤ S.card * (exp (-(σ * t)) * E ^ n) * exp (σ * t) :=
          mul_le_mul_of_nonneg_right key (exp_pos _).le
      _ = S.card * E ^ n * (exp (-(σ * t)) * exp (σ * t)) := by ring
      _ = S.card * E ^ n := by rw [h6, mul_one]
  · have hne : (S.equivFin.symm i : Fin n → Fin q) ≠ S.equivFin.symm j := fun h =>
      hij (S.equivFin.symm.injective (Subtype.ext h))
    exact hSgood _ (S.equivFin.symm i).2 _ (S.equivFin.symm j).2 hne

/-- Gilbert–Varshamov: for every alphabet size `q ≥ 2` and slack `δ > 0` there are exponentially
many words of length `n` over `Fin q`, any two of which agree in at most `(1/q + δ) n`
positions. -/
theorem exists_code (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ N : ℕ, exp (c * n) ≤ N ∧ ∃ C : Fin N → (Fin n → Fin q),
      ∀ i j, i ≠ j → ((Finset.univ.filter fun b => C i b = C j b).card : ℝ) ≤ (1 / q + δ) * n := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hinv : 1 / (q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
  have hpos : 0 < (1 - 1 / (q : ℝ)) / 2 := by linarith
  obtain ⟨c, hc, h⟩ := exists_code_aux q hq (min δ ((1 - 1 / q) / 2)) (lt_min hδ hpos)
    (by linarith [min_le_right δ ((1 - 1 / (q : ℝ)) / 2)])
  refine ⟨c, hc, fun n => ?_⟩
  obtain ⟨N, hN, C, hC⟩ := h n
  refine ⟨N, hN, C, fun i j hij => (hC i j hij).trans ?_⟩
  gcongr
  exact min_le_left _ _

end SelfApproaching.Proof
