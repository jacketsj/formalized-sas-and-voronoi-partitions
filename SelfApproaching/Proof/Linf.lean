import SelfApproaching.Definitions

namespace SelfApproaching.Proof

open Real

/-- The sign vectors `{-1, 1}^d`, enumerated by `Fin (2 ^ d)`. -/
private noncomputable def signVec (d : ℕ) (i : Fin (2 ^ d)) : Fin d → ℝ :=
  fun k => if (finFunctionFinEquiv.symm i) k = 0 then 1 else -1

private lemma abs_signVec (d : ℕ) (i : Fin (2 ^ d)) (k : Fin d) : |signVec d i k| = 1 := by
  unfold signVec; split_ifs <;> simp

/-- The radii `r i = 1 / (i + 1)`, strictly decreasing and positive. -/
private noncomputable def rad (d : ℕ) (i : Fin (2 ^ d)) : ℝ := 1 / ((i : ℝ) + 1)

private lemma rad_pos (d : ℕ) (i : Fin (2 ^ d)) : 0 < rad d i := by
  unfold rad; positivity

private lemma rad_lt {d : ℕ} {i j : Fin (2 ^ d)} (h : i < j) : rad d j < rad d i := by
  unfold rad
  have : (i : ℝ) < j := by exact_mod_cast h
  apply one_div_lt_one_div_of_lt <;> [positivity; linarith]

private noncomputable def pt (d : ℕ) (i : Fin (2 ^ d)) : Fin d → ℝ :=
  fun k => rad d i * signVec d i k

private lemma linfDist_self (d : ℕ) (x : Fin d → ℝ) : linfDist x x = 0 := by
  simp [linfDist]

private lemma linfDist_pt {d : ℕ} {a b : Fin (2 ^ d)} (hab : a ≠ b) :
    linfDist (pt d a) (pt d b) = rad d a + rad d b := by
  have hne : finFunctionFinEquiv.symm a ≠ finFunctionFinEquiv.symm b := fun h =>
    hab (finFunctionFinEquiv.symm.injective h)
  obtain ⟨k0, hk0⟩ := Function.ne_iff.mp hne
  have ha := rad_pos d a
  have hb := rad_pos d b
  have hle : ∀ k, |pt d a k - pt d b k| ≤ rad d a + rad d b := by
    intro k
    calc |pt d a k - pt d b k| ≤ |pt d a k| + |pt d b k| := abs_sub _ _
      _ = rad d a + rad d b := by
        simp only [pt, abs_mul, abs_signVec, abs_of_pos ha, abs_of_pos hb, mul_one]
  have hk : |pt d a k0 - pt d b k0| = rad d a + rad d b := by
    simp only [pt, signVec]
    have hfin : ∀ u v : Fin 2, u ≠ v → (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0) := by decide
    rcases hfin _ _ hk0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2, abs_of_pos (by linarith)]; ring
    · rw [if_neg h1, if_pos h2, abs_of_neg (by linarith)]; ring
  haveI : Nonempty (Fin d) := ⟨k0⟩
  unfold linfDist
  apply le_antisymm (ciSup_le hle)
  rw [← hk]
  exact le_ciSup (f := fun k => |pt d a k - pt d b k|) (Set.finite_range _).bddAbove k0

theorem linf_strict_sas_exists (d : ℕ) :
    ∃ x : Fin (2 ^ d) → (Fin d → ℝ), IsStrictSAS linfDist x := by
  refine ⟨pt d, fun i j k hij hki => ?_⟩
  rw [linfDist_pt hki]
  have hlt := rad_lt hij
  by_cases hkj : k = j
  · subst hkj
    rw [linfDist_self]
    linarith [rad_pos d i, rad_pos d k]
  · rw [linfDist_pt hkj]
    linarith

end SelfApproaching.Proof
