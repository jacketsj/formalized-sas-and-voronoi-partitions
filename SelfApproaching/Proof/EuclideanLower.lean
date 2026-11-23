import SelfApproaching.Definitions
import SelfApproaching.Proof.EuclideanLower.Construction

namespace SelfApproaching.Proof

open Real EuclideanLowerAux

theorem euclidean_strict_sas_exists (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : Fin ⌈(9 * d : ℝ) / 4⌉₊ → EuclideanSpace ℝ (Fin d), IsStrictSAS dist x := by
  set k := (d - 1) / 4 with hk
  set r := d - 4 * k with hr
  have hr1 : 1 ≤ r := by omega
  have hr4 : r ≤ 4 := by omega
  have hdk : d = 4 * k + r := by omega
  have iter : ∀ i ≤ k, ∃ x : ℕ → EuclideanSpace ℝ (Fin d), Inv d x (r + 5 * i) (r + 4 * i) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨initSeq d r, by simpa using init_inv r (by omega)⟩
    | succ i ih =>
      intro hi
      obtain ⟨x, hx⟩ := ih (by omega)
      obtain ⟨x', hx'⟩ := step (by omega) (by omega) hx
      rw [show r + 5 * (i + 1) = r + 5 * i + 5 by ring, show r + 4 * (i + 1) = r + 4 * i + 4 by ring]
      exact ⟨x', hx'⟩
  obtain ⟨x, hx⟩ := iter k le_rfl
  obtain ⟨y, hy⟩ := final hx
  have hceil : ⌈(9 * d : ℝ) / 4⌉₊ = r + 5 * k + d + 1 := by
    rw [Nat.ceil_eq_iff (by omega), show r + 5 * k + d + 1 - 1 = r + 5 * k + d by omega]
    have h1 : (d : ℝ) = 4 * k + r := by exact_mod_cast hdk
    have h2 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have h3 : (r : ℝ) ≤ 4 := by exact_mod_cast hr4
    push_cast
    constructor <;> linarith
  rw [hceil]
  exact ⟨fun i => y i, fun i j l hij hli => hy i j l hij j.2 l.2 (fun h => hli (Fin.ext h))⟩

end SelfApproaching.Proof
