import SelfApproaching.Definitions
import SelfApproaching.Proof.Codes
import SelfApproaching.Proof.LpSmall
import SelfApproaching.Proof.LpLarge

namespace SelfApproaching.Proof

open Real

theorem lp_strict_sas_exponential (p : ℝ) (hp : 0 < p) (hp2 : p ≠ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, ∃ ℓ : ℕ, exp (c * d) ≤ ℓ ∧
      ∃ x : Fin ℓ → (Fin d → ℝ), IsStrictSAS (lpDist p) x := by
  rcases le_or_gt p 1 with h | h
  · exact lp_small_strict_sas_exponential p hp h
  · exact lp_large_strict_sas_exponential_of_codes (fun q hq δ hδ => exists_code q hq δ hδ) p h hp2

end SelfApproaching.Proof
