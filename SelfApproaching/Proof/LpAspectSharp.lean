import SelfApproaching.Definitions
import SelfApproaching.Proof.LpAspectSharp.Osc
import SelfApproaching.Proof.LpAspectSharp.Approx
import SelfApproaching.Proof.LpAspectSharp.Equilateral

/-!
# SASs with bounded aspect ratio in `(ℝ^d, ℓ_p)`: Theorem 5 with the paper's exponent

For `p ≥ 1` and `q = (2p+2)/(2p-1)`, an SAS in `(ℝ^d, ℓ_p)` with aspect ratio less than `b`
has length `O(d^{3q/2} ⌈log b⌉)`.

The proof follows `lp_sas_length_le_of_aspect` (exponent `6`), but uses a separable
approximation of `|a - b|^p` with `O(K)` terms and error `O(K^{-p})` (the rate of Jackson's
theorem used in the paper) instead of `O(K^{-1})`:
* `cos_integral_decomp` (`Osc`): repeated integration by parts writes the Fourier coefficients of
  the `6`-periodic extension of `|t|^p` as `∑_{j<m} a_j (-1)^n / n^{2j+2} + O(|n|^{-(p+1)})`;
* `exists_separable_approx_of_decomp` (`Approx`): the terms `(-1)^n / n^{2j+2}` sum to Bernoulli
  polynomials in `t = a - b` (exactly separable), and the remainder series is truncated at
  `|n| ≤ K` with error `O(K^{-p})`;
* `lp_sas_length_le_of_aspect_of_approx` (`Equilateral`): the rank argument with parameters
  `s ≍ d^{q/2}`, `ε = 1/(4ps)`, followed by the bucketing argument.
-/

namespace SelfApproaching.Proof

open Real

theorem lp_sas_length_le_of_aspect_sharp (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (b : ℝ), 1 < b → ∀ (ℓ : ℕ) (x : Fin ℓ → (Fin d → ℝ)),
      IsSAS (lpDist p) x → AspectRatioLT (lpDist p) x b →
        (ℓ : ℝ) ≤ C * (d : ℝ) ^ (3 / 2 * ((2 * p + 2) / (2 * p - 1))) * ⌈log b⌉₊ :=
  LpAspectSharp.lp_sas_length_le_of_aspect_of_approx p hp
    (LpAspectSharp.exists_separable_approx_of_decomp p hp
      (LpAspectSharp.cos_integral_decomp p (by linarith)))

end SelfApproaching.Proof
