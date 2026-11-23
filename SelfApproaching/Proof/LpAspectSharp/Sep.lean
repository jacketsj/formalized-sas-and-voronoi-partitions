import Mathlib
import SelfApproaching.Proof.LpAspect.Fourier

/-!
# Separable functions of two real variables

`SepLE F N` says that `F a b = ∑_{l ∈ ι} φ_l(a) ψ_l(b)` with at most `N` terms. Such functions
are closed under sums, products and powers; polynomials in `a - b` and real parts of
trigonometric polynomials in `a - b` are separable.
-/

namespace SelfApproaching.Proof.LpAspectSharp

open Real

/-- `F` is a sum of at most `N` products `φ(a) ψ(b)`. -/
def SepLE (F : ℝ → ℝ → ℝ) (N : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι ≤ N ∧
    ∃ φ ψ : ι → ℝ → ℝ, ∀ a b, F a b = ∑ l, φ l a * ψ l b

namespace SepLE

lemma mono {F : ℝ → ℝ → ℝ} {N M : ℕ} (h : SepLE F N) (hNM : N ≤ M) : SepLE F M := by
  obtain ⟨ι, _, hc, φ, ψ, h⟩ := h
  exact ⟨ι, inferInstance, hc.trans hNM, φ, ψ, h⟩

lemma congr {F G : ℝ → ℝ → ℝ} {N : ℕ} (h : SepLE F N) (hFG : ∀ a b, F a b = G a b) :
    SepLE G N := by
  obtain ⟨ι, _, hc, φ, ψ, h⟩ := h
  exact ⟨ι, inferInstance, hc, φ, ψ, fun a b => (hFG a b).symm.trans (h a b)⟩

lemma zero : SepLE (fun _ _ => 0) 0 :=
  ⟨Empty, inferInstance, by simp, fun _ _ => 0, fun _ _ => 0, fun _ _ => by simp⟩

lemma prod_fun (f g : ℝ → ℝ) : SepLE (fun a b => f a * g b) 1 :=
  ⟨Unit, inferInstance, by simp, fun _ => f, fun _ => g, fun a b => by simp⟩

lemma add {F G : ℝ → ℝ → ℝ} {N M : ℕ} (hF : SepLE F N) (hG : SepLE G M) :
    SepLE (fun a b => F a b + G a b) (N + M) := by
  obtain ⟨ι, _, hc, φ, ψ, h⟩ := hF
  obtain ⟨κ, _, hc', φ', ψ', h'⟩ := hG
  refine ⟨ι ⊕ κ, inferInstance, by rw [Fintype.card_sum]; omega,
    Sum.elim φ φ', Sum.elim ψ ψ', fun a b => ?_⟩
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [h, h']

lemma mul {F G : ℝ → ℝ → ℝ} {N M : ℕ} (hF : SepLE F N) (hG : SepLE G M) :
    SepLE (fun a b => F a b * G a b) (N * M) := by
  obtain ⟨ι, _, hc, φ, ψ, h⟩ := hF
  obtain ⟨κ, _, hc', φ', ψ', h'⟩ := hG
  refine ⟨ι × κ, inferInstance, by rw [Fintype.card_prod]; exact Nat.mul_le_mul hc hc',
    fun l a => φ l.1 a * φ' l.2 a, fun l b => ψ l.1 b * ψ' l.2 b, fun a b => ?_⟩
  simp only
  rw [h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sum {α : Type*} (s : Finset α) (F : α → ℝ → ℝ → ℝ) (N : α → ℕ)
    (h : ∀ i ∈ s, SepLE (F i) (N i)) :
    SepLE (fun a b => ∑ i ∈ s, F i a b) (∑ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine ((h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun a b => ?_
    rw [Finset.sum_insert hi]

lemma pow {F : ℝ → ℝ → ℝ} {N : ℕ} (h : SepLE F N) (i : ℕ) :
    SepLE (fun a b => F a b ^ i) (N ^ i) := by
  induction i with
  | zero => exact (prod_fun (fun _ => 1) (fun _ => 1)).congr fun a b => by simp
  | succ i ih => exact (ih.mul h).congr fun a b => by ring

/-- A polynomial in an affine function of `a - b` is separable. -/
lemma poly (P : Polynomial ℝ) (c e : ℝ) :
    ∃ N, SepLE (fun a b => P.eval (c * (a - b) + e)) N := by
  have hlin : SepLE (fun a b => c * (a - b) + e) 2 :=
    ((prod_fun (fun a => c * a + e) (fun _ => 1)).add
      (prod_fun (fun _ => 1) (fun b => -(c * b)))).congr fun a b => by ring
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), 1 * 2 ^ i, ?_⟩
  refine (sum _ _ _ fun i _ => (prod_fun (fun _ => P.coeff i) (fun _ => 1)).mul
    (hlin.pow i)).congr fun a b => ?_
  rw [Polynomial.eval_eq_sum_range]
  simp

attribute [local instance] LpAspect.fact_six

/-- The real part of a trigonometric polynomial in `a - b` (period `6`) is separable. -/
lemma trig (S : Finset ℤ) (r : ℤ → ℂ) :
    SepLE (fun a b => (∑ n ∈ S, r n * fourier n ((a - b : ℝ) : AddCircle (6 : ℝ))).re)
      (S.card * 2) := by
  set e : ℤ → ℝ → ℂ := fun n t => fourier n (t : AddCircle (6 : ℝ)) with he
  have he_mul : ∀ n a b, e n a * e n (-b) = e n (a - b) := by
    intro n a b
    simp only [he, fourier_coe_apply, ← Complex.exp_add]
    congr 1; push_cast; ring
  refine ⟨S × Bool, inferInstance, by rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe],
    fun l a => if l.2 then (r l.1 * e l.1 a).re else -(r l.1 * e l.1 a).im,
    fun l b => if l.2 then (e l.1 (-b)).re else (e l.1 (-b)).im, fun a b => ?_⟩
  simp only
  rw [Fintype.sum_prod_type, Complex.re_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fintype.sum_bool]
  change (r n * e n (a - b)).re = _
  rw [← he_mul, ← mul_assoc]
  simp only [if_true, Bool.false_eq_true, if_false, Complex.mul_re, Complex.mul_im]
  ring

end SepLE

end SelfApproaching.Proof.LpAspectSharp
