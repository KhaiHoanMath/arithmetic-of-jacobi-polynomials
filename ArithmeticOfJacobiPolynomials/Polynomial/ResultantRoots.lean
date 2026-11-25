/- Assembled by AxiomProver. -/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# The resultant of a factor through the derivative of the product

Let `F = a ∏_{i=1}^d (X - ξ_i)` with `a ≠ 0` and let `G` be a polynomial of degree `e` over a
field. For `H = F G`, differentiating at the roots of `F` gives `H'(ξ_i) = F'(ξ_i) G(ξ_i)`, and
`F'(ξ_i) = a ∏_{j ≠ i} (ξ_i - ξ_j)`. Together with `Res(F, G) = a^e ∏_i G(ξ_i)` this yields the
identity (1.7) of the manuscript (§1.4, cf. [Deng, Lemma 5.3]):
`|Res(F, G)| = |a|^{e-d} ∏_i |H'(ξ_i)| / ∏_{i<j} |ξ_i - ξ_j|^2` for simple roots and `d ≤ e`.

## Main results

* `resultant_C_mul_prod_X_sub_C`: `Res(F, G) = a^e ∏_i G(ξ_i)`.
* `prod_eval_derivative_mul_eq`: `∏_i H'(ξ_i) = a^d (∏_{i ≠ j} (ξ_i - ξ_j)) ∏_i G(ξ_i)`.
* `resultant_mul_prod_eq_prod_eval_derivative`: the identity (1.7) in multiplicative form over
  any field, with the ordered-pair product `∏_{i ≠ j} (ξ_i - ξ_j) = ∏_{i<j} (-(ξ_i - ξ_j)^2)`.
* `norm_resultant_eq_div`: the identity (1.7) over a normed field such as `ℝ` or `ℂ`.
* `abs_resultant_eq_div`: the real form, with `V = ∏_{i<j} (ξ_i - ξ_j)^2`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- A product over the ordered pairs `i ≠ j` of `Fin d` is the product over `i < j` of the
two orientations. -/
theorem prod_prod_erase_eq_prod_prod_lt {M : Type*} [CommMonoid M] {d : ℕ}
    (f : Fin d → Fin d → M) :
    ∏ i, ∏ j ∈ univ.erase i, f i j =
      ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (f i j * f j i) := by
  have hsplit : ∀ i : Fin d, ∏ j ∈ univ.erase i, f i j =
      (∏ j ∈ univ.filter (fun j => i < j), f i j) *
        ∏ j ∈ univ.filter (fun j => j < i), f i j := by
    intro i
    rw [← Finset.prod_union]
    · congr 1
      ext j
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim (fun h => h.ne') (fun h => h.ne)⟩
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact lt_asymm h1 h2
  simp_rw [hsplit, Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_comm' (by intro x y; simp)

section Field

variable {K : Type*} [Field K]

/-- `∏_j (X - ξ_j)` as a product over the multiset of values of `ξ`. -/
theorem prod_X_sub_C_eq_multiset {d : ℕ} (α : Fin d → K) :
    ∏ j, (X - C (α j)) = ((univ.val.map α).map fun a => X - C a).prod := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

private theorem roots_C_mul_prod_X_sub_C {d : ℕ} {a : K} (ha : a ≠ 0) (α : Fin d → K) :
    (C a * ∏ j, (X - C (α j))).roots = univ.val.map α := by
  rw [roots_C_mul _ ha, prod_X_sub_C_eq_multiset, roots_multiset_prod_X_sub_C]

private theorem natDegree_C_mul_prod_X_sub_C {d : ℕ} {a : K} (ha : a ≠ 0) (α : Fin d → K) :
    (C a * ∏ j, (X - C (α j))).natDegree = d := by
  rw [natDegree_C_mul ha, natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (α j))]
  simp

private theorem leadingCoeff_C_mul_prod_X_sub_C {d : ℕ} (a : K) (α : Fin d → K) :
    (C a * ∏ j, (X - C (α j))).leadingCoeff = a := by
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_prod]
  simp

/-- **Resultant through the roots of the first factor.** If `F = a ∏_i (X - ξ_i)` with `a ≠ 0`,
then `Res(F, G) = a^e ∏_i G(ξ_i)` with `e = deg G`. -/
theorem resultant_C_mul_prod_X_sub_C {d : ℕ} {a : K} (ha : a ≠ 0) (α : Fin d → K) (G : K[X]) :
    resultant (C a * ∏ j, (X - C (α j))) G = a ^ G.natDegree * ∏ i, G.eval (α i) := by
  have hroots := roots_C_mul_prod_X_sub_C ha α
  have hsplit : (C a * ∏ j, (X - C (α j))).Splits := by
    rw [splits_iff_card_roots, hroots, natDegree_C_mul_prod_X_sub_C ha α]
    simp
  rw [resultant_eq_prod_eval _ G G.natDegree le_rfl hsplit, hroots,
    leadingCoeff_C_mul_prod_X_sub_C, Multiset.map_map]
  rfl

/-- The derivative of `F = a ∏_j (X - ξ_j)` at `ξ_i` is `a ∏_{j ≠ i} (ξ_i - ξ_j)`. -/
theorem eval_derivative_C_mul_prod_X_sub_C {d : ℕ} (a : K) (α : Fin d → K) (i : Fin d) :
    (derivative (C a * ∏ j, (X - C (α j)))).eval (α i) = a * ∏ j ∈ univ.erase i, (α i - α j) := by
  rw [derivative_C_mul, eval_mul, eval_C, derivative_prod_finset, eval_finsetSum]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [eval_prod]
  · intro k _ hki
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (mem_erase.mpr ⟨Ne.symm hki, mem_univ _⟩)
      (by simp), zero_mul]
  · simp

/-- At a root of `F`, the derivative of `F G` is `F'(ξ) G(ξ)`. -/
theorem eval_derivative_mul_of_isRoot {F G : K[X]} {x : K} (hx : F.eval x = 0) :
    (derivative (F * G)).eval x = (derivative F).eval x * G.eval x := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul, hx, zero_mul, add_zero]

/-- **Derivative of the product at the roots of a factor.** For `F = a ∏_i (X - ξ_i)` and any
`G`, `∏_i (F G)'(ξ_i) = a^d (∏_{i ≠ j} (ξ_i - ξ_j)) ∏_i G(ξ_i)`. -/
theorem prod_eval_derivative_mul_eq {d : ℕ} (a : K) (α : Fin d → K) (G : K[X]) :
    ∏ i, (derivative ((C a * ∏ j, (X - C (α j))) * G)).eval (α i) =
      a ^ d * (∏ i, ∏ j ∈ univ.erase i, (α i - α j)) * ∏ i, G.eval (α i) := by
  have hroot : ∀ i, (C a * ∏ j, (X - C (α j))).eval (α i) = 0 := by
    intro i
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (mem_univ i) (by simp), mul_zero]
  simp_rw [eval_derivative_mul_of_isRoot (hroot _), eval_derivative_C_mul_prod_X_sub_C,
    Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin]

/-- The ordered-pair product of root differences in terms of the squared Vandermonde factors:
`∏_{i ≠ j} (ξ_i - ξ_j) = ∏_{i<j} (-(ξ_i - ξ_j)^2)`. -/
theorem prod_prod_erase_sub_eq {d : ℕ} (α : Fin d → K) :
    ∏ i, ∏ j ∈ univ.erase i, (α i - α j) =
      ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (-(α i - α j) ^ 2) := by
  rw [prod_prod_erase_eq_prod_prod_lt (fun i j => α i - α j)]
  congr 1; ext i; congr 1; ext j; ring

/-- **The resultant–derivative identity (1.7), multiplicative form, over a field.**
For `F = a ∏_{i=1}^d (X - ξ_i)` with `a ≠ 0`, `G` of degree `e` and `H = F G`,
`Res(F, G) · a^d · ∏_{i<j} (-(ξ_i - ξ_j)^2) = a^e ∏_i H'(ξ_i)`. -/
theorem resultant_mul_prod_eq_prod_eval_derivative {d : ℕ} {a : K} (ha : a ≠ 0)
    (α : Fin d → K) (G : K[X]) :
    resultant (C a * ∏ j, (X - C (α j))) G * a ^ d *
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (-(α i - α j) ^ 2) =
      a ^ G.natDegree *
        ∏ i, (derivative ((C a * ∏ j, (X - C (α j))) * G)).eval (α i) := by
  rw [prod_eval_derivative_mul_eq, resultant_C_mul_prod_X_sub_C ha, prod_prod_erase_sub_eq]
  ring

end Field

section Normed

variable {K : Type*} [NormedField K]

/-- **The resultant–derivative identity (1.7) over a normed field** (e.g. `ℝ` or `ℂ`).
For `F = a ∏_{i=1}^d (X - ξ_i)` with `a ≠ 0` and distinct roots `ξ_i`, `G` of degree `e ≥ d`
and `H = F G`,
`‖Res(F, G)‖ = ‖a‖^{e-d} ∏_i ‖H'(ξ_i)‖ / ∏_{i<j} ‖ξ_i - ξ_j‖^2`. -/
theorem norm_resultant_eq_div {d : ℕ} {a : K} (ha : a ≠ 0) {α : Fin d → K}
    (hα : Function.Injective α) (G : K[X]) (hde : d ≤ G.natDegree) :
    ‖resultant (C a * ∏ j, (X - C (α j))) G‖ =
      ‖a‖ ^ (G.natDegree - d) *
          (∏ i, ‖(derivative ((C a * ∏ j, (X - C (α j))) * G)).eval (α i)‖) /
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), ‖α i - α j‖ ^ 2 := by
  have key := congrArg norm (resultant_mul_prod_eq_prod_eval_derivative ha α G)
  simp only [norm_mul, norm_pow, norm_prod, norm_neg] at key
  have hV : 0 < ∏ i, ∏ j ∈ univ.filter (fun j => i < j), ‖α i - α j‖ ^ 2 := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i ≠ j := (mem_filter.mp hj).2.ne
    exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hα.ne hij))) 2
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  apply (eq_div_iff hV.ne').mpr
  have hpow : ‖a‖ ^ G.natDegree = ‖a‖ ^ (G.natDegree - d) * ‖a‖ ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hde]
  rw [hpow] at key
  have hd : 0 < ‖a‖ ^ d := pow_pos ha' d
  apply mul_right_cancel₀ hd.ne'
  linear_combination key

end Normed

/-- **The resultant–derivative identity (1.7) over `ℝ`.** For `F = a ∏_{i=1}^d (X - ξ_i)` with
`a ≠ 0` and distinct real roots, `G` of degree `e ≥ d` and `H = F G`,
`|Res(F, G)| = |a|^{e-d} ∏_i |H'(ξ_i)| / V` with `V = ∏_{i<j} (ξ_i - ξ_j)^2`. -/
theorem abs_resultant_eq_div {d : ℕ} {a : ℝ} (ha : a ≠ 0) {α : Fin d → ℝ}
    (hα : Function.Injective α) (G : ℝ[X]) (hde : d ≤ G.natDegree) :
    |resultant (C a * ∏ j, (X - C (α j))) G| =
      |a| ^ (G.natDegree - d) *
          (∏ i, |(derivative ((C a * ∏ j, (X - C (α j))) * G)).eval (α i)|) /
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 := by
  have := norm_resultant_eq_div ha hα G hde
  simpa only [Real.norm_eq_abs, sq_abs] using this

end ArithmeticOfJacobiPolynomials
