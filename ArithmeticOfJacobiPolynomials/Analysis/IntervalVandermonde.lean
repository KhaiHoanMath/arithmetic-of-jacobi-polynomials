/- Assembled by AxiomProver. -/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Tactic

/-!
# The Chebyshev–Hadamard interval Vandermonde estimate

The manuscript's proof of Lemma 2.5, §2.4, uses shifted Chebyshev
polynomials and Hadamard's inequality. Hadamard follows here from Mathlib's
volume-form bound; no additional literature input is needed.
-/

public section

open Polynomial Finset

namespace ArithmeticOfJacobiPolynomials

/-- Hadamard's inequality squared, obtained from the library volume bound. -/
theorem det_sq_le_prod_column_sq_norm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    M.det ^ 2 ≤ ∏ j, ∑ i, M i j ^ 2 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin k) ℝ
  let v : Fin k → EuclideanSpace ℝ (Fin k) := fun j => WithLp.toLp 2 (fun i => M i j)
  have he : b.toBasis.det v = M.det := by
    rw [Module.Basis.det_apply]
    rfl
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl, he] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, ← Finset.prod_pow] at hsq
  simpa only [EuclideanSpace.real_norm_sq_eq] using hsq

/-- A degree-ordered polynomial evaluation determinant equals the Vandermonde
determinant times the product of leading coefficients. -/
theorem det_polynomial_eval {k : ℕ} (q : Fin k → ℝ[X]) (t : Fin k → ℝ)
    (hq : ∀ j, (q j).natDegree = j.val) :
    (Matrix.of fun i j => (q j).eval (t i)).det =
      (Matrix.vandermonde t).det * ∏ j, (q j).leadingCoeff := by
  let C : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => (q j).coeff i.val
  have he : Matrix.of (fun i j => (q j).eval (t i)) = Matrix.vandermonde t * C := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply, C]
    rw [Polynomial.eval_eq_sum_range' (by rw [hq]; exact j.isLt)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have htri : C.IsUpperTriangular := by
    intro i j hij
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hq]; exact hij)
  rw [he, Matrix.det_mul, Matrix.det_of_isUpperTriangular htri]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  change (q j).coeff j.val = (q j).leadingCoeff
  rw [← hq, Polynomial.coeff_natDegree]

/-- The unnormalized shifted Chebyshev polynomial. Its evaluation is bounded
by one; its leading coefficient supplies the manuscript's powers of two. -/
noncomputable def shiftedChebyshev (j : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (j : ℤ)).comp (Polynomial.C 2 * X + Polynomial.C (-1))

theorem shiftedChebyshev_natDegree (j : ℕ) : (shiftedChebyshev j).natDegree = j := by
  have hlin : (Polynomial.C (2 : ℝ) * X + Polynomial.C (-1)).natDegree = 1 :=
    Polynomial.natDegree_linear (by norm_num)
  rw [shiftedChebyshev, Polynomial.natDegree_comp, hlin]
  simp

theorem shiftedChebyshev_leadingCoeff (j : ℕ) :
    (shiftedChebyshev j).leadingCoeff = 2 ^ (j - 1) * 2 ^ j := by
  have hlin : (Polynomial.C (2 : ℝ) * X + Polynomial.C (-1)).natDegree = 1 :=
    Polynomial.natDegree_linear (by norm_num)
  have hlc : (Polynomial.C (2 : ℝ) * X + Polynomial.C (-1)).leadingCoeff = 2 :=
    Polynomial.leadingCoeff_linear (by norm_num)
  rw [shiftedChebyshev, Polynomial.leadingCoeff_comp (by rw [hlin]; decide), hlc]
  simp [Polynomial.Chebyshev.leadingCoeff_T]

theorem abs_shiftedChebyshev_eval_le_one (j : ℕ) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    |(shiftedChebyshev j).eval t| ≤ 1 := by
  have h : |2 * t - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  simpa [shiftedChebyshev, Polynomial.eval_comp, sub_eq_add_neg] using
    Polynomial.Chebyshev.abs_eval_T_real_le_one (j : ℤ) h

theorem prod_shiftedChebyshev_leadingCoeff (k : ℕ) :
    (∏ j : Fin k, (shiftedChebyshev j.val).leadingCoeff) = 2 ^ ((k - 1) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel]
    rw [ih, shiftedChebyshev_leadingCoeff]
    by_cases hk : k = 0
    · subst k; norm_num
    · rw [← pow_add, ← pow_add]
      congr 1
      have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have he : k = (k - 1) + 1 := by omega
      nlinarith

/-- Squared Hadamard for a real matrix with entries bounded by one. -/
theorem det_sq_le_card_pow {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) : M.det ^ 2 ≤ (k : ℝ) ^ k := by
  refine (det_sq_le_prod_column_sq_norm M).trans ?_
  calc
    (∏ j, ∑ i, M i j ^ 2) ≤ ∏ _j : Fin k, (k : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact Finset.sum_nonneg fun i hi => sq_nonneg _
      · intro j hj
        calc
          (∑ i, M i j ^ 2) ≤ ∑ _i : Fin k, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have h := pow_le_pow_left₀ (abs_nonneg (M i j)) (hM i j) 2
            simpa only [sq_abs, one_pow] using h
          _ = k := by simp
    _ = (k : ℝ) ^ k := by simp

/-- The squared pairwise-distance product is the squared Vandermonde determinant. -/
theorem pairwise_distance_product_eq_det_sq {k : ℕ} (t : Fin k → ℝ) :
    (∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j => i < j), (t i - t j) ^ 2) =
      (Matrix.vandermonde t).det ^ 2 := by
  rw [Matrix.det_vandermonde, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.filter_lt_eq_Ioi, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  ring

/-- **Lemma 2.5.** The manuscript's Chebyshev–Hadamard interval estimate,
including the empty and singleton cases. Proved without any citation hypothesis. -/
theorem intervalVandermondeBound (k : ℕ) (t : Fin k → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j => i < j), (t i - t j) ^ 2 ≤
      (k : ℝ) ^ k / 2 ^ (2 * (k - 1) ^ 2) := by
  let q : Fin k → ℝ[X] := fun j => shiftedChebyshev j.val
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => (q j).eval (t i)
  have hdet : M.det = (Matrix.vandermonde t).det * 2 ^ ((k - 1) ^ 2) := by
    change (Matrix.of fun i j => (q j).eval (t i)).det = _
    rw [det_polynomial_eval q t (fun j => shiftedChebyshev_natDegree j.val)]
    rw [show (∏ j, (q j).leadingCoeff) = 2 ^ ((k - 1) ^ 2) from
      prod_shiftedChebyshev_leadingCoeff k]
  have hbound := det_sq_le_card_pow M (fun i j => abs_shiftedChebyshev_eval_le_one j.val (ht i))
  rw [hdet, mul_pow, ← pow_mul] at hbound
  rw [pairwise_distance_product_eq_det_sq, le_div_iff₀ (by positivity)]
  simpa only [Nat.mul_comm] using hbound

end ArithmeticOfJacobiPolynomials
