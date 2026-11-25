module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.List.GetD

/-! # Constant-first coefficient lists -/

public section

namespace ArithmeticOfJacobiPolynomials.DerivativeModel

open Polynomial

/-- The polynomial with the given coefficients, starting with the constant term. -/
@[expose] noncomputable def ofCoeffs {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: l => C a + X * ofCoeffs l

@[simp] theorem ofCoeffs_nil {R : Type*} [Semiring R] : ofCoeffs ([] : List R) = 0 := rfl

@[simp] theorem ofCoeffs_cons {R : Type*} [Semiring R] (a : R) (l : List R) :
    ofCoeffs (a :: l) = C a + X * ofCoeffs l := rfl

theorem coeff_ofCoeffs {R : Type*} [Semiring R] (l : List R) (n : ℕ) :
    (ofCoeffs l).coeff n = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [List.getD]
  | cons a l ih =>
    cases n with
    | zero => simp [List.getD]
    | succ n => simp [coeff_X_mul, ih, List.getD]

theorem natDegree_ofCoeffs {R : Type*} [Semiring R] (l : List R) (d : ℕ)
    (hlen : l.length = d + 1) (hlc : l.getD d 0 ≠ 0) : (ofCoeffs l).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_ofCoeffs]
    exact List.getD_eq_default _ _ (hlen ▸ hi)
  · rwa [coeff_ofCoeffs]

theorem map_ofCoeffs {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (l : List R) :
    (ofCoeffs l).map φ = ofCoeffs (l.map φ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

end ArithmeticOfJacobiPolynomials.DerivativeModel
