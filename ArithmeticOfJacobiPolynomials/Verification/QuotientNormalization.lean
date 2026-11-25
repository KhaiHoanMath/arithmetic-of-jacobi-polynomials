module

public import ArithmeticOfJacobiPolynomials.Verification.ModularArithmetic

/-! # Identifying the relation for arithmetic in the quotient
The coefficient checks multiply by the leading coefficient. This works for
a nonmonic polynomial and avoids computing its leading coefficient's inverse.
-/

public section

namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial DerivativeModel

private theorem ofCoeffs_append_singleton {R : Type*} [CommRing R] (l : List R) (a : R) :
    ofCoeffs (l ++ [a]) = ofCoeffs l + C a * X ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, ofCoeffs_cons, ih, List.length_cons, pow_succ]
    ring

private theorem value_polynomial {p : ℕ} (f : List ℕ) :
    value (Polynomial.C : ZMod p →+* (ZMod p)[X]) Polynomial.X f =
      ofCoeffs (f.reverse.map (fun n : ℕ => (n : ZMod p))) := by
  induction f with
  | nil => simp [value]
  | cons a l ih =>
    simp only [value, ih, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      ofCoeffs_append_singleton, List.length_map, List.length_reverse]
    exact add_comm _ _

private theorem coeff_value_polynomial {p : ℕ} (f : List ℕ) (i : ℕ) :
    (value (Polynomial.C : ZMod p →+* (ZMod p)[X]) Polynomial.X f).coeff i =
      (f.reverse.getD i 0 : ZMod p) := by
  rw [value_polynomial, coeff_ofCoeffs]
  simpa only [Nat.cast_zero] using
    List.getD_map f.reverse 0 (n := i) (fun n : ℕ => (n : ZMod p))

private theorem mk_value_polynomial {p : ℕ} (h : (ZMod p)[X]) (f : List ℕ) :
    AdjoinRoot.mk h (value (Polynomial.C : ZMod p →+* (ZMod p)[X]) Polynomial.X f) =
      value (AdjoinRoot.of h) (AdjoinRoot.root h) f := by
  induction f with
  | nil => simp [value]
  | cons c l ih => simp [value, ih, AdjoinRoot.mk_X]

/-- The checked lower coefficients determine the relation for the root of a
full-degree modular reduction. Both lists include all intermediate zero coefficients. -/
theorem root_pow_eq_value {p : ℕ} [Fact p.Prime] (l : List (ZMod p)) (f : List ℕ)
    (hlen : l.length = f.length + 1) (hlc : l.getD f.length 0 ≠ 0)
    (hr : ∀ i : Fin f.length, l.getD i.val 0 +
      l.getD f.length 0 * (f.reverse.getD i.val 0 : ZMod p) = 0) :
    (AdjoinRoot.root (ofCoeffs l)) ^ f.length =
      value (AdjoinRoot.of (ofCoeffs l)) (AdjoinRoot.root (ofCoeffs l)) f := by
  have he : ofCoeffs l = C (l.getD f.length 0) *
      (Polynomial.X ^ f.length -
        value (Polynomial.C : ZMod p →+* (ZMod p)[X]) Polynomial.X f) := by
    ext i
    rw [coeff_C_mul, coeff_sub, coeff_X_pow, coeff_value_polynomial, coeff_ofCoeffs]
    rcases lt_trichotomy i f.length with h | rfl | h
    · have hi := hr ⟨i, h⟩
      simp only [ite_eq_right h.ne, zero_sub, mul_neg]
      exact eq_neg_of_add_eq_zero_left hi
    · simp
    · rw [List.getD_eq_default l 0 (hlen ▸ h)]
      rw [List.getD_eq_default f.reverse 0 (by simpa using h.le)]
      simp [h.ne']
  let h := ofCoeffs l
  have hz := congrArg (AdjoinRoot.mk h) he
  change AdjoinRoot.mk h h = _ at hz
  rw [AdjoinRoot.mk_self, map_mul, map_sub, map_pow, AdjoinRoot.mk_X,
    mk_value_polynomial] at hz
  have hu : IsUnit (AdjoinRoot.mk h (C (l.getD f.length 0))) :=
    ((Ne.isUnit hlc).map Polynomial.C).map (AdjoinRoot.mk h)
  exact sub_eq_zero.mp ((hu.mul_right_inj).mp (by simpa using hz.symm))

end ArithmeticOfJacobiPolynomials.ModularArithmetic
