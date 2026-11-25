module

public import ArithmeticOfJacobiPolynomials.Verification.ModularArithmetic
public import ArithmeticOfJacobiPolynomials.Verification.QuotientFrobenius
import Mathlib.Tactic

/-! # Computing Frobenius with a table of powers
The rows, in descending order, are the powers of the residue representing
(X^p). A single matrix-vector product then computes Frobenius on each residue.
-/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial

/-- Test the constant row and each multiplication connecting two successive rows. -/
@[expose] def tabCheck (p : ℕ) (f xp : List ℕ) : List (List ℕ) → Bool
  | [] => true
  | [r] => r == unitVec f
  | r :: s :: rows => (r == mul p f xp s) && tabCheck p f xp (s :: rows)

/-- Form the linear combination of the supplied rows with coefficients from `u`. -/
@[expose] def lin (p : ℕ) (f : List ℕ) : List (List ℕ) → List ℕ → List ℕ
  | r :: rows, c :: cs => addMul p c (lin p f rows cs) r
  | _, _ => zeros f

private theorem tabCheck_tail {p : ℕ} {f xp r : List ℕ} {rows : List (List ℕ)}
    (ht : tabCheck p f xp (r :: rows) = true) : tabCheck p f xp rows = true := by
  cases rows with
  | nil => rfl
  | cons s ss => exact (Bool.and_eq_true_iff.mp ht).2

private theorem table_length_head {p : ℕ} {f xp r : List ℕ} {rows : List (List ℕ)}
    (hf : 0 < f.length) (ht : tabCheck p f xp (r :: rows) = true) : r.length = f.length := by
  induction rows generalizing r with
  | nil =>
    simp only [tabCheck, beq_iff_eq] at ht
    simpa [ht] using length_unitVec (f := f) hf
  | cons s ss ih =>
    simp only [tabCheck, Bool.and_eq_true, beq_iff_eq] at ht
    rw [ht.1, length_mul _ _ _ (ih ht.2)]

theorem length_lin_of_table {p : ℕ} {f xp u : List ℕ} {tabs : List (List ℕ)}
    (hf : 0 < f.length) (ht : tabCheck p f xp tabs = true) (hu : tabs.length = u.length) :
    (lin p f tabs u).length = f.length := by
  induction tabs generalizing u with
  | nil =>
    cases u <;> simp_all [lin, zeros]
  | cons r rs ih =>
    cases u with
    | nil => simp at hu
    | cons c cs =>
      have hl := ih (u := cs) (tabCheck_tail ht) (by simpa using hu)
      rw [lin, length_addMul _ (hl.trans (table_length_head hf ht).symm), hl]

private theorem table_value_head {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R)
    (x : R) {f xp r : List ℕ} {rows : List (List ℕ)} (hf : 0 < f.length)
    (hx : x ^ f.length = value φ x f) (ht : tabCheck p f xp (r :: rows) = true) :
    value φ x r = value φ x xp ^ rows.length := by
  induction rows generalizing r with
  | nil =>
    simp only [tabCheck, beq_iff_eq] at ht
    simp [ht, value_unitVec]
  | cons s ss ih =>
    have hs := tabCheck_tail ht
    simp only [tabCheck, Bool.and_eq_true, beq_iff_eq] at ht
    rw [ht.1, value_mul _ _ _ _ _ hx (table_length_head hf hs), ih hs,
      List.length_cons, pow_succ']

/-- The checked linear combination is the p-th power in the quotient ring. -/
theorem value_lin_frobenius {p : ℕ} [Fact p.Prime] (h : (ZMod p)[X])
    {f xp u : List ℕ} {tabs : List (List ℕ)} (hf : 0 < f.length)
    (hx : AdjoinRoot.root h ^ f.length = value (AdjoinRoot.of h) (AdjoinRoot.root h) f)
    (hxp : value (AdjoinRoot.of h) (AdjoinRoot.root h) xp = AdjoinRoot.root h ^ p)
    (ht : tabCheck p f xp tabs = true) (hu : tabs.length = u.length) :
    value (AdjoinRoot.of h) (AdjoinRoot.root h) (lin p f tabs u) =
      value (AdjoinRoot.of h) (AdjoinRoot.root h) u ^ p := by
  induction tabs generalizing u with
  | nil =>
    cases u with
    | nil => simp [lin, zeros, value_zeros, value, (Fact.out : p.Prime).ne_zero]
    | cons c cs => simp at hu
  | cons r rs ih =>
    cases u with
    | nil => simp at hu
    | cons c cs =>
      have hlen : rs.length = cs.length := by simpa using hu
      have hs := tabCheck_tail ht
      have hl := length_lin_of_table hf hs hlen
      rw [lin, value_addMul _ _ _ (hl.trans (table_length_head hf ht).symm),
        ih hs hlen, table_value_head _ _ hf hx ht, hxp, hlen, value,
        adjoinRoot_add_pow_prime, mul_pow, adjoinRoot_of_pow_prime]
      rw [← pow_mul, Nat.mul_comm p cs.length, pow_mul]
      ring

end ArithmeticOfJacobiPolynomials.ModularArithmetic
