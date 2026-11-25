module

public import ArithmeticOfJacobiPolynomials.Verification.Frobenius
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoeffs
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! # Arithmetic in a monic polynomial quotient
A residue is a list of exactly `d` coefficients in descending order. The
defining relation is `X^d = F(X)`, with `F` represented by a list of length
`d`. The implementation uses natural numbers reduced modulo the prime.
-/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

variable {p : ℕ} {R : Type*} [CommRing R]

/-- Evaluate a descending coefficient list using a map of the prime field. -/
@[expose] def value (φ : ZMod p →+* R) (x : R) : List ℕ → R
  | [] => 0
  | c :: cs => φ (c : ZMod p) * x ^ cs.length + value φ x cs

/-- Add a scalar multiple of a coefficient vector. -/
@[expose] def addMul (p a : ℕ) (u v : List ℕ) : List ℕ :=
  List.zipWith (fun b c => (b + a * c) % p) u v

theorem length_addMul (a : ℕ) {u v : List ℕ} (h : u.length = v.length) :
    (addMul p a u v).length = u.length := by simp [addMul, h]

theorem value_addMul (φ : ZMod p →+* R) (x : R) (a : ℕ) {u v : List ℕ}
    (h : u.length = v.length) :
    value φ x (addMul p a u v) = value φ x u + φ (a : ZMod p) * value φ x v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all [addMul, value]
  | cons b bs ih =>
    cases v with
    | nil => simp at h
    | cons c cs =>
      have hl : bs.length = cs.length := by simpa using h
      change φ (((b + a * c) % p : ℕ) : ZMod p) * x ^ (addMul p a bs cs).length +
        value φ x (addMul p a bs cs) = _
      rw [length_addMul _ hl, ih hl, ZMod.natCast_mod]
      simp only [value, Nat.cast_add, Nat.cast_mul, map_add, map_mul, ← hl]
      ring

theorem value_append_zero (φ : ZMod p →+* R) (x : R) (u : List ℕ) :
    value φ x (u ++ [0]) = x * value φ x u := by
  induction u with
  | nil => simp [value]
  | cons a l ih =>
    simp only [List.cons_append, value, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, pow_succ, ih]
    ring

/-- Multiply a residue by `X`, reducing its leading term by the defining relation. -/
@[expose] def shift (p : ℕ) (f : List ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => addMul p a (l ++ [0]) f

theorem length_shift (f u : List ℕ) (h : u.length = f.length) :
    (shift p f u).length = f.length := by
  cases u <;> simp_all [shift, addMul]

theorem value_shift (φ : ZMod p →+* R) (x : R) (f u : List ℕ)
    (hx : x ^ f.length = value φ x f) (h : u.length = f.length) :
    value φ x (shift p f u) = x * value φ x u := by
  cases u with
  | nil => simp [shift, value]
  | cons a l =>
    have hl : (l ++ [0]).length = f.length := by simpa using h
    rw [shift, value_addMul φ x _ hl, value_append_zero, ← hx, ← h]
    simp only [value, List.length_cons, pow_succ]
    ring

@[expose] def zeros (f : List ℕ) := List.replicate f.length 0

theorem value_zeros (φ : ZMod p →+* R) (x : R) (n : ℕ) :
    value φ x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

/-- Multiply a residue by a polynomial, using Horner's rule and `shift`. -/
@[expose] def mulAux (p : ℕ) (f v : List ℕ) : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | a :: l, acc => mulAux p f v l (addMul p a (shift p f acc) v)

theorem length_mulAux (f v l acc : List ℕ) (hv : v.length = f.length)
    (ha : acc.length = f.length) : (mulAux p f v l acc).length = f.length := by
  induction l generalizing acc with
  | nil => exact ha
  | cons a l ih =>
    apply ih
    rw [length_addMul _ ((length_shift f acc ha).trans hv.symm), length_shift f acc ha]

theorem value_mulAux (φ : ZMod p →+* R) (x : R) (f v l acc : List ℕ)
    (hx : x ^ f.length = value φ x f) (hv : v.length = f.length) (ha : acc.length = f.length) :
    value φ x (mulAux p f v l acc) =
      value φ x acc * x ^ l.length + value φ x l * value φ x v := by
  induction l generalizing acc with
  | nil => simp [mulAux, value]
  | cons a l ih =>
    have hs : (shift p f acc).length = v.length := (length_shift f acc ha).trans hv.symm
    rw [mulAux, ih _ ((length_addMul _ hs).trans (length_shift f acc ha)),
      value_addMul φ x _ hs, value_shift φ x f acc hx ha]
    simp only [value, List.length_cons, pow_succ]
    ring

@[expose] def mul (p : ℕ) (f u v : List ℕ) : List ℕ := mulAux p f v u (zeros f)

theorem length_mul (f u v : List ℕ) (hv : v.length = f.length) :
    (mul p f u v).length = f.length := length_mulAux f v u _ hv (by simp [zeros])

theorem value_mul (φ : ZMod p →+* R) (x : R) (f u v : List ℕ)
    (hx : x ^ f.length = value φ x f) (hv : v.length = f.length) :
    value φ x (mul p f u v) = value φ x u * value φ x v := by
  rw [mul, value_mulAux φ x f v u _ hx hv (by simp [zeros])]
  simp [zeros, value_zeros]

theorem value_append (φ : ZMod p →+* R) (x : R) (u v : List ℕ) :
    value φ x (u ++ v) = value φ x u * x ^ v.length + value φ x v := by
  induction u with
  | nil => simp [value]
  | cons a l ih =>
    simp only [List.cons_append, value, List.length_append, pow_add, ih]
    ring

/-- The degree-bounded representative of one, for a positive-degree modulus. -/
@[expose] def unitVec (f : List ℕ) := List.replicate (f.length - 1) 0 ++ [1]

theorem length_unitVec (f : List ℕ) (hd : 0 < f.length) : (unitVec f).length = f.length := by
  simp [unitVec]
  omega

theorem value_unitVec (φ : ZMod p →+* R) (x : R) (f : List ℕ) :
    value φ x (unitVec f) = 1 := by
  simp [unitVec, value_append, value_zeros, value]

end ArithmeticOfJacobiPolynomials.ModularArithmetic
