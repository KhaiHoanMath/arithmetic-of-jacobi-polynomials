module

public import ArithmeticOfJacobiPolynomials.Verification.ModularArithmetic
public import ArithmeticOfJacobiPolynomials.Verification.QuotientFrobenius
public import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

/-! # Checking modular polynomial products by integer evaluation

For polynomials with nonnegative integer coefficients, evaluation at a sufficiently
large base determines every coefficient. Evaluating at one bounds each coefficient.
A certificate for a product modulo a monic polynomial records its quotient and the
coefficientwise multiples of the characteristic.
-/

public section

namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial

namespace Kronecker

private theorem split_eval (F : ℕ[X]) (b : ℕ) :
    F.eval b = b * F.divX.eval b + F.coeff 0 := by
  conv_lhs => rw [← X_mul_divX_add F]
  simp

private theorem split_one (F : ℕ[X]) : F.eval 1 = F.divX.eval 1 + F.coeff 0 := by
  simpa using split_eval F 1

private theorem first_digit {b : ℕ} {F G : ℕ[X]} (hF : F.eval 1 < b) (hG : G.eval 1 < b)
    (he : F.eval b = G.eval b) : F.coeff 0 = G.coeff 0 := by
  have hf0 : F.coeff 0 < b := by have := split_one F; omega
  have hg0 : G.coeff 0 < b := by have := split_one G; omega
  rw [split_eval F, split_eval G] at he
  have h := congrArg (· % b) he
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hf0, Nat.mod_eq_of_lt hg0] using h

private theorem eval_inj {b : ℕ} {F G : ℕ[X]} (hF : F.eval 1 < b) (hG : G.eval 1 < b)
    (he : F.eval b = G.eval b) : F = G := by
  ext n
  induction n generalizing F G with
  | zero => exact first_digit hF hG he
  | succ n ih =>
    have h0 := first_digit hF hG he
    rw [split_eval F, split_eval G, h0, Nat.add_left_inj] at he
    have hd := Nat.eq_of_mul_eq_mul_left (by omega : 0 < b) he
    rw [← coeff_divX (p := F), ← coeff_divX (p := G)]
    apply ih <;> first | assumption | (have := split_one F; omega) | (have := split_one G; omega)

/-- Pack a descending list of natural coefficients as digits in the indicated base. -/
@[expose] def pack (b : ℕ) (cs : List ℕ) : ℕ := cs.foldl (fun acc a => acc * b + a) 0

private noncomputable def poly : List ℕ → ℕ[X]
  | [] => 0
  | a :: cs => C a * X ^ cs.length + poly cs

private theorem fold_eq (cs : List ℕ) (b acc : ℕ) :
    cs.foldl (fun s a => s * b + a) acc = acc * b ^ cs.length + (poly cs).eval b := by
  induction cs generalizing acc with
  | nil => simp [poly]
  | cons a cs ih =>
    rw [List.foldl_cons, ih]
    simp [poly, pow_succ]
    ring

private theorem eval_poly (cs : List ℕ) (b : ℕ) : (poly cs).eval b = pack b cs := by
  simpa [pack] using (fold_eq cs b 0).symm

private theorem eval₂_poly {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R)
    (cs : List ℕ) : (poly cs).eval₂ (Nat.castRingHom R) x = value φ x cs := by
  induction cs with
  | nil => simp [poly, value]
  | cons a cs ih => simp [poly, value, ih]

/-- The exact integer identity and two coefficient bounds for a modular multiplication. -/
@[expose] def Product (b p : ℕ) (f a t c q plus minus : List ℕ) : Prop :=
  (pack 1 a * pack 1 t + pack 1 q * pack 1 f + p * pack 1 plus < b) ∧
  (pack 1 c + pack 1 q + p * pack 1 minus < b) ∧
  pack b a * pack b t + pack b q * pack b f + p * pack b plus =
    pack b c + pack b q * b ^ f.length + p * pack b minus

instance (b p : ℕ) (f a t c q plus minus : List ℕ) :
    Decidable (Product b p f a t c q plus minus) := by unfold Product; infer_instance

/-- A checked packed product represents the product of the two residues in every
quotient satisfying the monic defining relation. -/
theorem value_product {p b : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R)
    (f a t c q plus minus : List ℕ) (hx : x ^ f.length = value φ x f)
    (h : Product b p f a t c q plus minus) :
    value φ x c = value φ x a * value φ x t := by
  let F := poly a * poly t + poly q * poly f + C p * poly plus
  let G := poly c + poly q * X ^ f.length + C p * poly minus
  have hfg : F = G := by
    apply eval_inj (b := b)
    · simpa [F, eval_poly] using h.1
    · simpa [G, eval_poly] using h.2.1
    · simpa [F, G, eval_poly] using h.2.2
  have hp : (p : R) = 0 := by rw [← map_natCast φ p, ZMod.natCast_self, map_zero]
  have he := congrArg (fun z : ℕ[X] => z.eval₂ (Nat.castRingHom R) x) hfg
  simpa [F, G, eval₂_add, eval₂_mul, eval₂_pow, eval₂_poly φ x, hp, hx, eq_comm] using he

/-- Dot product of two lists, truncated to their common length. -/
@[expose] def dot : List ℕ → List ℕ → ℕ
  | a :: as, c :: cs => a * c + dot as cs
  | _, _ => 0

private noncomputable def linearPoly : List (List ℕ) → List ℕ → ℕ[X]
  | a :: as, c :: cs => C c * poly a + linearPoly as cs
  | _, _ => 0

private theorem eval_linearPoly (b : ℕ) (rows : List (List ℕ)) (cs : List ℕ) :
    (linearPoly rows cs).eval b = dot (rows.map (pack b)) cs := by
  induction rows generalizing cs with
  | nil => cases cs <;> simp [linearPoly, dot]
  | cons a as ih =>
    cases cs with
    | nil => simp [linearPoly, dot]
    | cons c cs => simp [linearPoly, dot, eval_poly, ih, mul_comm]

/-- The exact equality for a linear combination modulo the characteristic. The
packed rows and their coefficient sums can be reused for all Frobenius iterations. -/
@[expose] def Linear (b p : ℕ) (packed sums cs v carry : List ℕ) : Prop :=
  dot sums cs < b ∧ pack 1 v + p * pack 1 carry < b ∧
  dot packed cs = pack b v + p * pack b carry

instance (b p : ℕ) (packed sums cs v carry : List ℕ) :
    Decidable (Linear b p packed sums cs v carry) := by unfold Linear; infer_instance

/-- The weighted sum of the row values in the target ring. -/
def weighted {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R) :
    List (List ℕ) → List ℕ → R
  | r :: rs, c :: cs => φ (c : ZMod p) * value φ x r + weighted φ x rs cs
  | _, _ => 0

private theorem eval₂_linearPoly {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R)
    (rows : List (List ℕ)) (cs : List ℕ) :
    (linearPoly rows cs).eval₂ (Nat.castRingHom R) x = weighted φ x rows cs := by
  induction rows generalizing cs with
  | nil => cases cs <;> simp [linearPoly, weighted]
  | cons a as ih =>
    cases cs with
    | nil => simp [linearPoly, weighted]
    | cons c cs => simp [linearPoly, weighted, eval₂_poly φ x, ih]

theorem value_linear {p b : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R)
    (rows : List (List ℕ)) (packed sums cs v carry : List ℕ)
    (hpacks : packed = rows.map (pack b)) (hsums : sums = rows.map (pack 1))
    (h : Linear b p packed sums cs v carry) :
    value φ x v = weighted φ x rows cs := by
  let F := linearPoly rows cs
  let G := poly v + C p * poly carry
  have hfg : F = G := by
    apply eval_inj (b := b)
    · simpa [F, eval_linearPoly, ← hsums] using h.1
    · simpa [G, eval_poly] using h.2.1
    · simpa [F, G, eval_linearPoly, eval_poly, ← hpacks] using h.2.2
  have hp : (p : R) = 0 := by rw [← map_natCast φ p, ZMod.natCast_self, map_zero]
  have he := congrArg (fun z : ℕ[X] => z.eval₂ (Nat.castRingHom R) x) hfg
  simpa [F, G, eval₂_add, eval₂_mul, eval₂_poly φ x, eval₂_linearPoly φ x, hp] using he.symm

/-- The rows represent successive powers of the indicated element in descending order. -/
def Powers {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x y : R) :
    List (List ℕ) → Prop
  | [] => True
  | r :: rs => value φ x r = y ^ rs.length ∧ Powers φ x y rs

theorem powers_nil {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x y : R) :
    Powers φ x y [] := trivial

theorem powers_cons_iff {p : ℕ} {R : Type*} [CommRing R] {φ : ZMod p →+* R} {x y : R}
    {r : List ℕ} {rs : List (List ℕ)} :
    Powers φ x y (r :: rs) ↔ value φ x r = y ^ rs.length ∧ Powers φ x y rs := Iff.rfl

theorem value_linear_frobenius {p b : ℕ} [Fact p.Prime] (h : (ZMod p)[X])
    (rows : List (List ℕ)) (packed sums cs v carry : List ℕ)
    (hpacks : packed = rows.map (pack b)) (hsums : sums = rows.map (pack 1))
    (hlen : rows.length = cs.length)
    (hpows : Powers (AdjoinRoot.of h) (AdjoinRoot.root h) (AdjoinRoot.root h ^ p) rows)
    (hlin : Linear b p packed sums cs v carry) :
    value (AdjoinRoot.of h) (AdjoinRoot.root h) v =
      value (AdjoinRoot.of h) (AdjoinRoot.root h) cs ^ p := by
  rw [value_linear _ _ _ _ _ _ _ _ hpacks hsums hlin]
  clear hlin hpacks hsums
  induction rows generalizing cs with
  | nil =>
    cases cs with
    | nil => simp [weighted, value, (Fact.out : p.Prime).ne_zero]
    | cons c cs => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hr : rs.length = cs.length := by simpa using hlen
      rw [weighted, hpows.1, ih cs hr hpows.2, hr, value, adjoinRoot_add_pow_prime,
        mul_pow, adjoinRoot_of_pow_prime]
      rw [← pow_mul, Nat.mul_comm p cs.length, pow_mul]

end Kronecker
end ArithmeticOfJacobiPolynomials.ModularArithmetic
