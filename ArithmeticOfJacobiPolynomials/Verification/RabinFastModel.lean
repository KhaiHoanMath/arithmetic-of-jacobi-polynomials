module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeModel
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeRabin
public import ArithmeticOfJacobiPolynomials.Verification.QuotientNormalization
public import ArithmeticOfJacobiPolynomials.Verification.RabinFastConditions

/-! # Derivative irreducibility from packed Frobenius certificates -/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial DerivativeModel

/-- A unit at the end of a table and multiplication by `y` between successive rows
give the consecutive powers of `y` in descending order. -/
theorem powers_of_adjacent {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R)
    (x y : R) (rows : List (List ℕ))
    (hlast : ∀ i, i + 1 = rows.length → value φ x (rows.getD i []) = 1)
    (hnext : ∀ i, i + 1 < rows.length →
      value φ x (rows.getD i []) = y * value φ x (rows.getD (i + 1) [])) :
    Kronecker.Powers φ x y rows := by
  induction rows with
  | nil => exact Kronecker.powers_nil φ x y
  | cons r rs ih =>
    have hp := ih (fun i hi => hlast (i + 1) (by simp [hi]))
      (fun i hi => hnext (i + 1) (by simpa using hi))
    apply Kronecker.powers_cons_iff.mpr
    refine ⟨?_, hp⟩
    cases rs with
    | nil => simpa using hlast 0 rfl
    | cons s ss =>
      have hs : value φ x s = y ^ ss.length := (Kronecker.powers_cons_iff.mp hp).1
      have he : value φ x r = y * value φ x s := hnext 0 (by simp)
      rw [he, hs, List.length_cons, pow_succ']

/-- Each numerical record satisfying the coefficient, period and inverse checks
certifies the corresponding normalized first derivative over the rationals. -/
theorem irreducible_encoded_fast {m δ p scale : ℕ} {l : List ℤ} {f xp : List ℕ}
    {table : List (List ℕ)} {row inv chainVal : ℕ → List ℕ}
    {chainExp : ℕ → ℕ} {op : ℕ → ℕ × ℕ} {N : ℕ}
    {q plus minus carry : ℕ → List ℕ} {packed sums : List ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) [Fact p.Prime]
    (hc : FastConditions m δ p scale l f xp table row inv chainVal chainExp op N
      q plus minus packed sums carry) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ Polynomial.X ^ δ) := by
  apply irreducible_derivative_of_certificate hm hδ l scale hc.scale_ne hc.model_length
    hc.coefficients hc.content_one p (hc.degree_eq ▸ hc.leading_ne)
  let v := l.map (Int.castRingHom (ZMod p))
  let h := ofCoeffs v
  change Irreducible h
  have hd := hc.degree_eq
  have hp : 0 < f.length := by omega
  have hvl : v.length = f.length + 1 := by simpa [v, hd] using hc.model_length
  have get (i : ℕ) : v.getD i 0 = (l.getD i 0 : ZMod p) := by
    simpa only [v, Int.coe_castRingHom, Int.cast_zero] using
      List.getD_map l 0 (n := i) (Int.castRingHom (ZMod p))
  have hvtop : v.getD f.length 0 ≠ 0 := by rw [get]; exact hc.leading_ne
  have hx : AdjoinRoot.root h ^ f.length = value (AdjoinRoot.of h) (AdjoinRoot.root h) f := by
    apply root_pow_eq_value v f hvl hvtop
    intro i
    rw [get, get]
    exact hc.normalized i
  have hb : value (AdjoinRoot.of h) (AdjoinRoot.root h) (chainVal 0) = AdjoinRoot.root h := by
    rw [hc.chain_start, value_shift _ _ _ _ hx (length_unitVec f hp), value_unitVec, mul_one]
  have hxp := value_chain (AdjoinRoot.of h) (AdjoinRoot.root h) f hx chainVal chainExp op N hb
    hc.exponent_start hc.chain_steps
  rw [hc.chain_end, hc.exponent_end] at hxp
  apply irreducible_of_trace h f hp (natDegree_ofCoeffs v f.length hvl hvtop) hx row inv
    hc.trace_start hc.row_lengths _ hc.trace_end hc.inverses
  intro i
  apply Kronecker.value_linear_frobenius h table packed sums (row i.val) (row (i.val + 1))
    (carry i.val) hc.table_packed hc.table_sums
    (hc.table_length.trans (hc.row_lengths ⟨i.val, by omega⟩).symm) _ (hc.trace_steps i)
  apply powers_of_adjacent
  · intro j hj
    have eq : j = f.length - 1 := by rw [hc.table_length] at hj; omega
    rw [eq, hc.table_last, value_unitVec]
  · intro j hj
    have hi : j < f.length - 1 := by rw [hc.table_length] at hj; omega
    have hv := Kronecker.value_product (AdjoinRoot.of h) (AdjoinRoot.root h)
      f xp (table.getD (j + 1) []) (table.getD j []) (q j) (plus j) (minus j)
      hx (hc.table_products ⟨j, hi⟩)
    rwa [hxp] at hv

end ArithmeticOfJacobiPolynomials.ModularArithmetic
