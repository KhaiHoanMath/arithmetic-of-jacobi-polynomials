module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeModel
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeRabin
public import ArithmeticOfJacobiPolynomials.Verification.QuotientNormalization
public import ArithmeticOfJacobiPolynomials.Verification.RabinConditions

/-! # From a finite Frobenius certificate to the derivative -/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial DerivativeModel

/-- Each numerical record satisfying the coefficient, period and inverse checks
certifies the corresponding normalized first derivative over the rationals. -/
theorem irreducible_encoded {m δ p scale : ℕ} {l : List ℤ} {f xp : List ℕ}
    {table : List (List ℕ)} {row inv chainVal : ℕ → List ℕ}
    {chainExp : ℕ → ℕ} {op : ℕ → ℕ × ℕ} {N : ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) [Fact p.Prime]
    (hc : Conditions m δ p scale l f xp table row inv chainVal chainExp op N) :
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
  rw [hc.trace_steps i]
  exact value_lin_frobenius h hp hx hxp hc.table_valid
    (hc.table_length.trans (hc.row_lengths ⟨i.val, by omega⟩).symm)

end ArithmeticOfJacobiPolynomials.ModularArithmetic
