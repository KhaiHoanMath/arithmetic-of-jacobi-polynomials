module

public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoefficientFormula
public import ArithmeticOfJacobiPolynomials.Verification.Kronecker

/-! # Packed arithmetic certificates for the first-derivative reductions -/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open DerivativeModel

/-- A certificate identifies the integer polynomial and proves the Frobenius
period and the inverse identities in its reduction. Coefficient vectors in the
modular calculation are in descending order. The integer list is in ascending order. -/
structure FastConditions (m δ p scale : ℕ) (l : List ℤ) (f xp : List ℕ)
    (table : List (List ℕ)) (row inv chainVal : ℕ → List ℕ)
    (chainExp : ℕ → ℕ) (op : ℕ → ℕ × ℕ) (N : ℕ)
    (q plus minus : ℕ → List ℕ) (packed sums : List ℕ) (carry : ℕ → List ℕ) : Prop where
  scale_ne : scale ≠ 0
  model_length : l.length = 2 * m + 1
  degree_eq : f.length = 2 * m
  coefficients : ∀ i : Fin (2 * m + 1), (scale : ℚ) * (l.getD i.val 0 : ℚ) = targetCoeff m δ i.val
  content_one : (Finset.range l.length).gcd (fun i => l.getD i 0) = 1
  leading_ne : ((l.getD f.length 0 : ℤ) : ZMod p) ≠ 0
  normalized : ∀ i : Fin f.length, (l.getD i.val 0 : ZMod p) +
    (l.getD f.length 0 : ZMod p) * (f.reverse.getD i.val 0 : ZMod p) = 0
  chain_start : chainVal 0 = shift p f (unitVec f)
  exponent_start : chainExp 0 = 1
  chain_end : chainVal N = xp
  exponent_end : chainExp N = p
  chain_steps : ∀ i : Fin N, let j := (op i.val).1; let k := (op i.val).2
    j ≤ i.val ∧ k ≤ i.val ∧ (chainVal k).length = f.length ∧
      chainExp (i.val + 1) = chainExp j + chainExp k ∧
      chainVal (i.val + 1) = mul p f (chainVal j) (chainVal k)
  table_length : table.length = f.length
  table_last : table.getD (f.length - 1) [] = unitVec f
  table_products : ∀ i : Fin (f.length - 1), Kronecker.Product (2^48) p f xp
    (table.getD (i.val+1) []) (table.getD i.val []) (q i.val) (plus i.val) (minus i.val)
  table_packed : packed = table.map (Kronecker.pack (2^48))
  table_sums : sums = table.map (Kronecker.pack 1)
  trace_start : row 0 = shift p f (unitVec f)
  row_lengths : ∀ i : Fin (f.length + 1), (row i.val).length = f.length
  trace_steps : ∀ i : Fin f.length, Kronecker.Linear (2^48) p packed sums
    (row i.val) (row (i.val+1)) (carry i.val)
  trace_end : row f.length = row 0
  inverses : ∀ q : Fin (f.length + 1), q.val.Prime → q.val ∣ f.length →
    mul p f (inv q.val) (row (f.length / q.val)) =
      addMul p 1 (unitVec f) (mul p f (inv q.val) (row 0))

end ArithmeticOfJacobiPolynomials.ModularArithmetic
