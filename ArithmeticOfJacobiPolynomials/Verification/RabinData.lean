module

public import ArithmeticOfJacobiPolynomials.Verification.FrobeniusTable

/-! # Encoding the Appendix C polynomial certificates
A vector of `d` entries between 0 and `p-1` is stored as one base-`p` integer.
Its least significant digit is the first entry of the descending coefficient list.
The fixed width restores all zero entries.
-/

@[expose] public section

namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

def decode (p : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | d + 1, n => n % p :: decode p d (n / p)

/-- Data for one primitive derivative model and its Frobenius certificate. -/
structure RabinData where
  m : ℕ
  δ : ℕ
  p : ℕ
  scale : ℕ
  coeffs : List ℤ
  relation : ℕ
  exponents : List ℕ
  operations : List (ℕ × ℕ)
  powers : List ℕ
  table : List ℕ
  trace : List ℕ
  inverses : List (ℕ × ℕ)

namespace RabinData
def d (c : RabinData) := 2 * c.m
def unpack (c : RabinData) := decode c.p c.d
def f (c : RabinData) := c.unpack c.relation
def expAt (c : RabinData) (i : ℕ) := c.exponents.getD i 0
def opAt (c : RabinData) (i : ℕ) := c.operations.getD i (0, 0)
def chainAt (c : RabinData) (i : ℕ) := c.unpack (c.powers.getD i 0)
def row (c : RabinData) (i : ℕ) := c.unpack (c.trace.getD i 0)
def inv (c : RabinData) (q : ℕ) := c.unpack ((c.inverses.lookup q).getD 0)
def xp (c : RabinData) := c.chainAt c.operations.length
def tabs (c : RabinData) := c.table.map c.unpack
end RabinData
end ArithmeticOfJacobiPolynomials.ModularArithmetic
