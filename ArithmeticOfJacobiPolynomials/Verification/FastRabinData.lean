module

public import ArithmeticOfJacobiPolynomials.Verification.RabinData
public import ArithmeticOfJacobiPolynomials.Verification.Kronecker

/-! # Integer witnesses for the packed polynomial checks -/

@[expose] public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

/-- Quotients, signed carries, and packed row values for the two dense table calculations. -/
structure FastRabinData where
  quotients : List ℕ
  positive : List ℕ
  negative : List ℕ
  packed : List ℕ
  sums : List ℕ
  carries : List ℕ

def packingBase : ℕ := 2 ^ 48

namespace FastRabinData

def qAt (a : FastRabinData) (c : RabinData) (i : ℕ) :=
  c.unpack (a.quotients.getD i 0)

def carryBase (c : RabinData) := 4 * (c.d + 1) * c.p + 1

def plusAt (a : FastRabinData) (c : RabinData) (i : ℕ) :=
  decode (carryBase c) (2 * c.d) (a.positive.getD i 0)

def minusAt (a : FastRabinData) (c : RabinData) (i : ℕ) :=
  decode (carryBase c) (2 * c.d) (a.negative.getD i 0)

def carryAt (a : FastRabinData) (c : RabinData) (i : ℕ) :=
  decode (carryBase c) c.d (a.carries.getD i 0)

end FastRabinData
end ArithmeticOfJacobiPolynomials.ModularArithmetic
