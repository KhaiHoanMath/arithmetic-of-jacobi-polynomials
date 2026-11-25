/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The complete list of Galois groups in Zarhin's theorems

Zarhin, *Very simple 2-adic representations and hyperelliptic Jacobians* (2002),
Theorems 2.4, 2.6, 8.1 and 9.1 allow symmetric and alternating groups, the two Mathieu
groups in the indicated degrees, and groups containing the indicated projective special
linear groups. The definition below records all of these alternatives.

The Mathieu groups use the concrete permutation generators of GAP's `MathieuGroup`,
with labels shifted from `1,...,n` to `0,...,n-1`. See [BreuerCTbl, Chapter 11, §11.5] for the
  displayed `M12` generators.
-/

public section

namespace ArithmeticOfJacobiPolynomials.Zarhin

open scoped Polynomial

/-- The eleven-point Mathieu group, defined by its standard GAP permutation generators. -/
abbrev Mathieu11 : Type :=
  ↥(Subgroup.closure
    {([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 11)).formPerm,
      ([2, 6, 10, 7] : List (Fin 11)).formPerm * [3, 9, 4, 5].formPerm})

/-- The twelve-point Mathieu group, defined by its standard GAP permutation generators. -/
abbrev Mathieu12 : Type :=
  ↥(Subgroup.closure
    {([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 12)).formPerm,
      ([2, 6, 10, 7] : List (Fin 12)).formPerm * [3, 9, 4, 5].formPerm,
      Equiv.swap 0 11 * Equiv.swap 1 10 * Equiv.swap 2 5 * Equiv.swap 3 7 *
        Equiv.swap 4 8 * Equiv.swap 6 9})

variable {K : Type*} [Field K]

/-- The projective-linear alternative, for an odd prime power `q = p^r`. -/
def ProjectiveLinearCase (f : K[X]) : Prop :=
  ∃ (p r m : ℕ) (hp : Fact p.Prime),
    letI := hp
    Odd p ∧ 0 < r ∧ 3 ≤ m ∧ (p ^ r, m) ≠ (3, 4) ∧
      f.natDegree = ((p ^ r) ^ m - 1) / (p ^ r - 1) ∧
      ∃ ι : Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField p r) →* f.Gal,
        Function.Injective ι

/-- All the group alternatives in Zarhin (2002), without restricting to the paper's fields
or polynomial families. Degree and characteristic bounds belong to each cited theorem. -/
def AdmissibleGalois (f : K[X]) : Prop := by
  classical
  exact GaloisGroupIsSymmetric f ∨
    (galPerm f).range = alternatingGroup (f.rootSet f.SplittingField) ∨
    (f.natDegree = 11 ∧ Nonempty (f.Gal ≃* Mathieu11)) ∨
    (f.natDegree = 12 ∧
      (Nonempty (f.Gal ≃* Mathieu12) ∨ Nonempty (f.Gal ≃* Mathieu11))) ∨
    ProjectiveLinearCase f

/-- The manuscript's symmetric-group assumption is one of the source's alternatives. -/
theorem admissibleGalois_of_symmetric {f : K[X]} (h : GaloisGroupIsSymmetric f) :
    AdmissibleGalois f :=
  Or.inl h

end ArithmeticOfJacobiPolynomials.Zarhin
