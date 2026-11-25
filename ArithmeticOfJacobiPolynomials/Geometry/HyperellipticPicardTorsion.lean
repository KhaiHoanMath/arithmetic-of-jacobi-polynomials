/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchIndependence
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Hyperelliptic

/-!
# Branch classes generate all two-torsion in the geometric Picard group

For the hyperelliptic projective model over an algebraically closed field,
Stacks Tag 0C1Z computes the order of the whole Picard two-torsion group. The
proved branch-image cardinalities then show that every two-torsion class is a
sum of branch differences, in both degree parities (§6.5).
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

universe u

namespace ArithmeticOfJacobiPolynomials.Hyperelliptic

variable {k : Type u} [Field k] [IsAlgClosed k] {f : k[X]}

/-- The two-torsion of the Picard group has order `2^(2g)` by Stacks Tag 0C1Z. -/
theorem card_picardTwoTorsion (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) :
    Nat.card (AddSubgroup.torsionBy (Stacks.Picard.ofScheme (projectiveModel f)) (2 : ℤ)) =
      2 ^ (2 * genus f) := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_pi_zmod h2 hf hdeg 2 (by omega)
    (isUnit_iff_ne_zero.mpr h2)
  change Nat.card (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme (projectiveModel f))
    (2 : ℤ)) = _
  have hc := Nat.card_congr e.toEquiv
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hc
  simpa only [Nat.cast_ofNat, genus] using hc

/-- In even degree every geometric Picard two-torsion class is a sum of finite branch
point differences. -/
theorem range_branchTorsionHom_eq_twoTorsion (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f) :
    (branchTorsionHom h2 hf c₀).range =
      AddSubgroup.torsionBy (Stacks.Picard.ofScheme (projectiveModel f)) (2 : ℤ) := by
  have hdeg : 0 < f.natDegree := by
    rw [← card_branchRoot hf hsplit]
    exact Fintype.card_pos_iff.mpr ⟨c₀⟩
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_pi_zmod h2 hf hdeg 2 (by omega)
    (isUnit_iff_ne_zero.mpr h2)
  let : Finite (AddSubgroup.torsionBy
      (Stacks.Picard.ofScheme (projectiveModel f)) (2 : ℤ)) := Finite.of_equiv _ e.toEquiv.symm
  apply AddSubgroup.eq_of_le_of_card_ge
  · rintro x ⟨v, rfl⟩
    exact (AddSubgroup.torsionBy.nsmul_iff (n := 2)).mpr
      (two_nsmul_branchTorsionHom h2 hf c₀ v)
  · rw [card_picardTwoTorsion h2 hf hdeg, card_range_branchTorsionHom h2 hf hsplit heven c₀]

/-- In odd degree every geometric Picard two-torsion class is a sum of differences of
finite branch points and the unique branch point at infinity. -/
theorem range_branchTorsionHomInf_eq_twoTorsion (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hsplit : f.roots.card = f.natDegree) (hodd : Odd f.natDegree) :
    (branchTorsionHomInf (eval_zero_reflect_of_odd hodd) h2 hf hdeg).range =
      AddSubgroup.torsionBy (Stacks.Picard.ofScheme (projectiveModel f)) (2 : ℤ) := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_pi_zmod h2 hf hdeg 2 (by omega)
    (isUnit_iff_ne_zero.mpr h2)
  let : Finite (AddSubgroup.torsionBy
      (Stacks.Picard.ofScheme (projectiveModel f)) (2 : ℤ)) := Finite.of_equiv _ e.toEquiv.symm
  apply AddSubgroup.eq_of_le_of_card_ge
  · rintro x ⟨v, rfl⟩
    exact (AddSubgroup.torsionBy.nsmul_iff (n := 2)).mpr
      (two_nsmul_branchTorsionHomInf (eval_zero_reflect_of_odd hodd) h2 hf hdeg v)
  · rw [card_picardTwoTorsion h2 hf hdeg,
      card_range_branchTorsionHomInf (eval_zero_reflect_of_odd hodd)
        h2 hf hdeg hsplit hodd]

end ArithmeticOfJacobiPolynomials.Hyperelliptic
