/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.AffineTransport
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Separable

/-!
# From permutation groups to Galois groups

General facts linking `Gal(f/F)`, acting on the roots of `f` in its splitting field through
`galPerm`, with the permutation-group arguments of Section 5:

* `galPerm` is injective;
* if `f` is irreducible, its image acts transitively on the roots, and in characteristic zero
  there are exactly `deg f` roots;
* `Gal(f/F) = S_n` exactly when the image of `galPerm` is everything;
* irreducibility and the property `Gal = S_n` are invariant under `f ↦ a f(bX + c)` with
  `a, b ≠ 0`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {F : Type*} [Field F]

theorem galPerm_injective (f : F[X]) : Function.Injective (galPerm f) := by
  intro σ τ h
  apply Gal.ext
  intro x hx
  have h' := congrArg (fun π : Equiv.Perm (f.rootSet f.SplittingField) =>
    ((π ⟨x, hx⟩ : f.rootSet f.SplittingField) : f.SplittingField)) h
  exact h'

/-- An irreducible polynomial has a transitive Galois group on its roots. -/
theorem isPretransitive_range_galPerm {f : F[X]} (hf : Irreducible f) :
    MulAction.IsPretransitive (galPerm f).range (f.rootSet f.SplittingField) := by
  refine ⟨fun x y => ?_⟩
  have hx := (mem_rootSet.mp x.2).2
  have hy := (mem_rootSet.mp y.2).2
  have hmy := minpoly.eq_of_irreducible hf hy
  have hev : aeval (x : f.SplittingField) (minpoly F (y : f.SplittingField)) = 0 := by
    rw [← hmy, map_mul, hx, zero_mul]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root
    (Algebra.IsAlgebraic.isAlgebraic (R := F) (y : f.SplittingField)) hev
  exact ⟨⟨galPerm f σ, σ, rfl⟩, Subtype.ext hσ⟩

/-- In characteristic zero an irreducible polynomial has `deg f` distinct roots in its
splitting field. -/
theorem card_rootSet_of_irreducible [CharZero F] {f : F[X]} (hf : Irreducible f) :
    Fintype.card (f.rootSet f.SplittingField) = f.natDegree :=
  card_rootSet_eq_natDegree hf.separable (SplittingField.splits f)

theorem galoisGroupIsSymmetric_iff_range_eq_top (f : F[X]) :
    GaloisGroupIsSymmetric f ↔ (galPerm f).range = ⊤ := by
  rw [galoisGroupIsSymmetric_iff, MonoidHom.range_eq_top]
  exact ⟨fun h => h.2, fun h => ⟨galPerm_injective f, h⟩⟩

section Affine

variable (f : F[X]) {a b : F} (c : F)

/-- Restriction from the splitting field of `f` to that of `g = a f(bX + c)` intertwines the
root actions through the fixed bijection `x ↦ (x - c)/b`. -/
theorem galPerm_restrict_affine (ha : a ≠ 0) (hb : b ≠ 0) (σ : f.Gal) :
    have := fact_splits_affine (a := a) (b := b) f c
    galPerm _ (Gal.restrict (C a * f.comp (C b * X + C c)) f.SplittingField σ) =
      ((affineRootsEquiv f c ha hb f.SplittingField).trans
        (Gal.rootsEquivRootsAux (C a * f.comp (C b * X + C c)) f.SplittingField).symm).permCongr
        (galPerm f σ) := by
  set g := C a * f.comp (C b * X + C c) with hg
  set E := f.SplittingField
  have hfact : Fact ((g.map (algebraMap F E)).Splits) := fact_splits_affine f c
  set ψ := Gal.rootsEquivRootsAux g E with hψ
  set A := affineRootsEquiv f c ha hb E with hA
  set τ := Gal.restrict g E σ with hτ
  ext1 y
  rw [Equiv.permCongr_apply]
  apply ψ.injective
  rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  have h1 : ψ (galPerm g τ y) = τ • ψ y := by
    rw [hψ, Gal.smul_def, Equiv.symm_apply_apply, galPerm_apply]
  rw [h1]
  apply Subtype.ext
  have h3 := Gal.restrict_smul (p := g) (E := E) σ (ψ y)
  rw [hτ, h3, coe_affineRootsEquiv, galPerm_apply]
  change σ (ψ y : E) = (algebraMap F E b)⁻¹ * (σ ((A.symm (ψ y) : E)) - algebraMap F E c)
  have h2 : ((ψ y : E)) = A (A.symm (ψ y)) := by rw [Equiv.apply_symm_apply]
  conv_lhs => rw [h2, coe_affineRootsEquiv]
  have hcb : σ (algebraMap F E b) = algebraMap F E b := AlgEquiv.commutes (σ : E ≃ₐ[F] E) b
  have hcc : σ (algebraMap F E c) = algebraMap F E c := AlgEquiv.commutes (σ : E ≃ₐ[F] E) c
  rw [map_mul, map_inv₀, map_sub, hcb, hcc]

/-- `Gal = S_n` passes from `f` to `a f(bX + c)`. -/
theorem GaloisGroupIsSymmetric.affine (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : GaloisGroupIsSymmetric f) :
    GaloisGroupIsSymmetric (C a * f.comp (C b * X + C c)) := by
  have := fact_splits_affine (a := a) (b := b) f c
  rw [galoisGroupIsSymmetric_iff] at hf ⊢
  refine ⟨galPerm_injective _, fun π => ?_⟩
  obtain ⟨σ, hσ⟩ := hf.2 (((affineRootsEquiv f c ha hb f.SplittingField).trans
    (Gal.rootsEquivRootsAux (C a * f.comp (C b * X + C c)) f.SplittingField).symm).symm.permCongr π)
  refine ⟨Gal.restrict _ f.SplittingField σ, ?_⟩
  rw [galPerm_restrict_affine f c ha hb σ, hσ]
  ext x
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- `Gal = S_n` passes from `a f(bX + c)` back to `f`. -/
theorem GaloisGroupIsSymmetric.of_affine (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : GaloisGroupIsSymmetric (C a * f.comp (C b * X + C c))) :
    GaloisGroupIsSymmetric f := by
  have h := eq_C_mul_comp_affine_inv (f := f) (g := C a * f.comp (C b * X + C c)) ha hb rfl
  rw [h]
  exact GaloisGroupIsSymmetric.affine _ _ (inv_ne_zero ha) (inv_ne_zero hb) hg

theorem affine_comp_affine_inv (hb : b ≠ 0) :
    (C b * X + C c).comp (C b⁻¹ * X + C (-(c / b))) = X := by
  simp only [add_comp, mul_comp, C_comp, X_comp]
  have e1 : b * (c / b) = c := by field_simp
  have e2 : b * -(c / b) + c = 0 := by linear_combination -e1
  rw [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hb, C_1, one_mul, add_assoc, ← C_mul,
    ← C_add, e2, C_0, add_zero]

theorem affine_inv_comp_affine (hb : b ≠ 0) :
    (C b⁻¹ * X + C (-(c / b))).comp (C b * X + C c) = X := by
  simp only [add_comp, mul_comp, C_comp, X_comp]
  have e2 : b⁻¹ * c + -(c / b) = 0 := by ring
  rw [mul_add, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb, C_1, one_mul, add_assoc, ← C_mul,
    ← C_add, e2, C_0, add_zero]

/-- Substitution `p ↦ p(bX + c)` as a multiplicative automorphism of `F[X]` (for `b ≠ 0`). -/
noncomputable def affineSubstEquiv (hb : b ≠ 0) : F[X] ≃* F[X] where
  toFun p := p.comp (C b * X + C c)
  invFun q := q.comp (C b⁻¹ * X + C (-(c / b)))
  left_inv p := by
    change (p.comp (C b * X + C c)).comp (C b⁻¹ * X + C (-(c / b))) = p
    rw [comp_assoc, affine_comp_affine_inv c hb, comp_X]
  right_inv q := by
    change (q.comp (C b⁻¹ * X + C (-(c / b)))).comp (C b * X + C c) = q
    rw [comp_assoc, affine_inv_comp_affine c hb, comp_X]
  map_mul' p q := mul_comp p q _

theorem affineSubstEquiv_apply (hb : b ≠ 0) (p : F[X]) :
    affineSubstEquiv c hb p = p.comp (C b * X + C c) := (rfl)

/-- Irreducibility is invariant under `f ↦ a f(bX + c)` with `a, b ≠ 0`. -/
theorem irreducible_C_mul_comp_affine_iff (ha : a ≠ 0) (hb : b ≠ 0) :
    Irreducible (C a * f.comp (C b * X + C c)) ↔ Irreducible f := by
  rw [irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit ha)), ← affineSubstEquiv_apply c hb]
  exact MulEquiv.irreducible_iff (affineSubstEquiv c hb)

end Affine

end ArithmeticOfJacobiPolynomials
