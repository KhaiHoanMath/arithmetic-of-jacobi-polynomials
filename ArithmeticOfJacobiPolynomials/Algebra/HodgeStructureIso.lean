/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.HodgeGroupPower
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Hodge classes and groups under rational Hodge isomorphisms

Transport along a rational linear equivalence intertwining the real complex structures.
Tensor equivalences and conjugation of general linear groups use Mathlib constructions.
These lemmas let the Betti comparison of a power inherit the proved diagonal
Hodge and Mumford–Tate group formulas.
-/

@[expose] public noncomputable section

namespace ArithmeticOfJacobiPolynomials

open TensorProduct

variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

/-- Tensor transport: covariant on vectors and contravariant on dual vectors. -/
def hodgeTensorEquiv (e : M ≃ₗ[ℚ] N) (m n : ℕ) :
    TensorSpace ℚ M m n ≃ₗ[ℚ] TensorSpace ℚ N m n :=
  TensorProduct.congr (PiTensorProduct.congr fun _ : Fin m => e)
    (PiTensorProduct.congr fun _ : Fin n => e.symm.dualMap)

theorem hodgeTensorEquiv_apply (e : M ≃ₗ[ℚ] N) (m n : ℕ) (t : TensorSpace ℚ M m n) :
    hodgeTensorEquiv e m n t =
      tensorPush (fun _ : Fin m => (e : M →ₗ[ℚ] N))
        (fun _ : Fin n => (e.symm : N →ₗ[ℚ] M)) t := rfl

theorem hodgeTensorEquiv_symm_apply (e : M ≃ₗ[ℚ] N) (m n : ℕ)
    (t : TensorSpace ℚ N m n) :
    (hodgeTensorEquiv e m n).symm t = hodgeTensorEquiv e.symm m n t := rfl

/-- Mathlib's conjugation equivalence, expressed on linear automorphisms. -/
def hodgeAutCongr (e : M ≃ₗ[ℚ] N) : (M ≃ₗ[ℚ] M) ≃* (N ≃ₗ[ℚ] N) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ M).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ N))

theorem hodgeAutCongr_apply (e : M ≃ₗ[ℚ] N) (g : M ≃ₗ[ℚ] M) (y : N) :
    hodgeAutCongr e g y = e (g (e.symm y)) := rfl

theorem hodgeAutCongr_symm_apply (e : M ≃ₗ[ℚ] N) (g : N ≃ₗ[ℚ] N) :
    (hodgeAutCongr e).symm g = hodgeAutCongr e.symm g := rfl

theorem hodgeTensorEquiv_tensorMap (e : M ≃ₗ[ℚ] N) (m n : ℕ)
    (g : M ≃ₗ[ℚ] M) (t : TensorSpace ℚ M m n) :
    hodgeTensorEquiv e m n (tensorMap m n g t) =
      tensorMap m n (hodgeAutCongr e g) (hodgeTensorEquiv e m n t) := by
  apply tensorPush_tensorMap
  · intro k x
    simp only [LinearEquiv.coe_coe, hodgeAutCongr_apply, LinearEquiv.symm_apply_apply]
  · intro k y
    simp only [LinearEquiv.coe_coe, hodgeAutCongr_apply, LinearEquiv.symm_apply_apply]

namespace HodgeStructureNegOne

variable (H : HodgeStructureNegOne M) (K : HodgeStructureNegOne N) (e : M ≃ₗ[ℚ] N)
  (he : ∀ x, (e : M →ₗ[ℚ] N).baseChange ℝ (H.J x) =
    K.J ((e : M →ₗ[ℚ] N).baseChange ℝ x))

include he

/-- The inverse comparison also intertwines the complex structures. -/
theorem inverse_commutes_J (y : ℝ ⊗[ℚ] N) :
    (e.symm : N →ₗ[ℚ] M).baseChange ℝ (K.J y) =
      H.J ((e.symm : N →ₗ[ℚ] M).baseChange ℝ y) := by
  apply (e.baseChange ℚ ℝ).injective
  change (e.baseChange ℚ ℝ) ((e.baseChange ℚ ℝ).symm (K.J y)) =
    (e : M →ₗ[ℚ] N).baseChange ℝ
      (H.J ((e.baseChange ℚ ℝ).symm y))
  rw [LinearEquiv.apply_symm_apply, he]
  change K.J y = K.J ((e.baseChange ℚ ℝ) ((e.baseChange ℚ ℝ).symm y))
  rw [LinearEquiv.apply_symm_apply]

/-- Rational Hodge isomorphisms carry exactly the Hodge classes. -/
theorem hodgeTensorEquiv_mem_iff {m n : ℕ} {t : TensorSpace ℚ M m n} :
    hodgeTensorEquiv e m n t ∈ K.hodgeClasses m n ↔ t ∈ H.hodgeClasses m n := by
  constructor
  · intro ht
    have h := tensorPush_mem_hodgeClasses K H
      (fun _ : Fin m => (e.symm : N →ₗ[ℚ] M))
      (fun _ : Fin n => (e : M →ₗ[ℚ] N))
      (fun _ => inverse_commutes_J H K e he) (fun _ x => (he x).symm) ht
    change hodgeTensorEquiv e.symm m n (hodgeTensorEquiv e m n t) ∈ H.hodgeClasses m n at h
    rw [← hodgeTensorEquiv_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  · exact tensorPush_mem_hodgeClasses H K
      (fun _ : Fin m => (e : M →ₗ[ℚ] N))
      (fun _ : Fin n => (e.symm : N →ₗ[ℚ] M))
      (fun _ => he) (fun _ y => (inverse_commutes_J H K e he y).symm)

/-- Conjugating a Hodge-group element gives a Hodge-group element. -/
theorem hodgeAutCongr_mem_hodgeGroup {g : M ≃ₗ[ℚ] M} (hg : g ∈ H.hodgeGroup) :
    hodgeAutCongr e g ∈ K.hodgeGroup := by
  intro m n t ht
  obtain ⟨s, rfl⟩ := (hodgeTensorEquiv e m n).surjective t
  have hs := (hodgeTensorEquiv_mem_iff H K e he).1 ht
  rw [← hodgeTensorEquiv_tensorMap, hg m n s hs]

/-- Conjugating a Mumford–Tate-group element preserves its common Tate multiplier. -/
theorem hodgeAutCongr_mem_mumfordTateGroup {g : M ≃ₗ[ℚ] M}
    (hg : g ∈ H.mumfordTateGroup) : hodgeAutCongr e g ∈ K.mumfordTateGroup := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  intro m n p hp t ht
  obtain ⟨s, rfl⟩ := (hodgeTensorEquiv e m n).surjective t
  have hs := (hodgeTensorEquiv_mem_iff H K e he).1 ht
  rw [← hodgeTensorEquiv_tensorMap, hc m n p hp s hs, map_smul]

/-- Hodge groups are transported by the rational Hodge comparison. -/
theorem hodgeGroup_eq_map : K.hodgeGroup = H.hodgeGroup.map (hodgeAutCongr e).toMonoidHom := by
  ext g
  constructor
  · intro hg
    have h := hodgeAutCongr_mem_hodgeGroup K H e.symm (inverse_commutes_J H K e he) hg
    exact ⟨hodgeAutCongr e.symm g, h, by
      rw [← hodgeAutCongr_symm_apply]
      exact (hodgeAutCongr e).apply_symm_apply g⟩
  · rintro ⟨g, hg, rfl⟩
    exact hodgeAutCongr_mem_hodgeGroup H K e he hg

/-- Mumford–Tate groups are transported by the same rational comparison. -/
theorem mumfordTateGroup_eq_map :
    K.mumfordTateGroup = H.mumfordTateGroup.map (hodgeAutCongr e).toMonoidHom := by
  ext g
  constructor
  · intro hg
    have h := hodgeAutCongr_mem_mumfordTateGroup K H e.symm (inverse_commutes_J H K e he) hg
    exact ⟨hodgeAutCongr e.symm g, h, by
      rw [← hodgeAutCongr_symm_apply]
      exact (hodgeAutCongr e).apply_symm_apply g⟩
  · rintro ⟨g, hg, rfl⟩
    exact hodgeAutCongr_mem_mumfordTateGroup H K e he hg

end HodgeStructureNegOne

end ArithmeticOfJacobiPolynomials
