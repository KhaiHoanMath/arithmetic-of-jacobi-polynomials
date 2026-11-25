/- Assembled by AxiomProver. -/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The absolute Galois group of a number field inside `Gal(ℚ̄/ℚ)`

Let `Ω/k` be a field extension and `K` an intermediate field. Restriction of scalars is
Mathlib's group homomorphism `AlgEquiv.restrictScalarsHom k : Gal(Ω/K) →* Gal(Ω/k)`
(injective by `AlgEquiv.restrictScalarsHom_injective`). We show:

* `range_restrictScalarsHom`: its image is the
  fixing subgroup `K.fixingSubgroup = Gal(Ω/K) ⊆ Gal(Ω/k)`;
* `continuous_restrictScalarsHom`: it is continuous for the Krull topologies (no finiteness);
* `continuous_fixingSubgroupEquiv`: for `K/k` finite, the inverse identification
  `IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* Gal(Ω/K)` is continuous for the
  subspace topology on `K.fixingSubgroup`; hence
  `fixingSubgroupContinuousMulEquiv K : K.fixingSubgroup ≃ₜ* Gal(Ω/K)` is an isomorphism of
  topological groups (with inverse `AlgEquiv.restrictScalarsHom k`);
* `fixingSubgroup_index_eq_finrank`, `fixingSubgroup_finiteIndex`: for `Ω/k` Galois,
  `[Gal(Ω/k) : Gal(Ω/K)] = [K : k]`, finite when `K/k` is finite.

The section `Rat` specializes to `Ω = AlgebraicClosure ℚ` and a number field
`K ⊆ ℚ̄` (`FiniteDimensional ℚ K`): `Gal(ℚ̄/K)` is an open, closed subgroup of `Gal(ℚ̄/ℚ)` of
index `[K : ℚ]`, topologically isomorphic to `AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ`.
-/

public section

open Topology

namespace ArithmeticOfJacobiPolynomials

namespace NumberFieldGalois

section General

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)

variable {K}

/-- A `K`-automorphism of `Ω` fixes `K`. -/
theorem restrictScalarsHom_mem_fixingSubgroup (σ : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom k σ ∈ K.fixingSubgroup :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => by
    exact σ.commutes ⟨x, hx⟩

/-- The identification `K.fixingSubgroup ≃* Gal(Ω/K)` does not change the underlying map. -/
@[simp]
theorem fixingSubgroupEquiv_apply (φ : K.fixingSubgroup) (x : Ω) :
    IntermediateField.fixingSubgroupEquiv K φ x = (φ : Ω ≃ₐ[k] Ω) x :=
  rfl

/-- `AlgEquiv.restrictScalarsHom k` is a left inverse of `IntermediateField.fixingSubgroupEquiv`. -/
@[simp]
theorem restrictScalarsHom_fixingSubgroupEquiv (φ : K.fixingSubgroup) :
    AlgEquiv.restrictScalarsHom k (IntermediateField.fixingSubgroupEquiv K φ) = (φ : Ω ≃ₐ[k] Ω) :=
  AlgEquiv.ext fun x => by rw [AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_apply,
    fixingSubgroupEquiv_apply]

/-- `AlgEquiv.restrictScalarsHom k` is a right inverse of
`IntermediateField.fixingSubgroupEquiv`. -/
@[simp]
theorem fixingSubgroupEquiv_restrictScalarsHom (σ : Ω ≃ₐ[K] Ω) :
    IntermediateField.fixingSubgroupEquiv K
        ⟨AlgEquiv.restrictScalarsHom k σ, restrictScalarsHom_mem_fixingSubgroup σ⟩ = σ :=
  AlgEquiv.ext fun x => by rw [fixingSubgroupEquiv_apply]; rfl

/-- The image of `Gal(Ω/K)` in `Gal(Ω/k)` is the fixing subgroup of `K`. -/
theorem range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom k : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[k] Ω)).range = K.fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    exact restrictScalarsHom_mem_fixingSubgroup σ
  · intro hτ
    exact ⟨IntermediateField.fixingSubgroupEquiv K ⟨τ, hτ⟩,
      restrictScalarsHom_fixingSubgroupEquiv ⟨τ, hτ⟩⟩

/-- If `K/k` and `E/K` are finite, then `E/k` is finite. -/
theorem finiteDimensional_restrictScalars [FiniteDimensional k K] (E : IntermediateField K Ω)
    [FiniteDimensional K E] : FiniteDimensional k (E.restrictScalars k) := by
  have h : Module.Finite k E := Module.Finite.trans K E
  exact h

/-- If `E/k` is finite, then the compositum `K(E)` is finite over `K`. -/
theorem finiteDimensional_adjoin_intermediateField (E : IntermediateField k Ω)
    [FiniteDimensional k E] : FiniteDimensional K (IntermediateField.adjoin K (E : Set Ω)) := by
  have h := IntermediateField.adjoin_rank_le_of_isAlgebraic_right (E := K) (L := E)
  exact Module.rank_lt_aleph0_iff.1
    (h.trans_lt (Module.rank_lt_aleph0 k E))

variable (K) in
/-- **Restriction of scalars is continuous** for the Krull topologies on `Gal(Ω/K)` and
`Gal(Ω/k)`. -/
theorem continuous_restrictScalarsHom :
    Continuous (AlgEquiv.restrictScalarsHom k : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[k] Ω)) := by
  refine continuous_of_continuousAt_one
    (AlgEquiv.restrictScalarsHom k : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[k] Ω)) ?_
  rw [continuousAt_def, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff k Ω s).1 hs
  refine (krullTopology_mem_nhds_one_iff K Ω _).2 ⟨IntermediateField.adjoin K (E : Set Ω),
    finiteDimensional_adjoin_intermediateField E, fun σ hσ => Set.mem_preimage.2 (hEs ?_)⟩
  have hσ' : ∀ x ∈ IntermediateField.adjoin K (E : Set Ω), σ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  exact hσ' x (IntermediateField.subset_adjoin K _ hx)

variable (K) in
/-- For `K/k` finite, the identification `K.fixingSubgroup ≃* Gal(Ω/K)` is continuous for the
subspace topology on `K.fixingSubgroup ⊆ Gal(Ω/k)` and the Krull topology on `Gal(Ω/K)`. -/
theorem continuous_fixingSubgroupEquiv [FiniteDimensional k K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K) := by
  refine continuous_of_continuousAt_one (IntermediateField.fixingSubgroupEquiv K) ?_
  rw [continuousAt_def, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  have hfin : FiniteDimensional k (E.restrictScalars k) := finiteDimensional_restrictScalars E
  refine (mem_nhds_induced Subtype.val _ _).2
    ⟨((E.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)),
      (E.restrictScalars k).fixingSubgroup_isOpen.mem_nhds (Subgroup.one_mem _),
      fun φ hφ => Set.mem_preimage.2 (hEs ?_)⟩
  have hφ' : ∀ x ∈ E.restrictScalars k, (φ : Ω ≃ₐ[k] Ω) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hφ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  rw [fixingSubgroupEquiv_apply]
  exact hφ' x hx

variable (K) in
/-- The inverse `Gal(Ω/K) → K.fixingSubgroup` of `IntermediateField.fixingSubgroupEquiv K` is
continuous: it is restriction of scalars. -/
theorem continuous_fixingSubgroupEquiv_symm :
    Continuous (IntermediateField.fixingSubgroupEquiv K).symm := by
  have h : Continuous fun σ : Ω ≃ₐ[K] Ω =>
      (⟨AlgEquiv.restrictScalarsHom k σ, restrictScalarsHom_mem_fixingSubgroup σ⟩ :
        K.fixingSubgroup) :=
    (continuous_restrictScalarsHom (k := k) K).subtype_mk _
  have e : ⇑(IntermediateField.fixingSubgroupEquiv K).symm = fun σ : Ω ≃ₐ[K] Ω =>
      (⟨AlgEquiv.restrictScalarsHom k σ, restrictScalarsHom_mem_fixingSubgroup σ⟩ :
        K.fixingSubgroup) := by
    funext σ
    apply (IntermediateField.fixingSubgroupEquiv K).injective
    rw [MulEquiv.apply_symm_apply, fixingSubgroupEquiv_restrictScalarsHom]
  rw [e]
  exact h

variable (K) in
/-- For `K/k` finite, the fixing subgroup `Gal(Ω/K) ⊆ Gal(Ω/k)` (subspace topology) is
isomorphic as a topological group to `Ω ≃ₐ[K] Ω` (Krull topology), via
`IntermediateField.fixingSubgroupEquiv`; the inverse is restriction of scalars. -/
noncomputable def fixingSubgroupContinuousMulEquiv [FiniteDimensional k K] :
    K.fixingSubgroup ≃ₜ* (Ω ≃ₐ[K] Ω) where
  toMulEquiv := IntermediateField.fixingSubgroupEquiv K
  continuous_toFun := continuous_fixingSubgroupEquiv K
  continuous_invFun := continuous_fixingSubgroupEquiv_symm K

/-- `fixingSubgroupContinuousMulEquiv K φ` is `φ` as a map. -/
@[simp]
theorem fixingSubgroupContinuousMulEquiv_apply [FiniteDimensional k K] (φ : K.fixingSubgroup)
    (x : Ω) : fixingSubgroupContinuousMulEquiv K φ x = (φ : Ω ≃ₐ[k] Ω) x :=
  fixingSubgroupEquiv_apply φ x

/-- The inverse of `fixingSubgroupContinuousMulEquiv K` is restriction of scalars. -/
@[simp]
theorem coe_fixingSubgroupContinuousMulEquiv_symm_apply [FiniteDimensional k K]
    (σ : Ω ≃ₐ[K] Ω) :
    ((fixingSubgroupContinuousMulEquiv K).symm σ : Ω ≃ₐ[k] Ω) =
      AlgEquiv.restrictScalarsHom k σ := by
  apply AlgEquiv.ext
  intro x
  rw [AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_apply,
    ← fixingSubgroupContinuousMulEquiv_apply,
    ContinuousMulEquiv.apply_symm_apply]

variable (K) in
/-- For `Ω/k` Galois, the index of `Gal(Ω/K)` in `Gal(Ω/k)` is `[K : k]`. -/
theorem fixingSubgroup_index_eq_finrank [IsGalois k Ω] :
    K.fixingSubgroup.index = Module.finrank k K :=
  (IntermediateField.finrank_eq_fixingSubgroup_index Ω K).symm

variable (K) in
/-- For `Ω/k` Galois and `K/k` finite, `Gal(Ω/K)` has finite index in `Gal(Ω/k)`. -/
theorem fixingSubgroup_finiteIndex [IsGalois k Ω] [FiniteDimensional k K] :
    K.fixingSubgroup.FiniteIndex :=
  ⟨by rw [fixingSubgroup_index_eq_finrank]; exact Module.finrank_pos.ne'⟩

end General

section Rat

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

/-- For a number field `K ⊆ ℚ̄`, `Gal(ℚ̄/K)` is open in `Gal(ℚ̄/ℚ)`. -/
theorem rat_isOpen_fixingSubgroup [FiniteDimensional ℚ K] :
    IsOpen (K.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
  K.fixingSubgroup_isOpen

/-- For a number field `K ⊆ ℚ̄`, `Gal(ℚ̄/K)` is closed in `Gal(ℚ̄/ℚ)`. -/
theorem rat_isClosed_fixingSubgroup [FiniteDimensional ℚ K] :
    IsClosed (K.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
  K.fixingSubgroup_isClosed

/-- `[Gal(ℚ̄/ℚ) : Gal(ℚ̄/K)] = [K : ℚ]`. -/
theorem rat_fixingSubgroup_index_eq_finrank :
    K.fixingSubgroup.index = Module.finrank ℚ K :=
  fixingSubgroup_index_eq_finrank K

/-- For a number field `K ⊆ ℚ̄`, `Gal(ℚ̄/K)` has finite index in `Gal(ℚ̄/ℚ)`. -/
theorem rat_fixingSubgroup_finiteIndex [FiniteDimensional ℚ K] :
    K.fixingSubgroup.FiniteIndex :=
  fixingSubgroup_finiteIndex K

/-- The image of `Gal(ℚ̄/K) = AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ` under restriction of
scalars is the fixing subgroup of `K` in `Gal(ℚ̄/ℚ)`. -/
theorem rat_range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom ℚ : (AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).range = K.fixingSubgroup :=
  range_restrictScalarsHom

/-- For a number field `K ⊆ ℚ̄`, the fixing subgroup of `K` in `Gal(ℚ̄/ℚ)` is isomorphic, as a
topological group, to `Gal(ℚ̄/K) = AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ`. -/
noncomputable def ratFixingSubgroupContinuousMulEquiv [FiniteDimensional ℚ K] :
    K.fixingSubgroup ≃ₜ* (AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) :=
  fixingSubgroupContinuousMulEquiv K

end Rat

end NumberFieldGalois

end ArithmeticOfJacobiPolynomials
