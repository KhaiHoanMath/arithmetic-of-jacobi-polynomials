/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.EllAdicCohomologyFunctoriality
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeGeometricPoints

/-!
# The Galois action on `ℓ`-adic cohomology of a base change

Let `K` be a field, `L/K` a field extension (for instance `L = K̄`) and `X : Over (Spec K)` a
scheme over `K`.

* `ArithmeticOfJacobiPolynomials.EllAdicGalois.baseChange K L X` is the scheme `X_L = X ×_{Spec K}
Spec L`
  (the pullback of `X ⟶ Spec K` along `Spec L ⟶ Spec K`).
* For `σ : L ≃ₐ[K] L`, `galoisMap K L X σ : X_L ⟶ X_L` is `1 × Spec σ`
  (`pullback.map` of `𝟙 X` and `Spec σ`, the underlying morphism of `GroupScheme.specAut K L σ`).
  Since `Spec` is contravariant,
  `galoisMap (σ * τ) = galoisMap σ ≫ galoisMap τ` (`galoisMap_mul`) and `galoisMap 1 = 𝟙`
  (`galoisMap_one`); `galoisAut K L X σ` is the corresponding automorphism of `X_L`.
* `galoisRep K L X ℓ n : (L ≃ₐ[K] L) →* Multiplicative (AddAut (H^n(X_L, ℤ_ℓ)))` is the action
  of `L ≃ₐ[K] L` on `ℓ`-adic cohomology (`AddAut` is an additive group in Mathlib, hence
  `Multiplicative`). It is a group homomorphism (a left action) and `σ` acts by pullback along
  `1 × Spec σ` (`galoisRep_apply`):
  `toAdd (galoisRep K L X ℓ n σ) α = EllAdicCohomology.pullbackMap ℓ n (galoisAut K L X σ) α`.

No continuity of the action, comparison theorems or cycle classes are treated.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ArithmeticOfJacobiPolynomials

namespace EllAdicGalois

open GroupScheme

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] (X : Over (Spec (.of K)))

/-- The base change `X_L = X ×_{Spec K} Spec L` of a scheme over `K`. -/
noncomputable abbrev baseChange : Scheme.{u} :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The automorphism `1 × Spec σ` of `X_L` attached to `σ : L ≃ₐ[K] L`, as a morphism. -/
@[expose]
noncomputable def galoisMap (σ : L ≃ₐ[K] L) : baseChange K L X ⟶ baseChange K L X :=
  pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (𝟙 X.left)
    (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (𝟙 _) (by simp)
    (by rw [Category.comp_id]; exact (Over.w (specAut K L σ)).symm)

variable {K L X}

@[reassoc]
theorem galoisMap_fst (σ : L ≃ₐ[K] L) :
    galoisMap K L X σ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem galoisMap_snd (σ : L ≃ₐ[K] L) :
    galoisMap K L X σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : L →+* L)) :=
  pullback.lift_snd _ _ _

/-- `1 × Spec 1` is the identity. -/
theorem galoisMap_one : galoisMap K L X 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [galoisMap_fst, Category.id_comp]
  · rw [galoisMap_snd, specMap_algEquiv_one, Category.comp_id, Category.id_comp]

/-- `1 × Spec (σ * τ) = (1 × Spec σ) ≫ (1 × Spec τ)`. -/
theorem galoisMap_mul (σ τ : L ≃ₐ[K] L) :
    galoisMap K L X (σ * τ) = galoisMap K L X σ ≫ galoisMap K L X τ := by
  apply pullback.hom_ext
  · rw [galoisMap_fst, Category.assoc, galoisMap_fst, galoisMap_fst]
  · rw [galoisMap_snd, Category.assoc, galoisMap_snd, galoisMap_snd_assoc,
      specMap_algEquiv_mul]

variable (K L X) in
/-- The automorphism `1 × Spec σ` of `X_L`, with inverse `1 × Spec σ⁻¹`. -/
@[expose]
noncomputable def galoisAut (σ : L ≃ₐ[K] L) : baseChange K L X ≅ baseChange K L X where
  hom := galoisMap K L X σ
  inv := galoisMap K L X σ⁻¹
  hom_inv_id := by rw [← galoisMap_mul, mul_inv_cancel, galoisMap_one]
  inv_hom_id := by rw [← galoisMap_mul, inv_mul_cancel, galoisMap_one]

@[simp]
theorem galoisAut_hom (σ : L ≃ₐ[K] L) : (galoisAut K L X σ).hom = galoisMap K L X σ :=
  rfl

variable (K L X) in
/-- `σ ↦ 1 × Spec σ⁻¹` as a group homomorphism `(L ≃ₐ[K] L) →* Aut X_L` (recall that in
`Aut X_L = (X_L ≅ X_L)`, `x * y` is `y ≪≫ x`). -/
@[expose]
noncomputable def galoisAutHom : (L ≃ₐ[K] L) →* Aut (baseChange K L X) where
  toFun σ := Aut.of (galoisAut K L X σ⁻¹)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change galoisMap K L X 1⁻¹ = 𝟙 _
    rw [inv_one, galoisMap_one]
  map_mul' σ τ := by
    apply Aut.ext
    apply Iso.ext
    change galoisMap K L X (σ * τ)⁻¹ = galoisMap K L X τ⁻¹ ≫ galoisMap K L X σ⁻¹
    rw [mul_inv_rev, galoisMap_mul]

variable (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)

variable (K L X) in
/-- The action of `L ≃ₐ[K] L` on the `ℓ`-adic cohomology `H^n(X_L, ℤ_ℓ)` of the base change,
a group homomorphism to the additive automorphisms. -/
@[expose]
noncomputable def galoisRep :
    (L ≃ₐ[K] L) →* Multiplicative (AddAut ((baseChange K L X).EllAdicCohomology ℓ n)) :=
  (EllAdicCohomology.autAction (baseChange K L X) ℓ n).comp (galoisAutHom K L X)

/-- `σ` acts on `H^n(X_L, ℤ_ℓ)` by pullback along `1 × Spec σ`. -/
theorem galoisRep_apply (σ : L ≃ₐ[K] L) (α : (baseChange K L X).EllAdicCohomology ℓ n) :
    Multiplicative.toAdd (galoisRep K L X ℓ n σ) α =
      EllAdicCohomology.pullbackMap ℓ n (galoisAut K L X σ) α := by
  change EllAdicCohomology.pullbackMap ℓ n (galoisAut K L X σ⁻¹).symm α = _
  rw [EllAdicCohomology.pullbackMap_congr ℓ n (galoisAut K L X σ⁻¹).symm (galoisAut K L X σ)
    (by change galoisMap K L X σ⁻¹⁻¹ = galoisMap K L X σ; rw [inv_inv])]

end EllAdicGalois

end ArithmeticOfJacobiPolynomials
