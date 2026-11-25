/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.TateProduct
public import ArithmeticOfJacobiPolynomials.Algebra.TateGeometricAction
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Products and powers of commutative group schemes: points, Tate modules, Galois actions

Let `K` be a field, `L/K` a field extension and `A`, `B` commutative group schemes over `K`
(`A B : Over (Spec K)` with `[GrpObj] [IsCommMonObj]`). The product `A ⊗ B` (the cartesian
product in `Over (Spec K)`, i.e. the fibre product over `Spec K`) is a commutative group object
for Mathlib's product group structure (`GrpObj.tensorObj.instTensorObj`,
`instIsCommMonObjTensorObj`).

* `GroupScheme.GeomPoints.prodEquiv K L A B : (A ⊗ B)(L) ≃+ A(L) × B(L)`, `P ↦ (P ≫ fst, P ≫ snd)`,
  inverse `(P, Q) ↦ lift P Q`; it is Galois-equivariant (`GeomPoints.prodEquiv_smul`).
* `GroupScheme.powObj K A h`, the `h`-fold product `A ⊗ (A ⊗ (⋯ ⊗ 𝟙_))` (iterated tensor), a
  commutative group object, with `GeomPoints.powEquiv K L A h : A^h(L) ≃+ (Fin h → A(L))`, Galois
  equivariant for the diagonal action (`GeomPoints.powEquiv_smul`).
* Tate modules: `GroupScheme.tateProdEquiv`, `GroupScheme.rationalTateProdEquiv` (equivariant for
  the product representation), `GroupScheme.tatePowEquiv`, and
  `GroupScheme.rationalTatePowEquiv ℓ K L A h : V_ℓ(A^h(L)) ≃ ⨁_{i < h} V_ℓ(A(L))`, intertwining the
  Galois representation with the diagonal one (`rationalTatePowEquiv_representation`); hence
  `GroupScheme.ker_rationalTate_representation_powObj`: for `h ≥ 1` the Galois group acts on
  `V_ℓ(A^h(L))` and on `V_ℓ(A(L))` with the same kernel (proof of Corollary 6.6: "for powers, the
  groups act diagonally on direct sums").

* `GroupScheme.isProper_tensorObj_hom`, `GroupScheme.smooth_tensorObj_hom`: properness and
  smoothness over `K` pass to products. (Geometric integrality of products is in
  `ArithmeticOfJacobiPolynomials.Geometry.AbelianVarietyProduct`.)

This is generic: nothing here is specific to Jacobians or abelian varieties.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry PadicInt
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace ArithmeticOfJacobiPolynomials

open Stacks.AbelianGroup

/-- `M × (Fin h → M) ≃+ (Fin (h + 1) → M)`, `(a, f) ↦ Fin.cons a f`. -/
@[expose]
def finConsAddEquiv (M : Type*) [AddCommGroup M] (h : ℕ) :
    M × (Fin h → M) ≃+ (Fin (h + 1) → M) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp only [Fin.cons_zero, Fin.tail_cons]
  right_inv f := by simp only [Fin.cons_self_tail]
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Prod.fst_add, Fin.cons_zero, Pi.add_apply]
    · simp only [Prod.snd_add, Fin.cons_succ, Pi.add_apply]

/-- `finConsAddEquiv M h (a, f) = Fin.cons a f`. -/
theorem finConsAddEquiv_apply {M : Type*} [AddCommGroup M] {h : ℕ} (p : M × (Fin h → M)) :
    finConsAddEquiv M h p = Fin.cons p.1 p.2 :=
  rfl

/-- `finConsAddEquiv` is equivariant for diagonal actions. -/
theorem finConsAddEquiv_smul {G M : Type*} [AddCommGroup M] [SMul G M] {h : ℕ} (g : G) (a : M)
    (f : Fin h → M) : finConsAddEquiv M h (g • a, g • f) = g • finConsAddEquiv M h (a, f) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [finConsAddEquiv_apply, Fin.cons_zero, Pi.smul_apply]
  · simp only [finConsAddEquiv_apply, Fin.cons_succ, Pi.smul_apply]

namespace GroupScheme

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

section Prod

variable (A B : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

namespace GeomPoints

/-- The first projection `(A ⊗ B)(L) →+ A(L)`, `P ↦ P ≫ fst`. -/
@[expose]
noncomputable def fstHom : GeomPoints K L (A ⊗ B) →+ GeomPoints K L A where
  toFun P := (toHom K L A).symm (toHom K L (A ⊗ B) P ≫ fst A B)
  map_zero' := (toHom K L A).injective (by
    simp only [Equiv.apply_symm_apply, toHom_zero]
    exact (IsMonHom.monoidHom (fst A B) (specOver K L)).map_one)
  map_add' P Q := (toHom K L A).injective (by
    simp only [Equiv.apply_symm_apply, toHom_add]
    exact (IsMonHom.monoidHom (fst A B) (specOver K L)).map_mul _ _)

/-- The second projection `(A ⊗ B)(L) →+ B(L)`, `P ↦ P ≫ snd`. -/
@[expose]
noncomputable def sndHom : GeomPoints K L (A ⊗ B) →+ GeomPoints K L B where
  toFun P := (toHom K L B).symm (toHom K L (A ⊗ B) P ≫ snd A B)
  map_zero' := (toHom K L B).injective (by
    simp only [Equiv.apply_symm_apply, toHom_zero]
    exact (IsMonHom.monoidHom (snd A B) (specOver K L)).map_one)
  map_add' P Q := (toHom K L B).injective (by
    simp only [Equiv.apply_symm_apply, toHom_add]
    exact (IsMonHom.monoidHom (snd A B) (specOver K L)).map_mul _ _)

variable {K L A B}

/-- On morphisms, `fstHom K L A B P = P ≫ fst`. -/
@[simp]
theorem toHom_fstHom (P : GeomPoints K L (A ⊗ B)) :
    toHom K L A (fstHom K L A B P) = toHom K L (A ⊗ B) P ≫ fst A B :=
  (toHom K L A).apply_symm_apply _

/-- On morphisms, `sndHom K L A B P = P ≫ snd`. -/
@[simp]
theorem toHom_sndHom (P : GeomPoints K L (A ⊗ B)) :
    toHom K L B (sndHom K L A B P) = toHom K L (A ⊗ B) P ≫ snd A B :=
  (toHom K L B).apply_symm_apply _

variable (K L A B)

/-- **Points of a product.** `(A ⊗ B)(L) ≃+ A(L) × B(L)`, `P ↦ (P ≫ fst, P ≫ snd)`, with inverse
`(P, Q) ↦ lift P Q`; additive for Mathlib's group structure on the product `A ⊗ B`. -/
@[expose]
noncomputable def prodEquiv : GeomPoints K L (A ⊗ B) ≃+ GeomPoints K L A × GeomPoints K L B where
  toFun P := (fstHom K L A B P, sndHom K L A B P)
  invFun Q := (toHom K L (A ⊗ B)).symm (lift (toHom K L A Q.1) (toHom K L B Q.2))
  left_inv P := (toHom K L (A ⊗ B)).injective (by
    simp only [Equiv.apply_symm_apply, toHom_fstHom, toHom_sndHom, lift_comp_fst_snd])
  right_inv Q := Prod.ext ((toHom K L A).injective (by
      simp only [toHom_fstHom, Equiv.apply_symm_apply, lift_fst]))
    ((toHom K L B).injective (by simp only [toHom_sndHom, Equiv.apply_symm_apply, lift_snd]))
  map_add' P Q := by simp only [map_add, Prod.mk_add_mk]

variable {K L A B}

/-- `prodEquiv K L A B P = (P ≫ fst, P ≫ snd)`. -/
theorem prodEquiv_apply (P : GeomPoints K L (A ⊗ B)) :
    prodEquiv K L A B P = (fstHom K L A B P, sndHom K L A B P) :=
  rfl

/-- On morphisms, the inverse of `prodEquiv` is `lift`. -/
theorem toHom_prodEquiv_symm (Q : GeomPoints K L A × GeomPoints K L B) :
    toHom K L (A ⊗ B) ((prodEquiv K L A B).symm Q) = lift (toHom K L A Q.1) (toHom K L B Q.2) :=
  (toHom K L (A ⊗ B)).apply_symm_apply _

/-- The first projection is Galois-equivariant. -/
theorem fstHom_smul (σ : L ≃ₐ[K] L) (P : GeomPoints K L (A ⊗ B)) :
    fstHom K L A B (σ • P) = σ • fstHom K L A B P :=
  (toHom K L A).injective (by rw [toHom_fstHom, toHom_smul, toHom_smul, toHom_fstHom,
    Category.assoc])

/-- The second projection is Galois-equivariant. -/
theorem sndHom_smul (σ : L ≃ₐ[K] L) (P : GeomPoints K L (A ⊗ B)) :
    sndHom K L A B (σ • P) = σ • sndHom K L A B P :=
  (toHom K L B).injective (by rw [toHom_sndHom, toHom_smul, toHom_smul, toHom_sndHom,
    Category.assoc])

/-- **Galois equivariance.** `(A ⊗ B)(L) ≃+ A(L) × B(L)` commutes with the Galois action (acting
componentwise on `A(L) × B(L)`). -/
theorem prodEquiv_smul (σ : L ≃ₐ[K] L) (P : GeomPoints K L (A ⊗ B)) :
    prodEquiv K L A B (σ • P) = σ • prodEquiv K L A B P := by
  rw [prodEquiv_apply, prodEquiv_apply, fstHom_smul, sndHom_smul, Prod.smul_mk]

end GeomPoints

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Tate module of a product.** `T_ℓ((A ⊗ B)(L)) ≃ T_ℓ(A(L)) × T_ℓ(B(L))`. -/
@[expose]
noncomputable def tateProdEquiv :
    tateModule (GeomPoints K L (A ⊗ B)) ℓ ≃ₗ[ℤ_[ℓ]]
      tateModule (GeomPoints K L A) ℓ × tateModule (GeomPoints K L B) ℓ :=
  (tateModule.mapEquiv ℓ (GeomPoints.prodEquiv K L A B)).trans (tateModule.prodEquiv ℓ _ _)

/-- **Galois equivariance.** `T_ℓ((A ⊗ B)(L)) ≃ T_ℓ(A(L)) × T_ℓ(B(L))` intertwines the Galois
representation on `T_ℓ((A ⊗ B)(L))` with the product of the Galois representations. -/
theorem tateProdEquiv_galoisRepresentation (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L (A ⊗ B)) ℓ) :
    tateProdEquiv K L A B ℓ (galoisRepresentation ℓ K L (A ⊗ B) σ x) =
      ((galoisRepresentation ℓ K L A).prod (galoisRepresentation ℓ K L B)) σ
        (tateProdEquiv K L A B ℓ x) :=
  (congrArg (tateModule.prodEquiv ℓ _ _)
    (tateModule.mapEquiv_representation (L ≃ₐ[K] L) (GeomPoints.prodEquiv K L A B)
      GeomPoints.prodEquiv_smul σ x)).trans
    (tateModule.prodEquiv_representation (L ≃ₐ[K] L) σ _)

/-- **Rational Tate module of a product.** `V_ℓ((A ⊗ B)(L)) ≃ V_ℓ(A(L)) × V_ℓ(B(L))`. -/
@[expose]
noncomputable def rationalTateProdEquiv :
    rationalTate ℓ (GeomPoints K L (A ⊗ B)) ≃ₗ[ℚ_[ℓ]]
      rationalTate ℓ (GeomPoints K L A) × rationalTate ℓ (GeomPoints K L B) :=
  (rationalTate.mapEquiv ℓ (GeomPoints.prodEquiv K L A B)).trans (rationalTate.prodEquiv ℓ _ _)

/-- **Galois equivariance.** `V_ℓ((A ⊗ B)(L)) ≃ V_ℓ(A(L)) × V_ℓ(B(L))` intertwines the Galois
representations (product representation on the right). -/
theorem rationalTateProdEquiv_representation (σ : L ≃ₐ[K] L)
    (v : rationalTate ℓ (GeomPoints K L (A ⊗ B))) :
    rationalTateProdEquiv K L A B ℓ
        (rationalTate.representation ℓ (GeomPoints K L (A ⊗ B)) (L ≃ₐ[K] L) σ v) =
      ((rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)).prod
        (rationalTate.representation ℓ (GeomPoints K L B) (L ≃ₐ[K] L))) σ
        (rationalTateProdEquiv K L A B ℓ v) :=
  (congrArg (rationalTate.prodEquiv ℓ _ _)
    (rationalTate.mapEquiv_representation (L ≃ₐ[K] L) (GeomPoints.prodEquiv K L A B)
      GeomPoints.prodEquiv_smul σ v)).trans
    (rationalTate.prodEquiv_representation (L ≃ₐ[K] L) σ _)

/-- Given `e : B(L) ≃+ (Fin h → A(L))`, the isomorphism
`(A ⊗ B)(L) ≃+ A(L) × B(L) ≃+ A(L) × (Fin h → A(L)) ≃+ (Fin (h + 1) → A(L))`. -/
@[expose]
noncomputable def GeomPoints.consEquiv {h : ℕ}
    (e : GeomPoints K L B ≃+ (Fin h → GeomPoints K L A)) :
    GeomPoints K L (A ⊗ B) ≃+ (Fin (h + 1) → GeomPoints K L A) :=
  (GeomPoints.prodEquiv K L A B).trans
    (((AddEquiv.refl _).prodCongr e).trans (finConsAddEquiv _ h))

variable {K L A B} in
/-- `consEquiv e P = Fin.cons (P ≫ fst) (e (P ≫ snd))`. -/
theorem GeomPoints.consEquiv_apply {h : ℕ} (e : GeomPoints K L B ≃+ (Fin h → GeomPoints K L A))
    (P : GeomPoints K L (A ⊗ B)) :
    GeomPoints.consEquiv K L A B e P =
      finConsAddEquiv _ h (GeomPoints.fstHom K L A B P, e (GeomPoints.sndHom K L A B P)) :=
  rfl

variable {K L A B} in
/-- If `e` is Galois-equivariant, so is `GeomPoints.consEquiv e`. -/
theorem GeomPoints.consEquiv_smul {h : ℕ} (e : GeomPoints K L B ≃+ (Fin h → GeomPoints K L A))
    (he : ∀ (σ : L ≃ₐ[K] L) (P : GeomPoints K L B), e (σ • P) = σ • e P) (σ : L ≃ₐ[K] L)
    (P : GeomPoints K L (A ⊗ B)) :
    GeomPoints.consEquiv K L A B e (σ • P) = σ • GeomPoints.consEquiv K L A B e P := by
  rw [GeomPoints.consEquiv_apply, GeomPoints.consEquiv_apply, GeomPoints.fstHom_smul,
    GeomPoints.sndHom_smul, he, finConsAddEquiv_smul]

end Prod

section Pow

variable (A : Over (Spec (.of K)))

/-- The `h`-fold product `A^h = A ⊗ (A ⊗ (⋯ ⊗ (A ⊗ 𝟙_)))` in `Over (Spec K)` (iterated cartesian
product, the empty product being the terminal object `𝟙_ = Spec K`). -/
@[expose]
noncomputable def powObj : ℕ → Over (Spec (.of K))
  | 0 => 𝟙_ (Over (Spec (.of K)))
  | h + 1 => A ⊗ powObj h

/-- `A^0` is the terminal object. -/
theorem powObj_zero : powObj K A 0 = 𝟙_ (Over (Spec (.of K))) :=
  rfl

/-- `A^(h+1) = A ⊗ A^h`. -/
theorem powObj_succ (h : ℕ) : powObj K A (h + 1) = A ⊗ powObj K A h :=
  rfl

variable [GrpObj A]

/-- The group object structure on `A^h`: Mathlib's group structures on `𝟙_` and on products. -/
noncomputable instance instGrpObjPowObj : ∀ h : ℕ, GrpObj (powObj K A h)
  | 0 => inferInstanceAs (GrpObj (𝟙_ (Over (Spec (.of K)))))
  | h + 1 =>
    letI := instGrpObjPowObj h
    inferInstanceAs (GrpObj (A ⊗ powObj K A h))

variable [IsCommMonObj A]

/-- `A^h` is commutative when `A` is. -/
theorem isCommMonObj_powObj : ∀ h : ℕ, IsCommMonObj (powObj K A h)
  | 0 => inferInstanceAs (IsCommMonObj (𝟙_ (Over (Spec (.of K)))))
  | h + 1 =>
    haveI := isCommMonObj_powObj h
    inferInstanceAs (IsCommMonObj (A ⊗ powObj K A h))

instance instIsCommMonObjPowObj (h : ℕ) : IsCommMonObj (powObj K A h) :=
  isCommMonObj_powObj K A h

namespace GeomPoints

/-- `A^0(L)` is the trivial group. -/
@[expose]
noncomputable def powZeroEquiv : GeomPoints K L (powObj K A 0) ≃+ (Fin 0 → GeomPoints K L A) where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := (toHom K L (powObj K A 0)).injective
    (SemiCartesianMonoidalCategory.toUnit_unique _ _)
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- **Points of a power.** `A^h(L) ≃+ (Fin h → A(L))`, built from `prodEquiv` (the `0`-th
coordinate of `P : A^(h+1)(L) = (A ⊗ A^h)(L)` is `P ≫ fst`, the others those of `P ≫ snd`). -/
@[expose]
noncomputable def powEquiv : ∀ h : ℕ, GeomPoints K L (powObj K A h) ≃+ (Fin h → GeomPoints K L A)
  | 0 => powZeroEquiv K L A
  | h + 1 => consEquiv K L A (powObj K A h) (powEquiv h)

variable {K L A}

/-- **Galois equivariance.** `A^h(L) ≃+ (Fin h → A(L))` commutes with the Galois action (acting
diagonally on `Fin h → A(L)`). -/
theorem powEquiv_smul : ∀ (h : ℕ) (σ : L ≃ₐ[K] L) (P : GeomPoints K L (powObj K A h)),
    powEquiv K L A h (σ • P) = σ • powEquiv K L A h P
  | 0, _, _ => Subsingleton.elim _ _
  | h + 1, σ, P => consEquiv_smul (powEquiv K L A h) (powEquiv_smul h) σ P

end GeomPoints

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Tate module of a power.** `T_ℓ(A^h(L)) ≃ (Fin h → T_ℓ(A(L)))`. -/
@[expose]
noncomputable def tatePowEquiv (h : ℕ) :
    tateModule (GeomPoints K L (powObj K A h)) ℓ ≃ₗ[ℤ_[ℓ]]
      (Fin h → tateModule (GeomPoints K L A) ℓ) :=
  (tateModule.mapEquiv ℓ (GeomPoints.powEquiv K L A h)).trans
    (tateModule.piEquiv ℓ fun _ : Fin h => GeomPoints K L A)

/-- **Galois equivariance.** Each coordinate of `T_ℓ(A^h(L)) ≃ (Fin h → T_ℓ(A(L)))` intertwines the
Galois representations. -/
theorem tatePowEquiv_galoisRepresentation (h : ℕ) (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L (powObj K A h)) ℓ) (i : Fin h) :
    tatePowEquiv K L A ℓ h (galoisRepresentation ℓ K L (powObj K A h) σ x) i =
      galoisRepresentation ℓ K L A σ (tatePowEquiv K L A ℓ h x i) :=
  (congrArg (fun y => tateModule.piEquiv ℓ (fun _ : Fin h => GeomPoints K L A) y i)
    (tateModule.mapEquiv_representation (L ≃ₐ[K] L) (GeomPoints.powEquiv K L A h)
      (GeomPoints.powEquiv_smul h) σ x)).trans
    (tateModule.piEquiv_representation (M := fun _ : Fin h => GeomPoints K L A) (L ≃ₐ[K] L) σ _ i)

/-- **Rational Tate module of a power, as a direct sum.**
`V_ℓ(A^h(L)) ≃ V_ℓ(Fin h → A(L)) ≃ ⨁_{i < h} V_ℓ(A(L))`. -/
@[expose]
noncomputable def rationalTatePowEquiv (h : ℕ) :
    rationalTate ℓ (GeomPoints K L (powObj K A h)) ≃ₗ[ℚ_[ℓ]]
      DirectSum (Fin h) fun _ => rationalTate ℓ (GeomPoints K L A) :=
  (rationalTate.mapEquiv ℓ (GeomPoints.powEquiv K L A h)).trans
    (rationalTate.powEquivDirectSum ℓ (Fin h) (GeomPoints K L A))

/-- **For powers, the Galois group acts diagonally on the direct sum.** Under
`V_ℓ(A^h(L)) ≃ ⨁_{i < h} V_ℓ(A(L))`, the Galois representation on `V_ℓ(A^h(L))` is the diagonal
representation `Representation.directSum fun _ => ρ`, `ρ` the Galois representation on
`V_ℓ(A(L))`. -/
theorem rationalTatePowEquiv_representation (h : ℕ) (σ : L ≃ₐ[K] L)
    (v : rationalTate ℓ (GeomPoints K L (powObj K A h))) :
    rationalTatePowEquiv K L A ℓ h
        (rationalTate.representation ℓ (GeomPoints K L (powObj K A h)) (L ≃ₐ[K] L) σ v) =
      Representation.directSum
        (fun _ : Fin h => rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)) σ
        (rationalTatePowEquiv K L A ℓ h v) :=
  (congrArg (rationalTate.powEquivDirectSum ℓ (Fin h) (GeomPoints K L A))
    (rationalTate.mapEquiv_representation (L ≃ₐ[K] L) (GeomPoints.powEquiv K L A h)
      (GeomPoints.powEquiv_smul h) σ v)).trans
    (rationalTate.powEquivDirectSum_representation (L ≃ₐ[K] L) σ _)

/-- **Kernel of the Galois action on a power.** For `h ≥ 1`, the kernel of the Galois
representation on `V_ℓ(A^h(L))` equals the kernel of the Galois representation on `V_ℓ(A(L))`. -/
theorem ker_rationalTate_representation_powObj {h : ℕ} (hh : 0 < h) :
    (rationalTate.representation ℓ (GeomPoints K L (powObj K A h)) (L ≃ₐ[K] L)).ker =
      (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)).ker :=
  (rationalTate.ker_representation_eq_of_addEquiv (L ≃ₐ[K] L) (GeomPoints.powEquiv K L A h)
    (GeomPoints.powEquiv_smul h)).trans (rationalTate.ker_representation_fin_pow _ hh)

/-- **Images of the Galois action on a power.** For `h ≥ 1`, the images of the Galois group in
`GL(V_ℓ(A^h(L)))` and in `GL(V_ℓ(A(L)))` are isomorphic. -/
theorem nonempty_range_rationalTate_representation_powObj_mulEquiv {h : ℕ} (hh : 0 < h) :
    Nonempty ((rationalTate.representation ℓ (GeomPoints K L (powObj K A h))
        (L ≃ₐ[K] L)).asGroupHom.range ≃*
      (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)).asGroupHom.range) :=
  nonempty_range_asGroupHom_mulEquiv_of_ker_eq (ker_rationalTate_representation_powObj K L A ℓ hh)

end Pow

section Morphisms

variable {K}

/-- The product of two proper `K`-schemes is proper over `K`. -/
theorem isProper_tensorObj_hom (A B : Over (Spec (.of K))) [IsProper A.hom] [IsProper B.hom] :
    IsProper (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

/-- The product of two smooth `K`-schemes is smooth over `K`. -/
theorem smooth_tensorObj_hom (A B : Over (Spec (.of K))) [Smooth A.hom] [Smooth B.hom] :
    Smooth (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end Morphisms

end GroupScheme

end ArithmeticOfJacobiPolynomials
