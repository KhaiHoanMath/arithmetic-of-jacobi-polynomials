/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.AbelianWeilPairing
public import ArithmeticOfJacobiPolynomials.Algebra.EllAdicLie
public import ArithmeticOfJacobiPolynomials.Algebra.EllAdicLieSymplectic
public import ArithmeticOfJacobiPolynomials.Algebra.FiniteIndexLie
public import ArithmeticOfJacobiPolynomials.Algebra.JacobianTate
public import ArithmeticOfJacobiPolynomials.Algebra.NumberFieldGaloisAction
public import ArithmeticOfJacobiPolynomials.Algebra.TatePairing
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeProduct
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The `ℓ`-adic Lie representation of an abelian variety, and its restriction to number fields

This file builds, on the rational Tate module
`V_ℓ(A(L)) = rationalTate ℓ (GeomPoints K L A)` of an abelian variety `A/K` (with `L/K`
algebraically closed), the representation that the `ℓ`-adic Lie algebra
`ArithmeticOfJacobiPolynomials.ellAdicLie`
is applied to in the proof of Corollary 6.6: "Passing to a number field
preserves the Lie algebra because the Galois subgroup has finite index. For powers, the groups act
diagonally on direct sums."

The representation is the transport, through a finite basis
`b : Basis (Fin m) ℚ_ℓ V_ℓ(A(L))`, of the Galois action
`rationalTate.autRepresentation ℓ (GeomPoints K L A) (L ≃ₐ[K] L)`.

## Generic part (`AbelianTateLie.unitsOfEquiv`, any finite-dimensional normed `W`)

* `unitsOfEquiv e : (V ≃ₗ V) →* (W →L W)ˣ`, conjugation by a linear equivalence `e : V ≃ₗ W`;
* `continuous_unitsOfEquiv_comp`: a jointly continuous action `G × V → V` (module topology on `V`)
  gives a continuous homomorphism `G →* (W →L W)ˣ` (`G` a topological group);
* `mem_range_unitsOfEquiv_comp_iff`: description of the range;
* `diagUnits r`, `ellAdicLie_map_diagUnits`: for the diagonal embedding `(W →L W)ˣ → ((Fin r → W) →L
  (Fin r → W))ˣ`, `Lie(diag G) = diag(Lie G)`.

## The Tate module of an abelian variety (`GroupScheme` namespace below)

* `rationalTateUnits`: `G →* (Fin m → ℚ_ℓ →L Fin m → ℚ_ℓ)ˣ`, the matrix representation of `G` on
  `V_ℓ M` through the basis `b`;
* `GroupScheme.tateGaloisUnits`: the case `M = A(L)`, `G = Aut(L/K)`;
  `continuous_tateGaloisUnits` (Krull topology; uses
  `continuous_rationalTate_representation_geomPoints`), `tateGaloisUnits_apply_single` (matrix
  entries are `b.repr (σ (b j)) i`);
* `ellAdicLie_fixingSubgroup_map_tateGaloisUnits`: `Lie(ρ_b(Gal(L/E))) = Lie(ρ_b(Gal(L/K)))` for
  every finite extension `E/K` inside `L` (`IsGalois K L`);
* `ellAdicLie_fixingSubgroup_eq_of_range_eq`: **transfer** — if `Lie(ρ_b(Gal(L/K)))` equals a given
  set `S` (the conclusion of a cited Lie-algebra theorem), then so does `Lie(ρ_b(Gal(L/E)))`;
* `tateGaloisUnits_range_le_similitudeUnits`: `ρ_b` lands in `GSp(V_b, ψ_b)` when the Galois action
  lies in `GSp(V_ℓ, ψ)`; `ellAdicLie_eq_similitude_iff`.

## Powers (`powTateUnits`)

`powTateUnits` is the transport of the Galois action on `V_ℓ(A^h(L))` through the product
basis; `powTateUnits_eq_diagUnits_comp` shows it is the diagonal embedding of `tateGaloisUnits`
(the *same* `σ` acts on each factor), and the Lie algebra of its image, and of the image of
`Gal(L/E)`, is the diagonal copy of the Lie algebra on a single factor.
-/

@[expose] public section

open NormedSpace Filter Topology

namespace ArithmeticOfJacobiPolynomials

namespace AbelianTateLie

section Transport

variable {ℓ : ℕ} [Fact ℓ.Prime] {V W : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V]
  [NormedAddCommGroup W] [NormedSpace ℚ_[ℓ] W] [hfd : FiniteDimensional ℚ_[ℓ] W]

/-- Conjugation by a linear equivalence as a continuous linear automorphism. -/
noncomputable def conjEquiv (e : V ≃ₗ[ℚ_[ℓ]] W) (φ : V ≃ₗ[ℚ_[ℓ]] V) : W ≃L[ℚ_[ℓ]] W :=
  (e.symm.trans (φ.trans e)).toContinuousLinearEquiv

theorem conjEquiv_apply (e : V ≃ₗ[ℚ_[ℓ]] W) (φ : V ≃ₗ[ℚ_[ℓ]] V) (w : W) :
    conjEquiv e φ w = e (φ (e.symm w)) :=
  rfl

/-- Conjugation by a linear equivalence `e : V ≃ₗ W` to a finite-dimensional normed space:
`φ ↦ e ∘ φ ∘ e⁻¹`, viewed as a unit of the Banach algebra `W →L W` (all linear maps of a
finite-dimensional space are continuous). -/
noncomputable def unitsOfEquiv (e : V ≃ₗ[ℚ_[ℓ]] W) :
    (V ≃ₗ[ℚ_[ℓ]] V) →* (W →L[ℚ_[ℓ]] W)ˣ where
  toFun φ := (conjEquiv e φ).toUnit
  map_one' := Units.ext (ContinuousLinearMap.ext fun w => by
    change conjEquiv e 1 w = w
    simp [conjEquiv_apply])
  map_mul' φ ψ := Units.ext (ContinuousLinearMap.ext fun w => by
    change conjEquiv e (φ * ψ) w = conjEquiv e φ (conjEquiv e ψ w)
    simp [conjEquiv_apply])

theorem unitsOfEquiv_apply (e : V ≃ₗ[ℚ_[ℓ]] W) (φ : V ≃ₗ[ℚ_[ℓ]] V) (w : W) :
    ((unitsOfEquiv e φ : (W →L[ℚ_[ℓ]] W)ˣ) : W →L[ℚ_[ℓ]] W) w = e (φ (e.symm w)) :=
  rfl

theorem unitsOfEquiv_injective (e : V ≃ₗ[ℚ_[ℓ]] W) : Function.Injective (unitsOfEquiv e) := by
  intro φ ψ h
  ext v
  have := congrArg (fun u : (W →L[ℚ_[ℓ]] W)ˣ => (u : W →L[ℚ_[ℓ]] W) (e v)) h
  simpa [unitsOfEquiv_apply] using this

variable {G : Type*} [Group G]

/-- The range of the transported representation: `u` lies in it iff some `g` acts as `u` in the
coordinates `e`. -/
theorem mem_range_unitsOfEquiv_comp_iff (e : V ≃ₗ[ℚ_[ℓ]] W) (ρ : G →* (V ≃ₗ[ℚ_[ℓ]] V))
    (u : (W →L[ℚ_[ℓ]] W)ˣ) :
    u ∈ ((unitsOfEquiv e).comp ρ).range ↔
      ∃ g : G, ∀ w : W, (u : W →L[ℚ_[ℓ]] W) w = e (ρ g (e.symm w)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun w => rfl⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, Units.ext (ContinuousLinearMap.ext fun w => ?_)⟩
    exact (hg w).symm

/-- The range of the transported representation is the image of the range of `ρ` under the
conjugation isomorphism onto its image. -/
theorem range_unitsOfEquiv_comp (e : V ≃ₗ[ℚ_[ℓ]] W) (ρ : G →* (V ≃ₗ[ℚ_[ℓ]] V)) :
    ((unitsOfEquiv e).comp ρ).range = ρ.range.map (unitsOfEquiv e) :=
  (MonoidHom.map_range (unitsOfEquiv e) ρ).symm

/-- The image of a subgroup `H ≤ G` under the transported representation. -/
theorem map_unitsOfEquiv_comp (e : V ≃ₗ[ℚ_[ℓ]] W) (ρ : G →* (V ≃ₗ[ℚ_[ℓ]] V)) (H : Subgroup G) :
    H.map ((unitsOfEquiv e).comp ρ) = (H.map ρ).map (unitsOfEquiv e) :=
  (Subgroup.map_map _ _ _).symm

section Continuity

variable [TopologicalSpace V] [IsModuleTopology ℚ_[ℓ] V] [TopologicalSpace G] [ContinuousInv G]

/-- **Continuity of the transported representation.** If the action map `G × V → V` is jointly
continuous for the module topology of `V`, the transported representation
`G →* (W →L W)ˣ` is continuous (for the topology of the units of the Banach algebra `W →L W`). -/
theorem continuous_unitsOfEquiv_comp (e : V ≃ₗ[ℚ_[ℓ]] W) (ρ : G →* (V ≃ₗ[ℚ_[ℓ]] V))
    (hcont : Continuous fun q : G × V => ρ q.1 q.2) :
    Continuous ((unitsOfEquiv e).comp ρ) := by
  have hmain : Continuous fun g : G => (((unitsOfEquiv e).comp ρ) g : W →L[ℚ_[ℓ]] W) := by
    rw [continuous_clm_apply]
    intro w
    have h1 : Continuous fun g : G => ρ g (e.symm w) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    exact (IsModuleTopology.continuous_of_linearMap (e : V →ₗ[ℚ_[ℓ]] W)).comp h1
  rw [Units.continuous_iff]
  refine ⟨hmain, ?_⟩
  have := hmain.comp (continuous_inv : Continuous fun g : G => g⁻¹)
  refine this.congr fun g => ?_
  simp [map_inv]

end Continuity

end Transport

section Diagonal

variable {ℓ : ℕ} [Fact ℓ.Prime] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℚ_[ℓ] W]
  [hfd : FiniteDimensional ℚ_[ℓ] W] (r : ℕ)

omit hfd in
/-- The diagonal algebra homomorphism `(W →L W) → ((Fin r → W) →L (Fin r → W))`, `T ↦ (T, …, T)`. -/
noncomputable def diagHom : (W →L[ℚ_[ℓ]] W) →ₐ[ℚ_[ℓ]] ((Fin r → W) →L[ℚ_[ℓ]] (Fin r → W)) where
  toFun T := ContinuousLinearMap.pi fun i => T.comp (ContinuousLinearMap.proj i)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit hfd in
theorem diagHom_apply (T : W →L[ℚ_[ℓ]] W) (x : Fin r → W) (i : Fin r) :
    diagHom (ℓ := ℓ) (W := W) r T x i = T (x i) :=
  rfl

omit hfd in
theorem diagHom_injective [NeZero r] : Function.Injective (diagHom (ℓ := ℓ) (W := W) r) := by
  intro S T h
  ext w
  exact congrArg (fun U : (Fin r → W) →L[ℚ_[ℓ]] (Fin r → W) => U (fun _ => w) 0) h

theorem continuous_diagHom : Continuous (diagHom (ℓ := ℓ) (W := W) r) :=
  LinearMap.continuous_of_finiteDimensional (diagHom (ℓ := ℓ) (W := W) r).toLinearMap

omit hfd in
/-- The diagonal embedding on units. -/
noncomputable def diagUnits : (W →L[ℚ_[ℓ]] W)ˣ →* ((Fin r → W) →L[ℚ_[ℓ]] (Fin r → W))ˣ :=
  Units.map (diagHom (ℓ := ℓ) (W := W) r).toMonoidHom

omit hfd in
theorem coe_diagUnits (u : (W →L[ℚ_[ℓ]] W)ˣ) :
    (diagUnits r u : (Fin r → W) →L[ℚ_[ℓ]] (Fin r → W)) =
      diagHom (ℓ := ℓ) (W := W) r (u : W →L[ℚ_[ℓ]] W) :=
  rfl

end Diagonal

section DiagonalLie

variable {ℓ : ℕ} [Fact ℓ.Prime] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℚ_[ℓ] W]
  [FiniteDimensional ℚ_[ℓ] W] (r : ℕ) [NeZero r]

/-- **Lie algebra of a diagonal image.** For the diagonal embedding `u ↦ (u, …, u)` of units,
`Lie(diag G) = diag(Lie G)`: the exponential commutes with the continuous ring homomorphism
`diagHom`, `diagHom` is injective, and its range is closed (finite dimension), which forces a
Lie algebra element of the image to be diagonal (it is the derivative at `0` of
`t ↦ exp (t X)`). -/
theorem ellAdicLie_map_diagUnits (G : Subgroup (W →L[ℚ_[ℓ]] W)ˣ) :
    ellAdicLie ℓ (G.map (diagUnits r)) = diagHom (ℓ := ℓ) (W := W) r '' ellAdicLie ℓ G := by
  have hcomplete := FiniteDimensional.complete ℚ_[ℓ] W
  ext X
  constructor
  · intro hX
    -- `X` is diagonal: it is the derivative of `t ↦ exp (t • X)` at `0`, which lies in the
    -- closed subspace of diagonal operators.
    have hR := Submodule.closed_of_finiteDimensional
      (LinearMap.range (diagHom (ℓ := ℓ) (W := W) r).toLinearMap)
    have hmem : ∀ᶠ t in 𝓝 (0 : ℚ_[ℓ]),
        exp (t • X) ∈ LinearMap.range (diagHom (ℓ := ℓ) (W := W) r).toLinearMap := by
      filter_upwards [mem_ellAdicLie_iff.1 hX] with t ht
      obtain ⟨v, ⟨u, -, rfl⟩, he⟩ := ht
      exact ⟨(u : W →L[ℚ_[ℓ]] W), by rw [← he]; rfl⟩
    have h0 : (0 : ℚ_[ℓ]) • X ∈
        Metric.eball (0 : (Fin r → W) →L[ℚ_[ℓ]] (Fin r → W))
          (expSeries ℚ_[ℓ] ((Fin r → W) →L[ℚ_[ℓ]] (Fin r → W))).radius := by
      rw [zero_smul]
      exact Metric.mem_eball_self (padic_expSeries_radius_pos ℓ _)
    have hE : HasDerivAt (fun t : ℚ_[ℓ] => exp (t • X)) X 0 := by
      have := hasDerivAt_exp_smul_const_of_mem_ball (𝕂 := ℚ_[ℓ]) X 0 h0
      rwa [zero_smul, exp_zero, one_mul] at this
    have hslope := hasDerivAt_iff_tendsto_slope.mp hE
    have hXR : X ∈ LinearMap.range (diagHom (ℓ := ℓ) (W := W) r).toLinearMap := by
      refine hR.mem_of_tendsto hslope ?_
      filter_upwards [nhdsWithin_le_nhds hmem] with t ht
      rw [slope_def_module, zero_smul, exp_zero, sub_zero]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ht ?_)
      exact ⟨1, rfl⟩
    obtain ⟨Y, hY⟩ := hXR
    have hXY : X = diagHom (ℓ := ℓ) (W := W) r Y := hY.symm
    subst hXY
    refine ⟨Y, ?_, rfl⟩
    rw [mem_ellAdicLie_iff]
    filter_upwards [mem_ellAdicLie_iff.1 hX, padic_eventually_smul_mem_eball (p := ℓ) Y]
      with t ht hball
    obtain ⟨v, ⟨u, hu, rfl⟩, he⟩ := ht
    refine ⟨u, hu, diagHom_injective r ?_⟩
    have hmap := map_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (diagHom (ℓ := ℓ) (W := W) r)
      (continuous_diagHom r) (t • Y) hball
    rw [map_smul] at hmap
    rw [← hmap] at he
    exact he
  · rintro ⟨Y, hY, rfl⟩
    rw [mem_ellAdicLie_iff]
    filter_upwards [mem_ellAdicLie_iff.1 hY, padic_eventually_smul_mem_eball (p := ℓ) Y]
      with t ht hball
    obtain ⟨u, hu, he⟩ := ht
    refine ⟨diagUnits r u, ⟨u, hu, rfl⟩, ?_⟩
    have hmap := map_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (diagHom (ℓ := ℓ) (W := W) r)
      (continuous_diagHom r) (t • Y) hball
    rw [map_smul] at hmap
    rw [coe_diagUnits, he, hmap]

end DiagonalLie

section Forms

variable {ℓ : ℕ} [Fact ℓ.Prime] {V W P : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V]
  [NormedAddCommGroup W] [NormedSpace ℚ_[ℓ] W] [FiniteDimensional ℚ_[ℓ] W]
  [AddCommGroup P] [Module ℚ_[ℓ] P]

/-- Transport of a bilinear form `ψ` on `V` to `W` along `e : V ≃ₗ W`: `ψ_e(x, y) =
ψ(e⁻¹ x, e⁻¹ y)`. -/
noncomputable def transportForm (e : V ≃ₗ[ℚ_[ℓ]] W) (ψ : V →ₗ[ℚ_[ℓ]] V →ₗ[ℚ_[ℓ]] P) :
    W →ₗ[ℚ_[ℓ]] W →ₗ[ℚ_[ℓ]] P :=
  ψ.compl₁₂ (e.symm : W →ₗ[ℚ_[ℓ]] V) (e.symm : W →ₗ[ℚ_[ℓ]] V)

omit [FiniteDimensional ℚ_[ℓ] W] in
@[simp]
theorem transportForm_apply (e : V ≃ₗ[ℚ_[ℓ]] W) (ψ : V →ₗ[ℚ_[ℓ]] V →ₗ[ℚ_[ℓ]] P) (x y : W) :
    transportForm e ψ x y = ψ (e.symm x) (e.symm y) :=
  rfl

variable (ℓ) in
/-- **`ℚ_ℓ · Id ⊕ 𝔰𝔭(W, ψ)`**, the Lie algebra of the Mumford–Tate-type group `GSp(W, ψ)`, as a
set of continuous endomorphisms of the normed space `W`. -/
def scalarPlusSymplectic (ψ : W →ₗ[ℚ_[ℓ]] W →ₗ[ℚ_[ℓ]] P) : Set (W →L[ℚ_[ℓ]] W) :=
  {X | (X : Module.End ℚ_[ℓ] W) ∈ (ℚ_[ℓ] ∙ (LinearMap.id : Module.End ℚ_[ℓ] W)) ⊔ symplecticLie ψ}

/-- `Lie(GSp(W, ψ)) = ℚ_ℓ · Id ⊕ 𝔰𝔭(W, ψ)`. -/
theorem ellAdicLie_similitudeUnits_eq_scalarPlusSymplectic (ψ : W →ₗ[ℚ_[ℓ]] W →ₗ[ℚ_[ℓ]] P) :
    ellAdicLie ℓ (similitudeUnits ψ) = scalarPlusSymplectic ℓ ψ :=
  ellAdicLie_similitudeUnits_eq_span_id_sup ψ

/-- `φ` is a similitude of `ψ` iff its conjugate is a similitude of the transported form. -/
theorem unitsOfEquiv_mem_similitudeUnits_iff (e : V ≃ₗ[ℚ_[ℓ]] W)
    (ψ : V →ₗ[ℚ_[ℓ]] V →ₗ[ℚ_[ℓ]] P) (φ : V ≃ₗ[ℚ_[ℓ]] V) :
    unitsOfEquiv e φ ∈ similitudeUnits (transportForm e ψ) ↔ φ ∈ similitudeGroup ψ := by
  rw [mem_similitudeUnits, mem_similitudeGroup]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x y => ?_⟩
    have := hc (e x) (e y)
    simpa [transportForm_apply, unitsOfEquiv_apply] using this
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x y => ?_⟩
    simpa [transportForm_apply, unitsOfEquiv_apply] using hc (e.symm x) (e.symm y)

/-- The same for symplectic elements. -/
theorem unitsOfEquiv_mem_symplecticUnits_iff (e : V ≃ₗ[ℚ_[ℓ]] W)
    (ψ : V →ₗ[ℚ_[ℓ]] V →ₗ[ℚ_[ℓ]] P) (φ : V ≃ₗ[ℚ_[ℓ]] V) :
    unitsOfEquiv e φ ∈ symplecticUnits (transportForm e ψ) ↔ φ ∈ symplecticGroup ψ := by
  rw [mem_symplecticUnits, mem_symplecticGroup]
  constructor
  · intro hc x y
    simpa [transportForm_apply, unitsOfEquiv_apply] using hc (e x) (e y)
  · intro hc x y
    simpa [transportForm_apply, unitsOfEquiv_apply] using hc (e.symm x) (e.symm y)

variable {G : Type*} [Group G]

/-- If every element of the image of `ρ` is a similitude of `ψ`, the transported representation
lands in `GSp(W, ψ_e)`. -/
theorem range_unitsOfEquiv_comp_le_similitudeUnits (e : V ≃ₗ[ℚ_[ℓ]] W)
    (ψ : V →ₗ[ℚ_[ℓ]] V →ₗ[ℚ_[ℓ]] P) (ρ : G →* (V ≃ₗ[ℚ_[ℓ]] V))
    (h : ∀ g, ρ g ∈ similitudeGroup ψ) :
    ((unitsOfEquiv e).comp ρ).range ≤ similitudeUnits (transportForm e ψ) := by
  rintro _ ⟨g, rfl⟩
  exact (unitsOfEquiv_mem_similitudeUnits_iff e ψ (ρ g)).2 (h g)

end Forms

section RationalTate

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (G : Type*) [Group G]
  [DistribMulAction G M] {m : ℕ} (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ M))

/-- **The matrix representation on `V_ℓ M`.** The action of `G` on `V_ℓ M = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ M`
(`rationalTate.autRepresentation`, base change of the action on `T_ℓ M`) written in the basis
`b`, as units of the Banach algebra of continuous endomorphisms of `Fin m → ℚ_ℓ`. -/
noncomputable def rationalTateUnits :
    G →* ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ :=
  (unitsOfEquiv b.equivFun).comp (rationalTate.autRepresentation ℓ M G)

variable {ℓ M G b}

theorem rationalTateUnits_apply (g : G) (w : Fin m → ℚ_[ℓ]) :
    ((rationalTateUnits ℓ M G b g : ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ) :
        (Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ])) w =
      b.equivFun (rationalTate.representation ℓ M G g (b.equivFun.symm w)) := by
  rw [← rationalTate.autRepresentation_apply]
  rfl

/-- **Matrix entries.** The `(i, j)` entry of `ρ_b(g)` is the `i`-th coordinate of `g • b j`. -/
theorem rationalTateUnits_apply_single (g : G) (i j : Fin m) :
    ((rationalTateUnits ℓ M G b g : ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ) :
        (Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ])) (Pi.single j 1) i =
      b.repr (rationalTate.representation ℓ M G g (b j)) i := by
  rw [rationalTateUnits_apply]
  simp [Module.Basis.equivFun_symm_apply, Pi.single_apply, Module.Basis.equivFun_apply]

/-- **The range of the matrix representation** is the set of operators of the form
`g ↦ b ∘ ρ(g) ∘ b⁻¹`. -/
theorem mem_range_rationalTateUnits_iff (u : ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ) :
    u ∈ (rationalTateUnits ℓ M G b).range ↔
      ∃ g : G, ∀ w, (u : (Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ])) w =
        b.equivFun (rationalTate.representation ℓ M G g (b.equivFun.symm w)) := by
  rw [rationalTateUnits, mem_range_unitsOfEquiv_comp_iff]
  simp only [rationalTate.autRepresentation_apply]

variable (b) in
/-- **Continuity of the matrix representation.** If the action map of the topological group `G`
on `V_ℓ M` is jointly continuous (`rationalTate.continuous_representation`), then
`rationalTateUnits` is continuous. -/
theorem continuous_rationalTateUnits [TopologicalSpace G] [IsTopologicalGroup G]
    (hcont : Continuous fun p : G × rationalTate ℓ M =>
      rationalTate.representation ℓ M G p.1 p.2) :
    Continuous (rationalTateUnits ℓ M G b) :=
  continuous_unitsOfEquiv_comp b.equivFun _ (hcont.congr fun p =>
    (rationalTate.autRepresentation_apply p.1 p.2).symm)

end RationalTate

end AbelianTateLie

/-! ### The Galois representation on `V_ℓ(A(L))` -/

section Geometric

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry GroupScheme Stacks.AbelianGroup

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] {ℓ : ℕ} [Fact ℓ.Prime]

namespace AbelianTateLie

/-- **The `ℓ`-adic matrix representation of `Aut(L/K)` on `V_ℓ(A(L))`**, through a
finite basis `b` of `V_ℓ(A(L)) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A(L))`: the units of `End(ℚ_ℓ^m)` by which
`σ ∈ Aut(L/K)` acts in the coordinates `b` (the base change of
`GroupScheme.galoisAutRepresentation`). -/
noncomputable abbrev tateGaloisUnits {m : ℕ}
    (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A))) :
    (L ≃ₐ[K] L) →* ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ :=
  rationalTateUnits ℓ (GeomPoints K L A) (L ≃ₐ[K] L) b

/-- A finite basis of `V_ℓ(A(L))`, of size `2 * dim A_L`
(`finrank_rationalTate_geomPoints`), for an abelian variety `A` and `(ℓ : L) ≠ 0`. -/
noncomputable def tateBasis [IsAlgClosed L] [IsAbelianVariety K A] (hℓ : (ℓ : L) ≠ 0) :
    Module.Basis (Fin (2 * geomDim L A)) ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A)) :=
  haveI := module_finite_rationalTate_geomPoints L A hℓ
  Module.finBasisOfFinrankEq ℚ_[ℓ] _ (finrank_rationalTate_geomPoints L A hℓ)

variable {A} {m : ℕ} (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L A)))

/-- **Matrix entries of the Galois representation**: the `(i, j)` entry of `ρ_b(σ)` is the `i`-th
coordinate of `σ • b j` for the action of `σ ∈ Aut(L/K)` on `V_ℓ(A(L))`. -/
theorem tateGaloisUnits_apply_single (σ : L ≃ₐ[K] L) (i j : Fin m) :
    ((tateGaloisUnits A b σ : ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))ˣ) :
        (Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ])) (Pi.single j 1) i =
      b.repr (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ (b j)) i :=
  rationalTateUnits_apply_single σ i j

/-- On `1 ⊗ x` the representation is `1 ⊗ (σ x)`, where `σ` acts on `T_ℓ(A(L))` through the
Galois action (`GroupScheme.galoisRepresentation`) on geometric points. -/
theorem representation_ofTate_geomPoints (σ : L ≃ₐ[K] L)
    (x : tateModule (GeomPoints K L A) ℓ) :
    rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ (rationalTate.ofTate ℓ _ x) =
      rationalTate.ofTate ℓ _ (galoisRepresentation ℓ K L A σ x) :=
  rationalTate.representation_ofTate σ x

variable [IsAlgClosed L] [IsAbelianVariety K A]

/-- **Continuity of the Galois representation `ρ_b`.** For `L/K` algebraic (e.g. `L = K̄`) the
matrix representation `Aut(L/K) → GL_m(ℚ_ℓ)` of `V_ℓ(A(L))` is continuous for the
Krull topology and the `ℓ`-adic topology of `GL_m(ℚ_ℓ)` (units of the Banach algebra of
continuous endomorphisms). -/
theorem continuous_tateGaloisUnits [Algebra.IsAlgebraic K L] (hℓ : (ℓ : L) ≠ 0) :
    Continuous (tateGaloisUnits A b) :=
  continuous_rationalTateUnits b (continuous_rationalTate_representation_geomPoints L A hℓ)

omit [IsAlgClosed L] [IsAbelianVariety K A] in
/-- In characteristic `0`, an algebraically closed algebraic extension `L/K` is Galois, so that
`Aut(L/K)` is a compact (profinite) group. -/
theorem isGalois_of_charZero [CharZero K] [IsAlgClosed L] [Algebra.IsAlgebraic K L] :
    IsGalois K L :=
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  inferInstance

section FiniteIndex

variable [IsGalois K L]

/-- **Finite-index restriction (Corollary 6.6, "passing to a number field").** For `L/K` Galois
(e.g. `L = K̄` with `K` of characteristic `0`) and every finite subextension `E/K` of `L`, the
Galois group `Gal(L/E) = E.fixingSubgroup` is open in the compact group `Gal(L/K)`, and
`ρ_b(Gal(L/E))` has the same `ℓ`-adic Lie algebra as `ρ_b(Gal(L/K))`, for the representation
on `V_ℓ(A(L))`. -/
theorem ellAdicLie_fixingSubgroup_map_tateGaloisUnits (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits A b)) =
      ellAdicLie ℓ (tateGaloisUnits A b).range :=
  ellAdicLie_map_eq_of_isOpen (tateGaloisUnits A b) (continuous_tateGaloisUnits b hℓ)
    E.fixingSubgroup E.fixingSubgroup_isOpen

omit [IsAlgClosed L] [IsAbelianVariety K A] [IsGalois K L] in
/-- The image of `Gal(L/E) = Aut(L/E)` (acting on `A(L)` through `Aut(L/K)`) is the image of
`E.fixingSubgroup`. -/
theorem range_comp_restrictScalarsHom (E : IntermediateField K L) :
    ((tateGaloisUnits A b).comp
      (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))).range =
      E.fixingSubgroup.map (tateGaloisUnits A b) := by
  rw [← MonoidHom.map_range, NumberFieldGalois.range_restrictScalarsHom]

/-- The same restriction statement for `Aut(L/E)`, the Galois group of the base change of `A` to
`E`, acting through its inclusion in `Aut(L/K)`. -/
theorem ellAdicLie_range_comp_restrictScalarsHom (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ ((tateGaloisUnits A b).comp
      (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))).range =
      ellAdicLie ℓ (tateGaloisUnits A b).range := by
  rw [range_comp_restrictScalarsHom]
  exact ellAdicLie_fixingSubgroup_map_tateGaloisUnits b hℓ E

/-- **Transfer of a Lie-algebra computation to finite extensions.** If the Lie algebra of the
image of `Gal(L/K)` on `V_ℓ(A(L))` is a given set `S` (the conclusion of a Lie-algebra theorem
for `K`, taken as an argument), then the image of `Gal(L/E)` has the same Lie algebra `S`, for
every finite extension `E/K` inside `L`. -/
theorem ellAdicLie_fixingSubgroup_eq_of_range_eq
    {S : Set ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))}
    (hS : ellAdicLie ℓ (tateGaloisUnits A b).range = S) (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits A b)) = S :=
  (ellAdicLie_fixingSubgroup_map_tateGaloisUnits b hℓ E).trans hS

/-- **Transfer in the form of the manuscript's Lie algebra.** Let `ψ` be a bilinear form on
`V_ℓ(A(L))` (the Weil pairing) and `ψ_b` its transport to `ℚ_ℓ^m`. If `Lie(ρ_b(Gal(L/K)))`
is `ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)`, then so is `Lie(ρ_b(Gal(L/E)))` for every finite `E/K` in `L`. -/
theorem ellAdicLie_fixingSubgroup_eq_scalarPlusSymplectic {P : Type*} [AddCommGroup P]
    [Module ℚ_[ℓ] P]
    (ψ : rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]] rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]] P)
    (hZ : ellAdicLie ℓ (tateGaloisUnits A b).range =
      scalarPlusSymplectic ℓ (transportForm b.equivFun ψ))
    (hℓ : (ℓ : L) ≠ 0) (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits A b)) =
      scalarPlusSymplectic ℓ (transportForm b.equivFun ψ) :=
  ellAdicLie_fixingSubgroup_eq_of_range_eq b hZ hℓ E

/-- The two forms of the hypothesis agree: `Lie(ρ_b(Gal(L/K))) = ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)` iff it equals
the Lie algebra of the similitude group `GSp(V_b, ψ_b)`; and, for a finite `E/K`, the statement for
`Gal(L/E)` is equivalent to the one for `Gal(L/K)`. -/
theorem ellAdicLie_fixingSubgroup_eq_similitude_iff {P : Type*} [AddCommGroup P] [Module ℚ_[ℓ] P]
    (ψ : rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]] rationalTate ℓ (GeomPoints K L A) →ₗ[ℚ_[ℓ]] P)
    (hℓ : (ℓ : L) ≠ 0) (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits A b)) =
        ellAdicLie ℓ (similitudeUnits (transportForm b.equivFun ψ)) ↔
      ellAdicLie ℓ (tateGaloisUnits A b).range =
        ellAdicLie ℓ (similitudeUnits (transportForm b.equivFun ψ)) := by
  rw [ellAdicLie_fixingSubgroup_map_tateGaloisUnits b hℓ E]

end FiniteIndex

section WeilPairing

variable {Â : Over (Spec (.of K))} [GrpObj Â] [IsCommMonObj Â]
  (D : DualPairingData ℓ L A Â) (φ : A ⟶ Â) [IsMonHom φ] [IsIso φ]

omit [IsAbelianVariety K A] [IsIso φ] in
/-- Each `σ ∈ Aut(L/K)` acts on `V_ℓ(A(L))` as a similitude of the Weil pairing
(multiplier the cyclotomic character). -/
theorem autRepresentation_mem_similitudeGroup_weil (hℓ : (ℓ : L) ≠ 0) (σ : L ≃ₐ[K] L) :
    rationalTate.autRepresentation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ ∈
      similitudeGroup (abelianWeilPairing D φ) :=
  (galoisSimilitudeRepresentation (he := D.isCompatible φ) hℓ (D.isEquivariant φ) σ).2

omit [IsAbelianVariety K A] [IsIso φ] in
/-- **`ρ_b` lands in `GSp(V_b, ψ_b)`**: the image of `Aut(L/K)` in `GL_m(ℚ_ℓ)` is contained in the
similitude group of the transported Weil pairing. -/
theorem tateGaloisUnits_range_le_similitudeUnits (hℓ : (ℓ : L) ≠ 0) :
    (tateGaloisUnits A b).range ≤
      similitudeUnits (transportForm b.equivFun (abelianWeilPairing D φ)) :=
  range_unitsOfEquiv_comp_le_similitudeUnits b.equivFun (abelianWeilPairing D φ) _
    (autRepresentation_mem_similitudeGroup_weil D φ hℓ)

end WeilPairing

section Power

variable (r : ℕ)

/-- **Coordinates on `V_ℓ(A^r(L))`**: the rational Tate module of the `r`-th power of `A`
(`GroupScheme.powObj K A r`) identified with `(Fin r → Fin m → ℚ_ℓ)` through
`GroupScheme.rationalTatePowEquiv` (the direct sum decomposition of `TateProduct`) and the basis
`b` on each factor. -/
noncomputable def powEquivPi :
    rationalTate ℓ (GeomPoints K L (powObj K A r)) ≃ₗ[ℚ_[ℓ]] (Fin r → Fin m → ℚ_[ℓ]) :=
  ((rationalTatePowEquiv K L A ℓ r).trans
    (DirectSum.linearEquivFunOnFintype ℚ_[ℓ] (Fin r)
      fun _ => rationalTate ℓ (GeomPoints K L A))).trans
    (LinearEquiv.piCongrRight fun _ => b.equivFun)

/-- **The `ℓ`-adic matrix representation of `Aut(L/K)` on `V_ℓ(A^r(L))`**, through the
product basis: the action of `σ` on `V_ℓ(A^r(L))` (base change of the action on
`T_ℓ((A^r)(L))`) transported along `powEquivPi`. -/
noncomputable def powTateUnits :
    (L ≃ₐ[K] L) →* ((Fin r → Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin r → Fin m → ℚ_[ℓ]))ˣ :=
  (unitsOfEquiv (powEquivPi (A := A) b r)).comp
    (rationalTate.autRepresentation ℓ (GeomPoints K L (powObj K A r)) (L ≃ₐ[K] L))

variable {r}

omit [IsAlgClosed L] [IsAbelianVariety K A] in
/-- Coordinates of the transported power representation: the *same* `σ` acts on every factor. -/
theorem powEquivPi_representation (σ : L ≃ₐ[K] L)
    (v : rationalTate ℓ (GeomPoints K L (powObj K A r))) (i : Fin r) :
    powEquivPi b r (rationalTate.representation ℓ (GeomPoints K L (powObj K A r)) (L ≃ₐ[K] L) σ v)
        i =
      b.equivFun (rationalTate.representation ℓ (GeomPoints K L A) (L ≃ₐ[K] L) σ
        ((rationalTatePowEquiv K L A ℓ r v) i)) := by
  have h := rationalTatePowEquiv_representation K L A ℓ r σ v
  change b.equivFun
      (DirectSum.linearEquivFunOnFintype ℚ_[ℓ] (Fin r) (fun _ => rationalTate ℓ (GeomPoints K L A))
        (rationalTatePowEquiv K L A ℓ r _) i) = _
  rw [h]
  simp [Representation.directSum_apply, DirectSum.lmap_apply]

omit [IsAlgClosed L] [IsAbelianVariety K A] in
/-- **Diagonal power transport.** The matrix representation on `V_ℓ(A^r(L))` is the diagonal
embedding `u ↦ (u, …, u)` of the matrix representation on `V_ℓ(A(L))`: `σ` acts on each factor by
`ρ_b(σ)`. -/
theorem powTateUnits_eq_diagUnits_comp :
    powTateUnits b r = (diagUnits r).comp (tateGaloisUnits A b) := by
  refine MonoidHom.ext fun σ => Units.ext (ContinuousLinearMap.ext fun w => ?_)
  funext i
  set v := (powEquivPi (A := A) b r).symm w with hv
  have hw : powEquivPi b r v = w := (powEquivPi (A := A) b r).apply_symm_apply w
  have hcoord : ∀ j, rationalTatePowEquiv K L A ℓ r v j = b.equivFun.symm (w j) := fun j => by
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, ← hw]
    rfl
  change powEquivPi b r (rationalTate.autRepresentation ℓ (GeomPoints K L (powObj K A r))
    (L ≃ₐ[K] L) σ v) i =
    diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r
      (tateGaloisUnits A b σ : (Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ])) w i
  rw [rationalTate.autRepresentation_apply, powEquivPi_representation, hcoord]
  rw [diagHom_apply]
  exact (rationalTateUnits_apply σ (w i)).symm

end Power

section PowerLie

variable {r : ℕ} [IsGalois K L] [NeZero r]

omit [IsAlgClosed L] [IsAbelianVariety K A] [IsGalois K L] in
/-- **Lie algebra of the image on a power.** For `V_ℓ(A^r(L))`, `r ≥ 1`,
`Lie(ρ(Gal(L/K)))` is the diagonal copy of the Lie algebra on a single factor. -/
theorem ellAdicLie_range_powTateUnits :
    ellAdicLie ℓ (powTateUnits b r).range =
      diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r '' ellAdicLie ℓ (tateGaloisUnits A b).range := by
  rw [powTateUnits_eq_diagUnits_comp, ← MonoidHom.map_range]
  exact ellAdicLie_map_diagUnits r _

/-- **Finite extensions and powers together.** For `E/K` finite inside `L`, the Lie algebra of the
image of `Gal(L/E)` on `V_ℓ(A^r(L))` is the diagonal copy of the Lie algebra on
`V_ℓ(A(L))` of the image of `Gal(L/K)`. -/
theorem ellAdicLie_fixingSubgroup_map_powTateUnits (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
      diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r '' ellAdicLie ℓ (tateGaloisUnits A b).range := by
  rw [powTateUnits_eq_diagUnits_comp, ← Subgroup.map_map, ellAdicLie_map_diagUnits,
    ellAdicLie_fixingSubgroup_map_tateGaloisUnits b hℓ E]

/-- **Transfer to powers over finite extensions.** If `Lie(ρ_b(Gal(L/K))) = S` on `V_ℓ(A(L))`,
then on `V_ℓ(A^r(L))` the image of `Gal(L/E)` has Lie algebra the diagonal image of `S`. -/
theorem ellAdicLie_fixingSubgroup_map_powTateUnits_eq
    {S : Set ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))}
    (hS : ellAdicLie ℓ (tateGaloisUnits A b).range = S) (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
      diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r '' S := by
  rw [ellAdicLie_fixingSubgroup_map_powTateUnits b hℓ E, hS]

end PowerLie

end AbelianTateLie

end Geometric

end ArithmeticOfJacobiPolynomials
