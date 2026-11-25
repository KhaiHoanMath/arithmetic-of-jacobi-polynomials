/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.PadicExpRadius
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.KrullTopology

/-!
# The `ℓ`-adic Lie algebra of a subgroup of `GL`, and its invariance under open subgroups

Let `p` be a prime and `A` a complete normed `ℚ_[p]`-algebra (e.g. `Matrix (Fin n) (Fin n) ℚ_[p]`
with an operator norm, or `V →L[ℚ_[p]] V` for a finite-dimensional normed space `V`).
For a subgroup `G ≤ Aˣ` we use the standard definition of its Lie algebra
(Serre, *Lie algebras and Lie groups*, Part II, LG 5; Bourbaki, *Lie*, Ch. III):
`Lie(G) = {X ∈ A | exp(t X) ∈ G for all t ∈ ℚ_[p] sufficiently close to 0}`,
formalized as `ArithmeticOfJacobiPolynomials.ellAdicLie p G`. (For a closed subgroup of `GL_n(ℚ_ℓ)`
this is the
Lie algebra of the `ℓ`-adic Lie group `G` by Cartan's theorem; we only use the definition.)

This is the step "passing to a number field preserves the Lie algebra because the Galois
subgroup has finite index" in the proof of Corollary 6.6 of the manuscript.

Main results:
* `ArithmeticOfJacobiPolynomials.ellAdicLie_mono`,
`ArithmeticOfJacobiPolynomials.zero_mem_ellAdicLie`,
  `ArithmeticOfJacobiPolynomials.smul_mem_ellAdicLie`,
  `ArithmeticOfJacobiPolynomials.ellAdicLie_top`;
* `ArithmeticOfJacobiPolynomials.ellAdicLie_eq_of_nhds`: if `H ≤ G` and `G ∩ W ⊆ H` for an open `W
∋ 1`, then
  `Lie(H) = Lie(G)`; variants `ArithmeticOfJacobiPolynomials.ellAdicLie_eq_of_isOpen_subgroupOf`
  (`H` open in
  `G`) and `ArithmeticOfJacobiPolynomials.ellAdicLie_eq_of_isClosed_of_finiteIndex` (`H` closed of
  finite index
  in `G`), `ArithmeticOfJacobiPolynomials.ellAdicLie_eq_of_isCompact_of_finiteIndex`;
* `ArithmeticOfJacobiPolynomials.ellAdicLie_map_eq_of_isOpen`: for a continuous `ρ : Γ →* Aˣ` from
a compact
  group and an open subgroup `Δ ≤ Γ`, `Lie(ρ Δ) = Lie(ρ Γ)`;
* `ArithmeticOfJacobiPolynomials.ellAdicLie_galois_fixingSubgroup`: the instance
  `Γ = Gal(ℚ̄/ℚ)`, `Δ = Gal(ℚ̄/K)` for a number field `K ⊆ ℚ̄`.
-/

public section

open NormedSpace Filter Topology

namespace ArithmeticOfJacobiPolynomials

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]

variable (p) in
/-- The `p`-adic Lie algebra of a subgroup `G` of the units of a normed `ℚ_[p]`-algebra `A`:
the `X ∈ A` such that `exp (t • X) ∈ G` for all `t ∈ ℚ_[p]` sufficiently close to `0`
(Serre, LG 5). -/
def ellAdicLie (G : Subgroup Aˣ) : Set A :=
  {X | ∀ᶠ t in 𝓝 (0 : ℚ_[p]), ∃ u ∈ G, (u : A) = exp (t • X)}

theorem mem_ellAdicLie_iff {G : Subgroup Aˣ} {X : A} :
    X ∈ ellAdicLie p G ↔ ∀ᶠ t in 𝓝 (0 : ℚ_[p]), ∃ u ∈ G, (u : A) = exp (t • X) :=
  Iff.rfl

/-- The Lie algebra is monotone in the group. -/
theorem ellAdicLie_mono {H G : Subgroup Aˣ} (h : H ≤ G) : ellAdicLie p H ⊆ ellAdicLie p G :=
  fun _ hX => hX.mono fun _ ⟨u, hu, he⟩ => ⟨u, h hu, he⟩

theorem zero_mem_ellAdicLie (G : Subgroup Aˣ) : (0 : A) ∈ ellAdicLie p G :=
  Eventually.of_forall fun t => ⟨1, G.one_mem, by rw [smul_zero, exp_zero, Units.val_one]⟩

/-- The Lie algebra is closed under `ℚ_[p]`-scalars. -/
theorem smul_mem_ellAdicLie {G : Subgroup Aˣ} {X : A} (c : ℚ_[p]) (hX : X ∈ ellAdicLie p G) :
    c • X ∈ ellAdicLie p G := by
  have hc : Tendsto (fun t : ℚ_[p] => t * c) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.mul_const c).tendsto (0 : ℚ_[p])
  refine (hc.eventually hX).mono fun t ht => ?_
  obtain ⟨u, hu, he⟩ := ht
  exact ⟨u, hu, by rw [he, mul_smul]⟩

theorem neg_mem_ellAdicLie {G : Subgroup Aˣ} {X : A} (hX : X ∈ ellAdicLie p G) :
    -X ∈ ellAdicLie p G := by
  simpa using smul_mem_ellAdicLie (-1 : ℚ_[p]) hX

variable [CompleteSpace A]

variable (p A) in
/-- The Lie algebra of the full unit group is everything. -/
theorem ellAdicLie_top : ellAdicLie p (⊤ : Subgroup Aˣ) = Set.univ := by
  refine Set.eq_univ_of_forall fun X => ?_
  filter_upwards [padic_eventually_exp_smul_mul_exp_neg_smul (p := p) X] with t ht
  exact ⟨⟨exp (t • X), exp ((-t) • X), ht.1, ht.2⟩, Subgroup.mem_top _, rfl⟩

/-- **Invariance of the Lie algebra.** If `H ≤ G` and `G ∩ W ⊆ H` for some open `W ∋ 1` of
`Aˣ`, then `Lie(H) = Lie(G)`: `exp (t • X)` tends to `1` as `t → 0`. -/
theorem ellAdicLie_eq_of_nhds {H G : Subgroup Aˣ} (hHG : H ≤ G)
    (hW : ∃ W : Set Aˣ, IsOpen W ∧ (1 : Aˣ) ∈ W ∧ ∀ u ∈ G, u ∈ W → u ∈ H) :
    ellAdicLie p H = ellAdicLie p G := by
  refine (ellAdicLie_mono hHG).antisymm fun X hX => ?_
  obtain ⟨W, hWo, h1W, hWH⟩ := hW
  have hW' : IsOpen ((Units.val : Aˣ → A) '' W) := Units.isOpenEmbedding_val.isOpenMap W hWo
  have h1W' : (1 : A) ∈ (Units.val : Aˣ → A) '' W := ⟨1, h1W, Units.val_one⟩
  have hev := (padic_tendsto_exp_smul_one (p := p) X).eventually (hW'.mem_nhds h1W')
  filter_upwards [hX, hev] with t ht hw
  obtain ⟨u, huG, hu⟩ := ht
  obtain ⟨w, hwW, hw⟩ := hw
  have huw : u = w := Units.ext (hu.trans hw.symm)
  exact ⟨u, hWH u huG (huw ▸ hwW), hu⟩

/-- If `H ≤ G` is open in `G` (subspace topology), then `Lie(H) = Lie(G)`. -/
theorem ellAdicLie_eq_of_isOpen_subgroupOf {H G : Subgroup Aˣ} (hHG : H ≤ G)
    (hH : IsOpen (H.subgroupOf G : Set G)) : ellAdicLie p H = ellAdicLie p G := by
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp hH
  refine ellAdicLie_eq_of_nhds hHG ⟨W, hWo, ?_, fun u huG huW => ?_⟩
  · have h1 : (1 : G) ∈ (Subtype.val ⁻¹' W : Set G) := by
      rw [hWeq]; exact (H.subgroupOf G).one_mem
    exact h1
  · have h : (⟨u, huG⟩ : G) ∈ (Subtype.val ⁻¹' W : Set G) := huW
    rw [hWeq] at h
    exact Subgroup.mem_subgroupOf.mp h

/-- If `H ≤ G` is closed and of finite index in `G`, then `Lie(H) = Lie(G)`. -/
theorem ellAdicLie_eq_of_isClosed_of_finiteIndex {H G : Subgroup Aˣ} (hHG : H ≤ G)
    (hH : IsClosed (H : Set Aˣ)) [(H.subgroupOf G).FiniteIndex] :
    ellAdicLie p H = ellAdicLie p G := by
  have hcl : IsClosed (H.subgroupOf G : Set G) := hH.preimage continuous_subtype_val
  exact ellAdicLie_eq_of_isOpen_subgroupOf hHG
    (Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl)

theorem units_t2Space : T2Space Aˣ := Units.isOpenEmbedding_val.isEmbedding.t2Space

/-- If `H ≤ G` is compact and of finite index in `G`, then `Lie(H) = Lie(G)`. -/
theorem ellAdicLie_eq_of_isCompact_of_finiteIndex {H G : Subgroup Aˣ} (hHG : H ≤ G)
    (hH : IsCompact (H : Set Aˣ)) [(H.subgroupOf G).FiniteIndex] :
    ellAdicLie p H = ellAdicLie p G :=
  haveI := units_t2Space (A := A)
  ellAdicLie_eq_of_isClosed_of_finiteIndex hHG hH.isClosed

/-- **Lie algebra of the image of an open subgroup.** For a compact topological group `Γ`, an
open subgroup `Δ ≤ Γ` and a continuous homomorphism `ρ : Γ →* Aˣ`, the images `ρ(Δ) ≤ ρ(Γ)`
have the same Lie algebra (`ρ(Δ)` is relatively open in `ρ(Γ)`: the complement is the image of
the compact set `Γ ∖ ρ⁻¹(ρ(Δ))`). -/
theorem ellAdicLie_map_eq_of_isOpen {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ρ : Γ →* Aˣ) (hρ : Continuous ρ)
    (Δ : Subgroup Γ) (hΔ : IsOpen (Δ : Set Γ)) :
    ellAdicLie p (Δ.map ρ) = ellAdicLie p ρ.range := by
  have := units_t2Space (A := A)
  set S : Subgroup Γ := (Δ.map ρ).comap ρ with hS
  have hSo : IsOpen (S : Set Γ) := Subgroup.isOpen_mono (Subgroup.le_comap_map ρ Δ) hΔ
  have hSc : IsClosed ((S : Set Γ)ᶜ) := hSo.isClosed_compl
  have hK : IsClosed (ρ '' (S : Set Γ)ᶜ) := (hSc.isCompact.image hρ).isClosed
  refine ellAdicLie_eq_of_nhds (Subgroup.map_le_range ρ Δ)
    ⟨(ρ '' (S : Set Γ)ᶜ)ᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨g, hg, hg1⟩
    exact hg (show ρ g ∈ Δ.map ρ by rw [hg1]; exact (Δ.map ρ).one_mem)
  · rintro u ⟨g, rfl⟩ hu
    by_contra hg
    exact hu ⟨g, hg, rfl⟩

/-- The same with `ρ(Γ)` written as `(⊤ : Subgroup Γ).map ρ`. -/
theorem ellAdicLie_map_eq_map_top_of_isOpen {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ρ : Γ →* Aˣ) (hρ : Continuous ρ)
    (Δ : Subgroup Γ) (hΔ : IsOpen (Δ : Set Γ)) :
    ellAdicLie p (Δ.map ρ) = ellAdicLie p ((⊤ : Subgroup Γ).map ρ) := by
  rw [← MonoidHom.range_eq_map]
  exact ellAdicLie_map_eq_of_isOpen ρ hρ Δ hΔ

/-- **Galois instance.** For a continuous representation `ρ` of `Gal(ℚ̄/ℚ)` and a number field
`K ⊆ ℚ̄`, the image of `Gal(ℚ̄/K)` has the same `p`-adic Lie algebra as the image of
`Gal(ℚ̄/ℚ)`. -/
theorem ellAdicLie_galois_fixingSubgroup (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (ρ : Gal(AlgebraicClosure ℚ/ℚ) →* Aˣ) (hρ : Continuous ρ) :
    ellAdicLie p (K.fixingSubgroup.map ρ) = ellAdicLie p ρ.range :=
  ellAdicLie_map_eq_of_isOpen ρ hρ K.fixingSubgroup K.fixingSubgroup_isOpen

section Instances

/-! ### Instances: matrices and endomorphisms of a finite-dimensional space -/

variable (p) in
/-- The `p`-adic Lie algebra of a subgroup of `GL_n(ℚ_[p])`, computed in `Mat_n(ℚ_[p])`
normed by the `L^∞` operator norm (any norm inducing the usual topology gives the same set). -/
noncomputable def matrixEllAdicLie (n : ℕ) (G : Subgroup (GL (Fin n) ℚ_[p])) :
    Set (Matrix (Fin n) (Fin n) ℚ_[p]) :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℚ_[p])
  letI := Matrix.linftyOpNormedAlgebra (R := ℚ_[p]) (n := Fin n) (α := ℚ_[p])
  ellAdicLie p G

/-- `matrixEllAdicLie` in terms of the matrix exponential for the usual topology. -/
theorem mem_matrixEllAdicLie_iff (n : ℕ) (G : Subgroup (GL (Fin n) ℚ_[p]))
    (X : Matrix (Fin n) (Fin n) ℚ_[p]) :
    X ∈ matrixEllAdicLie p n G ↔
      ∀ᶠ t in 𝓝 (0 : ℚ_[p]), ∃ u ∈ G, (u : Matrix (Fin n) (Fin n) ℚ_[p]) = exp (t • X) :=
  Iff.rfl

/-- Galois instance for `GL_n(ℚ_[p])`: for a continuous `ρ : Gal(ℚ̄/ℚ) →* GL_n(ℚ_[p])` and a
number field `K ⊆ ℚ̄`, `Lie(ρ Gal(ℚ̄/K)) = Lie(ρ Gal(ℚ̄/ℚ))`. -/
theorem matrixEllAdicLie_galois_fixingSubgroup (n : ℕ)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ρ : Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin n) ℚ_[p]) (hρ : Continuous ρ) :
    matrixEllAdicLie p n (K.fixingSubgroup.map ρ) = matrixEllAdicLie p n ρ.range :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℚ_[p])
  letI := Matrix.linftyOpNormedAlgebra (R := ℚ_[p]) (n := Fin n) (α := ℚ_[p])
  haveI := FiniteDimensional.complete ℚ_[p] (Matrix (Fin n) (Fin n) ℚ_[p])
  ellAdicLie_galois_fixingSubgroup K ρ hρ

/-- Galois instance for `GL(V)`, `V` a finite-dimensional normed `ℚ_[p]`-space. -/
theorem endEllAdicLie_galois_fixingSubgroup {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ρ : Gal(AlgebraicClosure ℚ/ℚ) →* (V →L[ℚ_[p]] V)ˣ) (hρ : Continuous ρ) :
    ellAdicLie p (K.fixingSubgroup.map ρ) = ellAdicLie p ρ.range :=
  haveI := FiniteDimensional.complete ℚ_[p] V
  ellAdicLie_galois_fixingSubgroup K ρ hρ

end Instances

end ArithmeticOfJacobiPolynomials
