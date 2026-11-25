/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure
public import ArithmeticOfJacobiPolynomials.Algebra.SymplecticSimilitude

/-!
# Hodge and Mumford–Tate groups of a rational Hodge structure of weight `-1`

For a rational Hodge structure `H` of type `{(-1,0),(0,-1)}` on `V`
(`ArithmeticOfJacobiPolynomials.HodgeStructureNegOne`, see
`ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure`), we define,
as subgroups of `GL(V) = (V ≃ₗ[ℚ] V)` (`ℚ`-points):

* `HodgeStructureNegOne.hodgeGroup H`: the `g` fixing every Hodge class in every tensor space
  `T m n = V^{⊗m} ⊗ (V^*)^{⊗n}`;
* `HodgeStructureNegOne.mumfordTateGroup H`: the `g` for which there is `c : ℚˣ` with
  `g • t = c^{-p} • t` for every Hodge class `t ∈ T m n` of twist `p` (`n - m = 2 p`).

These are the characterizations of Deligne, *Hodge cycles on abelian varieties* (LNM 900),
Prop. 3.4 (see also Moonen, *Notes on Mumford–Tate groups*, §1, and Mumford, *A note of Shimura's
paper "Discontinuous groups and abelian varieties"*), here **taken as the definitions** on
`ℚ`-points: the Mumford–Tate group (resp. Hodge group) is the stabilizer of all Hodge classes in
`GL(V) × 𝔾_m` acting on `T m n ⊗ ℚ(p)` (resp. in `GL(V)`); no algebraic-group structure is
formalized.

**Exponent convention.** The pair `(g, c)` acts on `T m n ⊗ ℚ(p)` by `g ⊗ c^p` (`𝔾_m` acting on
`ℚ(1)` by the identity character), so `t ⊗ 1` is fixed iff `g • t = c^{-p} • t`. For the
polarization `ψ ∈ T 0 2` (twist `1`, `ψ : V ⊗ V → ℚ(1)`), `g • ψ = c⁻¹ • ψ` means
`ψ (g x) (g y) = c • ψ x y`: `c` is the multiplier of `g` (`mumfordTateGroup_le_similitudeGroup`).

## Main results

* `hodgeGroup_le_mumfordTateGroup`;
* `Polarization.hodgeGroup_le_symplecticGroup`: `Hdg ≤ Sp(V, ψ)`;
* `Polarization.mumfordTateGroup_le_similitudeGroup`: `MT ≤ GSp(V, ψ)`;
* `Polarization.circleRep_mem_symplecticGroup`: `h(U(1)) ⊆ Sp(V_ℝ, ψ_ℝ)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace HodgeStructureNegOne

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (H : HodgeStructureNegOne V)

/-- **The Hodge group** (on `ℚ`-points): the automorphisms of `V` fixing every Hodge class in
every `T m n` (Deligne, LNM 900, Prop. 3.4, taken as the definition). -/
@[expose]
def hodgeGroup : Subgroup (V ≃ₗ[ℚ] V) where
  carrier := {g | ∀ m n : ℕ, ∀ t ∈ H.hodgeClasses m n, tensorMap m n g t = t}
  one_mem' := by
    intro m n t _
    exact tensorMap_one_apply m n t
  mul_mem' := by
    intro g h hg hh m n t ht
    rw [tensorMap_mul_apply, hh m n t ht, hg m n t ht]
  inv_mem' := by
    intro g hg m n t ht
    calc tensorMap m n g⁻¹ t = tensorMap m n g⁻¹ (tensorMap m n g t) := by rw [hg m n t ht]
      _ = t := tensorMap_inv_apply_self m n g t

/-- Membership in the Hodge group. -/
theorem mem_hodgeGroup {g : V ≃ₗ[ℚ] V} :
    g ∈ H.hodgeGroup ↔ ∀ m n : ℕ, ∀ t ∈ H.hodgeClasses m n, tensorMap m n g t = t :=
  Iff.rfl

/-- **The Mumford–Tate group** (on `ℚ`-points): the automorphisms `g` of `V` for which some
`c : ℚˣ` satisfies `g • t = c^{-p} • t` for every Hodge class `t ∈ T m n` of twist `p`
(`n - m = 2 p`); see the module docstring for the exponent convention. -/
@[expose]
def mumfordTateGroup : Subgroup (V ≃ₗ[ℚ] V) where
  carrier := {g | ∃ c : ℚˣ, ∀ m n : ℕ, ∀ p : ℤ, (n : ℤ) - m = 2 * p →
    ∀ t ∈ H.hodgeClasses m n, tensorMap m n g t = ((c ^ (-p) : ℚˣ) : ℚ) • t}
  one_mem' := by
    refine ⟨1, fun _ _ _ _ _ _ => ?_⟩
    rw [tensorMap_one_apply, one_zpow, Units.val_one, one_smul]
  mul_mem' := by
    rintro g h ⟨c, hg⟩ ⟨d, hh⟩
    refine ⟨d * c, fun m n p hp t ht => ?_⟩
    rw [tensorMap_mul_apply, hh m n p hp t ht, map_smul, hg m n p hp t ht, smul_smul, mul_zpow,
      Units.val_mul]
  inv_mem' := by
    rintro g ⟨c, hg⟩
    refine ⟨c⁻¹, fun m n p hp t ht => ?_⟩
    have h1 := tensorMap_inv_apply_self m n g t
    rw [hg m n p hp t ht, map_smul] at h1
    calc tensorMap m n g⁻¹ t
        = ((c⁻¹ ^ (-p) * c ^ (-p) : ℚˣ) : ℚ) • tensorMap m n g⁻¹ t := by
          rw [← mul_zpow, inv_mul_cancel, one_zpow, Units.val_one, one_smul]
      _ = ((c⁻¹ ^ (-p) : ℚˣ) : ℚ) • t := by rw [Units.val_mul, mul_smul, h1]

/-- Membership in the Mumford–Tate group. -/
theorem mem_mumfordTateGroup {g : V ≃ₗ[ℚ] V} :
    g ∈ H.mumfordTateGroup ↔ ∃ c : ℚˣ, ∀ m n : ℕ, ∀ p : ℤ, (n : ℤ) - m = 2 * p →
      ∀ t ∈ H.hodgeClasses m n, tensorMap m n g t = ((c ^ (-p) : ℚˣ) : ℚ) • t :=
  Iff.rfl

/-- **`Hdg ≤ MT`** (with `c = 1`). -/
theorem hodgeGroup_le_mumfordTateGroup : H.hodgeGroup ≤ H.mumfordTateGroup := by
  intro g hg
  refine H.mem_mumfordTateGroup.2 ⟨1, fun m n _ _ t ht => ?_⟩
  rw [(H.mem_hodgeGroup.1 hg) m n t ht, one_zpow, Units.val_one, one_smul]

namespace Polarization

variable {H} (P : H.Polarization)

/-- **`Hdg ≤ Sp(V, ψ)`**: the Hodge group preserves the polarization. -/
theorem hodgeGroup_le_symplecticGroup [FiniteDimensional ℚ V] :
    H.hodgeGroup ≤ symplecticGroup P.form := by
  intro g hg
  refine mem_symplecticGroup.2 fun x y => ?_
  have h := (H.mem_hodgeGroup.1 hg) 0 2 _ P.bilinTensor_mem_hodgeClasses
  have h' := bilin_eq_smul_of_tensorMap_bilinTensor P.form g 1 (h.trans (one_smul ℚ _).symm) x y
  rw [one_mul] at h'
  exact h'.symm

/-- **`MT ≤ GSp(V, ψ)`**: the Mumford–Tate group multiplies the polarization by a scalar (its
multiplier is the `c` of `mumfordTateGroup`). -/
theorem mumfordTateGroup_le_similitudeGroup [FiniteDimensional ℚ V] :
    H.mumfordTateGroup ≤ similitudeGroup P.form := by
  intro g hg
  obtain ⟨c, hc⟩ := H.mem_mumfordTateGroup.1 hg
  refine mem_similitudeGroup.2 ⟨c, fun x y => ?_⟩
  have h := hc 0 2 1 (by norm_num) _ P.bilinTensor_mem_hodgeClasses
  have h' := bilin_eq_smul_of_tensorMap_bilinTensor P.form g _ h x y
  rw [zpow_neg_one] at h'
  rw [h', smul_eq_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- **`h(U(1)) ⊆ Sp(V_ℝ, ψ_ℝ)`**. -/
theorem circleRep_mem_symplecticGroup (z : Circle) :
    H.circleRep z ∈ symplecticGroup (P.form.baseChange ℝ) :=
  mem_symplecticGroup.2 (P.baseChange_circleRep z)

end Polarization

end HodgeStructureNegOne

end ArithmeticOfJacobiPolynomials
