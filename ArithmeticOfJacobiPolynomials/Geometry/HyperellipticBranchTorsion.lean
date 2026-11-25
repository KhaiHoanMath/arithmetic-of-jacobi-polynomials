/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchCharts
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchDivisors

/-!
# Branch-point classes in `Pic X`: the map `(ℤ/2)^{roots} → Pic(X)[2]` and the relation of `y`

Let `k` be a field with `2 ≠ 0` and `f ∈ k[x]` separable, `X = projectiveModel f`. This file
continues `ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchDivisors` (§6.5: "divisor
classes
supported on the branch points describe the 2-torsion"). All divisor theory is Stacks':
effective Cartier divisors are `Stacks.Divisors.IsEffectiveCartierDivisor` ideal sheaves, their
classes live in the (additive) Picard group `Stacks.Picard.ofScheme X`
(`Stacks.Divisors.picardClass`), and linear equivalence is `Stacks.Divisors.LinearlyEquivalent`
(Tag 0CCT), unfolded through Weil divisors and orders of rational functions by
`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_of_two_local_ratios`. Nothing is claimed
about a
Jacobian.

## Main definitions and results

* `ArithmeticOfJacobiPolynomials.torsionHomOfSq`: for elements `e_i` of an abelian group with `2 •
e_i = 0`, the
  homomorphism `(ι → ℤ/2) →+ A`, `δ_i ↦ e_i`.
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchClass hf c = [𝒪(P_c)]` and
  `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchDiffClass hf c₀ c = [𝒪(P_c)] - [𝒪(P_{c₀})]`,
  with
  `2 • branchDiffClass = 0` (`two_nsmul_branchDiffClass`, from `2 P_c ~ 2 P_{c₀}`).
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchTorsionHom h2 hf c₀`,
  `(BranchRoot f → ZMod 2) →+ Stacks.Picard.ofScheme X`, `δ_c ↦ [P_c - P_{c₀}]`
  (`branchTorsionHom_single`), with values in the `2`-torsion (`two_nsmul_branchTorsionHom`).
* **Even degree** (`deg f = 2g + 2`, `f` split over `k`):
  `sum_branchClass_eq_of_even`: `∑_c [𝒪(P_c)] = deg f • [𝒪(P_{c₀})]`, i.e.
  `∑_c P_c ~ deg f · P_{c₀}` (the rational function `y/(x - c₀)^{g+1}`), hence
  `branchTorsionHom_one_of_even`: `branchTorsionHom h2 hf c₀` kills the all-ones vector.
* **Odd degree** (`deg f = 2g + 1`): `x' = 0` is a root of `x'^{2g+2} f(1/x')`, and the point
  `P_∞ = (x', w) = (0, 0)` of the chart at infinity (`infinityPoint`) is a branch point:
  its ideal sheaf `infinityIdeal` is an effective Cartier divisor
  (`isEffectiveCartierDivisor_infinityIdeal`, local equation `w` near `P_∞`).
  - `linearlyEquivalent_branchIdeal_sq_infinity`: `2 P_c ~ 2 P_∞` (the function `x - c`);
  - `sum_branchClass_add_infinity_eq` (`f` split): `∑_c P_c + P_∞ ~ (2g + 2) P_∞`
    (the function `y`, whose divisor is `∑_c P_c - (2g + 1) P_∞`);
  - `branchTorsionHomInf` (`δ_c ↦ [P_c - P_∞]`) kills the all-ones vector
    (`branchTorsionHomInf_one`).

In odd degree the base point must be `P_∞`: with a finite base root `c₀` the all-ones vector
is sent to `[P_{c₀} - P_∞]` (by the two relations above), which is not claimed to vanish.
Injectivity of these maps and non-triviality of the classes are not proved here.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-! ### Homomorphisms out of `(ℤ/2)^ι` -/

section TorsionHom

variable {A : Type*} [AddCommGroup A]

/-- For `a` with `2 • a = 0`, the homomorphism `ℤ/2 → A`, `1 ↦ a`. -/
noncomputable def zmodTwoHom (a : A) (ha : 2 • a = 0) : ZMod 2 →+ A :=
  ZMod.lift 2 ⟨zmultiplesHom A a, by rw [zmultiplesHom_apply, natCast_zsmul]; exact ha⟩

theorem zmodTwoHom_one (a : A) (ha : 2 • a = 0) : zmodTwoHom a ha 1 = a := by
  have h1 : (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) := Int.cast_one.symm
  rw [zmodTwoHom, h1, ZMod.lift_coe]
  exact one_zsmul a

variable {ι : Type*} [Fintype ι]

/-- **The homomorphism `(ℤ/2)^ι → A`** sending the `i`-th basis vector to `e_i`, for elements
`e_i` with `2 • e_i = 0`. -/
noncomputable def torsionHomOfSq (e : ι → A) (he : ∀ i, 2 • e i = 0) : (ι → ZMod 2) →+ A :=
  ∑ i, (zmodTwoHom (e i) (he i)).comp (Pi.evalAddMonoidHom (fun _ => ZMod 2) i)

variable (e : ι → A) (he : ∀ i, 2 • e i = 0)

theorem torsionHomOfSq_apply (v : ι → ZMod 2) :
    torsionHomOfSq e he v = ∑ i, zmodTwoHom (e i) (he i) (v i) := by
  rw [torsionHomOfSq, AddMonoidHom.finsetSum_apply]
  rfl

theorem torsionHomOfSq_single [DecidableEq ι] (i : ι) :
    torsionHomOfSq e he (Pi.single i 1) = e i := by
  rw [torsionHomOfSq_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, zmodTwoHom_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The all-ones vector is sent to the sum of all `e_i`. -/
theorem torsionHomOfSq_one : torsionHomOfSq e he 1 = ∑ i, e i := by
  rw [torsionHomOfSq_apply]
  exact Finset.sum_congr rfl fun i _ => zmodTwoHom_one (e i) (he i)

/-- The values are `2`-torsion. -/
theorem two_nsmul_torsionHomOfSq (v : ι → ZMod 2) : 2 • torsionHomOfSq e he v = 0 := by
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [← map_nsmul, two_nsmul]
  have hv : v + v = 0 := funext fun i => h2 (v i)
  rw [hv, map_zero]

/-- `∑_i (n_i - b) = 0` when `∑_i n_i = |ι| • b`. -/
theorem sum_sub_eq_zero_of_sum_eq_card_nsmul (n : ι → A) (b : A)
    (h : ∑ i, n i = Fintype.card ι • b) : ∑ i, (n i - b) = 0 := by
  rw [Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, sub_self]

end TorsionHom

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open _root_.Polynomial Divisors AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {k : Type u} [Field k] {f : k[X]} {c : k}

/-! ### The branch classes -/

set_option synthInstance.maxHeartbeats 400000 in
-- the `AddCommGroup` instance on `Stacks.Picard.ofScheme X` is found through a long chain
/-- The Picard group `Stacks.Picard.ofScheme X` as an additive commutative group (the instance
search for it is expensive, so it is cached here). -/
noncomputable instance picardAddCommGroup (polyX : Scheme.{u}) :
    AddCommGroup (Stacks.Picard.ofScheme polyX) := inferInstance

/-- The class `[𝒪(P_c)]` of a finite branch point in `Pic X`. -/
@[expose] noncomputable def branchClass (hf : f.Separable) (c : BranchRoot f) :
    Stacks.Picard.ofScheme (projectiveModel f) :=
  @Stacks.Divisors.picardClass _ _
    (isEffectiveCartierDivisor_branchIdeal hf (BranchRoot.eval_eq_zero c))

/-- **The branch class** `e_c = [𝒪(P_c - P_{c₀})] = [𝒪(P_c)] - [𝒪(P_{c₀})]`. -/
@[expose] noncomputable def branchDiffClass (hf : f.Separable) (c₀ c : BranchRoot f) :
    Stacks.Picard.ofScheme (projectiveModel f) :=
  branchClass hf c - branchClass hf c₀

/-- `2 e_c = 0` (`2 P_c ~ 2 P_{c₀}`). -/
theorem two_nsmul_branchDiffClass (h2 : (2 : k) ≠ 0) (hf : f.Separable) (c₀ c : BranchRoot f) :
    2 • branchDiffClass hf c₀ c = 0 := by
  rw [branchDiffClass, smul_sub, sub_eq_zero]
  exact two_nsmul_picardClass_branchIdeal_eq h2 hf (BranchRoot.eval_eq_zero c)
    (BranchRoot.eval_eq_zero c₀)

/-- **The homomorphism `(ℤ/2)^{roots} → Pic X`**, `δ_c ↦ [P_c - P_{c₀}]`. -/
@[expose] noncomputable def branchTorsionHom (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (c₀ : BranchRoot f) :
    (BranchRoot f → ZMod 2) →+ Stacks.Picard.ofScheme (projectiveModel f) :=
  torsionHomOfSq (branchDiffClass hf c₀) (two_nsmul_branchDiffClass h2 hf c₀)

theorem branchTorsionHom_single (h2 : (2 : k) ≠ 0) (hf : f.Separable) (c₀ : BranchRoot f)
    [DecidableEq (BranchRoot f)] (c : BranchRoot f) :
    branchTorsionHom h2 hf c₀ (Pi.single c 1) = branchDiffClass hf c₀ c :=
  torsionHomOfSq_single _ _ c

/-- **`branchTorsionHom` lands in the `2`-torsion of `Pic X`.** -/
theorem two_nsmul_branchTorsionHom (h2 : (2 : k) ≠ 0) (hf : f.Separable) (c₀ : BranchRoot f)
    (v : BranchRoot f → ZMod 2) : 2 • branchTorsionHom h2 hf c₀ v = 0 :=
  two_nsmul_torsionHomOfSq _ _ v

/-! ### The divisor `∑_c P_c` -/

theorem isEffectiveCartierDivisor_branchSumIdeal (hf : f.Separable) :
    Stacks.Divisors.IsEffectiveCartierDivisor (branchSumIdeal f) :=
  isEffectiveCartierDivisor_prod _ fun c =>
    isEffectiveCartierDivisor_branchIdeal hf (BranchRoot.eval_eq_zero c)

theorem picardClass_branchSumIdeal (hf : f.Separable) :
    haveI := isEffectiveCartierDivisor_branchSumIdeal hf
    Stacks.Divisors.picardClass (branchSumIdeal f) = ∑ c : BranchRoot f, branchClass hf c := by
  have : ∀ c : BranchRoot f, Stacks.Divisors.IsEffectiveCartierDivisor
      (branchIdeal f (BranchRoot.eval_eq_zero c)) := fun c =>
    isEffectiveCartierDivisor_branchIdeal hf (BranchRoot.eval_eq_zero c)
  exact picardClass_prod Finset.univ (fun c : BranchRoot f =>
    branchIdeal f (BranchRoot.eval_eq_zero c))

/-! ### Even degree: `∑_c P_c ~ deg f · P_{c₀}` -/

/-- **In even degree `2g + 2`, `∑_c P_c ~ (2g + 2) P_{c₀}`** (`f` separable and split over
`k`): the rational function `y/(x - c₀)^{g+1}` has divisor `∑_c P_c - (g + 1) · 2 P_{c₀}`.
In `Pic X`: `∑_c [𝒪(P_c)] = deg f • [𝒪(P_{c₀})]`. -/
theorem sum_branchClass_eq_of_even (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f) :
    ∑ c : BranchRoot f, branchClass hf c = f.natDegree • branchClass hf c₀ := by
  classical
  have hc₀ := BranchRoot.eval_eq_zero c₀
  have hdeg : 0 < f.natDegree := natDegree_pos_of_eval_eq_zero hf hc₀
  have hN : f.natDegree = 2 * genus f + 2 := by
    obtain ⟨m, hm⟩ := heven
    unfold genus
    omega
  have := isIntegral_projectiveModel hf hdeg
  have := isNormal_projectiveModel h2 hf hdeg
  have hP₀ := isEffectiveCartierDivisor_branchIdeal hf hc₀
  have hI := isEffectiveCartierDivisor_branchSumIdeal hf
  have hJ : Stacks.Divisors.IsEffectiveCartierDivisor
      (∏ _i ∈ Finset.range (genus f + 1), branchIdeal f hc₀ * branchIdeal f hc₀) :=
    isEffectiveCartierDivisor_prod _ fun _ => inferInstance
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  let W₂ : (projectiveModel f).affineOpens :=
    ⟨(projectiveModel f).basicOpen
      (infiniteWCoord f * infiniteCoord f (1 - C c₀.1 * Polynomial.X)),
      hUinf.basicOpen _⟩
  have hV₁ : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteWCoord f) := by
    change (projectiveModel f).basicOpen _ ≤ _
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  have hV₂ : W₂.1 ≤ (projectiveModel f).basicOpen
      (infiniteCoord f (1 - C c₀.1 * Polynomial.X)) := by
    change (projectiveModel f).basicOpen _ ≤ _
    rw [Scheme.basicOpen_mul]
    exact inf_le_right
  have hcov : ∀ x, x ∈ chartOpen f ∨ x ∈ W₂.1 := by
    intro x
    by_cases hx : x ∈ chartOpen f
    · exact Or.inl hx
    · right
      change x ∈ (projectiveModel f).basicOpen _
      rw [Scheme.basicOpen_mul]
      exact ⟨mem_basicOpen_infiniteWCoord_of_not_mem hf.ne_zero hN hx,
        mem_basicOpen_infiniteCoord_of_not_mem (by simp) hx⟩
  have hres₁ := hV₁.trans ((projectiveModel f).basicOpen_le _)
  have hres₂ := hV₂.trans ((projectiveModel f).basicOpen_le _)
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : Γ(projectiveModel f, W₂.1), w₂ =
      (projectiveModel f).presheaf.map (homOfLE hres₁).op (infiniteWCoord f) := ⟨_, rfl⟩
  have hτ₂ : (branchSumIdeal f).ideal W₂ = Ideal.span {w₂} := by
    rw [branchSumIdeal_ideal_eq_top W₂ fun c hc =>
      branchPoint_not_mem_basicOpen_infiniteWCoord (BranchRoot.eval_eq_zero c) (hV₁ hc),
      eq_comm, Ideal.span_singleton_eq_top, hw₂]
    exact isUnit_res_of_le_basicOpen _ hV₁
  have hσ₁ : (∏ _i ∈ Finset.range (genus f + 1), branchIdeal f hc₀ * branchIdeal f hc₀).ideal
      (chartAffineOpen f) =
      Ideal.span {finiteCoord f (Polynomial.X - C c₀.1) ^ (genus f + 1)} :=
    (ideal_prod_eq_span (Finset.range (genus f + 1))
      (fun _ => branchIdeal f hc₀ * branchIdeal f hc₀) (chartAffineOpen f)
      (fun _ => finiteCoord f (Polynomial.X - C c₀.1))
      (fun _ _ => branchIdeal_mul_self_ideal_chartOpen_coord hf hc₀)).trans
      (by rw [Finset.prod_const, Finset.card_range])
  have hσ₂ : (∏ _i ∈ Finset.range (genus f + 1), branchIdeal f hc₀ * branchIdeal f hc₀).ideal
      W₂ = Ideal.span {((projectiveModel f).presheaf.map (homOfLE hres₂).op
        (infiniteCoord f (1 - C c₀.1 * Polynomial.X))) ^ (genus f + 1)} :=
    (ideal_prod_eq_span (Finset.range (genus f + 1))
      (fun _ => branchIdeal f hc₀ * branchIdeal f hc₀) W₂
      (fun _ => (projectiveModel f).presheaf.map (homOfLE hres₂).op
        (infiniteCoord f (1 - C c₀.1 * Polynomial.X)))
      (fun _ _ => branchIdeal_mul_self_ideal_eq_span_of_le_coord hc₀ W₂ hV₂)).trans
      (by rw [Finset.prod_const, Finset.card_range])
  have hid : (projectiveModel f).presheaf.map
        (homOfLE (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op
          (finiteYCoord f) *
      (projectiveModel f).presheaf.map
        (homOfLE (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤
          chartOpenAtInfinity f)).op (infiniteCoord f (1 - C c₀.1 * Polynomial.X)) ^
            (genus f + 1) =
      (projectiveModel f).presheaf.map
        (homOfLE (inf_le_right : chartOpen f ⊓ chartOpenAtInfinity f ≤
          chartOpenAtInfinity f)).op (infiniteWCoord f) *
      (projectiveModel f).presheaf.map
        (homOfLE (inf_le_left : chartOpen f ⊓ chartOpenAtInfinity f ≤ chartOpen f)).op
          (finiteCoord f (Polynomial.X - C c₀.1)) ^ (genus f + 1) := by
    rw [overlap_w_identity, ← overlap_coord_identity]
    ring
  have hnz : (finiteYCoord f) ∈ nonZeroDivisors Γ(projectiveModel f, chartOpen f) :=
    sectionsEquivFinite_mem_nonZeroDivisors hf hdeg (by
      rw [sectionsEquivFinite_finiteYCoord]
      exact root_ne_zero hf.ne_zero)
  have h12 : ∀ (x : projectiveModel f) (h₁ : x ∈ (chartAffineOpen f).1) (h₂ : x ∈ W₂.1),
      (projectiveModel f).presheaf.germ (chartAffineOpen f).1 x h₁ (finiteYCoord f) *
          (projectiveModel f).presheaf.germ W₂.1 x h₂
            (((projectiveModel f).presheaf.map (homOfLE hres₂).op
              (infiniteCoord f (1 - C c₀.1 * Polynomial.X))) ^ (genus f + 1)) =
        (projectiveModel f).presheaf.germ W₂.1 x h₂ w₂ *
          (projectiveModel f).presheaf.germ (chartAffineOpen f).1 x h₁
            (finiteCoord f (Polynomial.X - C c₀.1) ^ (genus f + 1)) := by
    intro x h₁ h₂
    have hxinf : x ∈ chartOpenAtInfinity f := (projectiveModel f).basicOpen_le _ (hV₁ h₂)
    have hO : x ∈ chartOpen f ⊓ chartOpenAtInfinity f := ⟨h₁, hxinf⟩
    have e := congrArg ((projectiveModel f).presheaf.germ _ x hO) hid
    simp only [map_mul, map_pow, TopCat.Presheaf.germ_res_apply] at e
    simp only [map_pow, TopCat.Presheaf.germ_res_apply, hw₂]
    exact e
  have hlin := linearlyEquivalent_of_two_local_ratios (branchSumIdeal f) _ hI hJ
    (chartAffineOpen f) W₂ hcov (branchSumIdeal_ideal_chartOpen hf hsplit) hτ₂ hσ₁ hσ₂
    hnz (by rw [hw₂]; exact (isUnit_res_of_le_basicOpen _ hV₁).mem_nonZeroDivisors)
    (pow_mem (finiteCoord_mem_nonZeroDivisors hf hc₀) _)
    (pow_mem (isUnit_res_of_le_basicOpen _ hV₂).mem_nonZeroDivisors _) h12
  have key := (linearlyEquivalent_iff_picardClass_eq' (branchSumIdeal f) _).mp hlin
  have : ∀ _i ∈ Finset.range (genus f + 1), Stacks.Divisors.IsEffectiveCartierDivisor
      (branchIdeal f hc₀ * branchIdeal f hc₀) := fun _ _ => inferInstance
  rw [picardClass_branchSumIdeal hf, picardClass_prod (Finset.range (genus f + 1))
    (fun _ => branchIdeal f hc₀ * branchIdeal f hc₀), Finset.sum_const, Finset.card_range,
    Stacks.Divisors.picardClass_mul] at key
  rw [key, hN, ← two_nsmul, smul_smul]
  congr 1
  ring

/-- **In even degree, `branchTorsionHom` kills the all-ones vector**
(`∑_c P_c ~ deg f · P_{c₀}`). -/
theorem branchTorsionHom_one_of_even (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f) :
    branchTorsionHom h2 hf c₀ 1 = 0 := by
  have key := sum_branchClass_eq_of_even h2 hf hsplit heven c₀
  rw [branchTorsionHom, torsionHomOfSq_one]
  exact sum_sub_eq_zero_of_sum_eq_card_nsmul (fun c => branchClass hf c) (branchClass hf c₀)
    (by rw [card_branchRoot hf hsplit]; exact key)

/-! ### Restriction helpers -/

/-- The restriction of a non-zero-divisor to a nonempty smaller open of an integral scheme is a
non-zero-divisor. -/
theorem res_mem_nonZeroDivisors {Y : Scheme.{u}} [IsIntegral Y] {U V : Y.Opens} [Nonempty V]
    (h : V ≤ U) {s : Γ(Y, U)} (hs : s ∈ nonZeroDivisors Γ(Y, U)) :
    Y.presheaf.map (homOfLE h).op s ∈ nonZeroDivisors Γ(Y, V) := by
  have hU : Nonempty U := ⟨⟨_, h (Classical.choice ‹Nonempty V›).2⟩⟩
  have := IsIntegral.component_integral (X := Y) V
  have := IsIntegral.component_integral (X := Y) U
  refine mem_nonZeroDivisors_of_ne_zero fun hz => ?_
  exact nonZeroDivisors.ne_zero hs
    (map_injective_of_isIntegral (X := Y) (homOfLE h) (hz.trans (map_zero _).symm))

/-- If an ideal sheaf is cut out by `a` on an affine open `U`, it is cut out by the restriction of
`a` on the affine basic open `D(s) ⊆ U`. -/
theorem ideal_affineBasicOpen_eq_span {Y : Scheme.{u}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    {a : Γ(Y, U.1)} (h : I.ideal U = Ideal.span {a}) (s : Γ(Y, U.1)) :
    I.ideal (Y.affineBasicOpen s) =
      Ideal.span {Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op a} := by
  rw [← I.map_ideal_basicOpen U s, h, Ideal.map_span, Set.image_singleton]

theorem finiteYCoord_mem_nonZeroDivisors (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    finiteYCoord f ∈ nonZeroDivisors Γ(projectiveModel f, chartOpen f) :=
  sectionsEquivFinite_mem_nonZeroDivisors hf hdeg (by
    rw [sectionsEquivFinite_finiteYCoord]
    exact root_ne_zero hf.ne_zero)

/-! ### Odd degree: the branch point `P_∞` -/

variable (h0 : (reflect (2 * genus f + 2) f).eval 0 = 0)

/-- **The branch point `P_∞` is an effective Cartier divisor** (odd degree): `w` is a local
equation near `P_∞`. -/
theorem isEffectiveCartierDivisor_infinityIdeal (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    Stacks.Divisors.IsEffectiveCartierDivisor (infinityIdeal f h0) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  by_cases hx : x = infinityPoint f h0
  · subst hx
    exact ⟨_, (isAffineOpen_opensRange (affineChartAtInfinity f)).basicOpen
      (infiniteCoord f (infinityCofactor f)), infinityPoint_mem_basicOpen_cofactor h0 hf hdeg, _,
      isRegular_iff_mem_nonZeroDivisors.mpr (infiniteWCoord_res_mem_nonZeroDivisors h0 hf hdeg),
      infinityIdeal_ideal_basicOpen h0 hf hdeg⟩
  · obtain ⟨V, hxV, hPV⟩ := exists_affineOpen_not_mem_infinity h0 hx
    refine ⟨V.1, V.2, hxV, 1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one]
    exact pointIdeal_ideal_eq_top _ V hPV

/-- The class `[𝒪(P_∞)]` of the point at infinity in `Pic X` (odd degree). -/
@[expose] noncomputable def infinityClass (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    Stacks.Picard.ofScheme (projectiveModel f) :=
  @Stacks.Divisors.picardClass _ _ (isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg)

/-- **`2 P_c ~ 2 P_∞`** (odd degree): the function `x - c` has divisor `2 P_c - 2 P_∞`. -/
theorem linearlyEquivalent_branchIdeal_sq_infinity (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hc : f.eval c = 0) :
    Stacks.Divisors.LinearlyEquivalent (branchIdeal f hc ^ 2) (infinityIdeal f h0 ^ 2) := by
  have := isIntegral_projectiveModel hf hdeg
  have := isNormal_projectiveModel h2 hf hdeg
  have := isEffectiveCartierDivisor_branchIdeal hf hc
  have := isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  let W₂ : (projectiveModel f).affineOpens :=
    ⟨(projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X)),
      hUinf.basicOpen _⟩
  have hV : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X)) :=
    le_rfl
  have hWinf : W₂.1 ≤ chartOpenAtInfinity f := (projectiveModel f).basicOpen_le _
  have hcov : ∀ x, x ∈ chartOpen f ∨ x ∈ W₂.1 := by
    intro x
    by_cases hx : x ∈ chartOpen f
    · exact Or.inl hx
    · exact Or.inr (mem_basicOpen_infiniteCoord_of_not_mem (by simp) hx)
  have : Nonempty W₂.1 := ⟨⟨infinityPoint f h0, mem_basicOpen_infiniteCoord_of_not_mem (by simp)
    (infinityPoint_not_mem_chartOpen h0)⟩⟩
  have hσ₂ : (infinityIdeal f h0 * infinityIdeal f h0).ideal W₂ = Ideal.span
      {(projectiveModel f).presheaf.map (homOfLE (Scheme.basicOpen_le _ _)).op
        (infiniteCoord f Polynomial.X)} :=
    ideal_affineBasicOpen_eq_span _ (chartAffineOpenAtInfinity f)
      (infinityIdeal_mul_self_ideal_chartOpenAtInfinity h0 hf hdeg) _
  rw [sq, sq]
  refine Divisors.linearlyEquivalent_of_two_local_ratios _ _ inferInstance inferInstance
    (chartAffineOpen f) W₂ hcov
    (branchIdeal_mul_self_ideal_chartOpen_coord hf hc)
    (branchIdeal_mul_self_ideal_eq_span_of_le_coord hc W₂ hV)
    (infinityIdeal_mul_self_ideal_chartOpen h0) hσ₂
    (finiteCoord_mem_nonZeroDivisors hf hc)
    (isUnit_res_of_le_basicOpen _ hV).mem_nonZeroDivisors (Submonoid.one_mem _)
    (res_mem_nonZeroDivisors hWinf (infiniteCoord_X_mem_nonZeroDivisors hf hdeg)) ?_
  intro x h₁ h₂
  have hxinf : x ∈ chartOpenAtInfinity f := hWinf h₂
  have hO : x ∈ chartOpen f ⊓ chartOpenAtInfinity f := ⟨h₁, hxinf⟩
  have e := congrArg ((projectiveModel f).presheaf.germ _ x hO)
    (overlap_coord_identity (f := f) c)
  simp only [map_mul, TopCat.Presheaf.germ_res_apply] at e
  simp only [map_one, mul_one, TopCat.Presheaf.germ_res_apply]
  exact e

/-- **`2 [P_c] = 2 [P_∞]` in `Pic X`** (odd degree). -/
theorem two_nsmul_branchClass_eq_infinity (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (c : BranchRoot f) :
    2 • branchClass hf c = 2 • infinityClass h0 hf hdeg := by
  have hc := BranchRoot.eval_eq_zero c
  have := isEffectiveCartierDivisor_branchIdeal hf hc
  have := isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg
  have h := (linearlyEquivalent_iff_picardClass_eq' _ _).mp
    (linearlyEquivalent_branchIdeal_sq_infinity h0 h2 hf hdeg hc)
  rw [Stacks.Divisors.picardClass_pow, Stacks.Divisors.picardClass_pow] at h
  exact h

/-- The class `[P_c - P_∞]` (odd degree). -/
@[expose] noncomputable def branchDiffClassInf (hf : f.Separable) (hdeg : 0 < f.natDegree)
    (c : BranchRoot f) : Stacks.Picard.ofScheme (projectiveModel f) :=
  branchClass hf c - infinityClass h0 hf hdeg

theorem two_nsmul_branchDiffClassInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (c : BranchRoot f) : 2 • branchDiffClassInf h0 hf hdeg c = 0 := by
  rw [branchDiffClassInf, smul_sub, sub_eq_zero]
  exact two_nsmul_branchClass_eq_infinity h0 h2 hf hdeg c

/-- **The homomorphism `(ℤ/2)^{roots} → Pic X` based at `P_∞`** (odd degree),
`δ_c ↦ [P_c - P_∞]`. -/
@[expose] noncomputable def branchTorsionHomInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) :
    (BranchRoot f → ZMod 2) →+ Stacks.Picard.ofScheme (projectiveModel f) :=
  torsionHomOfSq (branchDiffClassInf h0 hf hdeg) (two_nsmul_branchDiffClassInf h0 h2 hf hdeg)

theorem branchTorsionHomInf_single (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) [DecidableEq (BranchRoot f)] (c : BranchRoot f) :
    branchTorsionHomInf h0 h2 hf hdeg (Pi.single c 1) = branchDiffClassInf h0 hf hdeg c :=
  torsionHomOfSq_single _ _ c

theorem two_nsmul_branchTorsionHomInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (v : BranchRoot f → ZMod 2) :
    2 • branchTorsionHomInf h0 h2 hf hdeg v = 0 :=
  two_nsmul_torsionHomOfSq _ _ v

/-- **The divisor of `y` in odd degree** (`f` separable and split over `k`, `deg f = 2g + 1`):
`div(y) = ∑_c P_c - (2g + 1) P_∞`, i.e. `∑_c P_c + P_∞ ~ (2g + 2) P_∞`. In `Pic X`:
`∑_c [𝒪(P_c)] + [𝒪(P_∞)] = (2g + 2) • [𝒪(P_∞)]`. -/
theorem sum_branchClass_add_infinity_eq (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hsplit : f.roots.card = f.natDegree) :
    ∑ c : BranchRoot f, branchClass hf c + infinityClass h0 hf hdeg =
      (2 * genus f + 2) • infinityClass h0 hf hdeg := by
  classical
  have := isIntegral_projectiveModel hf hdeg
  have := isNormal_projectiveModel h2 hf hdeg
  have hP := isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg
  have hS := isEffectiveCartierDivisor_branchSumIdeal hf
  have hI : Stacks.Divisors.IsEffectiveCartierDivisor (branchSumIdeal f * infinityIdeal f h0) :=
    inferInstance
  have hJ : Stacks.Divisors.IsEffectiveCartierDivisor
      (∏ _i ∈ Finset.range (genus f + 1), infinityIdeal f h0 * infinityIdeal f h0) :=
    isEffectiveCartierDivisor_prod _ fun _ => inferInstance
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  let Uaff : (projectiveModel f).affineOpens :=
    ⟨(projectiveModel f).basicOpen (infiniteCoord f (infinityCofactor f)), hUinf.basicOpen _⟩
  have hUinf' : Uaff.1 ≤ chartOpenAtInfinity f := (projectiveModel f).basicOpen_le _
  let s' : Γ(projectiveModel f, Uaff.1) := (projectiveModel f).presheaf.map (homOfLE hUinf').op
    (infiniteCoord f (∏ c : BranchRoot f, (1 - C c.1 * Polynomial.X)))
  let W₂ : (projectiveModel f).affineOpens := (projectiveModel f).affineBasicOpen s'
  have hW₂U : W₂.1 ≤ Uaff.1 := (projectiveModel f).basicOpen_le s'
  have hW₂inf : W₂.1 ≤ chartOpenAtInfinity f := hW₂U.trans hUinf'
  have hW₂eq : W₂.1 = Uaff.1 ⊓ (projectiveModel f).basicOpen
      (infiniteCoord f (∏ c : BranchRoot f, (1 - C c.1 * Polynomial.X))) :=
    Scheme.basicOpen_res _ _ _
  have hPW : ∀ c : BranchRoot f, branchPoint f c.1 (BranchRoot.eval_eq_zero c) ∉ W₂.1 := by
    intro c hc
    rw [hW₂eq] at hc
    have h2 := hc.2
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), infiniteCoord_mul,
      Scheme.basicOpen_mul] at h2
    exact branchPoint_not_mem_basicOpen_infiniteCoord (BranchRoot.eval_eq_zero c) h2.1
  have hmemW : ∀ x : projectiveModel f, x ∉ chartOpen f → x ∈ W₂.1 := by
    intro x hx
    rw [hW₂eq]
    refine ⟨mem_basicOpen_infiniteCoord_of_not_mem (eval_infinityCofactor_ne_zero h0 hf hdeg) hx,
      mem_basicOpen_infiniteCoord_of_not_mem ?_ hx⟩
    rw [eval_prod]
    simp
  have hcov : ∀ x, x ∈ chartOpen f ∨ x ∈ W₂.1 := fun x =>
    (em (x ∈ chartOpen f)).imp id (hmemW x)
  have hPinfU : infinityPoint f h0 ∈ Uaff.1 := infinityPoint_mem_basicOpen_cofactor h0 hf hdeg
  have : Nonempty Uaff.1 := ⟨⟨_, hPinfU⟩⟩
  have : Nonempty W₂.1 := ⟨⟨infinityPoint f h0, hmemW _ (infinityPoint_not_mem_chartOpen h0)⟩⟩
  have hτ₁ : (branchSumIdeal f * infinityIdeal f h0).ideal (chartAffineOpen f) =
      Ideal.span {finiteYCoord f} := by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, branchSumIdeal_ideal_chartOpen hf hsplit,
      pointIdeal_ideal_eq_top _ _ (infinityPoint_not_mem_chartOpen h0), Ideal.mul_top]
  have hUid : (infinityIdeal f h0 * infinityIdeal f h0).ideal Uaff = Ideal.span
      {(projectiveModel f).presheaf.map (homOfLE hUinf').op (infiniteCoord f Polynomial.X)} :=
    ideal_affineBasicOpen_eq_span _ (chartAffineOpenAtInfinity f)
      (infinityIdeal_mul_self_ideal_chartOpenAtInfinity h0 hf hdeg) _
  have hτ₂ : (branchSumIdeal f * infinityIdeal f h0).ideal W₂ = Ideal.span
      {(projectiveModel f).presheaf.map (homOfLE hW₂U).op
        ((projectiveModel f).presheaf.map
          (homOfLE ((projectiveModel f).basicOpen_le (infiniteCoord f (infinityCofactor f)))).op
            (infiniteWCoord f))} := by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      branchSumIdeal_ideal_eq_top W₂ fun c hc => hPW c hc, Ideal.top_mul]
    exact ideal_affineBasicOpen_eq_span _ Uaff (infinityIdeal_ideal_basicOpen h0 hf hdeg) s'
  have hσ₁ : (∏ _i ∈ Finset.range (genus f + 1), infinityIdeal f h0 * infinityIdeal f h0).ideal
      (chartAffineOpen f) = Ideal.span {1} :=
    (ideal_prod_eq_span (Finset.range (genus f + 1))
      (fun _ => infinityIdeal f h0 * infinityIdeal f h0) (chartAffineOpen f)
      (fun _ => (1 : Γ(projectiveModel f, chartOpen f)))
      (fun _ _ => infinityIdeal_mul_self_ideal_chartOpen h0)).trans
      (by rw [Finset.prod_const_one])
  have hσ₂ : (∏ _i ∈ Finset.range (genus f + 1), infinityIdeal f h0 * infinityIdeal f h0).ideal
      W₂ = Ideal.span {((projectiveModel f).presheaf.map (homOfLE hW₂U).op
        ((projectiveModel f).presheaf.map (homOfLE hUinf').op
          (infiniteCoord f Polynomial.X))) ^ (genus f + 1)} :=
    (ideal_prod_eq_span (Finset.range (genus f + 1))
      (fun _ => infinityIdeal f h0 * infinityIdeal f h0) W₂
      (fun _ => (projectiveModel f).presheaf.map (homOfLE hW₂U).op
        ((projectiveModel f).presheaf.map (homOfLE hUinf').op (infiniteCoord f Polynomial.X)))
      (fun _ _ => ideal_affineBasicOpen_eq_span _ Uaff hUid s')).trans
      (by rw [Finset.prod_const, Finset.card_range])
  have h12 : ∀ (x : projectiveModel f) (h₁ : x ∈ (chartAffineOpen f).1) (h₂ : x ∈ W₂.1),
      (projectiveModel f).presheaf.germ (chartAffineOpen f).1 x h₁ (finiteYCoord f) *
          (projectiveModel f).presheaf.germ W₂.1 x h₂
            (((projectiveModel f).presheaf.map (homOfLE hW₂U).op
              ((projectiveModel f).presheaf.map (homOfLE hUinf').op
                (infiniteCoord f Polynomial.X))) ^ (genus f + 1)) =
        (projectiveModel f).presheaf.germ W₂.1 x h₂
            ((projectiveModel f).presheaf.map (homOfLE hW₂U).op
              ((projectiveModel f).presheaf.map
                (homOfLE ((projectiveModel f).basicOpen_le
                  (infiniteCoord f (infinityCofactor f)))).op (infiniteWCoord f))) *
          (projectiveModel f).presheaf.germ (chartAffineOpen f).1 x h₁ 1 := by
    intro x h₁ h₂
    have hxinf : x ∈ chartOpenAtInfinity f := hW₂inf h₂
    have hO : x ∈ chartOpen f ⊓ chartOpenAtInfinity f := ⟨h₁, hxinf⟩
    have e := congrArg ((projectiveModel f).presheaf.germ _ x hO)
      (overlap_w_identity (f := f))
    simp only [map_mul, map_pow, TopCat.Presheaf.germ_res_apply] at e
    simp only [map_one, map_pow, mul_one, TopCat.Presheaf.germ_res_apply]
    exact e.symm
  have hlin := linearlyEquivalent_of_two_local_ratios (branchSumIdeal f * infinityIdeal f h0) _
    hI hJ (chartAffineOpen f) W₂ hcov hτ₁ hτ₂ hσ₁ hσ₂
    (finiteYCoord_mem_nonZeroDivisors hf hdeg)
    (res_mem_nonZeroDivisors hW₂U (infiniteWCoord_res_mem_nonZeroDivisors h0 hf hdeg))
    (Submonoid.one_mem _)
    (pow_mem (res_mem_nonZeroDivisors hW₂U
      (res_mem_nonZeroDivisors hUinf' (infiniteCoord_X_mem_nonZeroDivisors hf hdeg))) _) h12
  have key := (linearlyEquivalent_iff_picardClass_eq' _ _).mp hlin
  have : ∀ _i ∈ Finset.range (genus f + 1), Stacks.Divisors.IsEffectiveCartierDivisor
      (infinityIdeal f h0 * infinityIdeal f h0) := fun _ _ => inferInstance
  rw [Stacks.Divisors.picardClass_mul, picardClass_branchSumIdeal hf,
    picardClass_prod (Finset.range (genus f + 1))
      (fun _ => infinityIdeal f h0 * infinityIdeal f h0),
    Finset.sum_const, Finset.card_range, Stacks.Divisors.picardClass_mul] at key
  unfold infinityClass
  rw [key, ← two_nsmul, smul_smul]
  congr 1
  ring

/-- **In odd degree, `branchTorsionHomInf` kills the all-ones vector** (the relation coming from
`div(y)`). -/
theorem branchTorsionHomInf_one (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree)
    (hsplit : f.roots.card = f.natDegree) (hodd : Odd f.natDegree) :
    branchTorsionHomInf h0 h2 hf hdeg 1 = 0 := by
  have hN : f.natDegree = 2 * genus f + 1 := by
    obtain ⟨m, hm⟩ := hodd
    unfold genus
    omega
  have key := sum_branchClass_add_infinity_eq h0 h2 hf hdeg hsplit
  rw [branchTorsionHomInf, torsionHomOfSq_one]
  refine sum_sub_eq_zero_of_sum_eq_card_nsmul (fun c => branchClass hf c)
    (infinityClass h0 hf hdeg) ?_
  rw [card_branchRoot hf hsplit, hN]
  rw [show 2 * genus f + 2 = (2 * genus f + 1) + 1 from rfl, succ_nsmul] at key
  exact add_right_cancel key

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
