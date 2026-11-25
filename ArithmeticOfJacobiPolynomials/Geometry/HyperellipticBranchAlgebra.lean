/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchCharts

/-!
# Algebra for the independence of the branch-point classes

The algebraic inputs of
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchIndependence`, for a field `k` and `f ∈
k[x]`:

* the hyperelliptic involution `hypConj` of `k[x, y]/(y^2 - p)` and
  `exists_sq_mul_eq_of_sq_mul_eq`: if `α^2 P = β^2 Q` in `k[x, y]/(y^2 - p)` with `β ≠ 0`,
  `P ≠ 0`, then `g^2 P = N^2 Q` or `g^2 p P = N^2 Q` for polynomials `g, N`, `N ≠ 0`;
* `count_roots_mod_two_eq` and the multiplicities of the roots of `∏_{c ∈ S} (x - c)`;
* the finite chart is non-empty, the coordinates `finiteCoord f p` are non-zero rational
  functions for `p ≠ 0`, and a constant `l ∈ k` is the germ of `finiteCoord f (C l)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open _root_.Polynomial

/-! ### The hyperelliptic involution and the coefficients of `1, y` -/

section Conj

variable {k : Type u} [Field k] (p : k[X])

local notation "ι" => AdjoinRoot.of (polyX ^ 2 - C p : k[X][X])

local notation "𝐲" => AdjoinRoot.root (polyX ^ 2 - C p : k[X][X])

/-- The hyperelliptic involution `y ↦ -y` of `k[x, y]/(y^2 - p(x))`. -/
@[expose] noncomputable def hypConj : HyperellipticCoordRing p →+* HyperellipticCoordRing p :=
  AdjoinRoot.lift (AdjoinRoot.of (polyX ^ 2 - C p : k[X][X]))
    (-AdjoinRoot.root (polyX ^ 2 - C p : k[X][X])) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq, root_sq_eq_of, sub_self])

theorem hypConj_of (a : k[X]) : hypConj p (ι a) = ι a := by
  rw [hypConj, AdjoinRoot.lift_of]

theorem hypConj_root : hypConj p 𝐲 = -𝐲 := by
  rw [hypConj, AdjoinRoot.lift_root]

theorem hypConj_add_mul_root (a b : k[X]) : hypConj p (ι a + ι b * 𝐲) = ι a - ι b * 𝐲 := by
  rw [map_add, map_mul, hypConj_of, hypConj_of, hypConj_root]
  ring

/-- The involution is an involution. -/
theorem hypConj_hypConj (z : HyperellipticCoordRing p) : hypConj p (hypConj p z) = z := by
  rw [eq_quadCoord p z, hypConj_add_mul_root, map_sub, map_mul, hypConj_of, hypConj_of,
    hypConj_root]
  ring

/-- The norm `(a + b y)(a - b y) = a^2 - b^2 p`. -/
theorem mul_hypConj_add_mul_root (a b : k[X]) :
    (ι a + ι b * 𝐲) * hypConj p (ι a + ι b * 𝐲) = ι (a ^ 2 - b ^ 2 * p) := by
  rw [hypConj_add_mul_root, map_sub, map_pow, map_mul, map_pow]
  linear_combination (-(ι b ^ 2)) * root_sq_eq_of p

/-- **Squares in `k[x, y]/(y^2 - p)` up to `k[x]`**: if `α^2 P = β^2 Q` with `β ≠ 0`, `P ≠ 0`, then
`g^2 P = N^2 Q` or `g^2 p P = N^2 Q` for some `g, N ∈ k[x]`, `N ≠ 0` (`N` is the norm of `β`,
and `g` is the coefficient of `1` or of `y` in `α β(x, -y)`). -/
theorem exists_sq_mul_eq_of_sq_mul_eq (h2 : (2 : k) ≠ 0) (hp : p.Separable)
    (hdeg : 0 < p.natDegree) {α β : HyperellipticCoordRing p} (hβ : β ≠ 0) {P Q : k[X]}
    (hP : P ≠ 0) (h : α ^ 2 * ι P = β ^ 2 * ι Q) :
    ∃ g N : k[X], N ≠ 0 ∧ (g ^ 2 * P = N ^ 2 * Q ∨ g ^ 2 * (p * P) = N ^ 2 * Q) := by
  have := isDomain_hyperellipticCoordRing hp hdeg
  obtain ⟨b₀, b₁, hβeq⟩ : ∃ b₀ b₁ : k[X], β = ι b₀ + ι b₁ * 𝐲 := ⟨_, _, eq_quadCoord p β⟩
  have hN : β * hypConj p β = ι (b₀ ^ 2 - b₁ ^ 2 * p) := by
    rw [hβeq]
    exact mul_hypConj_add_mul_root p b₀ b₁
  have hσβ : hypConj p β ≠ 0 := by
    intro h0
    apply hβ
    rw [← hypConj_hypConj p β, h0, map_zero]
  have hNne : b₀ ^ 2 - b₁ ^ 2 * p ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    exact mul_ne_zero hβ hσβ hN
  obtain ⟨g₀, g₁, hγ⟩ : ∃ g₀ g₁ : k[X], α * hypConj p β = ι g₀ + ι g₁ * 𝐲 :=
    ⟨_, _, eq_quadCoord p (α * hypConj p β)⟩
  have e1 : (α * hypConj p β) ^ 2 * ι P = ι ((b₀ ^ 2 - b₁ ^ 2 * p) ^ 2 * Q) := by
    rw [map_mul, map_pow, ← hN]
    linear_combination (hypConj p β) ^ 2 * h
  have key : ι ((g₀ ^ 2 + g₁ ^ 2 * p) * P) + ι (2 * g₀ * g₁ * P) * 𝐲 =
      ι ((b₀ ^ 2 - b₁ ^ 2 * p) ^ 2 * Q) + ι 0 * 𝐲 := by
    rw [map_zero, zero_mul, add_zero, ← e1, hγ]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination (-(ι g₁ ^ 2 * ι P)) * root_sq_eq_of p
  have h1 := congrArg (quadCoord p 1) key
  rw [quadCoord_one, quadCoord_one] at h1
  have h0 := congrArg (quadCoord p 0) key
  rw [quadCoord_zero, quadCoord_zero] at h0
  have h2' : (2 : k[X]) ≠ 0 := by
    have h2C : (C 2 : k[X]) ≠ 0 := C_ne_zero.mpr h2
    rwa [map_ofNat] at h2C
  rcases mul_eq_zero.mp h1 with h1 | hP0
  · rcases mul_eq_zero.mp h1 with h1 | hg₁
    · rcases mul_eq_zero.mp h1 with h22 | hg₀
      · exact absurd h22 h2'
      · subst hg₀
        exact ⟨g₁, _, hNne, Or.inr (by linear_combination h0)⟩
    · subst hg₁
      exact ⟨g₀, _, hNne, Or.inl (by linear_combination h0)⟩
  · exact absurd hP0 hP

end Conj

/-! ### Multiplicities of roots -/

section Roots

variable {k : Type u} [Field k]

open Classical in
/-- If `g^2 P = N^2 Q` with `N, Q ≠ 0`, then `P` and `Q` have multiplicities of the same parity at
every point. -/
theorem count_roots_mod_two_eq {g N P Q : k[X]} (hN : N ≠ 0) (hQ : Q ≠ 0)
    (h : g ^ 2 * P = N ^ 2 * Q) (r : k) : P.roots.count r % 2 = Q.roots.count r % 2 := by
  have hR : N ^ 2 * Q ≠ 0 := mul_ne_zero (pow_ne_zero 2 hN) hQ
  have hL : g ^ 2 * P ≠ 0 := by
    rw [h]
    exact hR
  have e : (g ^ 2 * P).roots.count r = (N ^ 2 * Q).roots.count r := by rw [h]
  rw [roots_mul hL, roots_mul hR, roots_pow, roots_pow, Multiset.count_add,
    Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul] at e
  omega

variable {f : k[X]}

theorem prod_X_sub_C_branch_eq (S : Finset (BranchRoot f)) :
    ∏ c ∈ S, (polyX - C c.1) = ((S.val.map Subtype.val).map (fun a => polyX - C a)).prod := by
  rw [Multiset.map_map]
  rfl

open Classical in
theorem count_roots_prod_branch (S : Finset (BranchRoot f)) (c : BranchRoot f) :
    (∏ c' ∈ S, (polyX - C c'.1)).roots.count c.1 = if c ∈ S then 1 else 0 := by
  rw [prod_X_sub_C_branch_eq, roots_multiset_prod_X_sub_C,
    Multiset.count_map_eq_count' _ _ Subtype.val_injective]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem S.nodup h
  · exact Multiset.count_eq_zero.mpr h

theorem prod_X_sub_C_branch_ne_zero (S : Finset (BranchRoot f)) :
    ∏ c ∈ S, (polyX - C c.1) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun c _ => X_sub_C_ne_zero c.1

open Classical in
theorem count_roots_branch_eq_one (hf : f.Separable) (c : BranchRoot f) :
    f.roots.count c.1 = 1 :=
  Multiset.count_eq_one_of_mem (nodup_roots hf)
    ((mem_roots hf.ne_zero).mpr (BranchRoot.eval_eq_zero c))

end Roots

/-! ### Rational functions on the finite chart -/

section Chart

variable {k : Type u} [Field k] {f : k[X]}

/-- The finite chart is non-empty. -/
instance nonempty_chartOpen (f : k[X]) : Nonempty (chartOpen f) := by
  have : Nontrivial (HyperellipticCoordRing f) :=
    (injective_algebraMap_hyperellipticCoordRing f).nontrivial
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum (HyperellipticCoordRing f)) := inferInstance
  exact ⟨⟨affineChart f (q : Spec (CommRingCat.of (HyperellipticCoordRing f))),
    Scheme.Hom.mem_opensRange.mpr ⟨q, rfl⟩⟩⟩

theorem finiteCoord_one : finiteCoord f 1 = 1 := by
  rw [finiteCoord, map_one, map_one]

theorem finiteCoord_zero : finiteCoord f 0 = 0 := by
  rw [finiteCoord, map_zero, map_zero]

theorem finiteCoord_ne_zero {p : k[X]} (hp : p ≠ 0) : finiteCoord f p ≠ 0 := by
  intro h
  have e := congrArg (sectionsEquivFinite f) h
  rw [sectionsEquivFinite_finiteCoord, map_zero, ← AdjoinRoot.algebraMap_eq] at e
  exact hp (injective_algebraMap_hyperellipticCoordRing f (e.trans (map_zero _).symm))

variable [IsIntegral (projectiveModel f)]

theorem germ_finiteCoord_ne_zero {p : k[X]} (hp : p ≠ 0) :
    (projectiveModel f).germToFunctionField (chartOpen f) (finiteCoord f p) ≠ 0 := fun h =>
  finiteCoord_ne_zero hp ((projectiveModel f).germToFunctionField_injective _
    (h.trans (map_zero _).symm))

/-- The constant `l ∈ k` as a rational function (the germ at the generic point of the global
section `l`) is the germ of `l` on the finite chart. -/
theorem germ_top_globalStructureMap (l : k) :
    (projectiveModel f).presheaf.germ ⊤ (genericPoint (projectiveModel f)) trivial
        (globalStructureMap f l) =
      (projectiveModel f).germToFunctionField (chartOpen f) (finiteCoord f (C l)) := by
  have : Nonempty (⊤ : (projectiveModel f).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have e : (projectiveModel f).presheaf.map (homOfLE (le_top : chartOpen f ≤ ⊤)).op
      (globalStructureMap f l) = algebraMap k Γ(projectiveModel f, chartOpen f) l := by
    rw [algebraMap_sections]
    rfl
  have hres : (projectiveModel f).presheaf.map (homOfLE (le_top : chartOpen f ≤ ⊤)).op
      (globalStructureMap f l) = finiteCoord f (C l) := by
    apply (sectionsEquivFinite f).injective
    rw [e, sectionsEquivFinite_algebraMap, algebraMap_hyperellipticCoordRing,
      sectionsEquivFinite_finiteCoord]
  rw [← hres]
  simp only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply]

end Chart

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
