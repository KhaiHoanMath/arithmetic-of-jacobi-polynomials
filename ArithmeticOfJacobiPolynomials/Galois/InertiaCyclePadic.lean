/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import ArithmeticOfJacobiPolynomials.Galois.InertiaCycle
public import ArithmeticOfJacobiPolynomials.Padic.LocalRootResidues
public import Mathlib

/-!
# The local inertia cycle over `ℚ_p` (Lemma 5.1)

Let `f = Σ aⱼ Xʲ ∈ ℤ_[p][X]` have degree `N`, with `a₀` a unit, `v_p(a_N) = 1`, and reduction
`f̄` squarefree of degree `N - d`, `1 ≤ d < p` (`LocalRootResidues.LocalHyp p d f`).

## Setting

`K` is a finite Galois extension of `ℚ_[p]` (for the final statements, the splitting field of
`f` over `ℚ_[p]`), `𝒪 = integralClosure ℤ_[p] K` its ring of integers (a Dedekind domain), and
`P` a height one prime of `𝒪` lying over the maximal ideal of `ℤ_[p]` (one exists:
`exists_heightOneSpectrum_liesOver`). The valuation is the `P`-adic valuation `v = P.valuation K`
of `K`, which restricts to a power of the `p`-adic valuation on `ℤ_[p]` (`isPadicAt`). The
inertia group is Mathlib's `P.inertia Gal(K/ℚ_[p])`, i.e. the kernel of the action on `𝒪 / P`;
`mem_inertia_iff` shows that it is exactly the group of automorphisms `σ` with
`v (σ x - x) < 1` for all `x` with `v x ≤ 1` (trivial action on the residue field of `v`).

## Results

The results below describe the local setting and the unramified roots.
`SourceInertia.exists_mem_inertia_generator` gives the inertia cycle.

* `galPerm_apply_eq_of_mem_inertia` (the other roots are unramified, any `1 ≤ d`): every element
  of the inertia group fixes every root `y` with `v y ≤ 1`; these are the roots outside the
  `d`-cycle. (We prove "fixed by every inertia element", the form used by the manuscript.)
  `card_filter_rootSet_valuation_le_one`: there are exactly `N - d` such roots.
* `existsUnique_root_one_lt_of_one` and `galPerm_eq_one_of_mem_inertia_of_one` (the case
  `d = 1`): there is exactly one root with `1 < v y`, and inertia acts trivially on all roots.

`SourceInertiaCycle` uses `apply_eq_of_mem_inertia` to show that inertia fixes each root
with `v y ≤ 1`.

`SourceInertiaCycle` follows the manuscript using a Hensel factor, Eisenstein irreducibility over
the inertia field, and the wild and tame inertia descriptions of Stacks Tag 09EE. The negation and
centralizer argument for `f(cX²)` is in `InertiaCycle` and `SourceInertiaCycleGlobal`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace InertiaCyclePadic

open Polynomial IsDedekindDomain LocalRootResidues

section Setup

variable (p : ℕ) [hp : Fact p.Prime]

/-- The maximal ideal of `ℤ_[p]` as a point of `HeightOneSpectrum ℤ_[p]`. -/
@[expose] noncomputable def padicSpectrum : HeightOneSpectrum ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p], inferInstance, by
    rw [PadicInt.maximalIdeal_eq_span_p, Ne, Ideal.span_singleton_eq_bot]
    exact PadicInt.prime_p.ne_zero⟩

theorem padicSpectrum_asIdeal :
    (padicSpectrum p).asIdeal = IsLocalRing.maximalIdeal ℤ_[p] := rfl

theorem charZero_of_padic (K : Type*) [Field K] [Algebra ℚ_[p] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

omit [FiniteDimensional ℚ_[p] K] in
theorem algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K]
  exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

omit [FiniteDimensional ℚ_[p] K] in
instance isTorsionFree_integralClosure :
    Module.IsTorsionFree ℤ_[p] (integralClosure ℤ_[p] K) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro a b h
  exact algebraMap_padicInt_injective p K (congrArg Subtype.val h)

instance isFractionRing_integralClosure : IsFractionRing (integralClosure ℤ_[p] K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

instance isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure ℤ_[p] K) :=
  integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K

instance finite_integralClosure : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _

instance flat_integralClosure : Module.Flat ℤ_[p] (integralClosure ℤ_[p] K) :=
  Module.Flat.instOfIsDedekindDomainOfIsTorsionFree

instance isGaloisGroup_integralClosure [IsGalois ℚ_[p] K] :
    IsGaloisGroup Gal(K/ℚ_[p]) ℤ_[p] (integralClosure ℤ_[p] K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ ℚ_[p] K

omit [FiniteDimensional ℚ_[p] K] in
/-- The ring of integers of `K` has a height one prime lying over `p`. -/
theorem exists_heightOneSpectrum_liesOver :
    ∃ P : HeightOneSpectrum (integralClosure ℤ_[p] K),
      P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := by
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure ℤ_[p] K) (IsLocalRing.maximalIdeal ℤ_[p])
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have h := hQover.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective ℤ_[p] (integralClosure ℤ_[p] K))] at h
    exact (padicSpectrum p).ne_bot h
  exact ⟨⟨Q, hQmax.isPrime, hQ0⟩, hQover⟩

end Setup

section Valuation

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))

theorem exists_eq_mul_inv_of_valuation_le_one {x : K} (hx : P.valuation K x ≤ 1) :
    ∃ a s : integralClosure ℤ_[p] K, s ∉ P.asIdeal ∧ x = (a : K) * (s : K)⁻¹ := by
  have hx' : x ∈ HeightOneSpectrum.valuationSubringAtPrime K P := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hx
  unfold HeightOneSpectrum.valuationSubringAtPrime at hx'
  rw [ValuationSubring.mem_ofSubring] at hx'
  simp only [Localization.subalgebra.ofField, Ideal.mem_primeCompl_iff, exists_prop,
    Subring.mem_mk, Subalgebra.copy_toSubsemiring] at hx'
  exact hx'

theorem valuation_coe_eq_one {s : integralClosure ℤ_[p] K} (hs : s ∉ P.asIdeal) :
    P.valuation K (s : K) = 1 := by
  change P.valuation K (algebraMap (integralClosure ℤ_[p] K) K s) = 1
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (P.intValuation_le_one s)
    (not_lt.mp fun h => hs ((P.intValuation_lt_one_iff_mem s).mp h))

theorem valuation_coe_lt_one {s : integralClosure ℤ_[p] K} (hs : s ∈ P.asIdeal) :
    P.valuation K (s : K) < 1 := by
  change P.valuation K (algebraMap (integralClosure ℤ_[p] K) K s) < 1
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_lt_one_iff_mem s).mpr hs

theorem valuation_coe_le_one (s : integralClosure ℤ_[p] K) : P.valuation K (s : K) ≤ 1 := by
  change P.valuation K (algebraMap (integralClosure ℤ_[p] K) K s) ≤ 1
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact P.intValuation_le_one s

/-- Inertia acts trivially modulo `P` on `P`-integral elements of `K`. -/
theorem valuation_sub_lt_one_of_mem_inertia {σ : Gal(K/ℚ_[p])}
    (hσ : σ ∈ P.asIdeal.inertia Gal(K/ℚ_[p])) {x : K} (hx : P.valuation K x ≤ 1) :
    P.valuation K (σ x - x) < 1 := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_mul_inv_of_valuation_le_one P hx
  have ha : σ • a - a ∈ P.asIdeal := (Ideal.mem_inertia.mp hσ) a
  have hs' : σ • s - s ∈ P.asIdeal := (Ideal.mem_inertia.mp hσ) s
  have hσs : σ • s ∉ P.asIdeal := fun h => hs (by
    have := P.asIdeal.sub_mem h hs'
    rwa [sub_sub_cancel] at this)
  have hs0 : (s : K) ≠ 0 := by
    intro h
    exact hs (by
      rw [show s = 0 from Subtype.ext h]; exact P.asIdeal.zero_mem)
  have e1 : ((σ • a : integralClosure ℤ_[p] K) : K) = σ (a : K) := rfl
  have e2 : ((σ • s : integralClosure ℤ_[p] K) : K) = σ (s : K) := rfl
  have hσs0 : σ (s : K) ≠ 0 := by rwa [_root_.map_ne_zero]
  have key : σ ((a : K) * (s : K)⁻¹) - (a : K) * (s : K)⁻¹ =
      (((σ • a - a) * s - a * (σ • s - s) : integralClosure ℤ_[p] K) : K) *
        ((s : K) * ((σ • s : integralClosure ℤ_[p] K) : K))⁻¹ := by
    push_cast [e1, e2, AlgEquiv.smul_def]
    rw [map_mul, map_inv₀]
    field_simp
    ring
  rw [key, map_mul, map_inv₀, map_mul, valuation_coe_eq_one P hs, valuation_coe_eq_one P hσs,
    mul_one, inv_one, mul_one]
  exact valuation_coe_lt_one P
    (P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ ha) (P.asIdeal.mul_mem_left _ hs'))

/-- The inertia group is the group of automorphisms acting trivially on the residue field of
the `P`-adic valuation: `σ ∈ I_P ↔ ∀ x, v x ≤ 1 → v (σ x - x) < 1`. -/
theorem mem_inertia_iff (σ : Gal(K/ℚ_[p])) :
    σ ∈ P.asIdeal.inertia Gal(K/ℚ_[p]) ↔
      ∀ x : K, P.valuation K x ≤ 1 → P.valuation K (σ x - x) < 1 := by
  refine ⟨fun hσ x hx => valuation_sub_lt_one_of_mem_inertia P hσ hx, fun h => ?_⟩
  rw [Ideal.mem_inertia]
  intro b
  have h1 := h (b : K) (valuation_coe_le_one P b)
  have e : ((σ • b - b : integralClosure ℤ_[p] K) : K) = σ (b : K) - (b : K) := rfl
  rw [← e] at h1
  by_contra hb
  rw [valuation_coe_eq_one P hb] at h1
  exact lt_irrefl _ h1

omit [FiniteDimensional ℚ_[p] K] in
theorem galois_algebraMap_apply (σ : Gal(K/ℚ_[p])) (a : ℤ_[p]) :
    σ (algebraMap ℤ_[p] K a) = algebraMap ℤ_[p] K a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, AlgEquiv.commutes]

omit [FiniteDimensional ℚ_[p] K] in
theorem eval_map_galois_apply (σ : Gal(K/ℚ_[p])) (f : ℤ_[p][X]) (y : K) :
    (f.map (algebraMap ℤ_[p] K)).eval (σ y) = σ ((f.map (algebraMap ℤ_[p] K)).eval y) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, coeff_map, galois_algebraMap_apply]

variable [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- The `P`-adic valuation restricts to a power of the `p`-adic valuation on `ℤ_[p]`. -/
theorem isPadicAt : IsPadicAt (P.valuation K) (algebraMap ℤ_[p] K) := by
  unfold IsPadicAt
  intro a
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (integralClosure ℤ_[p] K) K,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem,
    ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    Ideal.LiesOver.over (P := P.asIdeal) (p := IsLocalRing.maximalIdeal ℤ_[p]),
    Ideal.under_def, Ideal.mem_comap]

theorem valuation_prime_eq :
    P.valuation K (p : K) = WithZero.exp (-(P.asIdeal.ramificationIdx ℤ_[p] : ℤ)) := by
  have : P.asIdeal.LiesOver (padicSpectrum p).asIdeal :=
    inferInstanceAs (P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]))
  have h := HeightOneSpectrum.intValuation_liesOver (padicSpectrum p) P (p : ℤ_[p])
  have hp1 : (padicSpectrum p).intValuation (p : ℤ_[p]) = WithZero.exp (-1) :=
    HeightOneSpectrum.intValuation_singleton _ PadicInt.prime_p.ne_zero
      PadicInt.maximalIdeal_eq_span_p
  rw [hp1, ← WithZero.exp_nsmul] at h
  have hval : P.valuation K (p : K) =
      P.intValuation (algebraMap ℤ_[p] (integralClosure ℤ_[p] K) (p : ℤ_[p])) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    simp
  rw [hval, ← h]
  congr 1
  simp

theorem card_inertia [IsGalois ℚ_[p] K] :
    Nat.card (P.asIdeal.inertia Gal(K/ℚ_[p])) = P.asIdeal.ramificationIdx ℤ_[p] := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (IsLocalRing.maximalIdeal ℤ_[p]) P.asIdeal]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal Gal(K/ℚ_[p])

/-- **The other roots are unramified.** Every element of the inertia group fixes every root `y`
of `f` with `v y ≤ 1`. -/
theorem apply_eq_of_mem_inertia {d : ℕ} {f : ℤ_[p][X]} (hf : LocalHyp p d f)
    {σ : Gal(K/ℚ_[p])} (hσ : σ ∈ P.asIdeal.inertia Gal(K/ℚ_[p])) {y : K}
    (hy : (f.map (algebraMap ℤ_[p] K)).eval y = 0) (hy1 : P.valuation K y ≤ 1) : σ y = y := by
  by_contra hne
  have hy' : (f.map (algebraMap ℤ_[p] K)).eval (σ y) = 0 := by
    rw [eval_map_galois_apply, hy, map_zero]
  exact not_valuation_sub_lt_one hf (isPadicAt P) hy hy1 hy' (Ne.symm hne)
    (valuation_sub_lt_one_of_mem_inertia P hσ hy1)

end Valuation

section SplittingField

variable {p : ℕ} [hp : Fact p.Prime]

/-- `f ∈ ℤ_[p][X]` viewed as a polynomial over `ℚ_[p]`. -/
noncomputable abbrev toPadic (f : ℤ_[p][X]) : ℚ_[p][X] := f.map (algebraMap ℤ_[p] ℚ_[p])

variable {d : ℕ} {f : ℤ_[p][X]}

theorem map_eq_map_toPadic (f : ℤ_[p][X]) :
    f.map (algebraMap ℤ_[p] (toPadic f).SplittingField) =
      (toPadic f).map (algebraMap ℚ_[p] (toPadic f).SplittingField) := by
  change _ = (f.map (algebraMap ℤ_[p] ℚ_[p])).map _
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (toPadic f).SplittingField]

theorem toPadic_ne_zero (hf : LocalHyp p d f) : toPadic f ≠ 0 := by
  intro h
  rw [toPadic, Polynomial.map_eq_zero_iff (IsFractionRing.injective ℤ_[p] ℚ_[p])] at h
  have := hf.isUnit_coeff_zero
  rw [h, coeff_zero] at this
  exact not_isUnit_zero this

theorem mem_rootSet_toPadic_iff (hf : LocalHyp p d f) (y : (toPadic f).SplittingField) :
    y ∈ (toPadic f).rootSet (toPadic f).SplittingField ↔
      (f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).eval y = 0 := by
  rw [mem_rootSet, map_eq_map_toPadic, aeval_def, eval_map]
  exact ⟨fun h => h.2, fun h => ⟨toPadic_ne_zero hf, h⟩⟩

theorem card_roots_toPadic (hf : LocalHyp p d f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    Multiset.card (f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).roots =
      f.natDegree := by
  have := charZero_of_padic p (toPadic f).SplittingField
  have := splits_iff_card_roots.mp (SplittingField.splits (toPadic f))
  rw [← map_eq_map_toPadic, natDegree_map_eq hf (isPadicAt P)] at this
  exact this

/-- **Lemma 5.1, the other roots are unramified** (any `1 ≤ d < p`). Every
element of the inertia group `I_P` fixes every root `y` of `f` with `v y ≤ 1` (by
`SourceInertia.exists_mem_inertia_generator` these are, for `d ≥ 2`, exactly the roots outside
the `d`-cycle). -/
theorem galPerm_apply_eq_of_mem_inertia (hf : LocalHyp p d f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    {τ : Gal((toPadic f).SplittingField/ℚ_[p])}
    (hτ : τ ∈ P.asIdeal.inertia Gal((toPadic f).SplittingField/ℚ_[p]))
    (x : (toPadic f).rootSet (toPadic f).SplittingField)
    (hx : P.valuation (toPadic f).SplittingField (x : (toPadic f).SplittingField) ≤ 1) :
    galPerm (toPadic f) τ x = x :=
  Subtype.ext (apply_eq_of_mem_inertia P hf hτ ((mem_rootSet_toPadic_iff hf x).mp x.2) hx)

open Classical in
/-- **Lemma 5.1, the other `N - d` roots** (any `1 ≤ d < p`): exactly
`N - d` roots of `f` (as elements of the splitting field, i.e. without multiplicity) have
`v y ≤ 1`; by `galPerm_apply_eq_of_mem_inertia` they are fixed by the inertia group. -/
theorem card_filter_rootSet_valuation_le_one (hf : LocalHyp p d f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    (Finset.univ.filter fun x : (toPadic f).rootSet (toPadic f).SplittingField =>
      P.valuation (toPadic f).SplittingField (x : (toPadic f).SplittingField) ≤ 1).card =
      f.natDegree - d := by
  classical
  have := charZero_of_padic p (toPadic f).SplittingField
  have hv := isPadicAt P
  have hroot_iff := mem_rootSet_toPadic_iff hf
  have hsplit := card_roots_toPadic hf P
  have hcard := card_filter_roots_one_lt hf hv hsplit
  have hf0 : f.map (algebraMap ℤ_[p] (toPadic f).SplittingField) ≠ 0 := by
    rw [map_eq_map_toPadic, Ne,
      Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (toPadic f).SplittingField).injective]
    exact toPadic_ne_zero hf
  have hle : Multiset.card ((f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).roots.filter
      (fun y => ¬ 1 < P.valuation (toPadic f).SplittingField y)) = f.natDegree - d := by
    have h2 := congrArg Multiset.card (Multiset.filter_add_not
      (fun y => 1 < P.valuation (toPadic f).SplittingField y)
      (f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).roots)
    rw [Multiset.card_add, hcard, hsplit] at h2
    omega
  have hnodup : ((f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).roots.filter
      (fun y => ¬ 1 < P.valuation (toPadic f).SplittingField y)).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro y
    rw [Multiset.count_filter]
    split_ifs with hy
    · exact zero_le_one
    · rw [count_roots]
      by_contra hlt
      rw [not_le, one_lt_rootMultiplicity_iff_isRoot hf0] at hlt
      have h0 : (f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).derivative.eval y = 0 :=
        hlt.2
      have h1 := valuation_derivative_eq_one hf hv hlt.1 (not_lt.mp hy)
      rw [h0, Valuation.map_zero] at h1
      exact zero_ne_one h1
  have hmap : (Finset.univ.filter fun x : (toPadic f).rootSet (toPadic f).SplittingField =>
      P.valuation (toPadic f).SplittingField (x : (toPadic f).SplittingField) ≤ 1).map
        (Function.Embedding.subtype _) =
      ((f.map (algebraMap ℤ_[p] (toPadic f).SplittingField)).roots.filter
        (fun y => ¬ 1 < P.valuation (toPadic f).SplittingField y)).toFinset := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Multiset.mem_toFinset, Multiset.mem_filter, not_lt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_roots hf0).mpr ((hroot_iff x).mp x.2), hx⟩
    · rintro ⟨hy, h1⟩
      exact ⟨⟨y, (hroot_iff y).mpr ((mem_roots hf0).mp hy)⟩, h1, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), hmap,
    Multiset.toFinset_card_of_nodup hnodup, hle]

/-- **Lemma 5.1, the case `d = 1`**: exactly one root `y` of `f` has
`1 < v y`. -/
theorem existsUnique_root_one_lt_of_one (hf : LocalHyp p 1 f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃! x : (toPadic f).rootSet (toPadic f).SplittingField,
      1 < P.valuation (toPadic f).SplittingField (x : (toPadic f).SplittingField) := by
  classical
  set K := (toPadic f).SplittingField with hK
  have := charZero_of_padic p K
  have hcard := card_filter_roots_one_lt hf (isPadicAt P) (card_roots_toPadic hf P)
  obtain ⟨y₀, hy₀⟩ := Multiset.card_eq_one.mp hcard
  have hmem : ∀ y, y ∈ (f.map (algebraMap ℤ_[p] K)).roots.filter (fun y => 1 < P.valuation K y)
      ↔ y = y₀ := by
    intro y; rw [hy₀, Multiset.mem_singleton]
  have hf0 : f.map (algebraMap ℤ_[p] K) ≠ 0 := by
    rw [map_eq_map_toPadic, Ne, Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] K).injective]
    exact toPadic_ne_zero hf
  have h₀ := (hmem y₀).mpr rfl
  rw [Multiset.mem_filter, mem_roots hf0, IsRoot.def] at h₀
  refine ⟨⟨y₀, (mem_rootSet_toPadic_iff hf y₀).mpr h₀.1⟩, h₀.2, ?_⟩
  intro x hx
  apply Subtype.ext
  refine (hmem x).mp ?_
  rw [Multiset.mem_filter, mem_roots hf0, IsRoot.def]
  exact ⟨(mem_rootSet_toPadic_iff hf x).mp x.2, hx⟩

/-- **Lemma 5.1, the case `d = 1`**: the inertia group acts trivially on
the roots of `f` (the isolated root with `1 < v y` is unique, hence fixed). -/
theorem galPerm_eq_one_of_mem_inertia_of_one (hf : LocalHyp p 1 f)
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic f).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    {τ : Gal((toPadic f).SplittingField/ℚ_[p])}
    (hτ : τ ∈ P.asIdeal.inertia Gal((toPadic f).SplittingField/ℚ_[p])) :
    galPerm (toPadic f) τ = 1 := by
  set K := (toPadic f).SplittingField with hK
  obtain ⟨x₀, hx₀, huniq⟩ := existsUnique_root_one_lt_of_one hf P
  ext x : 1
  rw [Equiv.Perm.one_apply]
  by_cases hx : P.valuation K (x : K) ≤ 1
  · exact galPerm_apply_eq_of_mem_inertia hf P hτ x hx
  rw [not_le] at hx
  -- `τ x` is again a root with `1 < v`, so it equals `x₀ = x`
  have hτx : 1 < P.valuation K (τ (x : K)) := by
    by_contra h
    rw [not_lt] at h
    have hy : (f.map (algebraMap ℤ_[p] K)).eval (τ (x : K)) = 0 := by
      rw [eval_map_galois_apply, (mem_rootSet_toPadic_iff hf x).mp x.2, map_zero]
    have hinv := apply_eq_of_mem_inertia P hf
      ((P.asIdeal.inertia Gal(K/ℚ_[p])).inv_mem hτ) hy h
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] at hinv
    rw [← hinv] at h
    exact absurd hx (not_lt.mpr h)
  rw [huniq (galPerm (toPadic f) τ x) hτx, huniq x hx]

end SplittingField

end InertiaCyclePadic

end ArithmeticOfJacobiPolynomials
