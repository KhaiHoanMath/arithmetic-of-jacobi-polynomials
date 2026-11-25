/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCurve
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticOverlap
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGlobalSections
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The affine charts of the hyperelliptic model are Dedekind domains

Let `k` be a field with `2 ≠ 0` and `f ∈ k[x]` separable of degree `≥ 1`. Let
`B = k[x, y]/(y^2 - p(x))` with `p` squarefree of positive degree. Every element of `B` is
`a(x) + c(x) y` (`exists_eq_add_mul_root`). Let `P ≠ 0` be a prime of `B` and `(π) = P ∩ k[x]`
(non-zero, as `B` is integral over `k[x]`). We exhibit `t ∈ P` with `P B_P = t B_P`
(`exists_generator_of_isPrime`):

* if `p ∈ P`, then `y ∈ P`, `p = π g` with `g ∉ P` (squarefreeness), and `t = y`: for
  `b = a + c y ∈ P` one has `a ∈ (π)`, `a = π a₁`, and `g b = y (y a₁ + g c)`;
* if `p ∉ P`, then `y ∉ P` and `t = π`: for `b = a + c y ∈ P`, either `b' = a - c y ∉ P` and
  `b' b = a^2 - c^2 p ∈ (π)`, or `b' ∈ P`, whence `2a, 2cy ∈ P`, so `a, c ∈ (π)` and
  `b ∈ π B`.

Hence the maximal ideal of `B_P` is principal and `B_P` is a discrete valuation ring
(`IsDiscreteValuationRing.TFAE`), so `B` is a Dedekind domain
(`isDedekindDomain_hyperellipticCoordRing`). The stalks of `X = projectiveModel f` at points of
codimension one are localizations of the chart rings at non-zero primes
(`isDiscreteValuationRing_stalk_of_isOpenImmersion`), so they are discrete valuation rings
(`isDiscreteValuationRing_stalk_projectiveModel`). The model is quasi-compact and locally
Noetherian.

This file is used by `HyperellipticDivisors`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open _root_.Polynomial AlgebraicGeometry CategoryTheory

universe u

/-! ### A local criterion for discrete valuation rings -/

/-- Let `R` be a Noetherian domain and `P ≠ 0` a prime. If some `t ∈ P` generates `P` up to
elements outside `P` (every `b ∈ P` satisfies `s b ∈ (t)` for some `s ∉ P`), then `R_P` is a
discrete valuation ring. -/
theorem isDiscreteValuationRing_localization_of_generator {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {t : R} (ht : t ∈ P)
    (H : ∀ b ∈ P, ∃ s ∉ P, ∃ h, s * b = t * h) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have hnf : ¬IsField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.not_isField (A := R) hP (Localization.AtPrime P)
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap R (Localization.AtPrime P) t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) ?_
    · obtain ⟨s, hs, h, hsb⟩ := H b hb
      have hu : IsUnit (algebraMap R (Localization.AtPrime P) s) :=
        IsLocalization.map_units _ (⟨s, hs⟩ : P.primeCompl)
      rw [Ideal.mem_comap]
      refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
      rw [← map_mul, hsb, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ ht
  have hprin : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr hprin

/-! ### The affine curve `y^2 = p(x)` -/

variable {k : Type u} [Field k] {p : k[X]}

local notation "ι" => algebraMap k[X] (HyperellipticCoordRing p)

local notation "𝐲" => AdjoinRoot.root (polyX ^ 2 - C p : k[X][X])

/-- Every element of `k[x, y]/(y^2 - p(x))` is `a(x) + c(x) y`. -/
theorem exists_eq_add_mul_root (b : HyperellipticCoordRing p) :
    ∃ a c : k[X], b = ι a + ι c * 𝐲 := by
  have hb : b ∈ Algebra.adjoin k[X] {AdjoinRoot.root (polyX ^ 2 - C p : k[X][X])} := by
    rw [AdjoinRoot.adjoinRoot_eq_top]
    trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨0, 1, by rw [map_zero, map_one, zero_add, one_mul]⟩
  | algebraMap r => exact ⟨r, 0, by rw [map_zero, zero_mul, add_zero]⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, c, rfl⟩ := hx
    obtain ⟨a', c', rfl⟩ := hz
    exact ⟨a + a', c + c', by rw [map_add, map_add]; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨a, c, rfl⟩ := hx
    obtain ⟨a', c', rfl⟩ := hz
    refine ⟨a * a' + c * c' * p, a * c' + a' * c, ?_⟩
    simp only [map_add, map_mul]
    linear_combination (ι c * ι c') * root_sq_eq_algebraMap p

theorem isUnit_two_hyperellipticCoordRing (h2 : (2 : k) ≠ 0) :
    IsUnit (2 : HyperellipticCoordRing p) := by
  have := (isUnit_iff_ne_zero.mpr h2).map (algebraMap k (HyperellipticCoordRing p))
  rwa [map_ofNat] at this

/-- **Local generators.** For `p` squarefree and `2 ≠ 0`, every
prime `P` of `k[x, y]/(y^2 - p(x))` contains some `t` such that every `b ∈ P` satisfies
`s b ∈ (t)` for some `s ∉ P`: `t = y` if `p ∈ P` and `t = π` if `p ∉ P`, where
`(π) = P ∩ k[x]`. -/
theorem exists_generator_of_isPrime (h2 : (2 : k) ≠ 0) (hp : Squarefree p)
    (P : Ideal (HyperellipticCoordRing p)) [hPp : P.IsPrime] :
    ∃ t ∈ P, ∀ b ∈ P, ∃ s ∉ P, ∃ h, s * b = t * h := by
  let π : k[X] := Submodule.IsPrincipal.generator (P.comap ι)
  have hπ : ∀ a : k[X], ι a ∈ P ↔ π ∣ a := fun a =>
    Ideal.mem_comap.symm.trans (Submodule.IsPrincipal.mem_iff_generator_dvd (P.comap ι))
  have hπu : ¬IsUnit π := by
    intro hu
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, ← map_one ι]
    exact (hπ 1).mpr (hu.dvd)
  by_cases hpP : ι p ∈ P
  · -- `p ∈ P`: the generator is `y`
    have hyP : 𝐲 ∈ P := hPp.mem_of_pow_mem 2 (by rw [root_sq_eq_algebraMap]; exact hpP)
    obtain ⟨g, hg⟩ := (hπ p).mp hpP
    have hgι : ι p = ι π * ι g := (congrArg _ hg).trans (map_mul _ _ _)
    have hgP : ι g ∉ P := by
      intro hgP
      obtain ⟨g₁, hg₁⟩ := (hπ g).mp hgP
      exact hπu (hp π ⟨g₁, hg.trans (by rw [hg₁]; ring)⟩)
    refine ⟨𝐲, hyP, fun b hb => ?_⟩
    obtain ⟨a, c, rfl⟩ := exists_eq_add_mul_root b
    have haP : ι a ∈ P := by
      have h := P.sub_mem hb (P.mul_mem_left (ι c) hyP)
      rwa [add_sub_cancel_right] at h
    obtain ⟨a₁, ha₁⟩ := (hπ a).mp haP
    have haι : ι a = ι π * ι a₁ := (congrArg _ ha₁).trans (map_mul _ _ _)
    refine ⟨ι g, hgP, 𝐲 * ι a₁ + ι g * ι c, ?_⟩
    linear_combination (ι g) * haι - (ι a₁) * hgι - (ι a₁) * root_sq_eq_algebraMap p
  · -- `p ∉ P`: the generator is `π`
    have hyP : 𝐲 ∉ P := by
      intro hy
      have h := P.pow_mem_of_mem hy 2 two_pos
      rw [root_sq_eq_algebraMap] at h
      exact hpP h
    have h2P : (2 : HyperellipticCoordRing p) ∉ P := fun h =>
      hPp.ne_top (Ideal.eq_top_of_isUnit_mem P h (isUnit_two_hyperellipticCoordRing h2))
    refine ⟨ι π, (hπ π).mpr dvd_rfl, fun b hb => ?_⟩
    obtain ⟨a, c, rfl⟩ := exists_eq_add_mul_root b
    by_cases hb' : ι a - ι c * 𝐲 ∈ P
    · have hsum : 2 * ι a ∈ P := by
        have e : 2 * ι a = (ι a + ι c * 𝐲) + (ι a - ι c * 𝐲) := by ring
        rw [e]
        exact P.add_mem hb hb'
      have hdiff : 2 * ι c * 𝐲 ∈ P := by
        have e : 2 * ι c * 𝐲 = (ι a + ι c * 𝐲) - (ι a - ι c * 𝐲) := by ring
        rw [e]
        exact P.sub_mem hb hb'
      have haP : ι a ∈ P := (hPp.mem_or_mem hsum).resolve_left h2P
      have hcP : ι c ∈ P :=
        (hPp.mem_or_mem ((hPp.mem_or_mem hdiff).resolve_right hyP)).resolve_left h2P
      obtain ⟨a₁, ha₁⟩ := (hπ a).mp haP
      obtain ⟨c₁, hc₁⟩ := (hπ c).mp hcP
      have haι : ι a = ι π * ι a₁ := (congrArg _ ha₁).trans (map_mul _ _ _)
      have hcι : ι c = ι π * ι c₁ := (congrArg _ hc₁).trans (map_mul _ _ _)
      refine ⟨1, fun h => hPp.ne_top ((Ideal.eq_top_iff_one P).mpr h), ι a₁ + ι c₁ * 𝐲, ?_⟩
      rw [haι, hcι]
      ring
    · have hprod : ι (a ^ 2 - c ^ 2 * p) ∈ P := by
        have e : ι (a ^ 2 - c ^ 2 * p) = (ι a - ι c * 𝐲) * (ι a + ι c * 𝐲) := by
          simp only [map_sub, map_mul, map_pow]
          linear_combination (ι c) ^ 2 * root_sq_eq_algebraMap p
        rw [e]
        exact P.mul_mem_left _ hb
      obtain ⟨h, hh⟩ := (hπ _).mp hprod
      have hhι : ι (a ^ 2 - c ^ 2 * p) = ι π * ι h := (congrArg _ hh).trans (map_mul _ _ _)
      refine ⟨ι a - ι c * 𝐲, hb', ι h, ?_⟩
      rw [← hhι]
      simp only [map_sub, map_mul, map_pow]
      linear_combination (-(ι c) ^ 2) * root_sq_eq_algebraMap p

theorem isNoetherianRing_hyperellipticCoordRing (p : k[X]) :
    IsNoetherianRing (HyperellipticCoordRing p) :=
  inferInstanceAs (IsNoetherianRing (k[X][X] ⧸ Ideal.span {(polyX ^ 2 - C p : k[X][X])}))

/-- **The affine curve `y^2 = p(x)` is a Dedekind domain** for `p` separable of positive degree
over a field with `2 ≠ 0`. -/
theorem isDedekindDomain_hyperellipticCoordRing (h2 : (2 : k) ≠ 0) (hp : p.Separable)
    (hdeg : 0 < p.natDegree) : IsDedekindDomain (HyperellipticCoordRing p) := by
  have := isDomain_hyperellipticCoordRing hp hdeg
  have := isNoetherianRing_hyperellipticCoordRing p
  refine isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr ⟨this, fun P hP _ => ?_⟩
  obtain ⟨t, ht, H⟩ := exists_generator_of_isPrime h2 hp.squarefree P
  exact isDiscreteValuationRing_localization_of_generator P hP ht H

/-! ### Stalks of the projective model -/

/-- If `g : Spec R ⟶ X` is an open immersion into an integral scheme, with `R` a Dedekind domain,
then the stalk of `X` at the image of a point of codimension one is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_isOpenImmersion {Y : Scheme.{u}} [IsIntegral Y]
    {R : CommRingCat.{u}} [IsDedekindDomain R] (g : Spec R ⟶ Y) [IsOpenImmersion g]
    (y : Spec R) (hy : Order.coheight (g y) = 1) :
    IsDiscreteValuationRing (Y.presheaf.stalk (g y)) := by
  have : y.asIdeal.IsPrime := y.isPrime
  let _ : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra (↑R) y
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hc : Order.coheight y = 1 := by
    rw [← coheight_eq_of_isOpenImmersion g]
    exact hy
  have hht : y.asIdeal.height = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight y
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal, hc] at h1
    exact_mod_cast h1
  have hne : y.asIdeal ≠ ⊥ := by
    intro h
    rw [← Ideal.height_eq_zero_iff_eq_bot, hht] at h
    exact one_ne_zero h
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hne
    ((Spec R).presheaf.stalk y)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv.symm

instance isLocallyNoetherian_projectiveModel (f : k[X]) :
    IsLocallyNoetherian (projectiveModel f) := by
  have := isProper_toSpecField f
  exact LocallyOfFiniteType.isLocallyNoetherian (toSpecField f)

instance compactSpace_projectiveModel (f : k[X]) : CompactSpace (projectiveModel f) := by
  have := isProper_toSpecField f
  exact QuasiCompact.compactSpace_of_compactSpace (toSpecField f)

variable {f : k[X]}

/-- **The local rings of the hyperelliptic model at points of codimension one are discrete
valuation rings** (for `f` separable of degree `≥ 1` and `2 ≠ 0` in `k`). -/
theorem isDiscreteValuationRing_stalk_projectiveModel (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (z : projectiveModel f) (hz : Order.coheight z = 1) :
    haveI := isIntegral_projectiveModel hf hdeg
    IsDiscreteValuationRing ((projectiveModel f).presheaf.stalk z) := by
  have := isIntegral_projectiveModel hf hdeg
  rcases mem_chart_or_mem_chart z with hz1 | hz0
  · have : IsDedekindDomain (CommRingCat.of (HyperellipticCoordRing f)) :=
      isDedekindDomain_hyperellipticCoordRing h2 hf hdeg
    have hmem : z ∈ (affineChart f).opensRange := by
      rw [opensRange_affineChart f]
      exact hz1
    obtain ⟨y, rfl⟩ : z ∈ Set.range (affineChart f) := hmem
    exact isDiscreteValuationRing_stalk_of_isOpenImmersion (affineChart f) y hz
  · have : IsDedekindDomain
        (CommRingCat.of (HyperellipticCoordRing (reflect (2 * genus f + 2) f))) :=
      isDedekindDomain_hyperellipticCoordRing h2 (separable_reflect_genus hf hdeg)
        (natDegree_reflect_genus_pos hf)
    have hmem : z ∈ (affineChartAtInfinity f).opensRange := by
      rw [opensRange_affineChartAtInfinity f]
      exact hz0
    obtain ⟨y, rfl⟩ : z ∈ Set.range (affineChartAtInfinity f) := hmem
    exact isDiscreteValuationRing_stalk_of_isOpenImmersion (affineChartAtInfinity f) y hz

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
