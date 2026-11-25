/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Galois.InertiaCyclePadic
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.Galois.InertiaMembership
public import ArithmeticOfJacobiPolynomials.Padic.SourceHensel
public import Mathlib

/-!
# The wild `p`-cycle from an Eisenstein factor (proof of Lemma 5.16)

The manuscript's argument: the reduction of `F` is `x^p Ḡ` with `Ḡ(0) ≠ 0`; Hensel's lemma gives a
factor `A` of `F` over `ℤ_p` of degree `p` with reduction `x^p`; it is Eisenstein, so a root `α` of
`A` generates a totally ramified extension of `ℚ_p` of degree `p`; hence `p` divides the order of
the inertia group of the splitting field; Cauchy's theorem gives an element of order `p`, a single
`p`-cycle since there are `< 2p` roots.

Here: `natDegree_dvd_ramificationIdx_of_eisenstein_root` (the tower step from the general input
`EisensteinPrimeTotallyRamified`), and the local theorem.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace SourceWild

open Polynomial renaming X → polyX

open Polynomial IsDedekindDomain InertiaCyclePadic NumberField

variable {p : ℕ} [Fact p.Prime]

/-- The tower step: if `α ∈ K` is a root of an Eisenstein polynomial `A` of degree `n` over `ℤ_[p]`,
then `n` divides the ramification index of every maximal ideal of the integral closure of `ℤ_[p]` in
`K` (from `EisensteinPrimeTotallyRamified` for `ℚ_[p](α)` and multiplicativity of ramification
indices in the tower `ℤ_[p] ⊂ 𝒪_{ℚ_[p](α)} ⊂ 𝒪_K`). -/
theorem natDegree_dvd_ramificationIdx_of_eisenstein_root (hE : EisensteinPrimeTotallyRamified)
    {A : ℤ_[p][X]} (hAm : A.Monic) (hA : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]))
    {K : Type} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] {α : K} (hα : aeval α A = 0)
    (P : Ideal (integralClosure ℤ_[p] K)) [P.IsMaximal] :
    A.natDegree ∣ P.ramificationIdx ℤ_[p] := by
  classical
  let F : IntermediateField ℚ_[p] K := IntermediateField.adjoin ℚ_[p] {α}
  have : IsScalarTower ℤ_[p] F K := IsScalarTower.of_algebraMap_eq fun x => rfl
  let β : F := IntermediateField.AdjoinSimple.gen ℚ_[p] α
  have hβ : aeval β A = 0 := by
    apply (algebraMap F K).injective
    rw [← aeval_algebraMap_apply, map_zero]
    simpa [β] using hα
  have hgen : IntermediateField.adjoin ℚ_[p] {β} = ⊤ := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  let φ : F →ₐ[ℤ_[p]] K := IsScalarTower.toAlgHom ℤ_[p] F K
  let ι : integralClosure ℤ_[p] F →ₐ[ℤ_[p]] integralClosure ℤ_[p] K := φ.mapIntegralClosure
  have hι : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    have h' := congrArg (fun z : integralClosure ℤ_[p] K => (z : K)) h
    exact (algebraMap F K).injective h'
  let _ : Algebra (integralClosure ℤ_[p] F) (integralClosure ℤ_[p] K) := ι.toRingHom.toAlgebra
  have : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] F) (integralClosure ℤ_[p] K) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Module.IsTorsionFree (integralClosure ℤ_[p] F) (integralClosure ℤ_[p] K) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hι
  have : Module.Flat (integralClosure ℤ_[p] F) (integralClosure ℤ_[p] K) := inferInstance
  have : Algebra.IsIntegral (integralClosure ℤ_[p] F) (integralClosure ℤ_[p] K) :=
    Algebra.IsIntegral.tower_top ℤ_[p]
  have hPmax : (P.under (integralClosure ℤ_[p] F)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := integralClosure ℤ_[p] F)
      (S := integralClosure ℤ_[p] K) P
  have : P.LiesOver (P.under (integralClosure ℤ_[p] F)) := ⟨rfl⟩
  have hQover : (P.under (integralClosure ℤ_[p] F)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
      (R := ℤ_[p]) (S := integralClosure ℤ_[p] K) P)).symm
  have h1 := (hE ℤ_[p] ℚ_[p] F (IsLocalRing.maximalIdeal ℤ_[p])
    (InertiaCyclePadic.padicSpectrum p).ne_bot A hAm hA β hβ hgen).2
    (P.under (integralClosure ℤ_[p] F)) hPmax.isPrime hQover
  rw [Ideal.ramificationIdx_tower (R := ℤ_[p]) (S := integralClosure ℤ_[p] F)
    (T := integralClosure ℤ_[p] K) (q := P.under (integralClosure ℤ_[p] F)) (r := P), h1]
  exact dvd_mul_right _ _

open Classical in
/-- **The wild `p`-cycle, local form** (proof of Lemma 5.16). Let `g ∈ ℤ_[p][X]` be
monic of degree `< 2p` with `p ∣ g_i` for `i < p`, `p² ∤ g_0` and `g_p` a unit. For every prime `P`
of the integers of the splitting field `K` of `g` over `ℚ_[p]` lying over `p`, some element of the
inertia group `I_P ≤ Gal(K/ℚ_[p])` acts on the roots of `g` as a single `p`-cycle. The proof is the
manuscript's: Hensel's lemma gives the Eisenstein factor `A` of degree `p`
(`exists_monic_eisenstein_factor`); a root of `A` in `K` gives `p ∣ e(P/p)` by
`EisensteinPrimeTotallyRamified`; `e(P/p) = |I_P|`; Cauchy's theorem; the number of roots is
`< 2p`. -/
theorem exists_isCycle_galPerm_mem_inertia_of_wild_local (hE : EisensteinPrimeTotallyRamified)
    {g : ℤ_[p][X]} (hg : g.Monic) (hdeg : g.natDegree < 2 * p)
    (hlow : ∀ i < p, (p : ℤ_[p]) ∣ g.coeff i) (h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ g.coeff 0)
    (hpp : IsUnit (g.coeff p))
    (P : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic g).SplittingField))
    [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ σ : (toPadic g).Gal,
      σ ∈ P.asIdeal.inertia Gal((toPadic g).SplittingField/ℚ_[p]) ∧
      (galPerm (toPadic g) σ).IsCycle ∧ (galPerm (toPadic g) σ).support.card = p := by
  have : IsGalois ℚ_[p] (toPadic g).SplittingField := IsGalois.mk
  obtain ⟨A, B, hAB, hAm, hAdeg, hAE⟩ := exists_monic_eisenstein_factor hg hlow h0 hpp
  -- a root `α` of the Eisenstein factor in the splitting field
  have hgne : g.map (algebraMap ℤ_[p] (toPadic g).SplittingField) ≠ 0 := (hg.map _).ne_zero
  have hsplit : Splits (g.map (algebraMap ℤ_[p] (toPadic g).SplittingField)) := by
    rw [map_eq_map_toPadic]; exact SplittingField.splits _
  have hAdvd : A.map (algebraMap ℤ_[p] (toPadic g).SplittingField) ∣
      g.map (algebraMap ℤ_[p] (toPadic g).SplittingField) := by
    rw [hAB, Polynomial.map_mul]; exact dvd_mul_right _ _
  have hAsplit := hsplit.of_dvd hgne hAdvd
  have hAdegK : (A.map (algebraMap ℤ_[p] (toPadic g).SplittingField)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (InertiaCyclePadic.algebraMap_padicInt_injective p _)]
    exact degree_ne_of_natDegree_ne (by rw [hAdeg]; exact (Fact.out : p.Prime).ne_zero)
  obtain ⟨α, hα⟩ := hAsplit.exists_eval_eq_zero hAdegK
  have hαA : aeval α A = 0 := by rw [aeval_def, ← eval_map]; exact hα
  -- `p ∣ e(P/p) = |I_P|`
  have hmax : P.asIdeal.IsMaximal := P.isMaximal
  have hdvd := natDegree_dvd_ramificationIdx_of_eisenstein_root hE hAm hAE hαA P.asIdeal
  rw [hAdeg, ← card_inertia P] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(P.asIdeal.inertia Gal((toPadic g).SplittingField/ℚ_[p]))) p hdvd
  have hord : orderOf (galPerm (toPadic g) (x : Gal((toPadic g).SplittingField/ℚ_[p]))) = p :=
    (orderOf_injective (galPerm (toPadic g)) (galPerm_injective (toPadic g))
      (x : Gal((toPadic g).SplittingField/ℚ_[p]))).trans ((Subgroup.orderOf_coe x).trans hx)
  -- the number of roots is `< 2p`
  have hroots : Fintype.card ((toPadic g).rootSet (toPadic g).SplittingField) ≤ g.natDegree := by
    have hfdeg : (toPadic g).natDegree = g.natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective ℤ_[p] ℚ_[p]) g
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, rootSet_def, Set.ncard_coe_finset,
      ← hfdeg]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
  have hsupp : (galPerm (toPadic g) (x : Gal((toPadic g).SplittingField/ℚ_[p]))).support.card <
      2 * orderOf (galPerm (toPadic g) (x : Gal((toPadic g).SplittingField/ℚ_[p]))) := by
    rw [hord]
    exact lt_of_le_of_lt ((Finset.card_le_univ _).trans hroots) hdeg
  have hcyc : (galPerm (toPadic g) (x : Gal((toPadic g).SplittingField/ℚ_[p]))).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by rw [hord]; exact Fact.out) hsupp
  refine ⟨(x : Gal((toPadic g).SplittingField/ℚ_[p])), x.2, hcyc, ?_⟩
  rw [← hcyc.orderOf, hord]

section Global

/-- For an integer `n`, `p² ∣ n` in `ℤ_[p]` implies `p² ∣ n` in `ℤ`. -/
theorem int_dvd_of_padic_dvd_sq {n : ℤ} (h : (p : ℤ_[p]) ^ 2 ∣ (n : ℤ_[p])) : (p : ℤ) ^ 2 ∣ n := by
  obtain ⟨w, hw⟩ := h
  have h1 := congrArg (PadicInt.toZModPow 2) hw
  rw [map_mul, map_pow, map_natCast, map_intCast] at h1
  have h2 : ((p : ZMod (p ^ 2)) ^ 2 : ZMod (p ^ 2)) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [h2, zero_mul] at h1
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd n (p ^ 2)).mp h1
  exact_mod_cast this

/-- An integer prime to `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_intCast_of_not_dvd {n : ℤ} (h : ¬ (p : ℤ) ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact h

open Classical in
omit [Fact p.Prime] in
/-- **The wild cycle, inertia form** (proof of Lemma 5.16). Let `f = c F` with `F ∈ ℤ[X]` of degree
`< 2p`, `p ∤ lc F`, `p ∣ [x^i] F` for `i < p`, `p² ∤ F(0)` and `p ∤ [x^p] F`. For every prime `P` of
`𝓞 K`, `K` the splitting field of `f`, lying over `p`, some element of the inertia group
`I_P ≤ Gal(K/ℚ)` acts on the roots of `f` as a single `p`-cycle.

The manuscript's route: Hensel's lemma gives the monic Eisenstein factor of degree `p` over `ℤ_[p]`
(`exists_monic_eisenstein_factor`); a root generates a totally ramified extension (the input
`EisensteinPrimeTotallyRamified`, Milne Prop 3.53), so `p ∣ e` and the local inertia group of the
splitting field `L` of `f` over `ℚ_[p]` contains an element of order `p`
(`exists_isCycle_galPerm_mem_inertia_of_wild_local`); a prime `Pl` of `L` over `p` gives the prime
`Pl ∩ 𝓞 L` of `𝓞 L` whose `Gal(L/ℚ)`-inertia contains the image of the local inertia element
(`Gal(L/ℚ_[p]) → Gal(L/ℚ)`), and `Polynomial.Gal.restrict` (`restrict_mem_inertia_comap`) carries it
into the inertia group of the contracted prime of `𝓞 K` (the identification "the local Galois group
is a decomposition subgroup of the global one", with local inertia mapping to global inertia). The
manuscript chooses one prime; since `Gal(K/ℚ)` is transitive on the primes over `p`
(`Ideal.exists_smul_eq_of_isGaloisGroup`) and `I_{τP} = τ I_P τ⁻¹` (`Ideal.inertia_smul`), a
conjugate of the element works for every prime `P`; a conjugate of a `p`-cycle is a `p`-cycle. -/
theorem exists_isCycle_galPerm_mem_inertia_of_wild_source (hE : EisensteinPrimeTotallyRamified)
    {p : ℕ} (hp : p.Prime) {f : ℚ[X]} {fZ : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hf : f = C c * fZ.map (Int.castRingHom ℚ)) (hdeg : fZ.natDegree < 2 * p)
    (hlc : ¬ (p : ℤ) ∣ fZ.leadingCoeff) (hlow : ∀ i < p, (p : ℤ) ∣ fZ.coeff i)
    (h0 : ¬ (p : ℤ) ^ 2 ∣ fZ.coeff 0) (hpp : ¬ (p : ℤ) ∣ fZ.coeff p)
    (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : f.Gal, σ ∈ P.inertia Gal(f.SplittingField/ℚ) ∧ (galPerm f σ).IsCycle ∧
      (galPerm f σ).support.card = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NumberField f.SplittingField := ⟨⟩
  have : IsGalois ℚ f.SplittingField := IsGalois.mk
  -- the monic normalization of `fZ` over `ℤ_[p]`
  obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd (p := p) hlc
  let g : ℤ_[p][X] := C ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * fZ.map (Int.castRingHom ℤ_[p])
  have hcoeff : ∀ i, g.coeff i = ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (fZ.coeff i : ℤ_[p]) := by
    intro i; simp [g, coeff_C_mul]
  have hdegg : g.natDegree = fZ.natDegree := by
    rw [natDegree_C_mul (Units.ne_zero _),
      natDegree_map_eq_of_injective (f := Int.castRingHom ℤ_[p]) Int.cast_injective]
  have hmonic : g.Monic := by
    rw [Monic, leadingCoeff, hdegg, hcoeff, ← leadingCoeff, ← hu]
    simp
  have hlowg : ∀ i < p, (p : ℤ_[p]) ∣ g.coeff i := fun i hi => by
    rw [hcoeff]
    have := map_dvd (Int.castRingHom ℤ_[p]) (hlow i hi)
    exact Dvd.dvd.mul_left (by simpa using this) _
  have h0g : ¬ (p : ℤ_[p]) ^ 2 ∣ g.coeff 0 := by
    intro h
    apply h0
    apply int_dvd_of_padic_dvd_sq
    have h' := Dvd.dvd.mul_left h (u : ℤ_[p])
    rw [hcoeff, ← mul_assoc] at h'
    simpa using h'
  have hppg : IsUnit (g.coeff p) := by
    rw [hcoeff]
    exact (Units.isUnit _).mul (isUnit_intCast_of_not_dvd hpp)
  -- the local theorem in the splitting field `L` of `g` over `ℚ_[p]`
  obtain ⟨Pl, hPl⟩ :=
    InertiaCyclePadic.exists_heightOneSpectrum_liesOver p (toPadic g).SplittingField
  obtain ⟨σl, hσin, hcycl, hcardl⟩ := exists_isCycle_galPerm_mem_inertia_of_wild_local hE hmonic
    (hdegg ▸ hdeg) hlowg h0g hppg Pl
  -- transfer to `Gal(f/ℚ)`
  have hsplitg : Splits (g.map (algebraMap ℤ_[p] (toPadic g).SplittingField)) := by
    rw [map_eq_map_toPadic]; exact SplittingField.splits _
  have hgL : g.map (algebraMap ℤ_[p] (toPadic g).SplittingField) =
      C (algebraMap ℤ_[p] (toPadic g).SplittingField ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) *
        fZ.map (Int.castRingHom (toPadic g).SplittingField) := by
    simp only [g, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
    rw [RingHom.ext_int ((algebraMap ℤ_[p] (toPadic g).SplittingField).comp
      (Int.castRingHom ℤ_[p])) (Int.castRingHom (toPadic g).SplittingField)]
  have hsplitZ : Splits (fZ.map (Int.castRingHom (toPadic g).SplittingField)) := by
    have h := hsplitg
    rw [hgL] at h
    have h2 := h.C_mul (algebraMap ℤ_[p] (toPadic g).SplittingField (u : ℤ_[p]))
    rwa [← mul_assoc, ← C_mul, ← map_mul, Units.mul_inv, map_one, C_1, one_mul] at h2
  have hfL : f.map (algebraMap ℚ (toPadic g).SplittingField) =
      C (algebraMap ℚ (toPadic g).SplittingField c) *
        fZ.map (Int.castRingHom (toPadic g).SplittingField) := by
    rw [hf, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ (toPadic g).SplittingField).comp (Int.castRingHom ℚ))
        (Int.castRingHom (toPadic g).SplittingField)]
  have hsplitf : Fact ((f.map (algebraMap ℚ (toPadic g).SplittingField)).Splits) :=
    ⟨by rw [hfL]; exact hsplitZ.C_mul _⟩
  have hfZ0 : fZ ≠ 0 := fun h => hlc (by simp [h])
  have hfne : f ≠ 0 := by
    rw [hf]
    exact mul_ne_zero (C_ne_zero.mpr hc)
      ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hfZ0)
  have hg0 : toPadic g ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective ℤ_[p] ℚ_[p])).mpr hmonic.ne_zero
  have hc' : algebraMap ℚ (toPadic g).SplittingField c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hu' : algebraMap ℤ_[p] (toPadic g).SplittingField ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ≠ 0 :=
    fun h => Units.ne_zero _
      (InertiaCyclePadic.algebraMap_padicInt_injective p _ (by rw [h, map_zero]))
  have hset : f.rootSet (toPadic g).SplittingField =
      (toPadic g).rootSet (toPadic g).SplittingField := by
    ext z
    rw [mem_rootSet, mem_rootSet, aeval_def, aeval_def, ← eval_map, ← eval_map, hfL,
      ← map_eq_map_toPadic g, hgL]
    simp only [eval_mul, eval_C, mul_eq_zero, hc', hu', false_or, ne_eq, hfne, hg0,
      not_false_eq_true, true_and]
  let ϕ : (toPadic g).SplittingField ≃ₐ[ℚ] (toPadic g).SplittingField :=
    AlgEquiv.restrictScalarsHom ℚ σl
  have hσp : σl ^ p = 1 := by
    apply galPerm_injective (toPadic g)
    have h := pow_orderOf_eq_one (galPerm (toPadic g) σl)
    rw [hcycl.orderOf, hcardl] at h
    rw [map_pow, map_one]
    exact h
  have hpow : Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ ^ p = 1 := by
    rw [← map_pow]
    have : ϕ ^ p = 1 := by
      have h := map_pow (AlgEquiv.restrictScalarsHom ℚ
        (S := ℚ_[p]) (A := (toPadic g).SplittingField))
        (σl : (toPadic g).SplittingField ≃ₐ[ℚ_[p]] (toPadic g).SplittingField) p
      rw [show (σl : (toPadic g).SplittingField ≃ₐ[ℚ_[p]] (toPadic g).SplittingField) ^ p = 1
        from hσp] at h
      exact h.symm.trans (map_one _)
    rw [this, map_one]
  obtain ⟨x, hx⟩ : ∃ x, galPerm (toPadic g) σl x ≠ x := by
    by_contra h
    push Not at h
    exact hcycl.ne_one (Equiv.ext h)
  have hxf : (x : (toPadic g).SplittingField) ∈ f.rootSet (toPadic g).SplittingField := by
    rw [hset]; exact x.2
  have hne1 : Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ ≠ 1 := by
    intro h1
    have h2 := Polynomial.Gal.restrict_smul ϕ ⟨(x : (toPadic g).SplittingField), hxf⟩
    rw [h1, one_smul] at h2
    exact hx (Subtype.ext (by exact h2.symm))
  have hordg : orderOf (Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ) = p :=
    orderOf_eq_prime hpow hne1
  -- the number of roots is `< 2p`
  have hroots : Fintype.card (f.rootSet f.SplittingField) ≤ fZ.natDegree := by
    have hfdeg : f.natDegree = fZ.natDegree := by
      rw [hf, natDegree_C_mul hc, natDegree_map_eq_of_injective (RingHom.injective_int _)]
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, rootSet_def, Set.ncard_coe_finset,
      ← hfdeg]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
  have hord : orderOf (galPerm f (Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ)) = p :=
    (orderOf_injective (galPerm f) (galPerm_injective f) _).trans hordg
  have hsupp : (galPerm f (Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ)).support.card <
      2 * orderOf (galPerm f (Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ)) := by
    rw [hord]
    exact lt_of_le_of_lt ((Finset.card_le_univ _).trans hroots) hdeg
  have hcyc : (galPerm f (Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ)).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by rw [hord]; exact hp) hsupp
  -- the inertia membership: `Gal(L/ℚ_[p])`-inertia of `Pl` gives `Gal(L/ℚ)`-inertia of the prime
  -- `Pl ∩ 𝓞 L` of `𝓞 L`, whose contraction to `𝓞 K` is carried by `Gal.restrict`
  let ι₁ : 𝓞 (toPadic g).SplittingField →+* integralClosure ℤ_[p] (toPadic g).SplittingField :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hPlover : Pl.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [← Ideal.under_under (A := ℤ) (B := ℤ_[p]), ← hPl.over]
    ext n
    rw [Ideal.mem_span_singleton, Ideal.under, Ideal.mem_comap]
    constructor
    · rintro ⟨k, rfl⟩
      have hp' : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.p_nonunit
      simpa using Ideal.mul_mem_right (k : ℤ_[p]) _ hp'
    · intro h
      by_contra hn
      exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_intCast_of_not_dvd hn))
        (by rwa [eq_intCast] at h)
  have : (Pl.asIdeal.comap ι₁).IsPrime := Ideal.comap_isPrime _ _
  have : (Pl.asIdeal.comap ι₁).LiesOver (Ideal.span {(p : ℤ)}) :=
    @liesOver_comap_int _ _ _ _ ι₁ Pl.asIdeal _ hPlover
  let σl' : Gal((toPadic g).SplittingField/ℚ_[p]) := σl
  have hσin' : σl' ∈ Pl.asIdeal.inertia Gal((toPadic g).SplittingField/ℚ_[p]) := hσin
  have hϕin : ϕ ∈ (Pl.asIdeal.comap ι₁).inertia Gal((toPadic g).SplittingField/ℚ) := by
    rw [Ideal.mem_inertia]
    intro x
    rw [Ideal.mem_comap, map_sub]
    exact (Ideal.mem_inertia.mp hσin' ) (ι₁ x)
  have hσg := restrict_mem_inertia_comap (g := f) hϕin
  set P₀ := (Pl.asIdeal.comap ι₁).comap
    (RingOfIntegers.mapRingHom (algebraMap f.SplittingField (toPadic g).SplittingField)) with hP₀
  have : P₀.IsPrime := Ideal.comap_isPrime _ _
  have : P₀.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_comap_int _ _ _
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P₀ P
    Gal(f.SplittingField/ℚ)
  let σ₀ : Gal(f.SplittingField/ℚ) := Polynomial.Gal.restrict f (toPadic g).SplittingField ϕ
  let τf : f.Gal := τ
  let σf : f.Gal := σ₀
  have hperm : galPerm f (τf * σf * τf⁻¹) =
      galPerm f τf * galPerm f σf * (galPerm f τf)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨τf * σf * τf⁻¹, ?_, ?_, ?_⟩
  · rw [← hτ, Ideal.inertia_smul]
    exact ⟨_, hσg, rfl⟩
  · rw [hperm]
    exact hcyc.conj
  · rw [hperm, Equiv.Perm.card_support_conj]
    rw [← hcyc.orderOf, hord]

open Classical in
omit [Fact p.Prime] in
/-- **The wild cycle** (proof of Lemma 5.16), global form without membership: under the hypotheses
of `exists_isCycle_galPerm_mem_inertia_of_wild_source`, `Gal(f/ℚ)` contains an element acting on
the roots of `f` as a single `p`-cycle (it lies in the inertia group of every prime above `p`
up to conjugacy; here a prime is chosen). -/
theorem exists_isCycle_galPerm_of_wild_source (hE : EisensteinPrimeTotallyRamified) {p : ℕ}
    (hp : p.Prime) {f : ℚ[X]} {fZ : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hf : f = C c * fZ.map (Int.castRingHom ℚ)) (hdeg : fZ.natDegree < 2 * p)
    (hlc : ¬ (p : ℤ) ∣ fZ.leadingCoeff) (hlow : ∀ i < p, (p : ℤ) ∣ fZ.coeff i)
    (h0 : ¬ (p : ℤ) ^ 2 ∣ fZ.coeff 0) (hpp : ¬ (p : ℤ) ∣ fZ.coeff p) :
    ∃ σ : f.Gal, (galPerm f σ).IsCycle ∧ (galPerm f σ).support.card = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NumberField f.SplittingField := ⟨⟩
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hPmax, hPover⟩ : ∃ P : Ideal (𝓞 f.SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
  obtain ⟨σ, -, h⟩ := exists_isCycle_galPerm_mem_inertia_of_wild_source hE hp hc hf hdeg hlc hlow
    h0 hpp P
  exact ⟨σ, h⟩

end Global

end SourceWild

end ArithmeticOfJacobiPolynomials
