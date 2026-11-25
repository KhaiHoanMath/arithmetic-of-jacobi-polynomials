/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.SourceInertiaCycle
public import ArithmeticOfJacobiPolynomials.Galois.InertiaRestrict
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.Galois.InertiaCycle
public import Mathlib

/-!
# Global inertia cycles in Lemma 5.1

The local theorem of `SourceInertiaCycle` (`exists_mem_inertia_generator`: Hensel/Eisenstein,
transitivity, Stacks 09EE) is carried to the splitting field `K` of `f ∈ ℤ[X]` over `ℚ`:
`Hyp p d f` gives `LocalHyp p d f` over `ℤ_[p]`; a prime of the local splitting field `L` over `p`
gives, by restriction `Gal(L/ℚ_[p]) → Gal(L/ℚ) → Gal(f/ℚ)` (`restrict_mem_inertia_comap`), an
inertia element of the contracted prime of `K`; conjugacy of the primes above `p`
(`Ideal.exists_smul_eq_of_isGaloisGroup`, `Ideal.inertia_smul`) gives the statement for every
prime `P`; and `galPerm` changes by a conjugate (`rootsEquivRoots`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace SourceInertia

open Polynomial NumberField IsDedekindDomain RootResidues LocalRootResidues InertiaCyclePadic

variable {p : ℕ}

/-- An integer prime to `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_intCast_of_not_dvd' [Fact p.Prime] {n : ℤ} (h : ¬ (p : ℤ) ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact h

/-- The `p`-adic valuation of a unit of `ℤ_[p]` is `0`. -/
theorem valuation_eq_zero_of_isUnit [Fact p.Prime] {m : ℤ_[p]} (hm : IsUnit m) :
    m.valuation = 0 := by
  have hne : m ≠ 0 := hm.ne_zero
  have h1 := PadicInt.norm_eq_zpow_neg_valuation hne
  rw [PadicInt.isUnit_iff.mp hm] at h1
  have hp1 : (p : ℝ) ≠ 1 := by
    have := (Fact.out : p.Prime).one_lt
    exact_mod_cast this.ne'
  have := (zpow_eq_one_iff_right₀ (Nat.cast_nonneg p) hp1).mp h1.symm
  omega

/-- **The bundled global hypotheses give the local ones**: `Hyp p d f` over `ℤ` implies
`LocalHyp p d f` over `ℤ_[p]`. -/
theorem localHyp_of_hyp [Fact p.Prime] {d : ℕ} {f : ℤ[X]} (hf : Hyp p d f) :
    LocalHyp p d (f.map (Int.castRingHom ℤ_[p])) := by
  have hinj : Function.Injective (Int.castRingHom ℤ_[p]) := RingHom.injective_int _
  have hred : (f.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod =
      f.map (Int.castRingHom (ZMod p)) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  refine ⟨?_, ?_, ?_, ?_, hf.pos, hf.lt⟩
  · rw [coeff_map]
    exact isUnit_intCast_of_not_dvd' hf.coeff_zero
  · obtain ⟨m, hm⟩ := hf.dvd_lead
    have hm2 : ¬ (p : ℤ) ∣ m := fun h => hf.not_sq_dvd_lead (by
      rw [hm, pow_two]; exact mul_dvd_mul_left _ h)
    have hmu : IsUnit (m : ℤ_[p]) := isUnit_intCast_of_not_dvd' hm2
    have hlc : (f.map (Int.castRingHom ℤ_[p])).leadingCoeff = (p : ℤ_[p]) * (m : ℤ_[p]) := by
      rw [leadingCoeff_map_of_injective hinj, hm]
      simp
    rw [hlc, PadicInt.valuation_mul PadicInt.prime_p.ne_zero hmu.ne_zero, PadicInt.valuation_p,
      valuation_eq_zero_of_isUnit hmu]
  · rw [hred, natDegree_map_eq_of_injective hinj]
    exact hf.natDegree_eq
  · rw [hred]
    exact hf.squarefree

section Local

variable [Fact p.Prime] {d : ℕ} {g : ℤ_[p][X]}

open Classical in
/-- **Lemma 5.1, first assertion, local form**: for
`LocalHyp p d g` with `2 ≤ d`, every prime `Pl` of the ring of integers of the splitting field of
`g` over `ℚ_[p]` lying over `p` has an inertia element acting on the roots as a single `d`-cycle. -/
theorem exists_isCycle_galPerm_mem_inertia_local (hg : LocalHyp p d g) (hd : 2 ≤ d)
    (Pl : HeightOneSpectrum (integralClosure ℤ_[p] (toPadic g).SplittingField))
    [Pl.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ σ : (toPadic g).Gal,
      σ ∈ Pl.asIdeal.inertia Gal((toPadic g).SplittingField/ℚ_[p]) ∧
      (galPerm (toPadic g) σ).IsCycle ∧ (galPerm (toPadic g) σ).support.card = d := by
  have : IsGalois ℚ_[p] (toPadic g).SplittingField := IsGalois.mk
  have hroot_iff := mem_rootSet_toPadic_iff hg
  have hsplit := card_roots_toPadic hg Pl
  have hfaith : ∀ σ : Gal((toPadic g).SplittingField/ℚ_[p]),
      (∀ y, (g.map (algebraMap ℤ_[p] (toPadic g).SplittingField)).eval y = 0 → σ y = y) →
        σ = 1 := by
    intro σ hσ
    exact Polynomial.Gal.ext (toPadic g) (fun x hx => by
      change σ x = x; exact hσ x ((hroot_iff x).mp hx))
  obtain ⟨τ, hτI, hsupp, y₀, hy₀, hy₀1, htrans, hcard⟩ :=
    exists_mem_inertia_generator Pl hg hd hsplit hfaith
  have hsuppiff : ∀ x : (toPadic g).rootSet (toPadic g).SplittingField,
      x ∈ (galPerm (toPadic g) τ).support ↔
        1 < Pl.valuation (toPadic g).SplittingField (x : (toPadic g).SplittingField) := by
    intro x
    rw [Equiv.Perm.mem_support, Ne, Subtype.ext_iff]
    exact hsupp x ((hroot_iff x).mp x.2)
  have hg0 : g.map (algebraMap ℤ_[p] (toPadic g).SplittingField) ≠ 0 := by
    rw [map_eq_map_toPadic, Ne,
      Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (toPadic g).SplittingField).injective]
    exact toPadic_ne_zero hg
  refine ⟨τ, hτI, ⟨⟨y₀, (hroot_iff y₀).mpr hy₀⟩, ?_, ?_⟩, ?_⟩
  · rw [← Equiv.Perm.mem_support, hsuppiff]; exact hy₀1
  · intro x hx
    rw [← Equiv.Perm.mem_support, hsuppiff] at hx
    obtain ⟨k, hk⟩ := htrans x ((hroot_iff x).mp x.2) hx
    refine ⟨k, Subtype.ext ?_⟩
    have e := (galPerm (toPadic g)).map_zpow τ k
    rw [← e]
    exact hk
  · have hmap : (galPerm (toPadic g) τ).support.map (Function.Embedding.subtype _) =
        (g.map (algebraMap ℤ_[p] (toPadic g).SplittingField)).roots.toFinset.filter
          (fun y => 1 < Pl.valuation (toPadic g).SplittingField y) := by
      ext y
      simp only [Finset.mem_map, Function.Embedding.coe_subtype, Finset.mem_filter,
        Multiset.mem_toFinset]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hsuppiff] at hx
        refine ⟨?_, hx⟩
        rw [mem_roots', IsRoot.def]
        exact ⟨hg0, (hroot_iff x).mp x.2⟩
      · rintro ⟨hy, h1⟩
        rw [mem_roots', IsRoot.def] at hy
        exact ⟨⟨y, (hroot_iff y).mpr hy.2⟩, (hsuppiff _).mpr h1, rfl⟩
    rw [← Finset.card_map (Function.Embedding.subtype _), hmap, hcard]

end Local

section Transfer

variable [Fact p.Prime]

/-- **Local inertia to global inertia** via the identification of the local Galois
group with a decomposition subgroup of the global group. Let `L ⊇ ℚ_[p]` be a finite Galois
extension in which `f ∈ ℚ[X]` splits, `Pl` a prime of `𝓞_L` over `p`, and
`σl ∈ I_{Pl} ≤ Gal(L/ℚ_[p])`.
Then for every prime `P` of the splitting field `K` of `f` over `p`, a conjugate of the restriction
of `σl` to `K` lies in the inertia group `I_P ≤ Gal(K/ℚ)`. -/
theorem exists_conj_mem_inertia_of_local {f : ℚ[X]} {L : Type*} [Field L] [Algebra ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] [Fact ((f.map (algebraMap ℚ L)).Splits)]
    (Pl : HeightOneSpectrum (integralClosure ℤ_[p] L))
    [Pl.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {σl : Gal(L/ℚ_[p])}
    (hσin : σl ∈ Pl.asIdeal.inertia Gal(L/ℚ_[p]))
    (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ τ ρ : Gal(f.SplittingField/ℚ),
      ρ = (Gal.restrict f L (AlgEquiv.restrictScalarsHom ℚ σl) : Gal(f.SplittingField/ℚ)) ∧
      τ * ρ * τ⁻¹ ∈ P.inertia Gal(f.SplittingField/ℚ) := by
  have : NumberField f.SplittingField := ⟨⟩
  have : IsGalois ℚ f.SplittingField := IsGalois.mk
  let ϕ : L ≃ₐ[ℚ] L := AlgEquiv.restrictScalarsHom ℚ σl
  let ι₁ : 𝓞 L →+* integralClosure ℤ_[p] L :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hPlover : Pl.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [← Ideal.under_under (A := ℤ) (B := ℤ_[p]),
      ← Ideal.LiesOver.over (P := Pl.asIdeal) (p := IsLocalRing.maximalIdeal ℤ_[p])]
    ext n
    rw [Ideal.mem_span_singleton, Ideal.under, Ideal.mem_comap]
    constructor
    · rintro ⟨k, rfl⟩
      have hp' : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.p_nonunit
      simpa using Ideal.mul_mem_right (k : ℤ_[p]) _ hp'
    · intro h
      by_contra hn
      exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_intCast_of_not_dvd' hn))
        (by rwa [eq_intCast] at h)
  have : (Pl.asIdeal.comap ι₁).IsPrime := Ideal.comap_isPrime _ _
  have : (Pl.asIdeal.comap ι₁).LiesOver (Ideal.span {(p : ℤ)}) :=
    @liesOver_comap_int _ _ _ _ ι₁ Pl.asIdeal _ hPlover
  have hϕin : ϕ ∈ (Pl.asIdeal.comap ι₁).inertia Gal(L/ℚ) := by
    rw [Ideal.mem_inertia]
    intro x
    rw [Ideal.mem_comap, map_sub]
    exact (Ideal.mem_inertia.mp hσin) (ι₁ x)
  have hσg := restrict_mem_inertia_comap (g := f) hϕin
  set P₀ := (Pl.asIdeal.comap ι₁).comap
    (RingOfIntegers.mapRingHom (algebraMap f.SplittingField L)) with hP₀
  have : P₀.IsPrime := Ideal.comap_isPrime _ _
  have : P₀.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_comap_int _ _ _
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P₀ P
    Gal(f.SplittingField/ℚ)
  refine ⟨τ, _, rfl, ?_⟩
  rw [← hτ, Ideal.inertia_smul]
  exact ⟨_, hσg, rfl⟩

end Transfer

section Global

open Classical in
/-- Core of `exists_isCycle_galPerm_mem_inertia_of_hyp`, for an abstract `fQ = f` over `ℚ`. -/
theorem exists_isCycle_galPerm_mem_inertia_core {d : ℕ} {f : ℤ[X]} {fQ : ℚ[X]}
    (hfQ : fQ = f.map (Int.castRingHom ℚ)) (hf : Hyp p d f) (hd : 2 ≤ d)
    (P : Ideal (𝓞 fQ.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : fQ.Gal, σ ∈ P.inertia Gal(fQ.SplittingField/ℚ) ∧ (galPerm fQ σ).IsCycle ∧
      (galPerm fQ σ).support.card = d := by
  have : Fact p.Prime := ⟨hf.prime⟩
  set g : ℤ_[p][X] := f.map (Int.castRingHom ℤ_[p]) with hgdef
  have hg : LocalHyp p d g := localHyp_of_hyp hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf.coeff_zero (by simp)
  have hfQ0 : fQ ≠ 0 := by
    rw [hfQ, Ne, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]; exact hf0
  have : NumberField fQ.SplittingField := ⟨⟩
  have : IsGalois ℚ fQ.SplittingField := IsGalois.mk
  have : Fact ((fQ.map (algebraMap ℚ fQ.SplittingField)).Splits) := ⟨SplittingField.splits fQ⟩
  -- the local splitting field
  have hmapL : fQ.map (algebraMap ℚ (toPadic g).SplittingField) =
      (toPadic g).map (algebraMap ℚ_[p] (toPadic g).SplittingField) := by
    rw [hfQ, Polynomial.map_map, toPadic, hgdef, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have : Fact ((fQ.map (algebraMap ℚ (toPadic g).SplittingField)).Splits) :=
    ⟨by rw [hmapL]; exact SplittingField.splits _⟩
  have : IsGalois ℚ_[p] (toPadic g).SplittingField := IsGalois.mk
  obtain ⟨Pl, hPl⟩ := exists_heightOneSpectrum_liesOver p (toPadic g).SplittingField
  obtain ⟨σl, hσin, hcycl, hcardl⟩ := exists_isCycle_galPerm_mem_inertia_local hg hd Pl
  obtain ⟨τ, ρ, hρ, hmem⟩ := exists_conj_mem_inertia_of_local (f := fQ) Pl hσin P
  -- the restriction to `fQ.Gal`
  let ϕ : (toPadic g).SplittingField ≃ₐ[ℚ] (toPadic g).SplittingField :=
    AlgEquiv.restrictScalarsHom ℚ σl
  let σ₀ : fQ.Gal := Gal.restrict fQ (toPadic g).SplittingField ϕ
  -- root sets in the local splitting field
  have hset : fQ.rootSet (toPadic g).SplittingField =
      (toPadic g).rootSet (toPadic g).SplittingField := by
    ext z
    rw [mem_rootSet, mem_rootSet, aeval_def, aeval_def, ← eval_map, ← eval_map, hmapL]
    exact ⟨fun h => ⟨toPadic_ne_zero hg, h.2⟩, fun h => ⟨hfQ0, h.2⟩⟩
  let r : fQ.rootSet fQ.SplittingField ≃ fQ.rootSet (toPadic g).SplittingField :=
    Gal.rootsEquivRootsAux fQ (toPadic g).SplittingField
  let e : fQ.rootSet fQ.SplittingField ≃ (toPadic g).rootSet (toPadic g).SplittingField :=
    r.trans (Set.equivOfEq hset)
  have key : ∀ x : fQ.rootSet fQ.SplittingField,
      ((r (galPerm fQ σ₀ x) : fQ.rootSet (toPadic g).SplittingField) :
        (toPadic g).SplittingField) = σl ((r x : fQ.rootSet (toPadic g).SplittingField) :
        (toPadic g).SplittingField) := by
    intro x
    have h := Gal.smul_def (p := fQ) (E := (toPadic g).SplittingField) σ₀ (r x)
    rw [Equiv.symm_apply_apply] at h
    have h' : r (galPerm fQ σ₀ x) = σ₀ • r x := h.symm
    rw [h']
    exact Gal.restrict_smul ϕ (r x)
  have hconj : galPerm (toPadic g) σl = e.permCongr (galPerm fQ σ₀) := by
    ext1 y
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    have hk := key (r.symm ((Set.equivOfEq hset).symm y))
    rw [Equiv.apply_symm_apply] at hk
    change σl (y : (toPadic g).SplittingField) = ((r (galPerm fQ σ₀
      (r.symm ((Set.equivOfEq hset).symm y))) : fQ.rootSet (toPadic g).SplittingField) :
        (toPadic g).SplittingField)
    rw [hk]
    rfl
  have hconj' : galPerm fQ σ₀ = e.symm.permCongr (galPerm (toPadic g) σl) := by
    rw [hconj, ← Equiv.permCongr_symm, Equiv.symm_apply_apply]
  have hcyc : (galPerm fQ σ₀).IsCycle := by
    rw [hconj']; exact isCycle_permCongr _ hcycl
  have hcard : (galPerm fQ σ₀).support.card = d := by
    rw [hconj', card_support_permCongr, hcardl]
  -- conjugate into the inertia group of `P`
  let τf : fQ.Gal := τ
  let ρf : fQ.Gal := ρ
  have hρσ : ρf = σ₀ := hρ
  have hperm : galPerm fQ (τf * ρf * τf⁻¹) =
      galPerm fQ τf * galPerm fQ ρf * (galPerm fQ τf)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨τf * ρf * τf⁻¹, hmem, ?_, ?_⟩
  · rw [hperm, hρσ]
    exact hcyc.conj
  · rw [hperm, hρσ, Equiv.Perm.card_support_conj]
    exact hcard

open Classical in
/-- **Lemma 5.1, first part, inertia form**: for every
prime `P` of the ring of integers of the splitting field `K` of `f` lying over `p`, some element
of the inertia group `I_P ≤ Gal(K/ℚ)` acts on the roots of `f` as a single `d`-cycle.
The local cycle is `SourceInertia.exists_mem_inertia_generator`, transferred to the global
splitting field by `exists_conj_mem_inertia_of_local`. -/
theorem exists_isCycle_galPerm_mem_inertia_of_hyp {d : ℕ} {f : ℤ[X]} (hf : Hyp p d f)
    (hd : 2 ≤ d) (P : Ideal (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      σ ∈ P.inertia Gal((f.map (Int.castRingHom ℚ)).SplittingField/ℚ) ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).support.card = d :=
  exists_isCycle_galPerm_mem_inertia_core rfl hf hd P

open Classical in
/-- **Lemma 5.1, first part, under the bundled hypotheses `Hyp p d f`**: `Gal(f/ℚ)`
contains an element acting on the roots of `f` as a single `d`-cycle. -/
theorem exists_isCycle_galPerm_of_hyp {d : ℕ} {f : ℤ[X]} (hf : Hyp p d f) (hd : 2 ≤ d) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (galPerm (f.map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).support.card = d := by
  have : Fact p.Prime := ⟨hf.prime⟩
  obtain ⟨P, hPmax, hPover⟩ := InertiaCycle.exists_isMaximal_liesOver p f
  obtain ⟨σ, -, h⟩ := exists_isCycle_galPerm_mem_inertia_of_hyp hf hd P
  exact ⟨σ, h⟩

open Classical in
/-- **Lemma 5.1, first part**. Let `f ∈ ℤ[X]`, `p` prime,
`2 ≤ d < p`, `p ∤ f(0)`, `p ∥ lc f`, and let the reduction `f̄` of `f` modulo `p` be squarefree
of degree `deg f - d`. Then some element of `Gal(f/ℚ)` acts on the roots of `f` as a single
`d`-cycle. -/
theorem exists_isCycle_galPerm (hp : p.Prime) {d : ℕ} {f : ℤ[X]} (hd : 2 ≤ d)
    (hdp : d < p) (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (galPerm (f.map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).support.card = d :=
  exists_isCycle_galPerm_of_hyp ⟨hp, h0, hlc, hlc2, hdeg, hsq, by omega, hdp⟩ hd

open Classical in
/-- **Lemma 5.1, first part, inertia form**: for every prime `P` of the ring of
integers of the splitting field `K` of `f` lying over `p`, some element of the inertia group
`I_P ≤ Gal(K/ℚ)` acts on the roots of `f` as a single `d`-cycle. -/
theorem exists_isCycle_galPerm_mem_inertia (hp : p.Prime) {d : ℕ} {f : ℤ[X]} (hd : 2 ≤ d)
    (hdp : d < p) (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (P : Ideal (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      σ ∈ P.inertia Gal((f.map (Int.castRingHom ℚ)).SplittingField/ℚ) ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm (f.map (Int.castRingHom ℚ)) σ).support.card = d :=
  exists_isCycle_galPerm_mem_inertia_of_hyp ⟨hp, h0, hlc, hlc2, hdeg, hsq, by omega, hdp⟩ hd P

open Classical in
/-- **Lemma 5.1, first part, inertia form with the prime**: there are a maximal
ideal `P` of the ring of integers of the splitting field `K` of `f` lying over `p` and an element
of the inertia group `I_P ≤ Gal(K/ℚ)` acting on the roots of `f` as a single `d`-cycle. -/
theorem exists_prime_isCycle_galPerm_mem_inertia (hp : p.Prime) {d : ℕ} {f : ℤ[X]}
    (hd : 2 ≤ d) (hdp : d < p) (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ P : Ideal (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
        σ ∈ P.inertia Gal((f.map (Int.castRingHom ℚ)).SplittingField/ℚ) ∧
        (galPerm (f.map (Int.castRingHom ℚ)) σ).IsCycle ∧
        (galPerm (f.map (Int.castRingHom ℚ)) σ).support.card = d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPmax, hPover⟩ := InertiaCycle.exists_isMaximal_liesOver p f
  exact ⟨P, hPmax, hPover,
    exists_isCycle_galPerm_mem_inertia hp hd hdp h0 hlc hlc2 hdeg hsq P⟩

open Classical in
/-- **Lemma 5.1, second part, inertia form**: under the hypotheses
of the first part with `1 ≤ d`, `p` odd, `p ∤ c` and `2d < p`, for every prime `P` of the ring of
integers of the splitting field `L` of `g = f(cX²)` lying over `p`, some element `σ` of the
inertia group `I_P ≤ Gal(L/ℚ)` acts on the roots of `g` as a single `2d`-cycle, and `σ^d` is
negation on the support of this cycle.  The first part is applied to `g` (`hyp_comp`: `g` satisfies
`Hyp p (2d)`); the negation statement is the centralizer argument
(`InertiaCycle.galPerm_comp_pow_apply_eq_neg`). -/
theorem exists_isCycle_galPerm_comp_mem_inertia (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ}
    {f : ℤ[X]} {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hd : 1 ≤ d) (h2d : 2 * d < p)
    (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (P : Ideal (𝓞 ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).Gal,
      σ ∈ P.inertia Gal(((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField/ℚ) ∧
      (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support.card = 2 * d ∧
      ∀ x ∈ (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support,
        ((galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ ^ d) x :
        ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) =
          -(x : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) := by
  have hf : Hyp p d f := ⟨hp, h0, hlc, hlc2, hdeg, hsq, hd, by omega⟩
  obtain ⟨σ, hσI, hcyc, hcard⟩ :=
    exists_isCycle_galPerm_mem_inertia_of_hyp (InertiaCycle.hyp_comp hf hp2 hc h2d)
      (by omega) P
  exact ⟨σ, hσI, hcyc, hcard, InertiaCycle.galPerm_comp_pow_apply_eq_neg
    (fun h => h0 (by rw [h]; exact dvd_zero _)) σ hcyc hcard⟩

open Classical in
/-- **Lemma 5.1, second part**: under the hypotheses of the first part with `1 ≤ d`,
`p` odd, `p ∤ c` and `2d < p`, for `g = f(cX²)` some element `σ` of `Gal(g/ℚ)` acts on the roots
of `g` as a single `2d`-cycle, and `σ^d` is negation on the support of this cycle. -/
theorem exists_isCycle_galPerm_comp (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} {f : ℤ[X]} {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) (hd : 1 ≤ d) (h2d : 2 * d < p)
    (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).Gal,
      (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).IsCycle ∧
      (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support.card = 2 * d ∧
      ∀ x ∈ (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support,
        ((galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ ^ d) x :
          ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) =
          -(x : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPmax, hPover⟩ := InertiaCycle.exists_isMaximal_liesOver p (f.comp (C c * X ^ 2))
  obtain ⟨σ, -, h⟩ := exists_isCycle_galPerm_comp_mem_inertia hp hp2 hc hd h2d h0 hlc hlc2 hdeg
    hsq P
  exact ⟨σ, h⟩

open Classical in
/-- **Lemma 5.1, second part, inertia form with the prime**: there are a maximal
ideal `P` of the ring of integers of the splitting field `L` of `g = f(cX²)` lying over `p` and
`σ` in the inertia group `I_P ≤ Gal(L/ℚ)` acting on the roots of `g` as a single `2d`-cycle with
`σ^d` negation on its support. -/
theorem exists_prime_isCycle_galPerm_comp_mem_inertia (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ}
    {f : ℤ[X]} {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hd : 1 ≤ d) (h2d : 2 * d < p)
    (h0 : ¬ (p : ℤ) ∣ f.coeff 0) (hlc : (p : ℤ) ∣ f.leadingCoeff)
    (hlc2 : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff)
    (hdeg : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree)
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ P : Ideal (𝓞 ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).Gal,
        σ ∈ P.inertia Gal(((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField/ℚ) ∧
        (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).IsCycle ∧
        (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support.card = 2 * d ∧
        ∀ x ∈ (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support,
          ((galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ ^ d) x :
        ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) =
            -(x : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPmax, hPover⟩ := InertiaCycle.exists_isMaximal_liesOver p (f.comp (C c * X ^ 2))
  exact ⟨P, hPmax, hPover,
    exists_isCycle_galPerm_comp_mem_inertia hp hp2 hc hd h2d h0 hlc hlc2 hdeg hsq P⟩


end Global

end SourceInertia

end ArithmeticOfJacobiPolynomials
