/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.JacobiCycle
public import ArithmeticOfJacobiPolynomials.Galois.InertiaRestrict

/-!
# Inertia membership of the Jacobi cycles (Proposition 5.2, inertia form)

The cycles of Proposition 5.2 are produced by Lemma 5.1 inside an inertia
group at `p` (`SourceInertia.exists_prime_isCycle_galPerm_mem_inertia`,
`SourceInertia.exists_prime_isCycle_galPerm_comp_mem_inertia`) and then transported along an
affine change of variables. Here we track the inertia membership through this transport:

* restriction `Gal(E/ℚ) → Gal(g/ℚ)` to the splitting field of `g` inside `E` maps the inertia
  group of a prime `P` of `𝓞 E` into the inertia group of its contraction
  (`restrict_mem_inertia_comap`), and contraction preserves lying over `p`;
* for `g = a f(bX + c)` the restriction of `σ ∈ Gal(f/ℚ)` acts on the roots of `g` by the
  conjugate of the action of `σ` on the roots of `f` (`exists_galPerm_restrict_eq_permCongr`).

The results are `exists_isCycle_galPerm_jacobiP_mem_inertia` and
`exists_isCycle_galPerm_jacobiP_comp_mem_inertia`: the cycles of Proposition 5.2 lie in the
inertia group of some maximal ideal of the ring of integers of the splitting field lying over `p`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField

variable {F : Type*} [Field F]

/-- **Affine transport of the root action, with the explicit element.** For `g = a f(bX + c)`
with `a, b ≠ 0` and `σ ∈ Gal(f/F)`, the restriction of `σ` to the splitting field of `g` acts on
the roots of `g` by a conjugate `e ∘ σ ∘ e⁻¹` of the action of `σ` on the roots of `f`; when
`c = 0`, `e` commutes with negation. -/
theorem exists_galPerm_restrict_eq_permCongr (f : F[X]) {a b : F} (c : F) (ha : a ≠ 0)
    (hb : b ≠ 0) [Fact (((C a * f.comp (C b * X + C c)).map
      (algebraMap F f.SplittingField)).Splits)] (σ : f.Gal) :
    ∃ e : f.rootSet f.SplittingField ≃
        (C a * f.comp (C b * X + C c)).rootSet (C a * f.comp (C b * X + C c)).SplittingField,
      galPerm _ (Gal.restrict (C a * f.comp (C b * X + C c)) f.SplittingField σ) =
        e.permCongr (galPerm f σ) ∧
      (c = 0 → ∀ x y : f.rootSet f.SplittingField,
        (y : f.SplittingField) = -(x : f.SplittingField) →
        ((e y : _) : (C a * f.comp (C b * X + C c)).SplittingField) =
          -((e x : _) : (C a * f.comp (C b * X + C c)).SplittingField)) := by
  set ψ := Gal.rootsEquivRootsAux (C a * f.comp (C b * X + C c)) f.SplittingField with hψ
  set A := affineRootsEquiv f c ha hb f.SplittingField with hA
  have hψcoe : ∀ w : (C a * f.comp (C b * X + C c)).rootSet
      (C a * f.comp (C b * X + C c)).SplittingField,
      ((ψ w : f.SplittingField)) = IsScalarTower.toAlgHom F
        (C a * f.comp (C b * X + C c)).SplittingField f.SplittingField
        (w : (C a * f.comp (C b * X + C c)).SplittingField) :=
    fun w => rfl
  refine ⟨A.trans ψ.symm, ?_, ?_⟩
  · ext1 y
    rw [Equiv.permCongr_apply]
    apply ψ.injective
    rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
    have h1 : ψ (galPerm _ (Gal.restrict (C a * f.comp (C b * X + C c)) f.SplittingField σ) y) =
        (Gal.restrict (C a * f.comp (C b * X + C c)) f.SplittingField σ) • ψ y := by
      rw [hψ, Gal.smul_def, Equiv.symm_apply_apply, galPerm_apply]
    rw [h1]
    apply Subtype.ext
    have h3 := Gal.restrict_smul (p := C a * f.comp (C b * X + C c)) (E := f.SplittingField) σ
      (ψ y)
    rw [h3, coe_affineRootsEquiv, galPerm_apply]
    change σ (ψ y : f.SplittingField) = (algebraMap F f.SplittingField b)⁻¹ *
      (σ ((A.symm (ψ y) : f.SplittingField)) - algebraMap F f.SplittingField c)
    have h2 : ((ψ y : f.SplittingField)) = A (A.symm (ψ y)) := by rw [Equiv.apply_symm_apply]
    conv_lhs => rw [h2, coe_affineRootsEquiv]
    have hcb : σ (algebraMap F f.SplittingField b) = algebraMap F f.SplittingField b :=
      AlgEquiv.commutes (σ : f.SplittingField ≃ₐ[F] f.SplittingField) b
    have hcc : σ (algebraMap F f.SplittingField c) = algebraMap F f.SplittingField c :=
      AlgEquiv.commutes (σ : f.SplittingField ≃ₐ[F] f.SplittingField) c
    rw [map_mul, map_inv₀, map_sub, hcb, hcc]
  · intro hc x y hxy
    subst hc
    have hinj := (IsScalarTower.toAlgHom F (C a * f.comp (C b * X + C 0)).SplittingField
      f.SplittingField).toRingHom.injective
    apply hinj
    change ((ψ (ψ.symm (A y)) : f.SplittingField)) = IsScalarTower.toAlgHom F
      (C a * f.comp (C b * X + C 0)).SplittingField f.SplittingField
      (-((ψ.symm (A x) : (C a * f.comp (C b * X + C 0)).SplittingField)))
    rw [map_neg, ← hψcoe, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      coe_affineRootsEquiv, coe_affineRootsEquiv, hxy]
    simp only [map_zero, sub_zero]
    ring

open Classical in
/-- **Affine transport of inertia cycles.** Let `g = a f(bX + c)` with `a, b ≠ 0` over `ℚ`, and
let `σ ∈ Gal(f/ℚ)` lie in the inertia group of a prime `P` of `𝓞` of the splitting field of `f`
lying over `p` and act on the roots of `f` as a single `d`-cycle (whose `k`-th power negates its
support if `c = 0`). Then some prime `Q` of `𝓞` of the splitting field of `g` lies over `p`
and some `τ` in its inertia group acts on the roots of `g` as a single `d`-cycle (whose `k`-th
power negates its support if `c = 0`). -/
theorem exists_mem_inertia_galPerm_affine_of_eq {f g : ℚ[X]} {a b c : ℚ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hg : g = C a * f.comp (C b * X + C c)) {p d k : ℕ} (σ : f.Gal)
    (hσ : (galPerm f σ).IsCycle) (hd : (galPerm f σ).support.card = d)
    (hneg : c = 0 → ∀ x ∈ (galPerm f σ).support,
      (((galPerm f σ ^ k) x : f.rootSet f.SplittingField) : f.SplittingField) = -(x : _))
    (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hσI : σ ∈ P.inertia Gal(f.SplittingField/ℚ)) :
    ∃ Q : Ideal (𝓞 g.SplittingField), Q.IsPrime ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ τ : g.Gal, τ ∈ Q.inertia Gal(g.SplittingField/ℚ) ∧
        (galPerm g τ).IsCycle ∧ (galPerm g τ).support.card = d ∧
        (c = 0 → ∀ y ∈ (galPerm g τ).support,
          (((galPerm g τ ^ k) y : g.rootSet g.SplittingField) : g.SplittingField) = -(y : _)) := by
  subst hg
  have : Fact (((C a * f.comp (C b * X + C c)).map (algebraMap ℚ f.SplittingField)).Splits) :=
    fact_splits_affine f c
  obtain ⟨e, he, hneg'⟩ := exists_galPerm_restrict_eq_permCongr f c ha hb σ
  refine ⟨P.comap (RingOfIntegers.mapRingHom
      (algebraMap (C a * f.comp (C b * X + C c)).SplittingField f.SplittingField)),
    Ideal.IsPrime.comap _, liesOver_comap_int _ P _,
    Gal.restrict (C a * f.comp (C b * X + C c)) f.SplittingField σ,
    restrict_mem_inertia_comap hσI, ?_, ?_, ?_⟩
  · rw [he]; exact isCycle_permCongr e hσ
  · rw [he, card_support_permCongr, hd]
  · intro hc y hy
    rw [he, support_permCongr, Finset.mem_map_equiv] at hy
    rw [he, ← zpow_natCast, permCongr_zpow, zpow_natCast, Equiv.permCongr_apply]
    have := hneg' hc (e.symm y) _ (hneg hc _ hy)
    rw [Equiv.apply_symm_apply] at this
    exact this

open Classical in
/-- **Proposition 5.2, first assertion, inertia form.** Under the hypotheses of Proposition 5.2,
with `d = n + 1 - k₀ ≥ 2`, there are a maximal ideal `P` of the ring of integers of the
splitting field `L` of `P_n^{(a/u,b/v)}` lying over `p` and an element of the inertia group
`I_P ≤ Gal(L/ℚ)` acting on the roots as a single `d`-cycle. -/
theorem exists_isCycle_galPerm_jacobiP_mem_inertia {p n : ℕ} {a u b v D r : ℤ}
    (h : JacobiCycleHypotheses p n a u b v D r)
    (hd : 2 ≤ n + 1 - jacobiCycleIndexNat p n D r) :
    ∃ P : Ideal (𝓞 (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).Gal,
        σ ∈ P.inertia Gal((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField/ℚ) ∧
        (galPerm _ σ).IsCycle ∧
        (galPerm _ σ).support.card = n + 1 - jacobiCycleIndexNat p n D r := by
  obtain ⟨-, -, h3, -, h0, hlc, hlc2, hdeg, hsq⟩ := h.localCycle_hypotheses
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPmax, hPover, τ, hτI, hτ, hcard⟩ :=
    SourceInertia.exists_prime_isCycle_galPerm_mem_inertia h.prime hd h3 h0 hlc hlc2 hdeg hsq
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast h.u_pos.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast h.D_pos.ne'
  have hs : (u : ℚ) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu') (by exact_mod_cast n.factorial_ne_zero)
  have hb : 2 * (D : ℚ) / u ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hD') hu'
  have hg := integralJacobi_map a u D r ((b : ℚ) / v) n h.u_pos.ne' h.r_eq
  rw [show (1 + C (2 * (D : ℚ) / u) * X : ℚ[X]) = C (2 * (D : ℚ) / u) * X + C 1 by
    rw [C_1, add_comm]] at hg
  have hf := eq_C_mul_comp_affine_inv hs hb hg
  have hc : -(1 / (2 * (D : ℚ) / u)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero hb)
  obtain ⟨Q, hQ, hQover, σ, hσI, hσ, hσcard, -⟩ :=
    exists_mem_inertia_galPerm_affine_of_eq (inv_ne_zero hs) (inv_ne_zero hb) hf (p := p) (k := 0) τ
      hτ hcard (fun h => absurd h hc) P hτI
  have : NumberField (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).SplittingField := ⟨⟩
  have := Int.ideal_span_isMaximal_of_prime p
  exact ⟨Q, Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)}), hQover, σ, hσI,
    hσ, hσcard⟩

open Classical in
/-- **Proposition 5.2, quadratic assertion, inertia form.** Under the hypotheses of
Proposition 5.2, with `d = n + 1 - k₀`, let `c ∈ ℚ^×` have `v_p(c) = 0` and `2d < p`. Then there
are a maximal ideal `P` of the ring of integers of the splitting field `L` of
`P_n^{(a/u,b/v)}(1 + cX²)` lying over `p` and an element `σ` of the inertia group
`I_P ≤ Gal(L/ℚ)` acting on the roots as a single `2d`-cycle whose `d`-th power is negation on the
roots it moves. -/
theorem exists_isCycle_galPerm_jacobiP_comp_mem_inertia {p n : ℕ} {a u b v D r : ℤ}
    (h : JacobiCycleHypotheses p n a u b v D r) {c : ℚ} (hc : c ≠ 0)
    (hcp : padicValRat p c = 0)
    (h2d : 2 * (n + 1 - jacobiCycleIndexNat p n D r) < p) :
    ∃ P : Ideal (𝓞 ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp
        (1 + C c * X ^ 2)).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).Gal,
        σ ∈ P.inertia Gal(((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp
          (1 + C c * X ^ 2)).SplittingField/ℚ) ∧
        (galPerm _ σ).IsCycle ∧
        (galPerm _ σ).support.card = 2 * (n + 1 - jacobiCycleIndexNat p n D r) ∧
        ∀ y ∈ (galPerm _ σ).support,
          (((galPerm _ σ ^ (n + 1 - jacobiCycleIndexNat p n D r)) y : _) :
            ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).SplittingField) =
            -((y : _) :
            ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).SplittingField) := by
  obtain ⟨h1, -, -, -, h0, hlc, hlc2, hdeg, hsq⟩ := h.localCycle_hypotheses
  have : Fact p.Prime := ⟨h.prime⟩
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast h.u_pos.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast h.D_pos.ne'
  -- `q = u c / (2D)` has `p`-adic valuation `0`
  set q : ℚ := (u : ℚ) * c / (2 * D) with hq
  have hq0 : q ≠ 0 := div_ne_zero (mul_ne_zero hu' hc) (mul_ne_zero two_ne_zero hD')
  have hp_u : ¬ (p : ℤ) ∣ u := fun hd => h.not_dvd (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left hd _) _)
  have hp_D : ¬ (p : ℤ) ∣ D := fun hd => h.not_dvd (dvd_mul_of_dvd_right hd _)
  have h3 : 3 ≤ p := lt_of_le_of_ne h.prime.two_le (Ne.symm h.odd)
  have hp_2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have := Int.le_of_dvd two_pos hd
    omega
  have hvint : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → padicValRat p (z : ℚ) = 0 := fun z hz => by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]; simp
  have hvq : padicValRat p q = 0 := by
    have h2 : padicValRat p (2 : ℚ) = 0 := by simpa using hvint 2 hp_2
    rw [hq, padicValRat.div (mul_ne_zero hu' hc) (mul_ne_zero two_ne_zero hD'),
      padicValRat.mul hu' hc, padicValRat.mul two_ne_zero hD', hcp, h2, hvint u hp_u,
      hvint D hp_D]
    simp
  have hst := not_dvd_num_mul_den_of_padicValRat_eq_zero hq0 hvq
  have ht : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hqst : ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) = (u : ℚ) * c / (2 * D) := by
    push_cast; exact Rat.num_div_den q
  generalize q.num = s at hst hqst
  generalize (q.den : ℤ) = t at hst ht hqst
  obtain ⟨P, hPmax, hPover, τ, hτI, hτ, hcard, hneg⟩ :=
    SourceInertia.exists_prime_isCycle_galPerm_comp_mem_inertia (c := s * t) h.prime
      h.odd hst h1 h2d h0 hlc hlc2 hdeg hsq
  -- the affine relation between `K_n(st X²)` and `P_n(1 + cX²)`
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hs : (u : ℚ) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu') (by exact_mod_cast n.factorial_ne_zero)
  have hrel : (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2) =
      C ((u : ℚ) ^ n * n.factorial)⁻¹ *
        (((integralJacobi a u D r n).comp (C (s * t) * X ^ 2)).map
          (Int.castRingHom ℚ)).comp (C (t : ℚ)⁻¹ * X + C 0) := by
    rw [Polynomial.map_comp, comp_assoc]
    have hq' : ((C (s * t) * X ^ 2 : ℤ[X]).map (Int.castRingHom ℚ)).comp
        (C (t : ℚ)⁻¹ * X + C 0) = C ((s : ℚ) / t) * X ^ 2 := by
      rw [C_0, add_zero, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, mul_comp, C_comp,
        pow_comp, X_comp, mul_pow, ← mul_assoc, ← C_pow, ← C_mul]
      congr 2
      simp only [eq_intCast, Int.cast_mul]
      field_simp
    rw [hq', integralJacobi_map_comp_C_mul_X_sq a u D r ((b : ℚ) / v) n h.u_pos.ne' h.r_eq,
      ← mul_assoc, ← C_mul, inv_mul_cancel₀ hs, C_1, one_mul]
    congr 3
    rw [mul_div_assoc, hqst]
    field_simp
  obtain ⟨Q, hQ, hQover, σ, hσI, hσ, hσcard, hσneg⟩ :=
    exists_mem_inertia_galPerm_affine_of_eq (inv_ne_zero hs) (inv_ne_zero ht') hrel (p := p) τ hτ
      hcard (fun _ => hneg) P hτI
  have : NumberField ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp
      (1 + C c * X ^ 2)).SplittingField := ⟨⟩
  have := Int.ideal_span_isMaximal_of_prime p
  exact ⟨Q, Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)}), hQover, σ, hσI,
    hσ, hσcard, hσneg rfl⟩

end ArithmeticOfJacobiPolynomials
