/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.PrimePowerIrreducibility
public import ArithmeticOfJacobiPolynomials.Combinatorics.DigitHull
public import ArithmeticOfJacobiPolynomials.MainResults
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Local irreducibility of the Kaneko–Zagier Jacobi polynomials over `ℚ_3` (Theorem A.1)

For `λ, μ ∈ {-1,1}` and `δ = (μ+1)/2`, the coefficients `b_j` of the monic polynomial
`T_n^{λ,μ}(X) = n! P_n^{(λ/3,μ/2)}(2X-1)/(n+λ/3+μ/2+1)_n` satisfy (eq. (five-tower))
`2 v_3(b_j) = 3(n-j) + Φ_{n,δ}(j)` (`two_mul_padicValRat_kanekoZagierCoeff`).

* degrees `3^a`: Corollary A.3 (and degree one);
* degrees `5·3^a`, `μ = -1` or `a ≥ 2`: the single edge `(0,(3n+1)/2)–(n,0)` from the digit
  single-edge property (the integer content of Lemma A.5);
* `μ = 1`, `n = 5, 15`: the factor degrees `1, 1, 3` and `2, 13` over `ℚ_3`.

The factor degrees for `n = 5, 15` here (`five_root_slope`, `fifteen_root_slope`,
`natDegree_factors_kanekoZagier_five`, `natDegree_factors_kanekoZagier_fifteen`,
`kanekoZagier_localIrreducibility`) come from a dominant-term argument on the constant terms of the
irreducible factors, which avoids exactly the hypothesis `NewtonPolygonRootSlopes`. The manuscript's
argument, the Newton faces of the polygon, is `kanekoZagier_localIrreducibility_of_newton` in
`SourceKanekoZagierNewton`, conditional on `NewtonPolygonRootSlopes`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

theorem padicValRat_three_int_div_three {l : ℤ} (hl : l = 1 ∨ l = -1) :
    padicValRat 3 ((l : ℚ) / 3) = -1 := by
  have h3 : padicValRat 3 (3 : ℚ) = 1 := by
    have := padicValRat.self (p := 3) (by norm_num)
    simpa using this
  rcases hl with rfl | rfl
  · rw [Int.cast_one, padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h3]; rfl
  · rw [Int.cast_neg, Int.cast_one, neg_div, padicValRat.neg,
      padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h3]; rfl

theorem padicValRat_three_int_div_two {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) :
    padicValRat 3 ((μ : ℚ) / 2) = 0 := by
  have h2 := padicValRat_two_of_ne_two (p := 3) (by norm_num)
  rcases hμ with rfl | rfl
  · rw [Int.cast_one, padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h2]; rfl
  · rw [Int.cast_neg, Int.cast_one, neg_div, padicValRat.neg,
      padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h2]; rfl

/-- Legendre's formula at `3`: `2 v_3(k!) + s_3(k) = k`. -/
theorem two_mul_padicValNat_three_factorial_add (k : ℕ) :
    2 * padicValNat 3 k.factorial + digitSum3 k = k := by
  have h := sub_one_mul_padicValNat_factorial (p := 3) k
  have hle := digitSum3_le k
  rw [digitSum3_eq] at hle ⊢
  norm_num at h
  omega

/-- One step of the numerator recursion: `v_3((2N+2+δ)!) - v_3((N+1)!) =
v_3((2N+δ)!) - v_3(N!) + v_3(2N+1+2δ)`. -/
theorem padicValNat_three_factorial_step (δ : ℕ) (hδ : δ ≤ 1) (N : ℕ) :
    (padicValNat 3 (2 * (N + 1) + δ).factorial : ℤ) - padicValNat 3 (N + 1).factorial =
      (padicValNat 3 (2 * N + δ).factorial : ℤ) - padicValNat 3 N.factorial +
        padicValNat 3 (2 * N + 1 + 2 * δ) := by
  have h2 : padicValNat 3 (2 * (N + 1)) = padicValNat 3 (N + 1) := by
    rw [padicValNat.mul (by norm_num) (by omega),
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]
  rw [show 2 * (N + 1) + δ = (2 * N + δ + 1) + 1 by ring, Nat.factorial_succ,
    Nat.factorial_succ (2 * N + δ), Nat.factorial_succ N,
    padicValNat.mul (by omega) (by positivity), padicValNat.mul (by omega) (by positivity),
    padicValNat.mul (by omega) (by positivity)]
  rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
  · rw [show 2 * N + 0 + 1 + 1 = 2 * (N + 1) by ring, h2]
    simp only [add_zero, mul_zero]; push_cast; ring
  · rw [show 2 * N + 1 + 1 = 2 * (N + 1) by ring, h2,
      show 2 * N + 1 + 2 * 1 = 2 * N + 1 + 1 + 1 by ring]
    push_cast; ring_nf

/-- The numerators of (4.24) for `β = μ/2`, `μ = 2δ - 1`:
`v_3((β+j+1)_m) = (v_3((2(j+m)+δ)!) - v_3((j+m)!)) - (v_3((2j+δ)!) - v_3(j!))`. -/
theorem padicValRat_three_ascPochhammer_half (δ : ℕ) (hδ : δ ≤ 1) (β : ℚ)
    (hβ : 2 * β = 2 * δ - 1) (j m : ℕ) :
    0 < (ascPochhammer ℚ m).eval (β + j + 1) ∧
      padicValRat 3 ((ascPochhammer ℚ m).eval (β + j + 1)) =
        ((padicValNat 3 (2 * (j + m) + δ).factorial : ℤ) - padicValNat 3 (j + m).factorial) -
          ((padicValNat 3 (2 * j + δ).factorial : ℤ) - padicValNat 3 j.factorial) := by
  have hpos : 0 < β + j + 1 := by
    have : (0 : ℝ) ≤ 0 := le_rfl
    have hδ' : (0 : ℚ) ≤ δ := Nat.cast_nonneg δ
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    linarith
  refine ⟨ascPochhammer_pos m _ hpos, ?_⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have hA := ascPochhammer_pos m _ hpos
    have hfac : β + j + 1 + m = ((2 * (j + m) + 1 + 2 * δ : ℕ) : ℚ) / 2 := by
      push_cast; linarith
    have hfac0 : ((2 * (j + m) + 1 + 2 * δ : ℕ) : ℚ) / 2 ≠ 0 := by positivity
    rw [ascPochhammer_succ_eval, hfac, padicValRat.mul hA.ne' hfac0, ih,
      padicValRat.div (by positivity) (by norm_num), padicValRat_two_of_ne_two (p := 3)
        (by norm_num), padicValRat.of_nat, show j + (m + 1) = (j + m) + 1 by ring,
      padicValNat_three_factorial_step δ hδ (j + m)]
    ring

/-- **The five-tower valuations.** For `λ, μ ∈ {-1,1}`, `μ = 2δ - 1` and `j ≤ n`, the
coefficient `b_j` of `T_n^{λ,μ}` is nonzero and `2 v_3(b_j) = 3(n-j) + Φ_{n,δ}(j)`. -/
theorem two_mul_padicValRat_kanekoZagierCoeff {l μ : ℤ} (hl : l = 1 ∨ l = -1) (δ : ℕ)
    (hδ : δ ≤ 1) (hμ : μ = 2 * δ - 1) (n j : ℕ) (hj : j ≤ n) :
    monicEndpointCoeff ((l : ℚ) / 3) ((μ : ℚ) / 2) n j ≠ 0 ∧
      2 * padicValRat 3 (monicEndpointCoeff ((l : ℚ) / 3) ((μ : ℚ) / 2) n j) =
        3 * ((n : ℤ) - j) + digitPhi n δ j := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  have hα := padicValRat_three_int_div_three hl
  have hβ := padicValRat_three_int_div_two hμ'
  have hden := padicValRat_ascPochhammer_of_neg (p := 3) (e := 1) one_pos
    (by rw [hα]; rfl) hβ.ge (n + j + 1) (n - j)
  have e1 : ((n + j + 1 : ℕ) : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 =
      (n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + j + 1 := by push_cast; ring
  rw [e1] at hden
  have hnum := padicValRat_three_ascPochhammer_half δ hδ ((μ : ℚ) / 2)
    (by rw [hμ]; push_cast; ring) j (n - j)
  rw [Nat.add_sub_cancel' hj] at hnum
  have hb := padicValRat_monicEndpointCoeff (p := 3) ((l : ℚ) / 3) ((μ : ℚ) / 2) n j hj
    hnum.1.ne' hden.1
  refine ⟨hb.1, ?_⟩
  rw [hb.2, hnum.2, hden.2]
  have hch := padicValNat_choose_add_factorial (p := 3) n j hj
  have l1 := two_mul_padicValNat_three_factorial_add (2 * n + δ)
  have l2 := two_mul_padicValNat_three_factorial_add (2 * j + δ)
  have l3 := two_mul_padicValNat_three_factorial_add (n - j)
  rw [digitPhi_eq]
  simp only [Nat.cast_one, one_mul]
  omega

/-- The leading Pochhammer symbol `(n + λ/3 + μ/2 + 1)_n` is nonzero. -/
theorem kanekoZagier_ascPochhammer_ne_zero {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) ≠ 0 := by
  have hden := padicValRat_ascPochhammer_of_neg (p := 3) (e := 1) one_pos
    (by rw [padicValRat_three_int_div_three hl]; rfl)
    (padicValRat_three_int_div_two hμ).ge (n + 1) n
  have e1 : ((n + 1 : ℕ) : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 =
      (n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1 := by push_cast; ring
  rw [e1] at hden
  exact hden.1

theorem kanekoZagier_irreducible_iff {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) :
    Irreducible ((kanekoZagierJacobi l μ n).map (algebraMap ℚ ℚ_[3])) ↔
      Irreducible ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ ℚ_[3])) := by
  rw [kanekoZagierJacobi_eq]
  exact irreducible_map_jacobiP_iff _ _ n (kanekoZagier_ascPochhammer_ne_zero hl hμ n)

/-- If `Φ_{n,δ}(0) = 1` and `Φ_{n,δ}(j) ≥ 1` for `0 < j < n`, then `T_n^{λ,μ}` has the single
Newton edge `(0, (3n+1)/2)–(n, 0)`, and `P_n^{(λ/3,μ/2)}` is irreducible over `ℚ_3`. -/
theorem irreducible_kanekoZagier_of_digitPhi {l μ : ℤ} (hl : l = 1 ∨ l = -1) (δ : ℕ)
    (hδ : δ ≤ 1) (hμ : μ = 2 * δ - 1) (n : ℕ) (hn : 0 < n) (h0 : digitPhi n δ 0 = 1)
    (h : ∀ j, 0 < j → j < n → 1 ≤ digitPhi n δ j) :
    Irreducible ((kanekoZagierJacobi l μ n).map (algebraMap ℚ ℚ_[3])) := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  have hA := kanekoZagier_ascPochhammer_ne_zero hl hμ' n
  obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic _ _ n hA
  have hcoeff : ∀ j, j ≤ n → (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j =
      monicEndpointCoeff ((l : ℚ) / 3) ((μ : ℚ) / 2) n j := by
    intro j hj
    rw [monicEndpoint_coeff _ _ n hA, ite_eq_left_iff.mpr (fun h => absurd hj h)]
  have hv := fun j hj => two_mul_padicValRat_kanekoZagierCoeff hl δ hδ hμ n j hj
  rw [kanekoZagier_irreducible_iff hl hμ']
  have hv0 := hv 0 (Nat.zero_le _)
  rw [h0, ← hcoeff 0 (Nat.zero_le _)] at hv0
  refine irreducible_map_padic_of_single_edge hmon (by omega) hv0.1 ?_ ?_
  · rw [hdeg, ← Int.isCoprime_iff_gcd_eq_one]
    exact ⟨2, -3, by push_cast at hv0; linarith [hv0.2]⟩
  · rw [hdeg]
    intro j hj0 hjn hcj
    have hvj := hv j hjn.le
    rw [← hcoeff j hjn.le] at hvj
    have hΦ := h j hj0 hjn
    have h1 := hv0.2
    push_cast at h1
    have hnΦ : (n : ℤ) * 1 ≤ n * digitPhi n δ j :=
      mul_le_mul_of_nonneg_left hΦ (by positivity)
    have hj' : (0 : ℤ) < j := by exact_mod_cast hj0
    set H := padicValRat 3 ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff 0)
    set w := padicValRat 3 ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j)
    have e1 : 2 * (H * ((n : ℤ) - j)) = (3 * n + 1) * (n - j) := by rw [← mul_assoc, h1]; ring
    have e2 : 2 * ((n : ℤ) * w) = n * (3 * (n - j) + digitPhi n δ j) := by
      rw [← hvj.2]; ring
    nlinarith

/-- **Theorem A.1, degrees `3^a`.** All four `P_{3^a}^{(λ/3,μ/2)}` are irreducible over
`ℚ_3`. -/
theorem irreducible_kanekoZagier_three_pow {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (a : ℕ) :
    Irreducible ((kanekoZagierJacobi l μ (3 ^ a)).map (algebraMap ℚ ℚ_[3])) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [kanekoZagier_irreducible_iff hl hμ]
    have hA := kanekoZagier_ascPochhammer_ne_zero hl hμ (3 ^ 0)
    obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic _ _ _ hA
    refine Polynomial.Monic.irreducible_of_degree_eq_one ?_ (hmon.map _)
    rw [degree_map, degree_eq_natDegree hmon.ne_zero, hdeg]; simp
  · have hα : padicValRat 3 ((l : ℚ) / 3) < 0 := by
      rw [padicValRat_three_int_div_three hl]; norm_num
    have := irreducible_jacobiP_half_of_odd_prime (p := 3) (by norm_num) a ha _ hα
    rw [kanekoZagierJacobi_eq]
    rcases hμ with rfl | rfl
    · simpa using this.2
    · have e : (((-1 : ℤ) : ℚ) / 2) = -1 / 2 := by norm_num
      rw [e]; exact this.1

/-- **Theorem A.1, degrees `5·3^a`, irreducible cases.** If `μ = -1` or `a ≥ 2`, then
`P_{5·3^a}^{(λ/3,μ/2)}` is irreducible over `ℚ_3`. -/
theorem irreducible_kanekoZagier_five_mul_three_pow {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (a : ℕ) (h : μ = -1 ∨ 2 ≤ a) :
    Irreducible ((kanekoZagierJacobi l μ (5 * 3 ^ a)).map (algebraMap ℚ ℚ_[3])) := by
  have hpos : 0 < 5 * 3 ^ a := by positivity
  rcases hμ with rfl | rfl
  · have ha : 2 ≤ a := by omega
    have := digitPhi_singleEdge_five_mul_three_pow_one a ha
    exact irreducible_kanekoZagier_of_digitPhi hl 1 le_rfl (by norm_num) _ hpos this.1 this.2
  · have := digitPhi_singleEdge_five_mul_three_pow a
    exact irreducible_kanekoZagier_of_digitPhi hl 0 (Nat.zero_le _) (by norm_num) _ hpos
      this.1 this.2

/-! ### Factor degrees -/

open UniqueFactorizationMonoid in
/-- Transfer of factor degrees from the monic endpoint polynomial to `P_n^{(λ/3,μ/2)}`: if
every factorization of `T_n^{λ,μ}` over `ℚ_3` into monic irreducibles has degree multiset
`D`, then so does the factorization of `P_n^{(λ/3,μ/2)}`. -/
theorem natDegree_factors_kanekoZagier_eq {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) (D : Multiset ℕ)
    (hD : ∀ S : Multiset ℚ_[3][X], (∀ g ∈ S, g.Monic ∧ Irreducible g) →
      S.prod = (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ ℚ_[3]) →
      S.map natDegree = D) :
    (factors ((kanekoZagierJacobi l μ n).map (algebraMap ℚ ℚ_[3]))).map natDegree = D := by
  classical
  have hA := kanekoZagier_ascPochhammer_ne_zero hl hμ n
  obtain ⟨hmon, -⟩ := monicEndpoint_monic _ _ n hA
  set Q := (kanekoZagierJacobi l μ n).map (algebraMap ℚ ℚ_[3]) with hQ
  set F := (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ ℚ_[3]) with hF
  have hFm : F.Monic := hmon.map _
  set σ := affineSubst ℚ_[3]
  have hFσ : F = C (algebraMap ℚ ℚ_[3] ((n.factorial : ℚ) /
      (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1))) * σ Q := by
    rw [hF, monicEndpoint_map, affineSubst_apply, hQ, kanekoZagierJacobi_eq]
  have hc : algebraMap ℚ ℚ_[3] ((n.factorial : ℚ) /
      (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1)) ≠ 0 := by
    rw [_root_.map_ne_zero]; exact div_ne_zero (by exact_mod_cast n.factorial_ne_zero) hA
  have hQ0 : Q ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hFσ
    exact hFm.ne_zero hFσ
  set M := factors Q
  set S := (M.map σ).map normalize with hS
  have hσdeg : ∀ g : ℚ_[3][X], (σ g).natDegree = g.natDegree := by
    intro g
    rw [affineSubst_apply, natDegree_comp]
    have : (2 * X - 1 : ℚ_[3][X]).natDegree = 1 := by
      compute_degree!
    rw [this, mul_one]
  have hSdeg : S.map natDegree = M.map natDegree := by
    rw [hS, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun g _ => ?_
    simp only [Function.comp_apply, natDegree_normalize, hσdeg]
  rw [← hSdeg]
  refine hD S (fun g hg => ?_) ?_
  · rw [hS, Multiset.map_map, Multiset.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hirr : Irreducible h := irreducible_of_factor h hh
    have hσirr : Irreducible (σ h) := (MulEquiv.irreducible_iff (affineSubst ℚ_[3])).mpr hirr
    exact ⟨monic_normalize hσirr.ne_zero, (normalize_associated _).symm.irreducible hσirr⟩
  · have hprod : S.prod = normalize (σ M.prod) := by
      rw [hS, map_multiset_prod σ M]
      generalize M.map σ = N
      induction N using Multiset.induction_on with
      | empty => simp
      | cons a N ih => rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.prod_cons,
          normalize_mul]
    have hσM0 : σ M.prod ≠ 0 := by
      intro h0
      have : M.prod = 0 := by
        have := congrArg σ.symm h0
        simpa using this
      exact hQ0 ((factors_prod hQ0).eq_zero_iff.mp this)
    refine eq_of_monic_of_associated (by rw [hprod]; exact monic_normalize hσM0) hFm ?_
    rw [hprod]
    refine (normalize_associated _).trans ((Associated.map σ (factors_prod hQ0)).trans ?_)
    rw [hFσ]
    exact (associated_isUnit_mul_left_iff (isUnit_C.mpr (IsUnit.mk0 _ hc))).mpr
      (Associated.refl _) |>.symm

/-- The valuation of the constant term of a product. -/
theorem valuation_coeff_zero_multiset_prod (S : Multiset ℚ_[3][X])
    (hS : ∀ g ∈ S, g.coeff 0 ≠ 0) :
    S.prod.coeff 0 ≠ 0 ∧
      (S.prod.coeff 0).valuation = (S.map fun g => (g.coeff 0).valuation).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha := hS a (Multiset.mem_cons_self _ _)
    have ih' := ih (fun g hg => hS g (Multiset.mem_cons_of_mem hg))
    rw [Multiset.prod_cons, mul_coeff_zero, Multiset.map_cons, Multiset.sum_cons]
    exact ⟨mul_ne_zero ha ih'.1, by rw [Padic.valuation_mul ha ih'.1, ih'.2]⟩

/-- Coefficient bounds `‖g_i‖ ≤ ρ^(deg g - i)` are multiplicative for monic polynomials. -/
theorem norm_coeff_mul_le {ρ : ℝ} (hρ : 0 ≤ ρ) {g h : ℚ_[3][X]} (hg : g.Monic) (hh : h.Monic)
    (bg : ∀ i, ‖g.coeff i‖ ≤ ρ ^ (g.natDegree - i))
    (bh : ∀ i, ‖h.coeff i‖ ≤ ρ ^ (h.natDegree - i)) (i : ℕ) :
    ‖(g * h).coeff i‖ ≤ ρ ^ ((g * h).natDegree - i) := by
  rw [hg.natDegree_mul hh, coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [norm_mul]
  by_cases h1 : x.1 ≤ g.natDegree
  · by_cases h2 : x.2 ≤ h.natDegree
    · calc ‖g.coeff x.1‖ * ‖h.coeff x.2‖ ≤ ρ ^ (g.natDegree - x.1) * ρ ^ (h.natDegree - x.2) :=
            mul_le_mul (bg _) (bh _) (norm_nonneg _) (by positivity)
        _ = ρ ^ (g.natDegree + h.natDegree - i) := by rw [← pow_add]; congr 1; omega
    · rw [coeff_eq_zero_of_natDegree_lt (p := h) (by omega), norm_zero, mul_zero]; positivity
  · rw [coeff_eq_zero_of_natDegree_lt (p := g) (by omega), norm_zero, zero_mul]; positivity

theorem norm_coeff_multiset_prod_le {ρ : ℝ} (hρ : 0 ≤ ρ) (S : Multiset ℚ_[3][X])
    (hS : ∀ g ∈ S, g.Monic ∧ ∀ i, ‖g.coeff i‖ ≤ ρ ^ (g.natDegree - i)) :
    S.prod.Monic ∧ ∀ i, ‖S.prod.coeff i‖ ≤ ρ ^ (S.prod.natDegree - i) := by
  induction S using Multiset.induction_on with
  | empty =>
    refine ⟨by simp, fun i => ?_⟩
    rw [Multiset.prod_zero, coeff_one]
    split_ifs <;> simp
  | cons a S ih =>
    have ha := hS a (Multiset.mem_cons_self _ _)
    have ih' := ih (fun g hg => hS g (Multiset.mem_cons_of_mem hg))
    rw [Multiset.prod_cons]
    exact ⟨ha.1.mul ih'.1, norm_coeff_mul_le hρ ha.1 ih'.1 ha.2 ih'.2⟩

/-- A monic irreducible `g` over `ℚ_3` whose roots have norm `ρ`, i.e. `‖g(0)‖ = ρ^(deg g)`,
satisfies `‖g_i‖ ≤ ρ^(deg g - i)`. -/
theorem norm_coeff_le_of_irreducible {g : ℚ_[3][X]} (hg : g.Monic) (hirr : Irreducible g)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (h0 : ‖g.coeff 0‖ = ρ ^ g.natDegree) (i : ℕ) :
    ‖g.coeff i‖ ≤ ρ ^ (g.natDegree - i) := by
  have hdeg : g.degree ≠ 0 := by
    rw [degree_eq_natDegree hirr.ne_zero]; exact_mod_cast hirr.natDegree_pos.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (PadicAlgCl 3) g hdeg
  have h1 := norm_pow_natDegree_eq_norm_coeff_zero hg hirr hz
  rw [PadicAlgCl.norm_extends, h0] at h1
  have hzρ : ‖z‖ = ρ := (pow_left_inj₀ (norm_nonneg _) hρ hirr.natDegree_pos.ne').mp h1
  have := norm_coeff_le_of_aeval_eq_zero hg hirr hz i
  rwa [PadicAlgCl.norm_extends, hzρ] at this

/-- A multiset of positive naturals, each at least `c > 0`, with sum `c` is `{c}`. -/
theorem multiset_eq_singleton_of_sum {s : Multiset ℕ} {c : ℕ} (hc : 0 < c) (hsum : s.sum = c)
    (h : ∀ x ∈ s, c ≤ x) : s = {c} := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hsum; omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hs0
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  rw [Multiset.sum_cons] at hsum
  have hxc := h x (Multiset.mem_cons_self _ _)
  have ht : t = 0 := by
    by_contra ht
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero ht
    have := h y (Multiset.mem_cons_of_mem hy)
    have := Multiset.le_sum_of_mem hy
    omega
  subst ht
  simp at hsum ⊢; omega

/-- The coefficient data of `T_n^{λ,μ}` used for the factor degrees. -/
theorem kanekoZagier_monicEndpoint_data {l μ : ℤ} (hl : l = 1 ∨ l = -1) (δ : ℕ) (hδ : δ ≤ 1)
    (hμ : μ = 2 * δ - 1) (n : ℕ) :
    (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).Monic ∧
      (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).natDegree = n ∧
      ∀ j ≤ n, (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j ≠ 0 ∧
        2 * padicValRat 3 ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j) =
          3 * ((n : ℤ) - j) + digitPhi n δ j := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  have hA := kanekoZagier_ascPochhammer_ne_zero hl hμ' n
  obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic _ _ n hA
  refine ⟨hmon, hdeg, fun j hj => ?_⟩
  rw [monicEndpoint_coeff _ _ n hA, ite_eq_left_iff.mpr (fun h => absurd hj h)]
  exact two_mul_padicValRat_kanekoZagierCoeff hl δ hδ hμ n j hj

/-- The no-unique-minimum condition for the coefficient valuations of `T_{15}^{λ,1}` forces the
root valuation `k/d` to be one of the two slopes `20/13`, `3/2`. The proof compares dominant
terms. -/
theorem fifteen_root_slope {T : ℚ[X]} (hT : T.natDegree = 15)
    (hv : ∀ j ≤ 15, T.coeff j ≠ 0 ∧
      2 * padicValRat 3 (T.coeff j) = 3 * (15 - (j : ℤ)) + digitPhi 15 1 j)
    {d : ℕ} {k : ℤ} (hd : 0 < d)
    (hmin : ∀ i, T.coeff i ≠ 0 → ∃ j, j ≠ i ∧ T.coeff j ≠ 0 ∧
      (d : ℤ) * padicValRat 3 (T.coeff j) + j * k ≤ d * padicValRat 3 (T.coeff i) + i * k) :
    13 * k = 20 * d ∨ 2 * k = 3 * d := by
  have hw : ∀ j ≤ 15, padicValRat 3 (T.coeff j) = (3 * (15 - (j : ℤ)) + digitPhi 15 1 j) / 2 :=
    fun j hj => by have := (hv j hj).2; omega
  have hle : ∀ j, T.coeff j ≠ 0 → j ≤ 15 := fun j hj => by
    by_contra h; exact hj (coeff_eq_zero_of_natDegree_lt (by omega))
  have key : ∀ i : ℕ, i ≤ 15 → (∀ j : ℕ, j ≤ 15 → j ≠ i →
      (d : ℤ) * ((3 * (15 - (i : ℤ)) + digitPhi 15 1 i) / 2) + i * k <
        d * ((3 * (15 - (j : ℤ)) + digitPhi 15 1 j) / 2) + j * k) → False := by
    intro i hi hlt
    obtain ⟨j, hji, hjc, hle'⟩ := hmin i (hv i hi).1
    have hj := hle j hjc
    rw [hw j hj, hw i hi] at hle'
    exact absurd hle' (not_le.mpr (hlt j hj hji))
  by_contra hne
  push Not at hne
  rcases lt_or_gt_of_ne hne.1 with h1 | h1
  · rcases lt_or_gt_of_ne hne.2 with h2 | h2
    · exact key 15 le_rfl fun j hj hji => by
        interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)
    · exact key 13 (by norm_num) fun j hj hji => by
        interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)
  · exact key 0 (by norm_num) fun j hj hji => by
      interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)

theorem multiset_eq_two_thirteen {s : Multiset ℕ} (hsum : s.sum = 15)
    (h : ∀ x ∈ s, 0 < x ∧ (13 ∣ x ∨ 2 ∣ x)) : s = {2, 13} := by
  have hodd : ∃ x ∈ s, ¬ 2 ∣ x := by
    by_contra hcon
    push Not at hcon
    have := Multiset.dvd_sum hcon
    rw [hsum] at this; omega
  obtain ⟨x, hx, hx2⟩ := hodd
  have hx15 : x ≤ 15 := hsum ▸ Multiset.le_sum_of_mem hx
  have hx13 : x = 13 := by
    rcases (h x hx).2 with h13 | h2
    · obtain ⟨c, rfl⟩ := h13; omega
    · exact absurd h2 hx2
  subst hx13
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  rw [Multiset.sum_cons] at hsum
  have ht : t = {2} := by
    refine multiset_eq_singleton_of_sum (by norm_num) (by omega) fun y hy => ?_
    have hy' := h y (Multiset.mem_cons_of_mem hy)
    have : y ≤ t.sum := Multiset.le_sum_of_mem hy
    rcases hy'.2 with h13 | h2
    · obtain ⟨c, rfl⟩ := h13; omega
    · obtain ⟨c, rfl⟩ := h2; omega
  subst ht
  decide

/-- **Theorem A.1, `n = 15`, `μ = 1`.** The factor degrees of `P_{15}^{(λ/3,1/2)}` over `ℚ_3`
are `2, 13`. This proof compares dominant terms. The Newton face proof is
`natDegree_factors_kanekoZagier_fifteen_of_newton`. -/
theorem natDegree_factors_kanekoZagier_fifteen {l : ℤ} (hl : l = 1 ∨ l = -1) :
    (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l 1 15).map (algebraMap ℚ ℚ_[3]))).map natDegree = {2, 13} := by
  refine natDegree_factors_kanekoZagier_eq hl (Or.inl rfl) 15 _ fun S hS hprod => ?_
  obtain ⟨hmon, hdeg, hv⟩ := kanekoZagier_monicEndpoint_data (μ := 1) hl 1 le_rfl (by norm_num) 15
  set T := monicEndpoint ((l : ℚ) / 3) (((1 : ℤ) : ℚ) / 2) 15
  have hT0 : T.coeff 0 ≠ 0 := (hv 0 (by norm_num)).1
  refine multiset_eq_two_thirteen ?_ fun x hx => ?_
  · rw [← natDegree_multiset_prod_of_monic _ fun g hg => (hS g hg).1, hprod, natDegree_map,
      hdeg]
  · rw [Multiset.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hdvd : g ∣ T.map (algebraMap ℚ ℚ_[3]) := hprod ▸ Multiset.dvd_prod hg
    obtain ⟨-, hmin⟩ := exists_ne_le_of_irreducible_factor hT0 (hS g hg).1 (hS g hg).2 hdvd
    have hd := (hS g hg).2.natDegree_pos
    have := fifteen_root_slope hdeg (fun j hj => by
      have := hv j hj; push_cast at this; exact this) hd hmin
    refine ⟨hd, ?_⟩
    omega

/-- The no-unique-minimum condition for the coefficient valuations of `T_5^{λ,1}` forces the
root valuation `k/d` to be one of the three slopes `2`, `5/3`, `1`. The proof compares dominant
terms. -/
theorem five_root_slope {T : ℚ[X]} (hT : T.natDegree = 5)
    (hv : ∀ j ≤ 5, T.coeff j ≠ 0 ∧
      2 * padicValRat 3 (T.coeff j) = 3 * (5 - (j : ℤ)) + digitPhi 5 1 j)
    {d : ℕ} {k : ℤ} (hd : 0 < d)
    (hmin : ∀ i, T.coeff i ≠ 0 → ∃ j, j ≠ i ∧ T.coeff j ≠ 0 ∧
      (d : ℤ) * padicValRat 3 (T.coeff j) + j * k ≤ d * padicValRat 3 (T.coeff i) + i * k) :
    k = 2 * d ∨ 3 * k = 5 * d ∨ k = d := by
  have hw : ∀ j ≤ 5, padicValRat 3 (T.coeff j) = (3 * (5 - (j : ℤ)) + digitPhi 5 1 j) / 2 :=
    fun j hj => by have := (hv j hj).2; omega
  have hle : ∀ j, T.coeff j ≠ 0 → j ≤ 5 := fun j hj => by
    by_contra h; exact hj (coeff_eq_zero_of_natDegree_lt (by omega))
  have key : ∀ i : ℕ, i ≤ 5 → (∀ j : ℕ, j ≤ 5 → j ≠ i →
      (d : ℤ) * ((3 * (5 - (i : ℤ)) + digitPhi 5 1 i) / 2) + i * k <
        d * ((3 * (5 - (j : ℤ)) + digitPhi 5 1 j) / 2) + j * k) → False := by
    intro i hi hlt
    obtain ⟨j, hji, hjc, hle'⟩ := hmin i (hv i hi).1
    have hj := hle j hjc
    rw [hw j hj, hw i hi] at hle'
    exact absurd hle' (not_le.mpr (hlt j hj hji))
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  rcases lt_or_gt_of_ne n1 with h1 | h1
  · rcases lt_or_gt_of_ne n2 with h2 | h2
    · rcases lt_or_gt_of_ne n3 with h3 | h3
      · exact key 5 le_rfl fun j hj hji => by
          interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)
      · exact key 4 (by norm_num) fun j hj hji => by
          interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)
    · exact key 1 (by norm_num) fun j hj hji => by
        interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)
  · exact key 0 (by norm_num) fun j hj hji => by
      interval_cases j <;> first | omega | (norm_num [digitPhi_eq, digitSum3_eq]; omega)

theorem natCast_sum_map_natDegree (s : Multiset ℚ_[3][X]) :
    (((s.map natDegree).sum : ℕ) : ℤ) = (s.map fun g => (g.natDegree : ℤ)).sum := by
  rw [Nat.cast_multiset_sum, Multiset.map_map]; rfl

theorem norm_eq_of_valuation {x : ℚ_[3]} (hx : x ≠ 0) {m : ℕ} (h : x.valuation = m) :
    ‖x‖ = (1 / 3 : ℝ) ^ m := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, h, zpow_neg, zpow_natCast, one_div, inv_pow]
  norm_num

/-- **Theorem A.1, `n = 5`, `μ = 1`.** The factor degrees of `P_5^{(λ/3,1/2)}` over `ℚ_3`
are `1, 1, 3`. This proof compares dominant terms using an explicit bound on the coefficient of
`X^3`. The Newton face proof is `natDegree_factors_kanekoZagier_five_of_newton`. -/
theorem natDegree_factors_kanekoZagier_five {l : ℤ} (hl : l = 1 ∨ l = -1) :
    (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l 1 5).map (algebraMap ℚ ℚ_[3]))).map natDegree = {1, 1, 3} := by
  classical
  refine natDegree_factors_kanekoZagier_eq hl (Or.inl rfl) 5 _ fun S hS hprod => ?_
  obtain ⟨hmon, hdeg, hv⟩ := kanekoZagier_monicEndpoint_data (μ := 1) hl 1 le_rfl (by norm_num) 5
  set T := monicEndpoint ((l : ℚ) / 3) (((1 : ℤ) : ℚ) / 2) 5
  have hv' : ∀ j ≤ 5, T.coeff j ≠ 0 ∧
      2 * padicValRat 3 (T.coeff j) = 3 * (5 - (j : ℤ)) + digitPhi 5 1 j := fun j hj => by
    have := hv j hj; push_cast at this; exact this
  have hT0 : T.coeff 0 ≠ 0 := (hv 0 (by norm_num)).1
  set kv : ℚ_[3][X] → ℤ := fun g => (g.coeff 0).valuation with hkv
  -- the data of each factor
  have hty : ∀ g ∈ S, 0 < g.natDegree ∧ g.coeff 0 ≠ 0 ∧
      (kv g = 2 * g.natDegree ∨ 3 * kv g = 5 * g.natDegree ∨ kv g = g.natDegree) := by
    intro g hg
    have hdvd : g ∣ T.map (algebraMap ℚ ℚ_[3]) := hprod ▸ Multiset.dvd_prod hg
    obtain ⟨hg0, hmin⟩ := exists_ne_le_of_irreducible_factor hT0 (hS g hg).1 (hS g hg).2 hdvd
    have hd := (hS g hg).2.natDegree_pos
    exact ⟨hd, hg0, five_root_slope hdeg hv' hd hmin⟩
  -- degree and constant-term sums
  have hD : (S.map natDegree).sum = 5 := by
    rw [← natDegree_multiset_prod_of_monic _ fun g hg => (hS g hg).1, hprod, natDegree_map,
      hdeg]
  have hK : (S.map kv).sum = 8 := by
    have h := (valuation_coeff_zero_multiset_prod S fun g hg => (hty g hg).2.1).2
    rw [hprod, coeff_map, eq_ratCast, Padic.valuation_ratCast] at h
    have h0 := (hv' 0 (by norm_num)).2
    norm_num [digitPhi_eq, digitSum3_eq] at h0
    rw [← h]; omega
  -- split the factors by slope
  set S1 := S.filter fun g => kv g = g.natDegree
  set R := S.filter fun g => ¬ kv g = g.natDegree
  set S2 := R.filter fun g => kv g = 2 * g.natDegree
  set S3 := R.filter fun g => ¬ kv g = 2 * g.natDegree
  have hsplit : S = S1 + (S2 + S3) := by
    rw [Multiset.filter_add_not, Multiset.filter_add_not]
  have hsumZ : ∀ f : ℚ_[3][X] → ℤ, (S.map f).sum =
      (S1.map f).sum + ((S2.map f).sum + (S3.map f).sum) := by
    intro f; conv_lhs => rw [hsplit]
    simp only [Multiset.map_add, Multiset.sum_add]
  have hmem1 : ∀ g ∈ S1, g ∈ S ∧ kv g = g.natDegree := fun g hg => Multiset.mem_filter.mp hg
  have hmem2 : ∀ g ∈ S2, g ∈ S ∧ kv g = 2 * g.natDegree := fun g hg =>
    ⟨(Multiset.mem_filter.mp (Multiset.mem_filter.mp hg).1).1, (Multiset.mem_filter.mp hg).2⟩
  have hmem3 : ∀ g ∈ S3, g ∈ S ∧ 3 * kv g = 5 * g.natDegree := by
    intro g hg
    have h1 := Multiset.mem_filter.mp hg
    have h2 := Multiset.mem_filter.mp h1.1
    have := (hty g h2.1).2.2
    exact ⟨h2.1, by omega⟩
  set A := (S1.map natDegree).sum
  set C := (S2.map natDegree).sum
  set B := (S3.map natDegree).sum
  have hABC : (A : ℤ) + ((C : ℤ) + B) = 5 := by
    have := hsumZ fun g => (g.natDegree : ℤ)
    have hAZ : (A : ℤ) = (S1.map fun g => (g.natDegree : ℤ)).sum := natCast_sum_map_natDegree S1
    have hBZ : (B : ℤ) = (S3.map fun g => (g.natDegree : ℤ)).sum := natCast_sum_map_natDegree S3
    have hCZ : (C : ℤ) = (S2.map fun g => (g.natDegree : ℤ)).sum := natCast_sum_map_natDegree S2
    have hSZ := natCast_sum_map_natDegree S
    rw [hD] at hSZ
    push_cast at hSZ
    linarith
  have hK1 : (S1.map kv).sum = A := by
    rw [natCast_sum_map_natDegree]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun g hg => (hmem1 g hg).2)
  have hK2 : (S2.map kv).sum = 2 * C := by
    rw [natCast_sum_map_natDegree, ← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun g hg => (hmem2 g hg).2)
  have hK3 : 3 * (S3.map kv).sum = 5 * B := by
    rw [natCast_sum_map_natDegree, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun g hg => (hmem3 g hg).2)
  have hKs := hsumZ kv
  rw [hK, hK1, hK2] at hKs
  have hcases : (A = 1 ∧ B = 3 ∧ C = 1) ∨ (A = 2 ∧ B = 0 ∧ C = 3) := by omega
  have hpos : ∀ T' : Multiset ℚ_[3][X], (∀ g ∈ T', g ∈ S) → ∀ x ∈ T'.map natDegree, 1 ≤ x := by
    intro T' hT' x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact (hty g (hT' g hg)).1
  rcases hcases with ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
  · -- the configuration `1, 3, 1`
    have e1 : S1.map natDegree = {1} := multiset_eq_singleton_of_sum one_pos hA
      (hpos S1 fun g hg => (hmem1 g hg).1)
    have e2 : S2.map natDegree = {1} := multiset_eq_singleton_of_sum one_pos hC
      (hpos S2 fun g hg => (hmem2 g hg).1)
    have e3 : S3.map natDegree = {3} := by
      refine multiset_eq_singleton_of_sum (by norm_num) hB fun x hx => ?_
      rw [Multiset.mem_map] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      have := (hmem3 g hg).2
      have := (hty g (hmem3 g hg).1).1
      omega
    rw [hsplit, Multiset.map_add, Multiset.map_add, e1, e2, e3]
    decide
  · -- the configuration `2, 0, 3` is excluded by the coefficient of `X^3`
    exfalso
    have hS3 : S3 = 0 := by
      rw [← Multiset.card_eq_zero]
      have : (S3.map fun _ => 1).sum ≤ B :=
        Multiset.sum_map_le_sum_map _ _ fun g hg => (hty g (hmem3 g hg).1).1
      simp at this; omega
    have hF : T.map (algebraMap ℚ ℚ_[3]) = S1.prod * S2.prod := by
      rw [← hprod, hsplit, hS3, add_zero, Multiset.prod_add]
    -- bounds for the two partial products
    have hb1 := norm_coeff_multiset_prod_le (ρ := 1 / 3) (by norm_num) S1 fun g hg =>
      ⟨(hS g (hmem1 g hg).1).1, norm_coeff_le_of_irreducible (hS g (hmem1 g hg).1).1
        (hS g (hmem1 g hg).1).2 (by norm_num)
        (norm_eq_of_valuation (hty g (hmem1 g hg).1).2.1 (hmem1 g hg).2)⟩
    have hb2 := norm_coeff_multiset_prod_le (ρ := 1 / 9) (by norm_num) S2 fun g hg =>
      ⟨(hS g (hmem2 g hg).1).1, norm_coeff_le_of_irreducible (hS g (hmem2 g hg).1).1
        (hS g (hmem2 g hg).1).2 (by norm_num) (by
          rw [norm_eq_of_valuation (m := 2 * g.natDegree) (hty g (hmem2 g hg).1).2.1
            (by have := (hmem2 g hg).2; simp only [hkv] at this; push_cast; exact this),
            pow_mul]
          norm_num)⟩
    have hd1 : S1.prod.natDegree = 2 := by
      rw [natDegree_multiset_prod_of_monic _ fun g hg => (hS g (hmem1 g hg).1).1]; exact hA
    have hd2 : S2.prod.natDegree = 3 := by
      rw [natDegree_multiset_prod_of_monic _ fun g hg => (hS g (hmem2 g hg).1).1]; exact hC
    have hc0 : ‖S1.prod.coeff 0‖ = 1 / 9 := by
      have h := valuation_coeff_zero_multiset_prod S1 fun g hg => (hty g (hmem1 g hg).1).2.1
      have hv1 : (S1.prod.coeff 0).valuation = (2 : ℕ) := by rw [h.2, hK1, hA]
      rw [norm_eq_of_valuation h.1 hv1]; norm_num
    -- the coefficient of `X^3`
    have g13 : S1.prod.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have g12 : S1.prod.coeff 2 = 1 := by
      have := hb1.1.coeff_natDegree; rwa [hd1] at this
    have g23 : S2.prod.coeff 3 = 1 := by
      have := hb2.1.coeff_natDegree; rwa [hd2] at this
    have h3 := congrArg (fun P => P.coeff 3) hF
    simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub, Nat.reduceSucc,
      g13, g12, g23, mul_one, one_mul, zero_mul, add_zero, coeff_map, eq_ratCast] at h3
    have n1 : ‖S1.prod.coeff 1 * S2.prod.coeff 2‖ ≤ 1 / 27 := by
      rw [norm_mul]
      have a1 := hb1.2 1
      have a2 := hb2.2 2
      rw [hd1] at a1; rw [hd2] at a2
      norm_num at a1 a2
      calc _ ≤ (1 / 3 : ℝ) * (1 / 9) := mul_le_mul a1 a2 (norm_nonneg _) (by norm_num)
        _ = 1 / 27 := by norm_num
    have n2 : ‖S2.prod.coeff 1‖ ≤ 1 / 81 := by
      have a2 := hb2.2 1
      rw [hd2] at a2; norm_num at a2; linarith
    have nrest : ‖S1.prod.coeff 1 * S2.prod.coeff 2 + S2.prod.coeff 1‖ < 1 / 9 := by
      have := IsUltrametricDist.norm_add_le_max (S1.prod.coeff 1 * S2.prod.coeff 2)
        (S2.prod.coeff 1)
      have : max ‖S1.prod.coeff 1 * S2.prod.coeff 2‖ ‖S2.prod.coeff 1‖ ≤ 1 / 27 :=
        max_le n1 (by linarith)
      linarith
    have htot : ‖((T.coeff 3 : ℚ) : ℚ_[3])‖ = 1 / 9 := by
      rw [h3, add_assoc]
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := S1.prod.coeff 0) (y := S1.prod.coeff 1 * S2.prod.coeff 2 + S2.prod.coeff 1)
        (by rw [hc0]; exact (ne_of_gt nrest))
      rw [this, hc0]; exact max_eq_left nrest.le
    have hv3 := hv' 3 (by norm_num)
    have hval3 : padicValRat 3 (T.coeff 3) = 4 := by
      have := hv3.2; norm_num [digitPhi_eq, digitSum3_eq] at this; omega
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hv3.1),
      Padic.valuation_ratCast, hval3] at htot
    norm_num at htot

theorem card_factors_of_irreducible {Q : ℚ_[3][X]} (h : Irreducible Q) :
    ((UniqueFactorizationMonoid.factors Q).map natDegree).card = 1 := by
  obtain ⟨b, -, hb⟩ := UniqueFactorizationMonoid.factors_eq_singleton_of_irreducible h
  rw [hb]; simp

/-- **Theorem A.1 (local irreducibility).** For every `a ≥ 0` and `λ, μ ∈ {-1,1}`,
`P_{3^a}^{(λ/3,μ/2)}` is irreducible over `ℚ_3`; `P_{5·3^a}^{(λ/3,μ/2)}` is irreducible over
`ℚ_3` precisely when `μ = -1` or `a ≥ 2`; and for `μ = 1` the degrees of its irreducible
factors over `ℚ_3` are `1, 1, 3` when `a = 0` and `2, 13` when `a = 1`. This proof compares
dominant terms. The manuscript's Newton polygon proof is
`kanekoZagier_localIrreducibility_of_newton`. -/
theorem kanekoZagier_localIrreducibility : KanekoZagierLocalIrreducibilityStatement := by
  unfold KanekoZagierLocalIrreducibilityStatement
  intro l μ hl hμ
  have h5 : μ = 1 → (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l μ 5).map (algebraMap ℚ ℚ_[3]))).map natDegree = {1, 1, 3} := by
    rintro rfl; exact natDegree_factors_kanekoZagier_five hl
  have h15 : μ = 1 → (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l μ 15).map (algebraMap ℚ ℚ_[3]))).map natDegree = {2, 13} := by
    rintro rfl; exact natDegree_factors_kanekoZagier_fifteen hl
  refine ⟨irreducible_kanekoZagier_three_pow hl hμ, fun a => ⟨fun hirr => ?_,
    irreducible_kanekoZagier_five_mul_three_pow hl hμ a⟩, h5, h15⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hμ1, ha⟩ := hcon
  have hμ1' : μ = 1 := by omega
  have hc := card_factors_of_irreducible hirr
  interval_cases a
  · rw [show 5 * 3 ^ 0 = 5 by norm_num, h5 hμ1'] at hc
    simp at hc
  · rw [show 5 * 3 ^ 1 = 15 by norm_num, h15 hμ1'] at hc
    simp at hc

end ArithmeticOfJacobiPolynomials
