/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B048
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FirstProduct

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorUnramifiedMass; sha256 7229e79198284a6f8a31ab47113bfc32e1ab41acb691847e5fa17bca8afdc03f -/
section
                                                       
                                                                   

/-! Coefficient masses for the original unramified correction and error. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler ProbeLocal

structure CubicCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
def CubicCoefficients.eval (c : CubicCoefficients) (T : ℂ) : ℂ :=
  cubic c.a c.b c.c c.d T
def CubicCoefficients.mass (c : CubicCoefficients) (r : ℝ) : ℝ :=
  cubicMass c.a c.b c.c c.d r

def unramifiedE₀ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectConstant (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹ (coordD Q eta v x)
def unramifiedE₁ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectLinear (coordR Q A x z) (coordV Q z) v
    (eta * (Q - 1) * (Q : ℂ) ^ (-x))

theorem coordK_split (Q : ℝ) (eta x w : ℂ) (hQ : 0 < Q) :
    coordK Q eta x w = (eta * (Q - 1) * (Q : ℂ) ^ (-x)) * (Q : ℂ) ^ (-w) := by
  unfold coordK
  rw [show -x - w = -x + -w by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

theorem unramified_marked_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0) :
    unramifiedMarked Q A eta v x w z =
      affine (unramifiedE₀ Q A eta v x z) (unramifiedE₁ Q A eta v x z)
        ((Q : ℂ) ^ (-w)) - coordD Q eta v x := by
  have hh := marked_defect_affine (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordD Q eta v x) v (eta * (Q - 1) * (Q : ℂ) ^ (-x))
    ((Q : ℂ) ^ (-w)) hR hV
  unfold unramifiedMarked
  rw [coordK_split Q eta x w hQ]
  change markedFactor _ _ _ _ (-coordD Q eta v x + v * (Q : ℂ) ^ (-w) * _) 1 = _
  exact eq_sub_of_add_eq hh

def unramifiedDefectCoefficients (Q : ℝ) (A eta v x z : ℂ) : QuadraticCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  ⟨correctionDefectConstant V D E₀, correctionDefectLinear V D v E₀ E₁,
    correctionDefectQuadratic V D v E₁⟩

theorem unramified_defect_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) :
    unramifiedClosed Q A eta v x w z - 1 =
      (unramifiedDefectCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  change continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) - 1 = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact correction_defect_quadratic _ _ _ _ _ _ hD

def unramifiedErrorCoefficients (Q : ℝ) (A eta v x z : ℂ) : CubicCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let B := star eta * (Q : ℂ) ^ x
  let nu := star v
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  let c := (1 - V) / (1 - D)
  let a := errorBracketConstant V D B nu E₀
  let b := errorBracketLinear V D B nu E₀ E₁
  let d := errorBracketQuadratic E₁
  ⟨c * a, c * (b - v * a), c * (d - v * b), -c * v * d⟩

theorem unramified_error_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1) :
    unramifiedSelected Q A eta v x w z + unramifiedClosed Q A eta v x w z * star v =
      (unramifiedErrorCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  have hi := selected_phase_identities Q eta v x w hQ heta hv
  change compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta * (Q : ℂ) ^ x) ((Q : ℂ) ^ (-w)) +
    continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
      (unramifiedMarked Q A eta v x w z) * star v = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact compensated_error_cubic _ _ _ _ _ _ _ _ hV hD hi.1
    (PrincipalSlotEstimate.unit_phase_inverse v hv)

theorem unramified_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧ 1 - coordD Q eta v x ≠ 0 := by
  refine ⟨one_sub_ne_zero_of_norm_le_half _
    ((coordR_norm_le Q (by linarith) A x z hA).trans
      (rpow_le_half Q _ hQ (by linarith))),
    one_sub_ne_zero_of_norm_le_half _ (first_region_V_half Q hQ z hz), ?_⟩
  apply one_sub_ne_zero_of_norm_le_half
  exact (coordD_norm_le Q (by linarith) eta v x heta hv).trans
    (rpow_le_half Q _ hQ (by linarith))

/-- Summable unramified correction defect coefficient mass. -/
theorem unramified_defect_coefficient_mass (Q sigma eps : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (heps : 0 < eps) (hx : (51 / 100 : ℝ) ≤ x.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hxw : 1 + eps ≤ x.re + sigma) :
    (unramifiedDefectCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      720 * Q ^ (-1 - min eps (1 / 50 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta hv hx hz
  let c := unramifiedDefectCoefficients Q A eta v x z
  have hb := quadraticMass_le_of_vertical_bound Q sigma sigma
    (240 * Q ^ (-1 - min eps (1 / 50 : ℝ))) c.a c.b c.c (by linarith) le_rfl (by
      intro w hw
      have hh := unramifiedClosed_first_region_bound Q A eta v x w z eps
        hQ hA heta hv heps hx hz (by rw [hw]; exact hsigma) (by rw [hw]; exact hxw)
      rw [unramified_defect_expansion Q A eta v x w z (by linarith) hR hV hD] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

/-- Actual unramified error coefficient mass, valid on both new reconstruction
lines.  Its prime exponent is strictly below −1/2. -/
theorem unramified_error_coefficient_mass (Q alpha eps sigma : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) :
    (unramifiedErrorCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      2880 * Q ^ (-(51 / 100 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta.le hv.le
    (by rw [hx]; linarith) (by rw [hz])
  let c := unramifiedErrorCoefficients Q A eta v x z
  have hb := cubicMass_le_of_vertical_bound Q (1 - alpha - 6 * eps) sigma
    (720 * Q ^ (-(51 / 100 : ℝ))) c.a c.b c.c c.d (by linarith) hsigma (by
      intro w hw
      have hh := unramifiedSelected_central_error Q alpha eps A eta v x w z
        hQ halpha halpha1 heps heps1 hA heta hv hx hw hz
      rw [unramified_error_expansion Q A eta v x w z (by linarith) hR hV hD heta hv] at hh
      exact hh)
  change cubicMass c.a c.b c.c c.d _ ≤ _
  nlinarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorUnramifiedMass -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorEulerExpansion; sha256 14efb7182bf6695aecca20f88310a0f04137e590c4e6a2d8b7578155b3da2022 -/
section
                                                         
                                                     
                                                

/-! Absolutely convergent expansion of a product of local polynomials.  Indexing
by finite prime subsets and their degree choices retains an explicit positive
scale for every term; regrouping equal ideals is unnecessary for Mellin inversion.
-/
noncomputable section
open scoped BigOperators NNReal
namespace Cycle25.Weighted.Numerator

def EulerIndex (ι : Type*) (n : ℕ) := Σ s : Finset ι, (s → Fin n)

def eulerTerm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (e : EulerIndex ι n) : ℂ :=
  ∏ p : e.1, f p.val (e.2 p)

def localMass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (p : ι) : ℝ :=
  ∑ j, ‖f p j‖

theorem euler_fiber_mass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, ‖eulerTerm f ⟨s, j⟩‖) = ∏ p ∈ s, localMass f p := by
  classical
  simp only [tsum_fintype, eulerTerm, norm_prod, localMass]
  exact (Fintype.prod_sum (fun p : s => fun j : Fin n => ‖f p.val j‖)).symm.trans
    (Finset.prod_coe_sort s (fun p => ∑ j, ‖f p j‖))

/-- Absolute convergence is obtained from summable local coefficient masses. -/
theorem euler_expansion_summable_norm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) : Summable (fun e : EulerIndex ι n => ‖eulerTerm f e‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro s
    exact (hasSum_fintype _).summable
  · simpa only [euler_fiber_mass, localMass] using
      summable_finsetProd_of_summable_nonneg
        (fun p => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hf

theorem euler_fiber_sum {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, eulerTerm f ⟨s, j⟩) = ∏ p ∈ s, ∑ j, f p j := by
  classical
  simp only [tsum_fintype, eulerTerm]
  rw [← Fintype.prod_sum]
  exact Finset.prod_coe_sort s (fun p => ∑ j, f p j)

/-- Exact product expansion, with no change to the original local factors. -/
theorem euler_expansion_hasProd {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    HasProd (fun p => 1 + ∑ j, f p j) (∑' e : EulerIndex ι n, eulerTerm f e) := by
  have hs := (euler_expansion_summable_norm f hf).of_norm
  have hsum := hs.hasSum.sigma (fun s => (hs.sigma_factor s).hasSum)
  simp only [euler_fiber_sum] at hsum
  exact hasProd_one_add_of_hasSum_prod hsum

theorem euler_expansion_eq_tprod {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∏' p, (1 + ∑ j, f p j)) = ∑' e : EulerIndex ι n, eulerTerm f e :=
  (euler_expansion_hasProd f hf).tprod_eq

theorem euler_expansion_mass_le_exp {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∑' e : EulerIndex ι n, ‖eulerTerm f e‖) ≤ Real.exp (∑' p, localMass f p) := by
  classical
  have hnonneg (p : ι) : 0 ≤ localMass f p :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs := euler_expansion_summable_norm f hf
  change (∑' e : (Σ s : Finset ι, s → Fin n), ‖eulerTerm f e‖) ≤ _
  rw [hs.tsum_sigma]
  simp only [euler_fiber_mass]
  apply (summable_finsetProd_of_summable_nonneg hnonneg hf).tsum_le_of_sum_le
  intro T
  calc
    (∑ s ∈ T, ∏ p ∈ s, localMass f p) ≤
        ∑ s ∈ (T.biUnion id).powerset, ∏ p ∈ s, localMass f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hs)
      · intro s hs hst
        exact Finset.prod_nonneg (fun p _ => hnonneg p)
    _ = ∏ p ∈ T.biUnion id, (1 + localMass f p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p ∈ T.biUnion id, localMass f p) :=
      Real.prod_one_add_le_exp_sum _ hnonneg
    _ ≤ _ := Real.exp_le_exp.mpr (hf.sum_le_tsum _ (fun _ _ => hnonneg _))

def positiveCpowHom (w : ℂ) : ℝ≥0 →* ℂ where
  toFun q := (q : ℂ) ^ w
  map_one' := by simp
  map_mul' q r := by
    convert! Complex.mul_cpow_ofReal_nonneg q.property r.property w using 1
    simp only [NNReal.coe_mul, Complex.ofReal_mul]
    rfl

def eulerScale {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0) (e : EulerIndex ι n) : ℝ≥0 :=
  ∏ p : e.1, Q p.val ^ (e.2 p).val

def eulerCoefficient {ι : Type*} {n : ℕ} (c : ι → Fin n → ℂ)
    (e : EulerIndex ι n) : ℂ := ∏ p : e.1, c p.val (e.2 p)

def localMellinTerm {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (p : ι) (j : Fin n) : ℂ :=
  c p j * ((Q p : ℂ) ^ (-w)) ^ j.val

theorem eulerTerm_mellin {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (e : EulerIndex ι n) :
    eulerTerm (localMellinTerm Q c w) e =
      eulerCoefficient c e * (eulerScale Q e : ℂ) ^ (-w) := by
  classical
  unfold eulerTerm localMellinTerm eulerCoefficient eulerScale
  rw [Finset.prod_mul_distrib]
  congr 1
  have he := map_prod (positiveCpowHom (-w)) (fun p : e.1 => Q p.val ^ (e.2 p).val)
    Finset.univ
  simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at he
  exact he.symm

theorem eulerScale_one_le {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (e : EulerIndex ι n) : 1 ≤ eulerScale Q e := by
  apply Finset.one_le_prod
  intro p hp
  exact one_le_pow₀ (hQ p.val)

theorem euler_coefficient_weight_eq {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ) (e : EulerIndex ι n) :
    ‖eulerTerm (localMellinTerm Q c (sigma : ℂ)) e‖ =
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma) := by
  rw [eulerTerm_mellin, norm_mul]
  have hpos : 0 < (eulerScale Q e : ℝ) := by
    have h := eulerScale_one_le Q hQ e
    exact lt_of_lt_of_le zero_lt_one h
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Complex.ofReal_re]

theorem euler_coefficients_summable_weight {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ)
    (hf : Summable (localMass (localMellinTerm Q c (sigma : ℂ)))) :
    Summable (fun e : EulerIndex ι n =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) := by
  simpa only [euler_coefficient_weight_eq Q hQ c sigma] using
    euler_expansion_summable_norm (localMellinTerm Q c (sigma : ℂ)) hf

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorEulerExpansion -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorPrimeExpansion; sha256 f819b71b8d633aee7831954c636c38465f2462cbb734d9a032b318be9aab2f95 -/
section
                                                         
                                                         

/-! Absolute Dirichlet expansion of the actual unramified correction product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def QuadraticCoefficients.vector (c : QuadraticCoefficients) : Fin 3 → ℂ := ![c.a,c.b,c.c]

theorem quadratic_vector_eval (c : QuadraticCoefficients) (T : ℂ) :
    (∑ j : Fin 3, c.vector j * T ^ j.val) = c.eval T := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.eval, quadratic, Fin.sum_univ_three]

theorem quadratic_vector_mass (c : QuadraticCoefficients) (Q : ℝ≥0) (w : ℂ)
    (hQ : 0 < (Q : ℝ)) :
    (∑ j : Fin 3, ‖c.vector j * ((Q : ℂ) ^ (-w)) ^ j.val‖) =
      c.mass ((Q : ℝ) ^ (-w.re)) := by
  simp [QuadraticCoefficients.vector, QuadraticCoefficients.mass, quadraticMass,
    Fin.sum_univ_three, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]

def primeScale (P : PrimeIdeal) : ℝ≥0 := P.val.absNorm

def actualUnramifiedCoefficients (η : Character) (u : FreeRow) (x z : ℂ)
    (P : PrimeIdeal) : Fin 3 → ℂ :=
  if P.val ∣ Ideal.span {u.val} then 0 else
    (unramifiedDefectCoefficients P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z).vector

theorem actual_unramified_local_expansion (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : PrimeIdeal) (hP : 4 ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    unramifiedFactor η u P x w z =
      1 + ∑ j : Fin 3, localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w P j := by
  by_cases hram : P.val ∣ Ideal.span {u.val}
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_true, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · simp only [unramifiedFactor, localMellinTerm, actualUnramifiedCoefficients,
      hram, ite_false]
    have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    obtain ⟨hR,hV,hD⟩ := unramified_denominators P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) hx hz
    have he := unramified_defect_expansion P.val.absNorm
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x w z (by linarith) hR hV hD
    rw [quadratic_vector_eval]
    change idealUnramifiedCorrection η u P x w z = _
    dsimp only [idealUnramifiedCorrection]
    change _ = 1 + (unramifiedDefectCoefficients _ _ _ _ _ _).eval _
    simpa only [primeScale, NNReal.coe_natCast, Complex.ofReal_natCast] using
      (eq_add_of_sub_eq he).trans (add_comm _ _)

theorem actual_unramified_local_mass (eps : ℝ) (η : Character) (u : FreeRow) (x w z : ℂ)
    (P : PrimeIdeal) (hP : 4 ≤ P.val.absNorm) (heps : 0 < eps)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    localMass (localMellinTerm primeScale (actualUnramifiedCoefficients η u x z) w) P ≤
      3 * firstPrimeDefectBound eps P := by
  unfold localMass localMellinTerm actualUnramifiedCoefficients
  split_ifs
  · simp only [Pi.zero_apply, zero_mul, norm_zero, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (firstPrimeDefectBound_nonneg eps P)
  · have hQ : (4 : ℝ) ≤ P.val.absNorm := by exact_mod_cast hP
    rw [quadratic_vector_mass _ _ _ (by change (0 : ℝ) < P.val.absNorm; linarith)]
    have hh := unramified_defect_coefficient_mass P.val.absNorm w.re eps
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      (idealRowHom u.val P.val) x z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) heps hx hz hw hxw
    simpa only [primeScale, NNReal.coe_natCast, firstPrimeDefectBound,
      show (720 : ℝ) = 3 * 240 by norm_num, mul_assoc] using hh

theorem actual_unramified_local_mass_summable (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    Summable (localMass (localMellinTerm
      (fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => actualUnramifiedCoefficients η u x z P.val) w)) := by
  apply (hS.summable.mul_left 3).of_nonneg_of_le
  · intro P
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P
    exact actual_unramified_local_mass eps η u x w z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hw hxw

theorem actual_unramified_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    unramifiedProduct S η u x w z =
      ∑' e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3,
        eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
          (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w) := by
  have hs := actual_unramified_local_mass_summable eps S hS η u x w z hx hz hw hxw
  have he := euler_expansion_eq_tprod _ hs
  simp only [eulerTerm_mellin] at he
  rw [← he]
  apply tprod_congr
  intro P
  exact actual_unramified_local_expansion η u x w z P.val
    (hS.norm_four P.val P.property) hx hz

theorem primeScale_one_le (P : PrimeIdeal) : 1 ≤ primeScale P := by
  have hn : 0 < P.val.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  change (1 : ℝ≥0) ≤ (P.val.absNorm : ℝ≥0)
  exact_mod_cast (Nat.succ_le_of_lt hn)

theorem actual_unramified_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    let Q := fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val
    let c := fun P : {P : PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
    Summable (fun e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ∧
    (∑' e : EulerIndex {P : PrimeIdeal // P.val ∉ S} 3,
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) ≤ Real.exp (1 / 2) := by
  dsimp only
  let Q := fun P : {P : PrimeIdeal // P.val ∉ S} => primeScale P.val
  let c := fun P : {P : PrimeIdeal // P.val ∉ S} => actualUnramifiedCoefficients η u x z P.val
  let f := localMellinTerm Q c (sigma : ℂ)
  have hf := actual_unramified_local_mass_summable eps S hS η u x (sigma : ℂ) z
    hx hz hsigma hxw
  have hQ : ∀ P, 1 ≤ Q P := fun P => primeScale_one_le P.val
  refine ⟨euler_coefficients_summable_weight Q hQ c sigma hf, ?_⟩
  have hb := euler_expansion_mass_le_exp f hf
  dsimp only [f] at hb
  simp only [euler_coefficient_weight_eq Q hQ c sigma] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hm : (∑' P, localMass f P) ≤
      ∑' P : {P : PrimeIdeal // P.val ∉ S}, 3 * firstPrimeDefectBound eps P.val := by
    apply hf.tsum_le_tsum _ (hS.summable.mul_left 3)
    intro P
    exact actual_unramified_local_mass eps η u x (sigma : ℂ) z P.val
      (hS.norm_four P.val P.property) hS.positive hx hz hsigma hxw
  rw [tsum_mul_left] at hm
  linarith [hS.small]

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorPrimeExpansion -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorRamifiedProduct; sha256 31a90bb781eb59b6e6fd3f9158b12e6566f0407478bbfc321ec67e415576c8a0 -/
section
                                                         
                                                              

/-! Finite coefficient expansion and subpower mass of the actual ramified product. -/
noncomputable section
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def actualRamifiedCoefficients (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : QuadraticCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedCorrectionCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

theorem actual_ramified_expansion (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z =
      (actualRamifiedCoefficients η u P hs x z).eval ((P.val.absNorm : ℂ) ^ (-w)) := by
  dsimp only [ramifiedCorrection, actualRamifiedCoefficients]
  erw [ramified_correction_expansion]
  simp only [span_primaryGenerator_of_supported P.val hs]

theorem actual_ramified_coefficient_mass (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ) ≤ P.val.absNorm) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (actualRamifiedCoefficients η u P hs x z).mass ((P.val.absNorm : ℝ) ^ (-sigma)) ≤ 579 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hh := ramified_correction_coefficient_mass p hp hg.1 hg.2
    (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z sigma
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) (actualACube_norm_le η p)
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp))
    hx hsigma hz hxw (multiplicity p u.val) (multiplicity_lt_six u p hp)
  change (ramifiedCorrectionCoefficients p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)).mass _ ≤ _
  simpa only [hspan] using hh

def ramifiedCoefficientVector (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (P : ramifiedPrimes S u) : Fin 3 → ℂ :=
  (actualRamifiedCoefficients η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x z).vector

def ramifiedTupleCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (j : ramifiedPrimes S u → Fin 3) : ℂ :=
  ∏ P, ramifiedCoefficientVector S hS η u x z P (j P)

def ramifiedTupleScale (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : ℝ≥0 := ∏ P, primeScale P.val ^ (j P).val

theorem ramified_product_expansion (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    ramifiedProduct S hS η u x w z =
      ∑ j : ramifiedPrimes S u → Fin 3,
        ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      (∏ P, ramifiedCoefficientVector S hS η u x z P (j P) *
        ((primeScale P.val : ℂ) ^ (-w)) ^ (j P).val) =
      ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w) := by
    rw [Finset.prod_mul_distrib]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    congr 1
    have hh := map_prod (positiveCpowHom (-w)) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simpa only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] using hh.symm
  simp_rw [← he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-w)) ^ j.val)]
  unfold ramifiedProduct
  change (∏ P : ramifiedPrimes S u,
    ramifiedCorrection η u P.val
      (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z) = _
  apply Finset.prod_congr rfl
  intro P hP
  rw [ramifiedCoefficientVector, quadratic_vector_eval, actual_ramified_expansion]
  rfl

theorem ramified_product_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (sigma : ℝ)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma) :
    (∑ j : ramifiedPrimes S u → Fin 3,
      ‖ramifiedTupleCoefficient S hS η u x z j‖ *
        (ramifiedTupleScale S u j : ℝ) ^ (-sigma)) ≤ 579 ^ (ramifiedPrimes S u).card := by
  have he (j : ramifiedPrimes S u → Fin 3) :
      ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma) =
      ∏ P : ramifiedPrimes S u,
        ‖ramifiedCoefficientVector S hS η u x z P (j P) *
          ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ (j P).val‖ := by
    have hpos : 0 < (ramifiedTupleScale S u j : ℝ) := by
      unfold ramifiedTupleScale
      exact_mod_cast Finset.prod_pos (fun (P : ramifiedPrimes S u) _ => pow_pos (lt_of_lt_of_le
        (by norm_num : (0 : ℝ≥0) < 1) (primeScale_one_le P.val)) _)
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(sigma : ℂ))
    simp only [Complex.neg_re, Complex.ofReal_re] at hn
    rw [← hn]
    simp only [Complex.neg_re, Complex.ofReal_re, ← norm_mul]
    unfold ramifiedTupleCoefficient ramifiedTupleScale
    have hh := map_prod (positiveCpowHom (-(sigma : ℂ))) (fun P : ramifiedPrimes S u =>
      primeScale P.val ^ (j P).val) Finset.univ
    simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
    rw [hh, ← Finset.prod_mul_distrib, norm_prod]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun P : ramifiedPrimes S u => fun j : Fin 3 =>
    ‖ramifiedCoefficientVector S hS η u x z P j * ((primeScale P.val : ℂ) ^ (-(sigma : ℂ))) ^ j.val‖)]
  calc
    _ ≤ ∏ _P : ramifiedPrimes S u, (579 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · intro P hP
        unfold ramifiedCoefficientVector
        rw [quadratic_vector_mass _ _ _ (by
          have := primeScale_one_le P.val
          exact lt_of_lt_of_le zero_lt_one this)]
        exact actual_ramified_coefficient_mass η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
          x z sigma hx hsigma hz hxw
    _ = _ := by simp

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorRamifiedProduct -/
