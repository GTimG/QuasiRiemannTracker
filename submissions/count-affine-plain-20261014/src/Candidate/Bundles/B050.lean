/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B044
import Candidate.Bundles.B049
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
import OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.RestoreCorrection

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorCorrectionExpansion; sha256 edb1adf233a212176c98dff8fb19d3a5b4c1c3dbf0d112555c7af2ef18b88a98 -/
section
                                                          
                                               

/-! Absolute Mellin coefficient packet for the original complete correction. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem weighted_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ) (i : ι) (j : κ) :
    ‖A i * B j‖ * ((N i * M j : ℝ≥0) : ℝ) ^ (-sigma) =
      (‖A i‖ * (N i : ℝ) ^ (-sigma)) * (‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  rw [norm_mul, NNReal.coe_mul, Real.mul_rpow (show (0 : ℝ) ≤ N i from (N i).property) (show (0 : ℝ) ≤ M j from (M j).property)]
  ring

theorem mellin_product_term {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (w : ℂ) (i : ι) (j : κ) :
    (A i * B j) * ((N i * M j : ℝ≥0) : ℂ) ^ (-w) =
      (A i * (N i : ℂ) ^ (-w)) * (B j * (M j : ℂ) ^ (-w)) := by
  have hh := map_mul (positiveCpowHom (-w)) (N i) (M j)
  simp only [positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hh
  rw [hh]
  ring

theorem weighted_product_summable {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    Summable (fun ij : ι × κ => ‖A ij.1 * B ij.2‖ *
      ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)

theorem weighted_product_mass {ι κ : Type*} (A : ι → ℂ) (B : κ → ℂ)
    (N : ι → ℝ≥0) (M : κ → ℝ≥0) (sigma : ℝ)
    (hA : Summable (fun i => ‖A i‖ * (N i : ℝ) ^ (-sigma)))
    (hB : Summable (fun i => ‖B i‖ * (M i : ℝ) ^ (-sigma))) :
    (∑' ij : ι × κ, ‖A ij.1 * B ij.2‖ * ((N ij.1 * M ij.2 : ℝ≥0) : ℝ) ^ (-sigma)) =
      (∑' i, ‖A i‖ * (N i : ℝ) ^ (-sigma)) *
      (∑' j, ‖B j‖ * (M j : ℝ) ^ (-sigma)) := by
  simp_rw [weighted_product_term]
  exact (hA.tsum_mul_tsum hB
    (hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity))).symm

def CorrectionIndex (S : Finset (Ideal O)) (u : FreeRow) :=
  (ramifiedPrimes S u → Fin 3) × EulerIndex {P : ProbePhysical.PrimeIdeal // P.val ∉ S} 3

def correctionCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (e : CorrectionIndex S u) : ℂ :=
  ramifiedTupleCoefficient S hS η u x z e.1 *
    eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2

def correctionScale (S : Finset (Ideal O)) (u : FreeRow) (e : CorrectionIndex S u) : ℝ≥0 :=
  ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2

theorem ramifiedTupleScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (j : ramifiedPrimes S u → Fin 3) : 1 ≤ ramifiedTupleScale S u j := by
  apply Finset.one_le_prod
  intro P hP
  exact one_le_pow₀ (primeScale_one_le P.val)

theorem correctionScale_one_le (S : Finset (Ideal O)) (u : FreeRow)
    (e : CorrectionIndex S u) : 1 ≤ correctionScale S u e := by
  unfold correctionScale
  exact one_le_mul_of_one_le_of_one_le (ramifiedTupleScale_one_le S u e.1)
    (eulerScale_one_le (fun P : {P : ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val)
      (fun P => primeScale_one_le P.val) e.2)

theorem continuedCorrection_coefficient_mass (eps sigma : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hsigma : -(1 / 100 : ℝ) ≤ sigma) (hxw : 1 + eps ≤ x.re + sigma) :
    Summable (fun e : CorrectionIndex S u => ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ∧
    (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
      (correctionScale S u e : ℝ) ^ (-sigma)) ≤
      579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2) := by
  obtain ⟨hU,hUm⟩ := actual_unramified_coefficient_mass eps sigma S hfirst η u x z hx hz hsigma hxw
  have hR := ramified_product_coefficient_mass S hS η u x z sigma hx hsigma hz
    (by linarith [hfirst.positive])
  have hRs := (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
    ‖ramifiedTupleCoefficient S hS η u x z j‖ * (ramifiedTupleScale S u j : ℝ) ^ (-sigma))).summable
  refine ⟨weighted_product_summable _ _ _ _ sigma hRs hU, ?_⟩
  change (∑' e : (ramifiedPrimes S u → Fin 3) × EulerIndex {P : ProbePhysical.PrimeIdeal // P.val ∉ S} 3,
    ‖ramifiedTupleCoefficient S hS η u x z e.1 *
      eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e.2‖ *
    ((ramifiedTupleScale S u e.1 * eulerScale (fun P => primeScale P.val) e.2 : ℝ≥0) : ℝ) ^ (-sigma)) ≤ _
  rw [weighted_product_mass _ _ _ _ sigma hRs hU, tsum_fintype]
  exact mul_le_mul hR hUm (tsum_nonneg (fun _ => by positivity)) (by positivity)

theorem continuedCorrection_coefficient_expansion (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + eps ≤ x.re + w.re) :
    continuedCorrection S hS η u x w z =
      ∑' e : CorrectionIndex S u, correctionCoefficient S hS η u x z e *
        (correctionScale S u e : ℂ) ^ (-w) := by
  have hU := (actual_unramified_coefficient_mass eps w.re S hfirst η u x z hx hz hw hxw).1
  have hUn : Summable (fun e : EulerIndex {P : ProbePhysical.PrimeIdeal // P.val ∉ S} 3 =>
      ‖eulerCoefficient (fun P => actualUnramifiedCoefficients η u x z P.val) e *
        (eulerScale (fun P => primeScale P.val) e : ℂ) ^ (-w)‖) := by
    convert hU using 1
    ext e
    have hp : 0 < (eulerScale (fun P : {P : ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val) e : ℝ) := by
      have hh := eulerScale_one_le (fun P : {P : ProbePhysical.PrimeIdeal // P.val ∉ S} => primeScale P.val)
        (fun P => primeScale_one_le P.val) e
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re]
  rw [continuedCorrection, ramified_product_expansion,
    actual_unramified_expansion eps S hfirst η u x w z hx hz hw hxw]
  have hprod := tsum_mul_tsum_of_summable_norm
    (hasSum_fintype (fun j : ramifiedPrimes S u → Fin 3 =>
      ‖ramifiedTupleCoefficient S hS η u x z j * (ramifiedTupleScale S u j : ℂ) ^ (-w)‖)).summable hUn
  simp only [tsum_fintype] at hprod
  rw [hprod]
  apply tsum_congr
  intro e
  exact (mellin_product_term _ _ _ _ w e.1 e.2).symm

theorem continuedCorrection_coefficient_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps sigma : ℝ) (S : Finset (Ideal O))
      (hS : SourceExclusions S) (hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (x z : ℂ), (51 / 100 : ℝ) ≤ x.re → (17 / 50 : ℝ) ≤ z.re →
      -(1 / 100 : ℝ) ≤ sigma → 1 + eps ≤ x.re + sigma →
      (∑' e : CorrectionIndex S u, ‖correctionCoefficient S hS η u x z e‖ *
        (correctionScale S u e : ℝ) ^ (-sigma)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 579 epsilon
    (by norm_num) hepsilon
  refine ⟨C * Real.exp (1 / 2), by positivity, ?_⟩
  intro eps sigma S hS hfirst η u x z hx hz hsigma hxw
  have hm := (continuedCorrection_coefficient_mass eps sigma S hS hfirst η u x z
    hx hz hsigma hxw).2
  have hc : (579 : ℝ) ^ (ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  exact hm.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq (by ring))

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorCorrectionExpansion -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorMass; sha256 e74a11337084380177dd82718ac14c570ec3fca9e7546bb7fa1f25958b39b010 -/
section
                                                         

/-! Absolute coefficient bounds for the quotient-free local errors. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

def ramifiedErrorCoefficients (eta a rho x z : ℂ) (j : ℕ) : CubicCoefficients :=
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  let d := ramifiedStrictCoefficient p hp hg eta a rho x z j
  ⟨c.a, c.b + d, c.c, 0⟩

theorem ramified_error_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      (ramifiedErrorCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hr := ramified_regular_expansion p hp hg eta a rho x w z j
  have hs := ramified_strict_expansion p hp hg eta a rho x w z j
  rw [hs] at hr
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.eval,cubic]
  rw [eq_add_of_sub_eq hr]
  dsimp only [QuadraticCoefficients.eval,quadratic]
  ring

theorem ramified_error_mass_le (eta a rho x z : ℂ) (j : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (ramifiedErrorCoefficients p hp hg eta a rho x z j).mass r ≤
      (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass r +
      ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ * r := by
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.mass,cubicMass,
    QuadraticCoefficients.mass,quadraticMass]
  simp only [norm_zero,zero_mul,add_zero]
  have hh := mul_le_mul_of_nonneg_right
    (norm_add_le (ramifiedRegularCoefficients p hp hg eta a rho x z j).b
      (ramifiedStrictCoefficient p hp hg eta a rho x z j)) hr
  linarith

/-- Only repeated ramified labels cost a factor Q^rho on the left line. -/
theorem ramified_error_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a phase x z : ℂ) (alpha eps rho : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hphase : phase ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) (j : ℕ) (hj : j < 6) :
    (ramifiedErrorCoefficients p hp hg eta a phase x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(1 / 2 - rho))) ≤
      1161 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) *
        (if 2 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ rho else 1) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0 < Q := by dsimp only [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp only [Q]; linarith
  have hR := ramified_regular_coefficient_mass p hp hg hc eta a phase x z
    alpha eps (1 / 2 - rho) hQ heta ha hphase halpha halpha1 heps heps1 hx hz hline j hj
  have hM := ramified_error_mass_le p hp hg eta a phase x z j
    (Q ^ (-(1 / 2 - rho))) (Real.rpow_nonneg hQ0.le _)
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hz' : (17 / 50 : ℝ) ≤ z.re := hz.ge
  by_cases hj2 : 2 ≤ j
  · rw [if_pos hj2]
    have hS := ramified_strict_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j hj
    have he : Q ^ (1 - (1 / 2 - rho)) = Q ^ (1 / 2 : ℝ) * Q ^ rho := by
      rw [←Real.rpow_add hQ0]
      congr 1
      ring
    change _ ≤ 6 * Q ^ (1 - (1 / 2 - rho)) at hS
    rw [he] at hS
    have hpow : 1 ≤ Q ^ rho := Real.one_le_rpow hQ1 hrho
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ) * Q ^ rho
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    nlinarith [Real.rpow_nonneg hQ0.le (1 / 2 : ℝ)]
  · rw [if_neg hj2,mul_one]
    have hS := ramified_boundary_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j (by omega)
    have hpow : Q ^ (-(1 / 2 - rho)) ≤ Q ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    change _ ≤ 6 * Q ^ (-(1 / 2 - rho)) at hS
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ)
    linarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorMass -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorActualError; sha256 9132d48be10872d201a3c5a7d8b8f8d2550605cd850a6015da19f3e99a0124b1 -/
section
                                                              
                                                    
                                                              
                                                              

/-! Quotient-free physical error factors, with coefficients independent of w. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def CubicCoefficients.vector (c : CubicCoefficients) : Fin 4 → ℂ := ![c.a,c.b,c.c,c.d]

theorem cubic_vector_eval (c : CubicCoefficients) (T : ℂ) :
    (∑ j : Fin 4, c.vector j * T ^ j.val) = c.eval T := by
  simp [CubicCoefficients.vector,CubicCoefficients.eval,cubic,Fin.sum_univ_four]

theorem cubic_vector_mass (c : CubicCoefficients) (Q : ℝ≥0) (w : ℂ)
    (hQ : 0 < (Q : ℝ)) :
    (∑ j : Fin 4, ‖c.vector j * ((Q : ℂ) ^ (-w)) ^ j.val‖) =
      c.mass ((Q : ℝ) ^ (-w.re)) := by
  simp [CubicCoefficients.vector,CubicCoefficients.mass,cubicMass,
    Fin.sum_univ_four,norm_mul,norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.neg_re]

def actualRamifiedErrorCoefficients (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedErrorCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

def actualErrorCoefficients (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  if P.val ∣ Ideal.span {u.val} then actualRamifiedErrorCoefficients η u P hs x z
  else unramifiedErrorCoefficients P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x z

def rawErrorSlot (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val) * (P.val.absNorm : ℂ)^x) ((P.val.absNorm : ℂ)^(-w)) +
    supportedCorrection η u P x w z * star (idealRowHom u.val P.val)

theorem actual_error_expansion (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    rawErrorSlot η u P hs x w z =
      (actualErrorCoefficients η u P hs x z).eval ((P.val.absNorm : ℂ)^(-w)) := by
  by_cases hd : P.val ∣ Ideal.span {u.val}
  · simp only [rawErrorSlot,row_phase_ramified u P hd,star_zero,mul_zero,add_zero,
      actualErrorCoefficients,if_pos hd]
    rw [continuedCompensatedLocal_ramified η u P hs hd]
    dsimp only [actualRamifiedErrorCoefficients]
    erw [ramified_error_expansion]
    simp only [span_primaryGenerator_of_supported P.val hs]
  · have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
    have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
    have hv := row_phase_norm_one_of_not_dvd u P hs hd
    have hV : ‖coordV P.val.absNorm z‖ < 1 :=
      (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖ < 1 :=
      (coordR_norm_le _ (by linarith) _ x z hA).trans_lt
        ((rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num))
    obtain ⟨hRn,hVn,hDn⟩ := unramified_denominators _ _ _ _ x z hQ hA heta.le hv.le hx hz
    simp only [rawErrorSlot,actualErrorCoefficients,if_neg hd,
      supportedCorrection,dif_pos hs,if_neg hd]
    rw [continuedCompensatedLocal_unramified η u P hs hd x w z hV hR]
    exact unramified_error_expansion _ _ _ _ x w z (by linarith) hRn hVn hDn heta hv

theorem actual_ramified_error_mass (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) (alpha eps rho : ℝ)
    (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (actualRamifiedErrorCoefficients η u P hs x z).mass
      ((P.val.absNorm : ℝ)^(-(1 / 2 - rho))) ≤
      1161 * (P.val.absNorm : ℝ)^(1 / 2 : ℝ) *
        (if 2 ≤ multiplicity (primaryGenerator P.val) u.val then (P.val.absNorm : ℝ)^rho else 1) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p} = P.val := span_primaryGenerator_of_supported P.val hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hh := ramified_error_coefficient_mass p hp hg.1 hg.2
    (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z
    alpha eps rho (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) (actualACube_norm_le η p)
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp))
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  change (ramifiedErrorCoefficients p hp hg.1 (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x z
    (multiplicity p u.val)).mass _ ≤ _
  simpa only [hspan] using hh

def repeatedDeficit (u : FreeRow) (P : ProbePhysical.PrimeIdeal) : ℝ≥0 :=
  if P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val
  then primeScale P else 1

theorem repeatedDeficit_one_le (u : FreeRow) (P : ProbePhysical.PrimeIdeal) : 1 ≤ repeatedDeficit u P := by
  unfold repeatedDeficit
  split_ifs
  · exact primeScale_one_le P
  · rfl

def errorSize (u : FreeRow) (P : ProbePhysical.PrimeIdeal) : ℝ :=
  if P.val ∣ Ideal.span {u.val} then (P.val.absNorm : ℝ)^(1 / 2 : ℝ)
  else (P.val.absNorm : ℝ)^(-(51 / 100 : ℝ))

theorem actual_error_coefficient_mass (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (actualErrorCoefficients η u P hs x z).mass ((P.val.absNorm : ℝ)^(-(1 / 2 - rho))) ≤
      2880 * errorSize u P * (repeatedDeficit u P : ℝ)^rho := by
  by_cases hd : P.val ∣ Ideal.span {u.val}
  · have hh := actual_ramified_error_mass η u P hs x z alpha eps rho hQ
      halpha halpha1 heps heps1 hx hz hrho hrho1 hline
    simp only [actualErrorCoefficients,if_pos hd,errorSize,repeatedDeficit,hd,true_and,
      primeScale] at *
    split_ifs with hj
    · simp only [ite_eq_left hj] at hh
      simp only [NNReal.coe_natCast]
      exact hh.trans (by gcongr <;> norm_num)
    · simp only [ite_eq_right hj,mul_one] at hh
      simp only [NNReal.coe_one,Real.one_rpow,mul_one]
      exact hh.trans (by gcongr <;> norm_num)
  · have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
    have hv := row_phase_norm_one_of_not_dvd u P hs hd
    simp only [actualErrorCoefficients,if_neg hd,errorSize,repeatedDeficit,hd,false_and,
      if_false,NNReal.coe_one,Real.one_rpow,mul_one]
    exact unramified_error_coefficient_mass _ alpha eps (1 / 2 - rho) _ _ _ x z
      hQ halpha halpha1 heps heps1 (actualAPhase_norm_le_one η _) heta hv hx hz hline

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorActualError -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.RowConductor; sha256 838c04825723588bc22f6cd01491b01e05b39de30b4ad9e6413928a121c581e7 -/
section
                                            
                                                               
                                                                         

/-! A radical-sized presentation of the actual physical row, with its exact
smoothed sums and the same reflected character coefficients. The radical
periodicity theorem is upstream; this module connects it to the natural
primitive/deletion reflection API without making a primitive-choice assumption.
-/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.RowConductor
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor ProbeHighRowFamily CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O

theorem idealCoeff_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff τ I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span _ hn, idealCoeff_span _ hn, he]

theorem inverse_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (n : O) :
    elementCoeff χ.inverse n = elementCoeff τ.inverse n := by
  rw [elementCoeff_inverse, elementCoeff_inverse, he]

theorem polynomial_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    (inv : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) :
    HeckeDyadic.polynomial χ inv W D σ ω = HeckeDyadic.polynomial τ inv W D σ ω := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  simp only [HeckeDyadic.summand, HeckeDyadic.coefficient,
    idealCoeff_eq_of_elementCoeff_eq χ τ he I.val]

theorem principal_iff_of_equal_elements (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) :
    χ.residue = 1 ↔ τ.residue = 1 := by
  apply HeckeFiniteDeletion.principal_iff_of_mask χ τ
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc, idealCoeff_eq_of_elementCoeff_eq χ τ he]
  · rw [ite_eq_right hc]
    simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem LFunction_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    LFunction χ s = LFunction τ s := by
  unfold LFunction
  rw [continuedLattice_eq_of_elementCoeff_eq χ τ he hs hs1]

/-- This preserves all coefficients, including their zeros at deleted primes. -/
theorem exists_row_small_presentation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ τ : Character,
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n := by
  obtain ⟨τ, hn, he⟩ := rawRow_small_presentation u
  refine ⟨τ.excludePrimes S hS, ?_, equal_elements_excludePrimes _ τ he S hS⟩
  change (τ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

/-- A combined primitive-plus-redundant scale already pays for all finite
Euler deletions. Its selected-prime deficit therefore does not require
claiming that the redundant primes belong to a fixed set. -/
theorem reflected_scale_selected_deficit
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, (P i).absNorm ^ (e i - 1) ≤
        fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hr := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => by have := he i; omega) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i - 1) := Nat.mul_le_mul_right _ (hcap.trans hτ)
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hr

theorem reflected_scale_selected_deficit_real
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    ((ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, ((P i).absNorm : ℝ) ^ (e i - 1) ≤
        (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv

theorem reflected_scale_pos (τ ψ : Character) :
    0 < (ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm := by
  apply mul_pos
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (redundantIdeal_ne_zero τ.modulus ψ.modulus))

/-- Exact original physical numerator reflection using a radical-sized
presentation. The output preserves the physical row and its inverse on all
ideals; the RHS is the actual upstream retained/discarded reflection. -/
theorem row_original_split (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue ≠ 1) :
    ∃ (τ ψ : Character) (g : ℂ),
      (∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n) ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u).inverse I = idealCoeff τ.inverse I) ∧
      τ.residue ≠ 1 ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.residue ≠ 1 ∧ ‖g‖ = 1 ∧
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
        τ.modulus.absNorm ∧
      (∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) →
        Function.Injective P → ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
        (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
        (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
          ∏ i, (P i).absNorm ^ (e i - 1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm) ∧
      ∀ (G : 𝓢(ℝ, ℂ)) (X R : ℝ), 0 < X →
        HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0 =
          g * (retainedSchwartz τ ψ G X R + discardedSchwartz τ ψ G X R) := by
  obtain ⟨τ, hτ, he⟩ := exists_row_small_presentation S hS u
  have hnτ : τ.residue ≠ 1 := fun h => hn ((principal_iff_of_equal_elements _ τ he).mpr h)
  obtain ⟨ψ, g, hp, hnp, hg, hcap, hsplit⟩ := original_split τ hnτ
  refine ⟨τ, ψ, g, he, ?_, hnτ, hp, hnp, hg, hτ, hcap, ?_, ?_⟩
  · exact idealCoeff_eq_of_elementCoeff_eq _ _ (inverse_elementCoeff_eq _ _ he)
  · intro k P hP hdis e he hdiv
    exact reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv
  · intro G X R hX
    rw [polynomial_eq_of_elementCoeff_eq _ τ he]
    exact hsplit G X R hX

end Cycle25.Weighted.RowConductor
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.RowConductor -/
