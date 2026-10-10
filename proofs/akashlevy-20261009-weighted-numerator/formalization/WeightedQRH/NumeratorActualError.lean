import WeightedQRH.NumeratorCorrectionExpansion
import WeightedQRH.NumeratorErrorMass
import OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.RestoreCorrection

/-! Quotient-free physical error factors, with coefficients independent of w. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
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

def actualRamifiedErrorCoefficients (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedErrorCoefficients p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x z (multiplicity p u.val)

def actualErrorCoefficients (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x z : ℂ) : CubicCoefficients :=
  if P.val ∣ Ideal.span {u.val} then actualRamifiedErrorCoefficients η u P hs x z
  else unramifiedErrorCoefficients P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x z

def rawErrorSlot (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val) * (P.val.absNorm : ℂ)^x) ((P.val.absNorm : ℂ)^(-w)) +
    supportedCorrection η u P x w z * star (idealRowHom u.val P.val)

theorem actual_error_expansion (η : Character) (u : FreeRow) (P : PrimeIdeal)
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

theorem actual_ramified_error_mass (η : Character) (u : FreeRow) (P : PrimeIdeal)
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

def repeatedDeficit (u : FreeRow) (P : PrimeIdeal) : ℝ≥0 :=
  if P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val
  then primeScale P else 1

theorem repeatedDeficit_one_le (u : FreeRow) (P : PrimeIdeal) : 1 ≤ repeatedDeficit u P := by
  unfold repeatedDeficit
  split_ifs
  · exact primeScale_one_le P
  · rfl

def errorSize (u : FreeRow) (P : PrimeIdeal) : ℝ :=
  if P.val ∣ Ideal.span {u.val} then (P.val.absNorm : ℝ)^(1 / 2 : ℝ)
  else (P.val.absNorm : ℝ)^(-(51 / 100 : ℝ))

theorem actual_error_coefficient_mass (η : Character) (u : FreeRow) (P : PrimeIdeal)
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

end WeightedQRH.Numerator
