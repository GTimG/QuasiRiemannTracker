/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B050
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorDeficit; sha256 281f03a45cd9fe06a40a490c9582b573ca2e01ed40ea429716d8c180c66a083e -/
section
                                                      
                                              

/-! The exact multiplicative conductor deficit of repeated physical error primes. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem repeated_prime_square_dvd (u : FreeRow) (P : HeckeInverseAmplification.PrimeIdeal) (hs : Supported P.val)
    (hj : 2 ≤ multiplicity (primaryGenerator P.val) u.val) :
    P.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hm : p ^ multiplicity p u.val ∣ u.val := ⟨unitPart u p hp, (unitPart_spec u p hp).1⟩
  have hdiv : p ^ 2 ∣ u.val := (pow_dvd_pow p hj).trans hm
  rw [←span_primaryGenerator_of_supported P.val hs,Ideal.span_singleton_pow]
  exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hdiv

def repeatedErrorPrimes (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) : Finset HeckeInverseAmplification.PrimeIdeal :=
  T.filter (fun P => P.val ∣ Ideal.span {u.val} ∧ 2 ≤ multiplicity (primaryGenerator P.val) u.val)

theorem repeated_deficit_product (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal) :
    (∏ P : T, (repeatedDeficit u P.val : ℝ)) =
      ∏ P ∈ repeatedErrorPrimes u T, (P.val.absNorm : ℝ) := by
  calc
    _ = ∏ P ∈ T, (repeatedDeficit u P : ℝ) := Finset.prod_coe_sort T _
    _ = _ := by
      simp only [repeatedDeficit,repeatedErrorPrimes,Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro P hP
      split_ifs <;> rfl


theorem radical_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) :
    ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
        (Ideal.span {u.val} : Ideal O).absNorm := by
  let R := repeatedErrorPrimes u T
  have hdiv (P : R) : P.val.val ^ 2 ∣ (Ideal.span {u.val} : Ideal O) := by
    have hm := Finset.mem_filter.mp P.property
    exact repeated_prime_square_dvd u P.val (hT P.val hm.1) hm.2.2
  have hh := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    (fun P : R => P.val.val) (fun P => P.val.property)
    (fun P Q h => Subtype.ext (Subtype.ext h)) (fun _ => 2)
    (fun _ => by norm_num) hdiv
  simp only [show (2 : ℕ) - 1 = 1 by norm_num,pow_one] at hh
  have hh' : ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) *
      (∏ P : R, (P.val.val.absNorm : ℝ)) ≤ (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast hh
  rw [repeated_deficit_product]
  have he := Finset.prod_coe_sort R (fun P : HeckeInverseAmplification.PrimeIdeal => (P.val.absNorm : ℝ))
  rw [he] at hh'
  exact hh'

theorem conductor_repeated_deficit (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 ≤ C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    Cu * (∏ P : T, (repeatedDeficit u P.val : ℝ)) ≤
      C * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hd := radical_repeated_deficit u T hT
  have hn : 0 ≤ ∏ P : T, (repeatedDeficit u P.val : ℝ) :=
    Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)
  exact (mul_le_mul_of_nonneg_right hCu hn).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hC)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorDeficit -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorFinitePacket; sha256 fe661178e1a23003c4983994a653f56f8bc6848f6974b02fe372753c0e71b6e8 -/
section
                                                      

/-! Finite products of physical local coefficient polynomials. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def finiteCoefficient {ι : Type*} [Fintype ι] {n : ℕ} (c : ι → Fin n → ℂ)
    (j : ι → Fin n) : ℂ := ∏ i, c i (j i)

def finiteScale {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (j : ι → Fin n) : ℝ≥0 := ∏ i, Q i ^ (j i).val

theorem finiteScale_one_le {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (j : ι → Fin n) : 1 ≤ finiteScale Q j := by
  exact Finset.one_le_prod (fun i _ => one_le_pow₀ (hQ i))

theorem finite_packet_term {ι : Type*} [Fintype ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (j : ι → Fin n) :
    (∏ i, c i (j i) * ((Q i : ℂ)^(-w))^(j i).val) =
      finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Finset.prod_mul_distrib]
  unfold finiteCoefficient finiteScale
  congr 1
  have hh := map_prod (positiveCpowHom (-w)) (fun i => Q i ^ (j i).val) Finset.univ
  simpa only [map_pow,positiveCpowHom,MonoidHom.coe_mk,OneHom.coe_mk] using hh.symm

theorem finite_packet_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) :
    (∏ i, ∑ j : Fin n, c i j * ((Q i : ℂ)^(-w))^j.val) =
      ∑ j : ι → Fin n, finiteCoefficient c j * (finiteScale Q j : ℂ)^(-w) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_packet_term Q c w j

theorem finite_packet_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ i, 1 ≤ Q i) (c : ι → Fin n → ℂ) (sigma : ℝ) :
    (∑ j : ι → Fin n, ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma)) =
      ∏ i, ∑ j : Fin n, ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖ := by
  have he (j : ι → Fin n) : ‖finiteCoefficient c j‖ * (finiteScale Q j : ℝ)^(-sigma) =
      ∏ i, ‖c i (j i) * ((Q i : ℂ)^(-(sigma : ℂ)))^(j i).val‖ := by
    rw [←norm_prod,finite_packet_term,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by
        have hh := finiteScale_one_le Q hQ j
        exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simp only [Complex.neg_re,Complex.ofReal_re]
  simp_rw [he]
  exact (Fintype.prod_sum (fun i : ι => fun j : Fin n =>
    ‖c i j * ((Q i : ℂ)^(-(sigma : ℂ)))^j.val‖)).symm

def errorCoefficientVector (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (P : T) : Fin 4 → ℂ :=
  (actualErrorCoefficients η u P.val (hT P.val P.property) x z).vector

def errorTupleCoefficient (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (j : T → Fin 4) : ℂ :=
  finiteCoefficient (errorCoefficientVector η u T hT x z) j

def errorTupleScale (T : Finset ProbePhysical.PrimeIdeal) (j : T → Fin 4) : ℝ≥0 :=
  finiteScale (fun P : T => primeScale P.val) j

theorem error_product_expansion (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    (∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x w z) =
      ∑ j : T → Fin 4, errorTupleCoefficient η u T hT x z j * (errorTupleScale T j : ℂ)^(-w) := by
  calc
    _ = ∏ P : T, ∑ j : Fin 4, errorCoefficientVector η u T hT x z P j *
        ((primeScale P.val : ℂ)^(-w))^j.val := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [errorCoefficientVector,cubic_vector_eval,actual_error_expansion η u P.val _
        (hη P.val P.property) x w z (hQ P.val P.property) hx hz]
      rfl
    _ = _ := finite_packet_expansion (fun P : T => primeScale P.val)
      (errorCoefficientVector η u T hT x z) w

theorem error_product_coefficient_mass (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) :
    (∑ j : T → Fin 4, ‖errorTupleCoefficient η u T hT x z j‖ *
      (errorTupleScale T j : ℝ)^(-(1 / 2 - rho))) ≤
      ∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho := by
  have hmass := finite_packet_mass (fun P : T => primeScale P.val)
    (fun P => primeScale_one_le P.val) (errorCoefficientVector η u T hT x z) (1 / 2 - rho)
  apply le_trans (le_of_eq hmass)
  apply Finset.prod_le_prod₀
  · intro P hP
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · intro P hP
    unfold errorCoefficientVector
    rw [cubic_vector_mass _ _ _ (by
      have hh := primeScale_one_le P.val
      exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hh))]
    simpa only [Complex.ofReal_re,primeScale,NNReal.coe_natCast] using
      actual_error_coefficient_mass η u P.val _ (hη P.val P.property)
        x z alpha eps rho (hQ P.val P.property) halpha halpha1 heps heps1 hx hz hrho hrho1 hline

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorFinitePacket -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorPacket; sha256 1f47ea1eda6274e15c4bb0a2ea6173428ab7780a41fee215d00717bae64cd399 -/
section
                                                       
                                                             

/-! Actual correction times arbitrary finite error slots as one absolutely
convergent coefficient series on both reconstruction lines. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def ErrorPacketIndex (S : Finset (Ideal O)) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) :=
  (T → Fin 4) × CorrectionIndex (markExclusions S T) u

def errorPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (e : ErrorPacketIndex S u T) : ℂ :=
  errorTupleCoefficient η u T hT x z e.1 *
    correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e.2

def errorPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (e : ErrorPacketIndex S u T) : ℝ≥0 :=
  errorTupleScale T e.1 * correctionScale (markExclusions S T) u e.2

theorem errorPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (e : ErrorPacketIndex S u T) : 1 ≤ errorPacketScale S u T e := by
  unfold errorPacketScale errorTupleScale
  exact one_le_mul_of_one_le_of_one_le
    (finiteScale_one_le (fun P : T => primeScale P.val) (fun P => primeScale_one_le P.val) e.1)
    (correctionScale_one_le (markExclusions S T) u e.2)

def errorProductSize (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) : ℝ :=
  ∏ P : T, 2880 * errorSize u P.val

def errorProductDeficit (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) : ℝ :=
  ∏ P : T, (repeatedDeficit u P.val : ℝ)

theorem errorProductSize_nonneg (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) :
    0 ≤ errorProductSize u T := by
  apply Finset.prod_nonneg
  intro P hP
  unfold errorSize
  split_ifs <;> positivity

theorem errorProductDeficit_one_le (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) :
    1 ≤ errorProductDeficit u T := by
  apply Finset.one_le_prod₀
  intro P hP
  exact_mod_cast repeatedDeficit_one_le u P.val

theorem error_product_mass_factor (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) (rho : ℝ) :
    (∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho) =
      errorProductSize u T * errorProductDeficit u T ^ rho := by
  rw [Finset.prod_mul_distrib]
  unfold errorProductSize errorProductDeficit
  congr 1
  exact (Real.finsetProd_rpow Finset.univ (fun P : T => (repeatedDeficit u P.val : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) rho)

theorem error_packet_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho)) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 - rho))) ∧
    (∑' e : ErrorPacketIndex S u T, ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 - rho))) ≤
      (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2)) *
        errorProductSize u T * errorProductDeficit u T ^ rho := by
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  obtain ⟨hH,hHm⟩ := continuedCorrection_coefficient_mass firsteps (1 / 2 - rho)
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx' hz.ge hleft hmargin
  have hE := error_product_coefficient_mass η u T hT hη x z alpha eps rho hQ
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline
  rw [error_product_mass_factor] at hE
  have hEs := (hasSum_fintype (fun j : T → Fin 4 =>
    ‖errorTupleCoefficient η u T hT x z j‖ * (errorTupleScale T j : ℝ)^(-(1 / 2 - rho)))).summable
  refine ⟨weighted_product_summable _ _ _ _ (1 / 2 - rho) hEs hH, ?_⟩
  change (∑' e : (T → Fin 4) × CorrectionIndex (markExclusions S T) u,
    ‖errorTupleCoefficient η u T hT x z e.1 *
      correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e.2‖ *
    ((errorTupleScale T e.1 * correctionScale (markExclusions S T) u e.2 : ℝ≥0) : ℝ)^(-(1 / 2 - rho))) ≤ _
  rw [weighted_product_mass _ _ _ _ (1 / 2 - rho) hEs hH,tsum_fintype]
  exact (mul_le_mul hE hHm (tsum_nonneg (fun _ => by positivity))
    (mul_nonneg (errorProductSize_nonneg u T) (Real.rpow_nonneg
      (le_trans zero_le_one (errorProductDeficit_one_le u T)) rho))).trans_eq (by ring)

theorem error_packet_expansion (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + firsteps ≤ x.re + w.re) :
    (∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x w z) *
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z =
    ∑' e : ErrorPacketIndex S u T, errorPacketCoefficient S hS η u T hT x z e *
      (errorPacketScale S u T e : ℂ)^(-w) := by
  have hC := (continuedCorrection_coefficient_mass firsteps w.re
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx hz hw hxw).1
  have hCn : Summable (fun e : CorrectionIndex (markExclusions S T) u =>
    ‖correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e *
      (correctionScale (markExclusions S T) u e : ℂ)^(-w)‖) := by
    convert hC using 1
    ext e
    have hp : 0 < (correctionScale (markExclusions S T) u e : ℝ) :=
      lt_of_lt_of_le zero_lt_one (by exact_mod_cast correctionScale_one_le (markExclusions S T) u e)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re]
  rw [error_product_expansion η u T hT hη x w z hQ hx hz,
    continuedCorrection_coefficient_expansion firsteps (markExclusions S T)
      (markedSourceExclusions S hS T) (marked_firstTail firsteps S hfirst T)
      η u x w z hx hz hw hxw]
  have hprod := tsum_mul_tsum_of_summable_norm
    (hasSum_fintype (fun j : T → Fin 4 =>
      ‖errorTupleCoefficient η u T hT x z j * (errorTupleScale T j : ℂ)^(-w)‖)).summable hCn
  simp only [tsum_fintype] at hprod
  rw [hprod]
  apply tsum_congr
  intro e
  exact (mellin_product_term _ _ _ _ w e.1 e.2).symm

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorPacket -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorMassDamping; sha256 6f40896e0fb14e7a4351d4f933b0b28c716b8de44ebc5803288e07f5a25b6835 -/
section
                                                      
                                                  

/-! Two-line absolute coefficient masses and actual conductor absorption. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

theorem coefficient_left_weight (A : ℂ) (N L rho : ℝ) (hN : 0 < N) (hL : 0 ≤ L) :
    ‖A‖ * N ^ (-(1 / 2 : ℝ)) * (L * N)^rho =
      L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.mul_rpow hL hN.le]
  calc
    _ = L^rho * ‖A‖ * (N^(-(1 / 2 : ℝ)) * N^rho) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN]
      rw [show -(1 / 2 : ℝ) + rho = -(1 / 2 - rho) by ring]
      ring

theorem coefficient_max_weight_bound (A : ℂ) (N L rho : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hrho : 0 ≤ rho) :
    ‖A‖ * N^(-(1 / 2 : ℝ)) * max 1 (L * N)^rho ≤
      ‖A‖ * N^(-(1 / 2 : ℝ)) + L^rho * (‖A‖ * N^(-(1 / 2 - rho))) := by
  rw [Real.rpow_max zero_le_one (mul_nonneg hL hN.le) hrho,Real.one_rpow]
  have ht : 0 ≤ (L * N)^rho := Real.rpow_nonneg (mul_nonneg hL hN.le) rho
  calc
    _ ≤ ‖A‖ * N^(-(1 / 2 : ℝ)) * (1 + (L * N)^rho) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le (by linarith) (by linarith)
    _ = _ := by rw [mul_add,mul_one,coefficient_left_weight A N L rho hN hL]

theorem mass_deficit_absorption (M B D L rho : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hmass : M ≤ B * D^rho) (hcap : L * D ≤ 1) :
    L^rho * M ≤ B := by
  calc
    _ ≤ L^rho * (B * D^rho) :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hL rho)
    _ = B * (L * D)^rho := by rw [Real.mul_rpow hL hD]; ring
    _ ≤ B * 1^rho := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hL hD) hcap hrho) hB
    _ = B := by rw [Real.one_rpow,mul_one]

theorem two_line_coefficient_mass {ι : Type*} (A : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 < N i) (L rho B : ℝ) (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hc : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ))))
    (hl : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 - rho))))
    (hcm : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ))) ≤ B)
    (hlm : L^rho * (∑' i, ‖A i‖ * (N i)^(-(1 / 2 - rho))) ≤ B) :
    Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ∧
    (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ 2 * B := by
  have hmajor := hc.add (hl.mul_left (L^rho))
  have hbound (i : ι) := coefficient_max_weight_bound (A i) (N i) L rho (hN i) hL hrho
  have hs : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) :=
    hmajor.of_nonneg_of_le (fun i => by have := hN i; positivity) hbound
  refine ⟨hs, ?_⟩
  have hm := hs.tsum_le_tsum hbound hmajor
  rw [hc.tsum_add (hl.mul_left _),tsum_mul_left] at hm
  linarith

theorem error_packet_damped_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ∧
    (∑' e : ErrorPacketIndex S u T, ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) *
      max 1 (L * (errorPacketScale S u T e : ℝ))^rho) ≤
      2 * (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
        errorProductSize u T) := by
  obtain ⟨hl,hlm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
  obtain ⟨hc,hcm⟩ := error_packet_coefficient_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps 0 hQ halpha halpha1 heps heps1 hx hz (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith)
  simp only [sub_zero,Real.rpow_zero,mul_one] at hc hcm
  have hB : 0 ≤ 579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) *
      errorProductSize u T := mul_nonneg (by positivity) (errorProductSize_nonneg u T)
  apply two_line_coefficient_mass _ _
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    L rho _ hL hrho hc hl hcm
  exact mass_deficit_absorption _ _ _ _ _ hB
    (le_trans zero_le_one (errorProductDeficit_one_le u T)) hL hrho hlm hcap

theorem actual_conductor_packet_cap (u : FreeRow) (T : Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (C Cu : ℝ) (hC : 0 < C)
    (hCu : Cu ≤ C * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ)) :
    (Cu / (C * (Ideal.span {u.val} : Ideal O).absNorm)) * errorProductDeficit u T ≤ 1 := by
  have hN : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hh := conductor_repeated_deficit u T hT C Cu hC.le hCu
  rw [div_mul_eq_mul_div]
  exact (div_le_one (mul_pos hC hN)).mpr hh

/-- The coefficient-series prefactor costs arbitrarily little row norm,
uniformly in the finite exclusions and selected labels. -/
theorem coefficient_prefactor_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (u : FreeRow),
      2 * (579 ^ (ramifiedPrimes S u).card * Real.exp (1 / 2)) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound
    579 epsilon (by norm_num) hepsilon
  refine ⟨2 * C * Real.exp (1 / 2),by positivity,?_⟩
  intro S u
  have hc : (579 : ℝ)^(ramifiedPrimes S u).card ≤
      C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon := by
    apply le_trans _ (hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
    apply pow_le_pow_right₀ (by norm_num)
    rw [←HeckeDeletionBounds.primeSet_card]
    exact Finset.card_filter_le _ _
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (Real.exp_pos (1 / 2)).le) (by norm_num : (0 : ℝ) ≤ 2)
  exact hh.trans_eq (by ring)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorMassDamping -/
