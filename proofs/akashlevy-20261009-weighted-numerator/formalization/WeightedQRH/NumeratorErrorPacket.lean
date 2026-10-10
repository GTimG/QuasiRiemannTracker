import WeightedQRH.NumeratorFinitePacket
import OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions

/-! Actual correction times arbitrary finite error slots as one absolutely
convergent coefficient series on both reconstruction lines. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def ErrorPacketIndex (S : Finset (Ideal O)) (u : FreeRow) (T : Finset PrimeIdeal) :=
  (T → Fin 4) × CorrectionIndex (markExclusions S T) u

def errorPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (e : ErrorPacketIndex S u T) : ℂ :=
  errorTupleCoefficient η u T hT x z e.1 *
    correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e.2

def errorPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : Finset PrimeIdeal)
    (e : ErrorPacketIndex S u T) : ℝ≥0 :=
  errorTupleScale T e.1 * correctionScale (markExclusions S T) u e.2

theorem errorPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow) (T : Finset PrimeIdeal)
    (e : ErrorPacketIndex S u T) : 1 ≤ errorPacketScale S u T e := by
  unfold errorPacketScale errorTupleScale
  exact one_le_mul_of_one_le_of_one_le
    (finiteScale_one_le (fun P : T => primeScale P.val) (fun P => primeScale_one_le P.val) e.1)
    (correctionScale_one_le (markExclusions S T) u e.2)

def errorProductSize (u : FreeRow) (T : Finset PrimeIdeal) : ℝ :=
  ∏ P : T, 2880 * errorSize u P.val

def errorProductDeficit (u : FreeRow) (T : Finset PrimeIdeal) : ℝ :=
  ∏ P : T, (repeatedDeficit u P.val : ℝ)

theorem errorProductSize_nonneg (u : FreeRow) (T : Finset PrimeIdeal) :
    0 ≤ errorProductSize u T := by
  apply Finset.prod_nonneg
  intro P hP
  unfold errorSize
  split_ifs <;> positivity

theorem errorProductDeficit_one_le (u : FreeRow) (T : Finset PrimeIdeal) :
    1 ≤ errorProductDeficit u T := by
  apply Finset.one_le_prod₀
  intro P hP
  exact_mod_cast repeatedDeficit_one_le u P.val

theorem error_product_mass_factor (u : FreeRow) (T : Finset PrimeIdeal) (rho : ℝ) :
    (∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho) =
      errorProductSize u T * errorProductDeficit u T ^ rho := by
  rw [Finset.prod_mul_distrib]
  unfold errorProductSize errorProductDeficit
  congr 1
  exact (Real.finsetProd_rpow Finset.univ (fun P : T => (repeatedDeficit u P.val : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) rho)

theorem error_packet_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
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
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
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

end WeightedQRH.Numerator
