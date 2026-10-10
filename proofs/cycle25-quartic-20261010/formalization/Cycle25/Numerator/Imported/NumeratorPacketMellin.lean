import Cycle25.Numerator.Imported.NumeratorMassDamping
import Cycle25.Numerator.Imported.MellinReconstruction

/-! Mellin inversion of the actual numerator with the complete error packet. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

instance correctionIndex_countable (S : Finset (Ideal O)) (u : FreeRow) :
    Countable (CorrectionIndex S u) := by unfold CorrectionIndex EulerIndex; infer_instance
instance errorPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) : Countable (ErrorPacketIndex S u T) := by
  unfold ErrorPacketIndex
  infer_instance

theorem error_packet_central_summable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (x z : ℂ) (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ))) := by
  have hC := (continuedCorrection_coefficient_mass firsteps (1 / 2)
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx hz (by norm_num) hmargin).1
  have hE := (hasSum_fintype (fun j : T → Fin 4 => ‖errorTupleCoefficient η u T hT x z j‖ *
    (errorTupleScale T j : ℝ)^(-(1 / 2 : ℝ)))).summable
  exact weighted_product_summable _ _ _ _ (1 / 2) hE hC

theorem actual_error_packet_mellin (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hmargin : 1 + firsteps ≤ x.re + 1 / 2)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0 < Y) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
      (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
      ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
          η u x ((1 / 2 : ℂ) + t * I) z)) =
    (Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' e : ErrorPacketIndex S u T,
      errorPacketCoefficient S hS η u T hT x z e *
        (errorPacketScale S u T e : ℂ)^(-(1 / 2 : ℂ)) *
        HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
          (Y / (errorPacketScale S u T e : ℝ)) 0 0 := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1 / 2 : ℂ) + t * I) z hQ hx hz
    (by simp; norm_num) (by simpa using hmargin)
  simp_rw [he]
  exact MellinReconstruction.weighted_numerator_mellin (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY
    (errorPacketCoefficient S hS η u T hT x z) (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e))
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)

theorem reconstructed_numerator_bound {κ : Type*} [Countable κ]
    (χ : Character) (W : ℝ → ℂ) (a b Y L rho M B : ℝ)
    (hsupp : Function.support W ⊆ Icc a b) (hY : 0 < Y) (hM : 0 ≤ M)
    (A : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (hmass : Summable (fun i => ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho))
    (hmb : (∑' i, ‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) ≤ B)
    (hpoly : ∀ i, N i ≤ b * Y → ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho) :
    ‖(Y : ℂ)^(-(1 / 2 : ℂ)) * ∑' i,
      A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
        Y^(-(1 / 2 : ℝ)) * (M * B) := by
  have hpoly' (i : κ) : ‖HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * max 1 (L * N i)^rho := by
    by_cases hi : N i ≤ b * Y
    · exact hpoly i hi
    · rw [MellinReconstruction.polynomial_zero_of_scale_cutoff χ W a b Y (N i)
        hsupp hY (hN i) (lt_of_not_ge hi),norm_zero]
      exact mul_nonneg hM (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) rho)
  have hbound (i : κ) :
      ‖A i * (N i : ℂ)^(-(1 / 2 : ℂ)) * HeckeDyadic.polynomial χ false W (Y / N i) 0 0‖ ≤
      M * (‖A i‖ * (N i)^(-(1 / 2 : ℝ)) * max 1 (L * N i)^rho) := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i)]
    rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (‖A i‖ * (N i)^(-(1 / 2 : ℝ))) * (M * max 1 (L * N i)^rho) :=
        mul_le_mul_of_nonneg_left (hpoly' i) (by have := hN i; positivity)
      _ = _ := by ring
  have hs := (hmass.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hn := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound (hmass.mul_left M))
  rw [tsum_mul_left] at hn
  have hm := hn.trans (mul_le_mul_of_nonneg_left hmb hM)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
  rw [show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hY.le _)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
