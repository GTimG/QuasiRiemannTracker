/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Explicit-face physical Fourier pair. Adapted from the PR137 Fourier adapter
(Sil, Hailey Collet and predecessor authors, Apache-2.0). The profile controls,
character orientation and physical prime amplitudes are unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositivePhysicalPair
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Fourier

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return QRH.Record12518109Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentEnergyBands CenteredMomentRowNorm
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentNaturalPrimitive ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The literal Fourier pair is controlled at every admitted point of the
explicit face. Constants and profile derivatives precede all Fourier heights. -/
theorem fourier_of_affine (face : SourceFace) (A : ChosenData)
    (bPhi error : ℝ) (hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop, affineAtFace face A bPhi error U degree control Ci) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ A.sourceMesh) → (∀ i, (z i).re = 17/50) →
      0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
      face.Admissible (length U X₁) (length U X₂) (∑ i, width i) 1 →
      ∀ j k : Fin 2, ∀ v w : ℝ,
      (∑ u ∈ rows, ‖polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W
          2 (U^(width i)) (z i)‖^2) ≤
      (C*(1+height)^degree*U^(1+error))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  obtain ⟨J,Cp,hCp,hprofile⟩ := numerator_fourier_profiles_control control
  let C := Ci*(1+diagonalControl radialMajorant)*Cp
  have hC : 0 < C := by
    have hh := diagonalControl_nonneg radialMajorant
    dsimp [C]
    positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hinput,eventually_fixed_source_keep A.F η,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (η.modulus.absNorm:ℝ)] with U ha hkeep hU hη
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hadmit j k v w
  have he := finite_pair_of_affine face A rows radialMajorant U bPhi error hU.le hsPhi
    radialMajorant_nonneg hη (fun u hu => (hrows u hu).2)
    (fun u hu => hkeep u (hrows u hu).1) radialMajorant_one degree control Ci ha
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w) X₁ X₂
    hX₁ hX₂ hadmit
  have heq :
      (∑ u ∈ rows, ‖polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W
          2 (U^(width i)) (z i)‖^2) =
      (∑ u ∈ rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏ i, normalizedSlot η rowMaskElement 1 u.val
          (CenteredMomentPrimeSlot.primePool A.F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η A.F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj A.F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq A.F u j v X₁ hX₁,
      inverse_annular_norm_eq A.F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd := diagonalControl_nonneg radialMajorant
  have hp := hprofile j k v w
  calc
    _ ≤ (Ci*(1+diagonalControl radialMajorant))*
        (Cp*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*(1+height)^degree*U^(1+error) := by
      gcongr
      linarith
    _ = _ := by dsimp [C]; ring

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.fourier_of_affine
