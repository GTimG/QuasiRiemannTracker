/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Explicit-face version of the physical reflected pair. Adapted from the
PR137 physical Input adapter (Sil, Hailey Collet and predecessor authors,
Apache-2.0). The underlying finite-energy comparison is unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveAffineInput

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open QRH.Record1252270103Return QRH.Record12518109Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentEnergyBands CenteredMomentRowNorm ConcretePrimeRowBridge
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion Cycle25WeightedNumeratorPhysical
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The genuine face energy bounds the literal finite physical pair. Every
row keep-condition, natural zero, mark coefficient and conjugation is retained.
Only the source-domain parameters are made explicit. -/
theorem finite_pair_of_affine (face : SourceFace) (A : ChosenData) (rows : Finset FreeRow)
    (Φ : 𝓢(ℝ,ℂ)) (U bPhi meshError : ℝ)
    (hU : 1 ≤ U) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (hp : ∀ x, 0 ≤ (Φ x).re)
    (hη : ((fixedSourcePrincipal A.F.S A.F.exclusions.prime).modulus.absNorm : ℝ) ≤ U)
    (hrows : ∀ u ∈ rows, rowNorm u ≤ U)
    (hkeep : ∀ u ∈ rows, initialKeep (fixedSourcePrincipal A.F.S A.F.exclusions.prime)
      (internalQ (weighted_sourceFixedIdeal A.F) (fixedSourcePrincipal A.F.S A.F.exclusions.prime)) u.val)
    (hone : ∀ x ∈ Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (haffine : affineAtFace face A bPhi meshError U degree control C)
    (T : Finset (Fin A.D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ)
    (hw : ∀ i, 0 ≤ width i) (hwmax : ∀ i, width i ≤ A.sourceMesh)
    (hz : ∀ i, (z i).re = 17/50) (hh : 0 ≤ height) (hzim : ∀ i, |(z i).im| ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hadmit : face.Admissible (length U X₁) (length U X₂) (∑ i, width i) 1) :
    (∑ u ∈ rows, ‖polynomial ((momentData (fixedSourcePrincipal A.F.S A.F.exclusions.prime)).character
      (momentElement u)) false (p.profile 0) X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal A.F.S A.F.exclusions.prime)).character
      (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏ i, normalizedSlot (fixedSourcePrincipal A.F.S A.F.exclusions.prime) rowMaskElement 1 u.val
        (CenteredMomentPrimeSlot.primePool A.F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient (fixedSourcePrincipal A.F.S A.F.exclusions.prime) A.F.W
          (U^(width i)) (z i)) 0 (U^(width i))‖^2) ≤
      C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+meshError) := by
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal A.F) η)
    Φ U bPhi 1 hU (by norm_num) hs hp (by simpa using hη) hrows hkeep hone
    (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) hX₁ hX₂
    (fun i => CenteredMomentPrimeSlot.primePool A.F.modulus ⊤ 2 (U^(width i)))
    (fun i => physicalSlotCoefficient η A.F.W (U^(width i)) (z i))
    (fun i => U^(width i)) (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hcoef : (fun (i:T) I => physicalSlotCoefficient η A.F.W (U^(width i)) (z i) I) =
      (fun (i:T) I => idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x => conj (A.F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all A.F η _
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (z i) I,hz i]
    norm_num
  rw [hcoef] at he
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq A.F.modulus ⊤ le_top
    η η (fun (_:T) => 1) (fixedBadMask*idealGenerator 1) 1 (p.profile 0) (p.profile 1)
    (fun _ => 2) (fun i => U^(width i))
    (fun i I => HeckePrimeAnnular.annularWeight (fun x => conj (A.F.W x))
      (U^(width i)) (33/50) (-(z i).im) I) 0 X₁ X₂
    (initialKeep η (internalQ (weighted_sourceFixedIdeal A.F) η)) Φ U
  have hb := haffine T (fun _ => 1) width (fun _ => 33/50) (fun i => -(z i).im)
    0 height hw hwmax (fun _ => le_rfl) (fun _ => le_rfl) hh
    (fun i => by simpa only [abs_neg] using hzim i) 1 le_rfl le_rfl Φ hs hp p X₁ X₂
    hX₁ hX₂ hadmit
  exact he.trans (heq.le.trans (by simpa [η] using hb))

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.finite_pair_of_affine
