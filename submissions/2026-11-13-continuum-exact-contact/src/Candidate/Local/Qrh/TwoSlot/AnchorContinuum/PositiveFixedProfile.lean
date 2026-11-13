/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed-profile restoration for the variable physical face. Adapted from
PR137 Fixed (Sil and predecessor authors, Apache-2.0). The conductor and
logarithmic costs are absorbed into an explicitly positive requested loss. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveRetained
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Fixed

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths Cycle25WeightedNumeratorPhysical
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The profile, primitive conductor and retained logarithm costs are all paid
before any row-dependent presentation or selected mark coefficients are chosen. -/
theorem retained_fixed_profile_with_cost (A : ChosenData) {s : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (κ : ℝ)
    (hk0 : (7/10:ℝ) ≤ κ) (hk1 : κ ≤ (3/4:ℝ))
    (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hkb : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bPhi error : ℝ) (herror : 0 < error)
    (hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace s) A bPhi error U di control Ci)
    (G : 𝓢(ℝ,ℂ)) (loss Cscale Ccond xi : ℝ)
    (hloss : 0 < loss) (hCscale : 0 < Cscale) (hCcond : 0 < Ccond) (hxi : 0 < xi) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (τ ψ : rows → Character) (X : rows → ℝ) (m : ℝ),
      (∀ i, ∀ n : O, elementCoeff (rowCharacter A.F.S A.F.exclusions.prime i.val) n =
        elementCoeff (τ i) n) → (∀ i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      (∀ i, (Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i), P) : ℝ) ≤ Ccond*U) →
      (∀ i, ((ψ i).modulus.absNorm : ℝ)*(Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i), P) : ℝ)
        ≤ Cscale*U^m*X i) →
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ A.sourceMesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (A.D.t/4)) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      ((2*(m+xi)+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨
        (2*(m+xi)+6*κ*(∑ i, width i) ≤ 1 ∨ T = ∅)) →
      (∑ i : rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W
          2 (U^(width j)) (z j)‖^2) ≤ C*(1+height)^degree*U^(1+A.D.t+error+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := retained_fourth_with_cost A hs hsmax κ hk0 hk1 hb hkb
    bPhi error herror hsPhi di control Ci hCi hinput (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by
    have hh := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G
    dsimp [B]
    linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m he hX hm hmmax hred hcombined T width z height
    hw hwmesh hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i : rows) : (Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i), P) : ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i : rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hh := hr.2 rows hrows τ ψ (fun _ => G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmesh hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hh.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+A.D.t+error) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+A.D.t+error)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.retained_fixed_profile_with_cost
