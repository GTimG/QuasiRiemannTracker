/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Fourier (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Gao/Hailey Collet/OpenAI physical Fourier transport, Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.Input
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.CertifiedFourier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentEnergyBands CenteredMomentRowNorm
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- Affine interior physical Fourier pair. The analytic premise is the actual
initial radial energy, not a row fourth moment or an improved zero-free endpoint. -/
theorem affine_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε : ℝ) (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh ε U degree control Ci) :
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) → (∀i,(z i).re=17/50) →
      0≤ height → (∀i,|(z i).im|≤ height) →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      0≤ length U X₁ → length U X₁≤1/2 →
      0≤ length U X₂ → length U X₂≤1/2 →
      0≤∑i,width i → (∑i,width i)≤cap →
      length U X₁+length U X₂+physicalLambda*(∑i,width i)≤ physicalB →
      ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨J,Cp,hCp,hprofile⟩:=numerator_fourier_profiles_control control
  let C:=Ci*(1+diagonalControl radialMajorant)*Cp
  have hC:0< C:=by have:=diagonalControl_nonneg radialMajorant;dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hinput,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (η.modulus.absNorm:ℝ)] with U ha hkeep hU hη
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap j k v w
  have he:=finite_physical_pair_affine F rows radialMajorant U bΦ mesh ε hU.le hsΦ
    radialMajorant_nonneg hη (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Ci ha
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w) X₁ X₂
    hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslo hshi hcap
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd:=diagonalControl_nonneg radialMajorant
  have hp:=hprofile j k v w
  calc
    _ ≤ (Ci*(1+diagonalControl radialMajorant))*
        (Cp*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*(1+height)^degree*U^(1+ε) := by
      gcongr
      linarith
    _ = _ := by dsimp [C];ring

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect

