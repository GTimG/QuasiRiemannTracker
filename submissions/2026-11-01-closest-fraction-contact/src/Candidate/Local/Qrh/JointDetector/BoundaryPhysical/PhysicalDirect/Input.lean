/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Input (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Zhongpai Gao Target830 Physical.Input, with inherited
OpenAI/Hailey Collet physical energy and reflection-mask identities. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.FourierProfiles
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return

namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentEnergyBands CenteredMomentRowNorm ConcretePrimeRowBridge
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- The literal affine initial-energy input, evaluated at radial width one.
The source is conjugated, matching the reflected physical numerator. -/
def physicalFace : QRH.Record12518109Source.SourceFace :=
  ⟨GenericArithmetic.physicalB,GenericArithmetic.physicalLambda,0,1/2,0,GenericArithmetic.cap⟩

def AffineAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  QRH.Record12518109Source.InitialAffineAt (α:=Fin D.N) F.modulus ⊤ le_top physicalFace
    (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
    η η (weighted_sourceFixedIdeal F) degree control C

/-- The genuine initial energy controls the finite physical reflected pair.
No conductor, Euler factor, source mask, or ramified zero is altered. -/
theorem finite_physical_pair_affine {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ mesh ε : ℝ)
    (hU : 1 ≤ U) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀x,0≤(Φ x).re)
    (hη : ((fixedSourcePrincipal F.S F.exclusions.prime).modulus.absNorm:ℝ)≤ U)
    (hrows : ∀u∈rows,rowNorm u≤ U)
    (hkeep : ∀u∈rows, initialKeep (fixedSourcePrincipal F.S F.exclusions.prime)
      (internalQ (weighted_sourceFixedIdeal F) (fixedSourcePrincipal F.S F.exclusions.prime)) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (haffine : AffineAt F bΦ mesh ε U degree control C)
    (T : Finset (Fin D.N)) (width : T→ℝ) (z : T→ℂ) (height : ℝ)
    (hw : ∀i,0≤ width i) (hwmax : ∀i,width i≤ mesh)
    (hz : ∀i,(z i).re=17/50) (hh : 0≤ height) (hzim : ∀i,|(z i).im|≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hlo₁ : 0≤ length U X₁) (hhi₁ : length U X₁≤1/2)
    (hlo₂ : 0≤ length U X₂) (hhi₂ : length U X₂≤1/2)
    (hslotlo : 0≤∑i,width i) (hslothi : (∑i,width i)≤GenericArithmetic.cap)
    (hcap : length U X₁+length U X₂+GenericArithmetic.physicalLambda*(∑i,width i)≤ GenericArithmetic.physicalB) :
    (∑u∈rows, ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 0) X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (U^(width i)) (z i))
        0 (U^(width i))‖^2) ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+ε) := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ 1 hU (by norm_num) hs hp (by simpa using hη) hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂ (fun _ hx=>(p.support 0 hx).2)
    (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=>CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
    (fun i=>physicalSlotCoefficient η F.W (U^(width i)) (z i))
    (fun i=>U^(width i)) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hcoef : (fun (i:T) I=>physicalSlotCoefficient η F.W (U^(width i)) (z i) I) =
      (fun (i:T) I=>idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x=>conj (F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all F η _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (z i) I,hz i]
    norm_num
  rw [hcoef] at he
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq F.modulus ⊤ le_top
    η η (fun (_:T)=>1) (fixedBadMask*idealGenerator 1) 1 (p.profile 0) (p.profile 1)
    (fun _=>2) (fun i=>U^(width i))
    (fun i I=>HeckePrimeAnnular.annularWeight (fun x=>conj (F.W x))
      (U^(width i)) (33/50) (-(z i).im) I) 0 X₁ X₂
    (initialKeep η (internalQ (weighted_sourceFixedIdeal F) η)) Φ U
  have hb := haffine T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) 1 le_rfl le_rfl Φ hs hp p X₁ X₂
    hX₁ hX₂ (by
      exact ⟨by simpa [physicalFace] using hlo₁, by norm_num [physicalFace] at hhi₁ ⊢; exact hhi₁,
        by simpa [physicalFace] using hlo₂, by norm_num [physicalFace] at hhi₂ ⊢; exact hhi₂,
        by simpa [physicalFace] using hslotlo, by simpa [physicalFace] using hslothi,
        by simpa [physicalFace] using hcap⟩)
  exact he.trans (heq.le.trans (by simpa [η] using hb))

end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
