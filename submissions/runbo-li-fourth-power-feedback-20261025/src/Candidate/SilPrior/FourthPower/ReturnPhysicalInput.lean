/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet PR69 PhysicalDirect/Input.lean, retaining the
inherited Gao/OpenAI physical energy and reflection-mask identities.
actual full-source finite physical pair; no physical moment is assumed.
No Geometry.Bounds/PhysicalSchedule instance is introduced. -/
import Candidate.SilPrior.FourthPower.ReturnSourceFaces
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.FourierProfiles

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter
namespace Candidate.SilPrior.FourthPower.ReturnPhysicalInput
open ReturnSourceFaces

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

/-- Actual initial energy at the full global source, with the conjugated
ordinary profile required by the reflected physical numerator. -/
def FullPhysicalAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  QRH.Record12518109Source.InitialAffineAt (α:=Fin D.N) F.modulus ⊤ le_top fullSourceFace
    (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
    η η (weighted_sourceFixedIdeal F) degree control C

/-- The genuine initial energy controls the finite physical reflected pair.
No conductor, Euler factor, source mask, or ramified zero is altered. -/
theorem finite_physical_pair_full {D : Cycle25.Weighted.MomentData}
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
    (hfull : FullPhysicalAt F bΦ mesh ε U degree control C)
    (T : Finset (Fin D.N)) (width : T→ℝ) (z : T→ℂ) (height : ℝ)
    (hw : ∀i,0≤ width i) (hwmax : ∀i,width i≤ mesh)
    (hz : ∀i,(z i).re=17/50) (hh : 0≤ height) (hzim : ∀i,|(z i).im|≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hadm : fullSourceFace.Admissible
      (length U X₁) (length U X₂) (∑i,width i) 1) :
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
  have hb := hfull T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) 1 le_rfl le_rfl Φ hs hp p X₁ X₂
    hX₁ hX₂ hadm
  exact he.trans (heq.le.trans (by simpa [η] using hb))

/-- Uniform ordinary source -> literal physical initial inlet, with the
conjugated source profile and the actual fixed principal target. The mesh and
error are preserved and all constants precede U, rows, slots and heights. -/
theorem full_input_of_unit {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource fullSourceFace mesh ε) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, FullPhysicalAt F bΦ mesh ε U degree control C := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  let Q := weighted_sourceFixedIdeal F
  exact hsource (Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (F.W.smooth ⊤))
    (Cycle25CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support F)
    bΦ hbΦ η η Q (weighted_sourceFixedIdeal_le_modulus F)
    (internalQ_ne_zero Q (weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top Q (weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F))

end Candidate.SilPrior.FourthPower.ReturnPhysicalInput
