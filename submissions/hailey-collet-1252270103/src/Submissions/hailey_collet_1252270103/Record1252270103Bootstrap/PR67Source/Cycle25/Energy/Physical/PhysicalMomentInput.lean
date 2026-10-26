import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Physical.PhysicalMoment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChild
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm HeckePrimeAnnular
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot
set_option maxHeartbeats 800000
local notation "O" => HeckeFamily.O

theorem weighted_physical_annular_all {D : WeightedQRH.MomentData} (S:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

/-- The certified positive endpoint applied directly to arbitrary physical numerator
profiles. The dependence on the two profiles remains their source seminorm control;
no bound on their Fourier frequencies is assumed here. -/
theorem finite_physical_pair_positiveAt {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ mesh ε κ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hpositive : PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 ε κ
      U η (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) degree control C)
    (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ)
    (hw : ∀i, 0 ≤ width i) (hwmax : ∀i, width i ≤ mesh)
    (hz : ∀i, (z i).re = 17/50) (hh : 0 ≤ height) (hzim : ∀i, |(z i).im| ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U) (hX₂max : X₂ ≤ U)
    (hcap : length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1+δ) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i, normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+δ+ε) := by
  let state := initialState η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by
    change 1+δ ≤ 2
    linarith
  have hX₁' : X₁ ≤ U^(1:ℝ) := by simpa using hX₁max
  have hX₂' : X₂ ≤ U^(1:ℝ) := by simpa using hX₂max
  have hpos := hpositive T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) state rfl hwidth p X₁ X₂
    hX₁ hX₂ hX₁' hX₂' hcap
  have he := finite_actual_pair_le_energy rows η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=>primePool F.modulus ⊤ 2 (U^(width i)))
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
    η η (fun (_:T)=>1) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1
    (p.profile 0) (p.profile 1) (fun _=>2) (fun i=>U^(width i))
    (fun i I=>HeckePrimeAnnular.annularWeight (fun x=>conj (F.W x))
      (U^(width i)) (33/50) (-(z i).im) I)
    0 X₁ X₂ (initialKeep η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)) Φ U
  exact he.trans (heq.le.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask] using hpos))

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end Record1252270103Bootstrap.PR67
