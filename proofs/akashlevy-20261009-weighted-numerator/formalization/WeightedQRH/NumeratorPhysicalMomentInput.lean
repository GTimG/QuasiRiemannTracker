import WeightedQRH.NumeratorPhysicalMoment
import WeightedQRH.MomentTerminalInput
import WeightedQRH.MomentDetectorPlainCapacity
import OAI.NumberTheory.DirichletL.Energy.ReferenceChild
import OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm CenteredMomentDetectorPlainCapacity
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot
set_option maxHeartbeats 800000
local notation "O" => HeckeFamily.O

/-- The certified positive endpoint applied directly to arbitrary physical numerator
profiles. The dependence on the two profiles remains their source seminorm control;
no bound on their Fourier frequencies is assumed here. -/
theorem finite_physical_pair_positiveAt {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ mesh ε : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, weighted_initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hpositive : PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 ε (3/4)
      U η (weighted_sourceFixedIdeal F) degree control C)
    (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ)
    (hw : ∀i, 0 ≤ width i) (hwmax : ∀i, width i ≤ mesh)
    (hz : ∀i, (z i).re = 17/50) (hh : 0 ≤ height) (hzim : ∀i, |(z i).im| ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U) (hX₂max : X₂ ≤ U)
    (hcap : length U X₁+length U X₂+6*(3/4)*(∑i,width i) ≤ 1+δ) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i, normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+δ+ε) := by
  let state := weighted_initialState η (internalQ (weighted_sourceFixedIdeal F) η)
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
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
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
    0 X₁ X₂ (weighted_initialKeep η (internalQ (weighted_sourceFixedIdeal F) η)) Φ U
  exact he.trans (heq.le.trans (by simpa [state,weighted_initialState,NaturalState.width,NaturalState.mask] using hpos))


/-- Each source prime slot is the conjugate of the actual negative-orientation
canonical amplitude, without deleting any natural ramified zeros. -/
theorem source_physical_slot_conj {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (P : ℝ) (z : ℂ)
    (hP : 0 < P) :
    normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
      (primePool F.modulus ⊤ 2 P)
      (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W P z) 0 P =
      conj (HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 P z) := by
  apply physical_slot_conj F.modulus ⊤ _ rowMaskElement u.val
    (momentData (fixedSourcePrincipal F.S F.exclusions.prime)).lambda_dvd
    (CenteredMomentDetectorDictionary.source_product_le_rowMask F.S F.exclusions.bad)
    F.W 2 P z hP
  intro I hI _
  exact HeckePrimeRow.identityClass_coprime F.modulus ⊤ (Finset.mem_filter.mp hI).2.2

/-- Conjugating the complete reflected numerator/selected-slot product places
both factors in the positive moment orientation. -/
theorem reflected_pair_norm_eq {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (u : FreeRow) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (P : ι → ℝ) (hP : ∀i, 0 < P i) (z : ι → ℂ) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=>conj (W₁ x)) X₁ 0 0 *
      polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=>conj (W₂ x)) X₂ 0 0 *
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (P i) (z i)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₂ X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (primePool F.modulus ⊤ 2 (P i))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (P i) (z i))
        0 (P i)‖ := by
  simp_rw [source_physical_slot_conj F u _ _ (hP _)]
  rw [CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₁ hX₁,
    CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₂ hX₂]
  simp only [Complex.conj_conj]
  rw [numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad,
    numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  rw [←Complex.norm_conj (_*_*∏i,_)]
  simp only [map_mul,map_prod,Complex.conj_conj]

end SevenEighths.WeightedNumeratorReflection
end
end OAI
