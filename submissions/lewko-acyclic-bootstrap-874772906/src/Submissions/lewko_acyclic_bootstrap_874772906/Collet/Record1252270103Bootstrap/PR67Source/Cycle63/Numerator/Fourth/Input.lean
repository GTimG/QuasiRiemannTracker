import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.InitialAffineContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorFourierProfiles
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Physical.PhysicalMomentInput
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Capacity.Schedule
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Cycle63.Numerator.Fourth
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
def AffineAt {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  Cycle63Moment.InitialAffineAt (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
    η η (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) degree control C

/-- The genuine initial energy controls the finite physical reflected pair.
No conductor, Euler factor, source mask, or ramified zero is altered. -/
theorem finite_physical_pair_affine {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ mesh ε : ℝ)
    (hU : 1 ≤ U) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀x,0≤(Φ x).re)
    (hη : ((fixedSourcePrincipal F.S F.exclusions.prime).modulus.absNorm:ℝ)≤ U)
    (hrows : ∀u∈rows,rowNorm u≤ U)
    (hkeep : ∀u∈rows, initialKeep (fixedSourcePrincipal F.S F.exclusions.prime)
      (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) (fixedSourcePrincipal F.S F.exclusions.prime)) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (haffine : AffineAt F bΦ mesh ε U degree control C)
    (T : Finset (Fin D.N)) (width : T→ℝ) (z : T→ℂ) (height : ℝ)
    (hw : ∀i,0≤ width i) (hwmax : ∀i,width i≤ mesh)
    (hz : ∀i,(z i).re=17/50) (hh : 0≤ height) (hzim : ∀i,|(z i).im|≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hlo₁ : Cycle63.CountAffine.windowBottom≤ length U X₁) (hhi₁ : length U X₁≤Cycle63.CountAffine.plainLengthTop)
    (hlo₂ : Cycle63.CountAffine.windowBottom≤ length U X₂) (hhi₂ : length U X₂≤Cycle63.CountAffine.plainLengthTop)
    (hslotlo : Cycle63.Optimization.slotFloor≤∑i,width i) (hslothi : (∑i,width i)≤Cycle63.Optimization.slotTop)
    (hcap : length U X₁+length U X₂+Arithmetic.lambda*(∑i,width i)≤ Arithmetic.B) :
    (∑u∈rows, ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 0) X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (U^(width i)) (z i))
        0 (U^(width i))‖^2) ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+ε) := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  have he := finite_actual_pair_le_energy rows η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)
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
    (initialKeep η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)) Φ U
  have hb := haffine T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) 1 le_rfl le_rfl Φ hs hp p X₁ X₂
    hX₁ hX₂ (by simpa using hlo₁) (by simpa using hhi₁)
    (by simpa using hlo₂) (by simpa using hhi₂)
    (by rw [mul_one]; exact hslotlo) (by rw [mul_one]; exact hslothi) (by rw [mul_one]; exact hcap)
  exact he.trans (heq.le.trans (by simpa [η] using hb))

end Cycle63.Numerator.Fourth

end
end Record1252270103Bootstrap.PR67
