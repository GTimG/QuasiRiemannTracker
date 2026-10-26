/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeContinuationSource
import Candidate.Cycle63.Physical.InitialSourceReduction

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstSourceReduction Cycle63InitialSource Cycle63FirstActual Cycle63FirstGeometry
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot CenteredMomentAllocatedRayDictionary
open HeckePrimeAnnular

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable (eta : Character) (theta : iota → RayQuotient.Characters M H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aSlot bSlot lo hi : ℝ) (haSlot : 0 < aSlot)
variable (hWs : Function.support W ⊆ Set.Icc aSlot bSlot)
variable (w sigma freq : iota → ℝ) (hsigma : ∀i,sigma i ∈ Set.Icc lo hi)
variable {Z oldMask bPhi ap bp : ℝ} (s : NaturalState Z oldMask bPhi)
variable (unit : ℝ) (hunit : 0 < unit) (hwide : s.width ≤ unit)
variable (hmask : (s.puncture.absNorm : ℝ) ≤ (Z^unit)^(20:ℝ))
variable (p : Profiles ap bp) (hap : 0 < ap)
variable (Lc t X1 X2 : ℝ) (hX1 : 0 < X1) (hX2 : 0 < X2)

/-- The actual equal-product comparison chosen for continuation is the
native affine comparison. Thus the next HIGH provider and AtState theorem
receive the literal constructed source, rather than an arbitrary Input
postulated to equal affineInput. -/
theorem nativeContinuationInput_eq_affineInput :
    nativeContinuationInput M H hH eta theta W hW aSlot bSlot lo hi haSlot hWs
      w sigma freq hsigma s unit hunit hwide hmask p hap t X1 X2
      (comparisonFirstAt (Z^unit) Lc) (comparisonSecondAt (Z^unit) Lc X1 X2) hX1 hX2
      (comparisonAt_positive (Z^unit) Lc X1 X2
        (zero_lt_one.trans_le (nativeContinuationState s unit hunit hwide hmask).base_ge_one) hX1 hX2).1
      (comparisonAt_positive (Z^unit) Lc X1 X2
        (zero_lt_one.trans_le (nativeContinuationState s unit hunit hwide hmask).base_ge_one) hX1 hX2).2
      (comparisonAt_same_product (Z^unit) Lc X1 X2
        (zero_lt_one.trans_le (nativeContinuationState s unit hunit hwide hmask).base_ge_one)) =
    affineInput M H hH eta theta W hW aSlot bSlot lo hi haSlot hWs
      (fun i=>w i/unit) sigma freq hsigma (nativeContinuationState s unit hunit hwide hmask)
      p hap Lc t X1 X2 hX1 hX2 := rfl

variable [Cycle63.AffineLedger] in
/-- Install the actual NEXT regional ledger's comparison on the rebased
daughter. The original ray dictionary remains unchanged, with weights
divided by the actual unit. This is the source consumed by the recursive
HIGH node and by the regional AtState theorem. -/
def nativeRegionalContinuationInput : Input iota :=
  affineInput M H hH eta theta W hW aSlot bSlot lo hi haSlot hWs
    (fun i=>w i/unit) sigma freq hsigma (nativeContinuationState s unit hunit hwide hmask)
    p hap (Cycle63.AffineLedger.comparisonLength
      (length (Z^unit) X1) (length (Z^unit) X2) (∑i,w i/unit)) t X1 X2 hX1 hX2

variable [Cycle63.AffineLedger] in
theorem nativeRegionalContinuationInput_energy :
    let state := nativeContinuationState s unit hunit hwide hmask
    let inp := nativeRegionalContinuationInput M H hH eta theta W hW aSlot bSlot lo hi haSlot hWs
      w sigma freq hsigma s unit hunit hwide hmask p hap t X1 X2 hX1 hX2
    energy inp.η state.mask 1 inp.t inp.W₁ inp.W₂
      inp.slots inp.coefficient inp.P inp.X₁ inp.X₂ state.radial.keep state.radial.profile state.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bSlot (Z^(w i)))
      (fun i I=>idealCoeff
        (relativeCharacter M H hH eta (theta i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (sigma i) (freq i) I)
      (fun i=>Z^(w i)) X1 X2 s.radial.keep s.radial.profile s.radial.scale := by
  let Lc := Cycle63.AffineLedger.comparisonLength
    (length (Z^unit) X1) (length (Z^unit) X2) (∑i,w i/unit)
  have hpos := comparisonAt_positive (Z^unit) Lc X1 X2
    (zero_lt_one.trans_le (nativeContinuationState s unit hunit hwide hmask).base_ge_one) hX1 hX2
  have hprod := comparisonAt_same_product (Z^unit) Lc X1 X2
    (zero_lt_one.trans_le (nativeContinuationState s unit hunit hwide hmask).base_ge_one)
  exact nativeContinuationInput_energy M H hH eta theta W hW aSlot bSlot lo hi haSlot hWs
    w sigma freq hsigma s unit hunit hwide hmask p hap t X1 X2
    (comparisonFirstAt (Z^unit) Lc) (comparisonSecondAt (Z^unit) Lc X1 X2)
    hX1 hX2 hpos.1 hpos.2 hprod

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.nativeContinuationInput_eq_affineInput
#print axioms OAI.SevenEighths.Cycle153RegionalLow.nativeRegionalContinuationInput_energy
