/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual canonical initial input supplies the MAIN scalar gap. The fixed
pool constant is separated before the selected label sums. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalar
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialMainRemainderGap

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Pool
open QRH.Record1252270103Source.InitialPhysical
open QRH.Record1252270103Source.Admission
open Record12518109Natural (balancedGeometrySide)
open Record1252270103Finite Record1252270103StepScalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal HeckeFamily.O) [NeZero rayM]
local instance initialRemainderFiniteQuotient : Finite (HeckeFamily.O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (HeckeFamily.O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal HeckeFamily.O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

/-- Source-face and cell admissions give the volume gap internally. The only
small-error gate is numerical and retains each mass/pool/zero/frequency term.
The exact original label, modifier, puncture and projector seed remain literal. -/
theorem initial_remainder_admissions (K : ℚ) (n low : Source) (b width : ℝ)
    (hZ1 : 1<Z) (hg : RealGeometry K n low b)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) (hB : (low.B:ℝ)≤1)
    (hw : width≤PhysicalLowGuard.step n)
    (hadm : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hlo : b-(n.allowance:ℝ)-width≤∑i,w i) (hhi : (∑i,w i)≤b)
    (P : Finset (Ideal HeckeFamily.O)) (ell mesh loss BD Bsource : ℝ) (depth : ℕ)
    (hpool : FixedCellPoolData P Z (sourceAReal n low b) ell mesh loss BD Bsource depth)
    (hell : 0<ell) (H0 radius : ℝ) (hH0 : 0<H0)
    (hr0 : 0≤radius+6*sourceAReal n low b) (hr : radius+6*sourceAReal n low b≤32)
    (ξ reserve epsMass epsZero saving : ℝ) (hz : 0≤epsZero)
    (herr : frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*(n.allowance:ℝ))
    (reflected : Bool) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal HeckeFamily.O) (hK : 0<Z^(1:ℝ)) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource (s) modifier R seed (Z^(1:ℝ)) Z ξ hK bin)) :
    let a:=sourceAReal n low b
    let weight:=mainWeight P ell H0 radius a/weightConstant ell
    let exponents:=geometryExponents (s) modifier R seed (Z^(1:ℝ)) Z ξ j.1.val
    let A:=Real.logb Z (volume (s))
    let Hlog:=Real.logb Z (firstMainRadius reflected (Z^(1:ℝ)) (volume (s)) Z ξ (3*a) reserve
      (FirstFamily.firstLabel (s) modifier R seed (Z^(1:ℝ)) Z ξ hK bin j))
    0<weightConstant ell ∧ 0≤weight ∧
    weight*Z^(2*epsMass+(Hlog+epsZero*A)-balancedGeometrySide reflected A exponents)
      ≤Z^((-a-(n.allowance:ℝ))-exponents 2) ∧
    weight*Z^(2*epsMass+(Hlog-saving)-balancedGeometrySide reflected A exponents)
      ≤Z^((-a-(n.allowance:ℝ)-saving)-exponents 2) := by
  dsimp only
  have hweight:=normalized_pool_weight P Z (sourceAReal n low b) ell mesh loss BD Bsource depth
    hpool hell H0 radius hH0 hr0 hr
  refine ⟨weightConstant_pos ell hell,hweight.1,?_⟩
  apply actual_remainder_admissions reflected (s) modifier R seed Z ξ (sourceAReal n low b)
    reserve (n.allowance:ℝ) 2 epsMass epsZero loss saving _ hZ1 hK bin j hg.a_pos.le he hz
  · exact initial_main_amplification_gap rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
      p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod K n low b width hZ1 hg he hL hB hw hadm hlo hhi
  · exact herr
  · exact hweight.2

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.initial_remainder_admissions
