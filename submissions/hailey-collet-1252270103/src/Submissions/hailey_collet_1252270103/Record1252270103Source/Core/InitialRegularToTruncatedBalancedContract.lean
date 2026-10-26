/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The remaining regular inlet is the literal full kept second-family norm.
The first radial profile and second ball profile are kept distinct. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedContract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedContract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularToTruncatedFamily

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentSourceMass CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentLogDyadic
open Cycle61InitialMass RayFourExpansion Record1252270103Finite
open Record1252270103Second SecondSectorDatum
open QRH.Record1252270103Low High.CoupledFirst High.GlobalPhysical Admission.FirstFamily
open OAI.SevenEighths.Record1252270103Source.Collision
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps
open Admission.SelectedSecondNatural InitialTruncated ExceptionalPrice
local notation "O" => HeckeFamily.O
local notation "source" => High.CoupledFirst.geometryFirstSource
local instance balancedInitialContractDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

def BalancedInitialSupplier (K:ℚ)(n low:Source)(b mesh ξ width:ℝ):Prop :=
  ∀(α:Type)[Fintype α][DecidableEq α],
  ∀(rayM:Ideal O)[NeZero rayM],
  ∀(H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H),
  ∀(Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ:ℝ)(hbΦ:2≤bΦ)(η η₀:Character)(Q:Ideal O),
    Q≤rayM→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
  ∀(R₀:Ideal O),R₀≠0→
  ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ:ℝ,0<C ∧ 0<τ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
  ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t ht height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤mesh)→0≤height→(∀i,|v i|≤height)→
    1+|t|+|ht|+height≤Z^τ→
  ∀p:Profiles (1/4) (9/4),∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1→
    (crossing n low:ℝ)≤∑i,w i→b-width≤∑i,w i→(∑i,w i)≤b→
  let Y₂:=Z^(49/100-(K:ℝ)*b)
  1≤Y₂→Y₂≤X₁→Y₂≤X₂→
  let Y₁:=X₁*X₂/Y₂
  let hY₂:0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let hY₁:0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  let hprod:Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
  let W:=initialRadialBump bΦ (by linarith)
  let N:=Fintype.card α
  ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
  balancedLiveBudget reflected s modifier R₀ 1 Z Z ξ 1 (Real.logb Z (volume s))
    (zero_lt_one.trans hZ) bin (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) ht≤
    C*(p.control controls)^2*geometryHighFactor reflected
      (geometrySupportConstant N 1 (1/4) (1/4)) bin*(1+|ht|+height)^degree

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.BalancedInitialSupplier
