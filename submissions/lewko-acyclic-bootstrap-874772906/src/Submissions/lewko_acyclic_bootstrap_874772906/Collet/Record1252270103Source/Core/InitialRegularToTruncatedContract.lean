/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The remaining regular inlet is the literal full kept second-family norm.
The first radial profile and second ball profile are kept distinct. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.ExceptionalInitialGeometryUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedFamily

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
local instance regularJointContractDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

/-- The full kept norm on exactly the same complete carrier used by the
complementary-family theorem. Neither normalization nor ratio selection is
postulated in this definition. -/
def regularJointNorm {α Label:Type*}[Fintype α][Fintype Label]
    {slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(Q:Ideal O):ℝ :=
  let keep:=regularKeep slots f.input f.modifier f.puncture f.seed f.physicalScale
    f.sectorScale Z f.mesh f.referenceRay Q f.rowMask
  let datum:=regularDatum slots f.input f.modifier f.puncture f.seed f.physicalScale
    f.sectorScale Z f.mesh W f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos
    f.referenceRay Q f.rowMask
  let phase:=familyWeight slots f.input f.modifier f.puncture f.seed W f.physicalScale
    f.sectorScale (fun _=>Z) (fun _=>f.mesh) f.energyScale f.amplitude keep
  ‖∑q:f.Carrier,phase q*(modifiedDatumBlock (datum q) (f.modifier q.1)).value W‖

/-- One analytic inlet, with all fixed anchors before the controls and all
moving data afterwards. The initial width cell is the literal grid cell;
the positive saving pays the later finite first-selection loss. -/
def RegularJointSupplier (K:ℚ)(n low:Source)(b mesh ξ reserve width:ℝ):Prop :=
  ∀(α:Type)[Fintype α][DecidableEq α],
  ∀(rayM:Ideal O)[NeZero rayM],
  ∀(H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H),
  ∀(Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ:ℝ)(hbΦ:2≤bΦ)(η η₀:Character)(Q:Ideal O),
    Q≤rayM→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
  ∀(R₀:Ideal O),R₀≠0→
  ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ σ:ℝ,0<C ∧ 0<τ ∧ 0<σ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
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
  let amp:=sourceAReal n low b
  let P:=CenteredMomentPrimePool.primePool rayM H fixedBadPrimes (1/2) 1 (Z^amp)
  ∀{Label:Type}[Fintype Label],∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
  ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin),
    Function.Injective (fun l=>(firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l),
      (column l).2.1.val))→
  ∀hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)
    (fun _=>logAnnulus),
  let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>live_projector_squarefree
    s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (fun _=>logAnnulus) (column l) (hLive l)
  let common:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 Z Z ξ 1
    (Real.logb Z (volume s)) (zero_lt_one.trans hZ) bin
    (fun q=>normPhase (coordinateBlock s modifier R₀ 1 W Z Z ξ q)) (column l)
  let H0:=fun l=>(source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l).1).H0
  let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let radius:=fun l=>literalFirstRadius reflected Z (volume s) Z ξ reserve (labels l)
  ∀(alloc:∀l,actualAllocations s.pools (common l)),
    (∀l,frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P≠0)→
  ∀χ₀:Label→RayCharacter,
  let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/
    (P.card:ℝ)*((radius l+6*amp)/(amp/2))
  let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  let chars:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
  let Hmain:=fun l=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (labels l)
  let Tsec:=fun l=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (labels l)
  let f:=mainAllocatedFamily s ballProfile (p.profile 0) (p.profile 1) Z R₀ common
    (fun l=>(column l).2.1.val) alloc chars (fun _=>ht) P hseed
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    Hmain Tsec (fun _=>volume s) amplitude ξ
    (fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) (labels l)) χ₀ (fixedBadMask*idealGenerator R₀)
  regularJointNorm f (internalQ Q η₀)≤C*(p.control controls)^2*
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    (1+|ht|+height)^degree*Z^(-σ)

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.regularJointNorm
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.RegularJointSupplier
