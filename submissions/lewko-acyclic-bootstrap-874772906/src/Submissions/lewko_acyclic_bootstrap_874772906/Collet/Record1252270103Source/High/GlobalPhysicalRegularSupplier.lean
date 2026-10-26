/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCanonicalNorm
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Contraction.SelectedMainExceptionalIdentity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularMesh
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularNorm
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFinite
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactorBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularCombinedPointNatural
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record1252270103Finite PhysicalScalar HighScalar Record1252270103Source.Collision
open Cycle61HighGeometry Record1252270103CommonGeometry
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open SelectedHighPaid Pool
local instance regularSupplierDecEq {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open Record1252270103StepScalar QRH.Record1252270103Graph CenteredMomentLogDyadic
open SelectedRegularCanonicalAbsolute
local instance regularSupplierFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open InitialRegularToTruncated Contraction.SelectedMainExceptional
open CoupledFirst Admission.FirstFamily ExceptionalPrice CenteredMomentFirstAnnularMajorant
local notation "source"=>CoupledFirst.geometryFirstSource

def RegularPointSupplier (n low:Source)(b reserve θ mesh ξ width:ℝ):Prop:=
  ∀(α:Type)[Fintype α],∀(M:Ideal O)[NeZero M],
  ∀(H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H),
  ∀(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2),
  ∀(η η₀:Character)(Q:Ideal O),Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
    internalQ Q η₀≤Ideal.span {(72:O)}→∀(R₀:Ideal O)(hR₀:R₀≠0),
  ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ:ℝ,0<C ∧ 0<τ ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    RegularPointAt (α:=α) M H hH W hW hWs η η₀ R₀ hR₀ Q n low
      b reserve θ mesh ξ width τ (Fintype.card α) degree controls C Z

theorem regular_supplier_of_points (K:ℚ)(n low:Source)(b reserve θ mesh ξ width:ℝ)
    (hf:FixedBudget reserve 100 100 1 θ)(hg:RealGeometry K n low b)(hn:ParentGood n)
    (hξ:0<ξ)(hξ1:ξ≤1)(hm:0≤mesh)(hmeshamp:mesh<sourceAReal n low b/2)
    (points:RegularPointSupplier n low b reserve θ mesh ξ width):
    RegularJointSupplier K n low b mesh ξ θ width:=by
  intro α _ _ M _ H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQM hQ hQt hQ72 R₀ hR₀
  obtain ⟨degree,controls,h00,Cpoint,τsource,hpoint,hτsource,epoint⟩:=
    points α M H hH Wslot hW hsW η η₀ Q hQM hQ hQt hQ72 R₀ hR₀
  obtain ⟨C,hC,enorm⟩:=regular_canonical_joint (α:=α) M H hH Wslot hW hsW η η₀ R₀ hR₀ Q K n low
    b reserve θ mesh ξ width τsource Cpoint (Fintype.card α) degree controls h00 hf hg hn hξ hξ1
    hf.positive.le (hf.small.trans (by norm_num)) hpoint hτsource
  have hr:0<reserve:=by linarith [hf.tiny,hf.positive]
  let amp:=sourceAReal n low b
  have hpool:=eventually_fixed_cell_pool M H hH fixedBadPrimes (Finset.Subset.refl _)
    amp (amp/2) mesh θ 10 4 (cellNewtonDepth amp) hm hmeshamp (by linarith [hg.a_pos]) hf.positive
  refine ⟨degree,controls,h00,C,τsource/4,reserve/8,hC,by positivity,by positivity,?_⟩
  filter_upwards [epoint,enorm,hpool] with Z hp hnZ hpoolZ
  refine ⟨hp.1,?_⟩
  intro hZ θslot w v t ht height hw hwm hh hv hext p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi
    Y₂ hy₂ hyl hyr Y₁ hY₂ hY₁ hprod s modifier Wfirst N ampLocal P Label _ reflected bin
  let i:Initial (α:=α) M H Z:=⟨θslot,w,v,t,p,X₁,X₂,Y₁,Y₂,hX₁,hX₂,hY₁,hY₂,hprod⟩
  have hi:InitialGeometry i n b width mesh (49/100-(K:ℝ)*b):=
    ⟨hw,hwm,hadm,hwlo,hwhi,hg.reference_pos.le,hyl,hyr,rfl⟩
  have hext':1+|ht|+height ≤ Z^(τsource/4):=by linarith [abs_nonneg t]
  let Result (X:ℝ)(hX:0<X):Prop:=
    ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 X Z ξ hX bin),
    Function.Injective (fun l=>(firstLabel s modifier R₀ 1 X Z ξ hX bin (column l),
      (column l).2.1.val))→
  ∀hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 X Z ξ hX bin)
    (fun _=>logAnnulus),
  let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>live_projector_squarefree
    s modifier R₀ 1 X Z ξ hX bin (fun _=>logAnnulus) (column l) (hLive l)
  let common:=fun l=>columnIdeal reflected s modifier R₀ 1 X Z ξ hX bin (column l)
  let scalar:=fun l=>balancedColumnScalar reflected s modifier R₀ 1 X Z ξ 1
    (Real.logb Z (volume s)) hX bin
    (fun q=>normPhase (coordinateBlock s modifier R₀ 1 Wfirst X Z ξ q)) (column l)
  let H0:=fun l=>(source s modifier R₀ 1 X Z ξ hX bin (column l).1).H0
  let labels:=fun l=>firstLabel s modifier R₀ 1 X Z ξ hX bin (column l)
  let radius:=fun l=>literalFirstRadius reflected X (volume s) Z ξ θ (labels l)
  ∀(alloc:∀l,actualAllocations s.pools (common l)),
    (∀l,frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P≠0)→
  ∀χ₀:Label→RayCharacter,
  let extra:=fun l=>((bands (H0 l)).card:ℝ)*((actualAllocations s.pools (common l)).card:ℝ)^2/
    (P.card:ℝ)*((radius l+6*amp)/(amp/2))
  let amplitude:=fun l=>‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P‖^2
  let chars:=fun l=>columnCharacter reflected s modifier R₀ 1 X Z ξ hX bin (column l)
  let Hmain:=fun l=>firstMainRadius reflected X (volume s) Z ξ (3*amp) θ (labels l)
  let Tsec:=fun l=>firstMainFourierScale reflected X (volume s) Z ξ (3*amp) θ 2 N (labels l)
  let f:=mainAllocatedFamily s ballProfile (p.profile 0) (p.profile 1) Z R₀ common
    (fun l=>(column l).2.1.val) alloc chars (fun _=>ht) P hseed
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    Hmain Tsec (fun _=>volume s) amplitude ξ
    (fun l=>first_main_radius_pos reflected X (volume s) Z ξ (3*amp) θ
      (zero_lt_one.trans hZ) (labels l)) χ₀ (fixedBadMask*idealGenerator R₀)
  regularJointNorm f (internalQ Q η₀)≤C*(p.control controls)^2*
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    (1+|ht|+height)^degree*Z^(-(reserve/8))
  have boundK:Result (Z^(1:ℝ)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1):=by
    intro column hinj hLive hseed common scalar H0 labels radius alloc hfreeze χ₀
      extra amplitude chars Hmain Tsec f
    let a:=i.anchor hH Wslot hW hsW hZ η η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
    have hhbound:=hnZ.2 hp.2 hZ i (49/100-(K:ℝ)*b) hi (le_refl _) bin reflected
      column hLive alloc P ht χ₀ hinj hfreeze hpoolZ Wfirst height hh hv hext'
    let F:=allocatedRegularFamily a column hLive alloc P amp ht N χ₀
    let rawRadius:=fun l=>literalFirstRadius reflected Z (volume s) Z ξ θ (labels l)
    have hradius:rawRadius=radius:=by
      funext l
      exact congrArg (fun X=>literalFirstRadius reflected X (volume s) Z ξ θ (labels l))
        (Real.rpow_one Z).symm
    have he:=regularMainFamily_joint_norm a column hLive alloc P amp ht N χ₀
      (p.profile 0) (p.profile 1) Wfirst H0 rawRadius (amp/2)
    have hmain:=he.le.trans hhbound
    have hradEq:=congrArg (fun r:Label→ℝ=>regularJointNorm
      (regularMainFamily F P (p.profile 0) (p.profile 1) Wfirst H0 r (amp/2)) a.Q) hradius
    have hmain':=hradEq.symm.le.trans hmain
    change regularJointNorm f (internalQ Q η₀) ≤ _ at hmain'
    calc
      _ ≤ C*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
          (p.control controls)^2*(1+|ht|+height)^degree*Z^(-(reserve/8)):=hmain'
      _ = _:=by ring
  exact ExceptionalPrice.positive_radius_transport Result (Real.rpow_one Z)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) (zero_lt_one.trans hZ) boundK

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_supplier_of_points
