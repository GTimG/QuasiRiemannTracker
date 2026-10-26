/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularPoints
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
local instance regularSmallDecEq {ι : Type*} : DecidableEq ι := Classical.decEq _
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
theorem regular_small_normalized {α:Type}[Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell reserve θ mesh ξ width τsource Bslot Cpoint:ℝ)(N depth degree:ℕ)
    (controls:Finset (ℕ×ℕ))(hf:FixedBudget reserve 100 100 1 θ)
    (hslot:1≤Bslot)(hpoint:0<Cpoint)(hτ:0<τsource)(hamp0:0<sourceAReal n low bcell):
    ∃Cs:ℝ,0<Cs ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀hp:RegularPointAt (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
      bcell reserve θ mesh ξ width τsource N degree controls Cpoint Z,
    ∀(hZ:1<Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
    ∀(seed:Ideal O)(hs:Squarefree seed)(bin:ℤ×(Fin 5→ℤ))(reflected:Bool),
    let a:=i.anchor hH W hW hWs hZ ηanchor η₀ R₀ seed hR₀ hs 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
    ∀{Label:Type}[Fintype Label](F:Family a Label),
    Fintype.card α≤N→
    Function.Injective (fun l=>FirstAllocationSelection.columnKey F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column l))→
    (∀l,frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P≠0)→
    sourceRadius F.s≤Z^(2:ℝ)→
    (∀l,Z^(-(32:ℝ))≤F.Hmain l)→(∀l,F.Hmain l≤Z^(32:ℝ))→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^(4:ℝ))→
    (∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))→
    (∀j,1≤F.s.hi j)→(∀j,1≤F.s.P j)→0≤F.s.b₁→0≤F.s.b₂→
    ∀(P:Finset (Ideal O)),
    FixedCellPoolData P Z (sourceAReal n low bcell) ((sourceAReal n low bcell)/2) mesh θ 10 4 depth→
    (∀p∈P,∀j I,I∈F.s.slots j→¬p∣I)→
    2/((sourceAReal n low bcell)/2)≤depth→(depth:ℝ)*sourceAReal n low bcell<5→
    (9/4:ℝ)^2*(F.s.X₁*F.s.X₂)≤Z^(2:ℝ)→
    (∀j,∀p∈F.s.slots j,‖restoredSlotCoeff F.s j p‖≤Bslot)→
    (∀j,∀p∈F.s.slots j,(p.absNorm:ℝ)≤2*F.s.P j)→
    ∀(W₁ W₂ Wa:𝓢(ℝ,ℂ)),F.s.W₁=(W₁:ℝ→ℂ)→F.s.W₂=(W₂:ℝ→ℂ)→
    F.s.b₁≤9/4→F.s.b₂≤9/4→
    ∀(H0 radius:Label→ℝ),(∀l,0<H0 l)→
    (∀l,0≤radius l+6*sourceAReal n low bcell ∧ radius l+6*sourceAReal n low bcell≤32)→
    (∀l,F.amp l=sourceAReal n low bcell)→
    (∀l,F.Tsec l=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
      (3*sourceAReal n low bcell) θ 2 N (a.label (F.column l)))→
    ∀(ht height:ℝ),0≤height→(∀j,|i.freq j|≤height)→(∀l,(F.stage l).t=ht)→
    1+|ht|+height≤Z^(τsource/4)→
    ∀(second:Bool)(t u:ℝ),mellinPairHeight t u≤Z^(τsource/4)→
    modifiedSecondNormalizedSum second F.datum (regularModifier F P)
      (regularFamilyWeight F Wa (fun _=>P) H0 radius ((sourceAReal n low bcell)/2)) t u≤
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*(mellinPairHeight t u)^degree*Z^(-(reserve/4)):=by
  obtain ⟨Cf,hCf,ef⟩:=regular_finite_normalized reserve θ Bslot Cpoint N depth degree hf hslot hpoint
  refine ⟨Cf*mellinShiftConstant^degree,by unfold mellinShiftConstant;positivity,?_⟩
  filter_upwards [ef,eventually_nested_source_height τsource hτ] with Z hfin hheight
  refine ⟨hfin.1,?_⟩
  intro hp hZ i r hi seed hs bin reflected a Label _ F hN hinj hfreeze hsource hHlo hHhi hfreq hpool
    hhi hP hb1 hb2 P hcell havoid hdepth hdepth5 hplain hcoeff hnorm W1 W2 Wa hW1 hW2 hb1' hb2'
    H0 radius hH0 hrad hamp hfourier ht height hh hfreqs hstage hext second t u hpair
  have hz:0<Z:=zero_lt_one.trans hZ
  let shifted:=mellinShift ht second t u
  have hbound:1+|shifted|+height≤Z^τsource:=by
    have h:=hheight.2 ht height 0 0 t u false second hh
    simp only [mellinPairHeight,norm_zero,add_zero,mul_one,one_mul,mellinShift] at h
    simpa [shifted,mellinShift] using h hext hpair
  have hg:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hcof:RegularCofactorBound F second P depth
      (regularFamilyWeight F Wa (fun _=>P) H0 radius ((sourceAReal n low bcell)/2)) t u (9/4) 4
      (Cpoint*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|shifted|+height)^degree*Z^(-(reserve/2))):=by
    apply regular_cofactor_of_centered (α:=α) (Label:=Label) (a:=a) (Z:=Z) F second P depth
      (regularFamilyWeight F Wa (fun _=>P) H0 radius ((sourceAReal n low bcell)/2)) ht t u
      _ (by positivity) hstage
    intro Row _ rows _ G hkey hL hLcap hψ S hS A hA T hT
    have hS':S⊆P:=Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hA':A⊆S:=Finset.mem_powerset.mp hA
    apply hp hZ i r hi seed hs bin reflected second F hamp rows G hkey hLcap
      (fun r=>hfourier (G.row r).val.1.1) P S A 10 4 depth hcell hS' hA'
      (Finset.mem_filter.mp hS).2 hdepth5 T hT shifted height hh
    · intro j hj;exact hfreqs j
    · linarith [abs_nonneg shifted]
    · intro j;exact (abs_add_le shifted (i.freq j)).trans (by linarith [hfreqs j])
    · exact hH0
    · exact hrad
  have hn:=hfin.2 a F hN hinj hfreeze hsource hHlo hHhi hfreq hpool hhi hP hb1 hb2
    P (sourceAReal n low bcell) mesh hamp0 hcell havoid hdepth hplain hcoeff hnorm
    W1 W2 hW1 hW2 hb1' hb2'
    (regularFamilyWeight F Wa (fun _=>P) H0 radius ((sourceAReal n low bcell)/2))
    second t u (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
    ((i.p.control controls)^2) (1+|shifted|+height) (by positivity) (sq_nonneg _) (by linarith [abs_nonneg shifted]) hcof
  have he:=pow_le_pow_left₀ (show 0≤1+|shifted|+height by positivity)
    (literal_mellin_shift_height ht height t u second hh) degree
  calc
    _≤Cf*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|shifted|+height)^degree*Z^(-(reserve/4)):=hn
    _≤Cf*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(mellinShiftConstant*mellinPairHeight t u*(1+|ht|+height))^degree*
        Z^(-(reserve/4)):=by gcongr
    _=_:=by simp only [mul_pow];ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_small_normalized
