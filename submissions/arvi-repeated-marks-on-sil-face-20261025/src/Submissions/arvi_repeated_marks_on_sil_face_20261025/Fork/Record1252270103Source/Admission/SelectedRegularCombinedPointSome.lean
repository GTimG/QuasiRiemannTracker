/- Repeated marks: fork of Record1252270103Source.Admission.SelectedRegularCombinedPointSome (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Admission.SelectedRegularHighPointSome
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW corners and HIGH bins use the same retained states and selector.
The one point constant precedes every moving canonical input and row family. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
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
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint
variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (Kgraph:ℚ)(bcell reserve θ mesh ξ width:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (sc:Scalar Kgraph n low bcell θ mesh ξ width)
variable (hmesh:100*mesh≤θ)(hwidth:width≤θ)(hbcell:bcell≤1)
variable (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))(hq:1/2≤(n.q:ℝ))
variable (R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)(hQM:Q≤M)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)
variable (bound:ℕ→ℝ)(hbound:∀k,0≤bound k)(J JL:ℕ)(SL SH:Finset (ℕ×ℕ))
variable (CL Cpref Cslot CH:ℝ)(hCL:0≤CL)(hCpref:0≤Cpref)(hCslot:0≤Cslot)(hCH:0≤CH)
local notation "P"=>regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hbound
local notation "amp"=>sourceAReal n low bcell

include hwidth hbcell hr hfee hq hQ72 hCL hCpref hCslot hCH in
/-- A single fixed constant bounds the complete original row family, after
applying the genuine earlier sources to the same actual retained states. -/
theorem eventually_actual_point_rm (hN:Fintype.card α≤N)
    (high:Source)(hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    ∃Cpoint:ℝ,0<Cpoint ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
      RegularLowAt (α:=α) M H hH n low bcell θ mesh εslot (P).τ N
        (fun _=>initialSlotBound W hW hWs) W ηanchor η₀ Q hQM Cslot Cpref JL SL CL Z→
      SelectedRegularHighPointSome.SourceAt_rm (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad
        reserve θ mesh amp N wmin rmin εslot hf hc sc.mesh_nonneg hmesh sc.geometry.a_pos
        R₀ hR₀ hβ hβhi high hB0 hB1 hlam hcap0 hcap1 hparent J (P).τ P SH CH Z→
      ∀(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
      ∀(seed:Ideal O)(hs:Squarefree seed)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),
      let a:=i.anchor hH W hW hWs hZ ηanchor η₀ R₀ seed hR₀ hs 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
      ∀{Label:Type}[Fintype Label](F:Family a Label),(∀l,F.amp l=amp)→
      ∀{Row:Type}(rows:Finset Row)(G:Selected F Row rows second),Function.Injective G.key→
        (G.L.absNorm:ℝ)≤Z^(4:ℝ)→
        (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
          (3*amp) θ 2 N (F.first (G.row u).val.1))→
      ∀(pool S A:Finset (Ideal O))(BD Bsource:ℝ)(depth:ℕ),
        FixedCellPoolData pool Z amp (amp/2) mesh θ BD Bsource depth→
        S⊆pool→A⊆S→S.card≤depth→(depth:ℝ)*amp<5→
      ∀T:Finset α,(∀u,T⊆(G.sel u).full)→
      ∀(t height:ℝ),0≤height→(∀j∈T,|i.freq j|≤height)→
        |t|≤Z^(P).τ→(∀j,|t+i.freq j|≤Z^(P).τ)→
      ∀(Wa:𝓢(ℝ,ℂ))(H0 mainRadius:Label→ℝ),(∀l,0<H0 l)→
        (∀l,0≤mainRadius l+6*amp ∧ mainRadius l+6*amp≤32)→
      (∑u:rows,‖regularSelectedCentered G S A T t u‖^2*
        selectedPaidWeight (G.sel u) (residualWeight F.datum
          (regularFamilyWeight F Wa (fun _=>pool) H0 mainRadius (amp/2)) (G.row u).val))≤
      Cpoint*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
        (i.p.control (regularProfileControl SL SH))^2*(1+|t|+height)^JL*Z^(-(reserve/2)):=by
  let pcCap:=((initialSlotBound W hW hWs)^N)^2*(2:ℝ)^N
  obtain ⟨Cpoint,hCpoint,hpay⟩:=regular_point_budgets_paid n reserve θ εslot wmin rmin N J JL
    hf hc hr hfee hq W bound hWs hW hbound CL Cpref Cslot CH pcCap SL SH
    hCL hCpref hCslot hCH (by dsimp [pcCap];positivity)
  refine ⟨Cpoint,hCpoint,?_⟩
  filter_upwards [eventual_scale_guards N θ ξ hf.positive sc.xi_pos.le sc.xi_loss,
    eventually_initial_low_point Kgraph n low bcell θ mesh ξ width εslot (P).τ sc N hN
      M H hH W hW hWs ηanchor η₀ Q hQM R₀ hR₀ Cslot Cpref JL SL CL]
    with Z hguard hLow
  refine ⟨hguard.1,?_⟩
  intro hZ hAtLow hAtHigh i r hi seed hs bin reflected second a Label instLabel F hamps Row rows G
    hinj hLcap hTsec pool S A BD Bsource depth hpool hS hA hdepth hdepthamp T hT
    t height hheight hfreq ht hslot Wa H0 mainRadius hH0 hradius
  have hgeometry:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  by_cases hrows:Nonempty rows
  · letI:Nonempty rows:=hrows
    let c:=initialCanonical i hH W hW hWs hZ ηanchor η₀ R₀
    have hnB:(n.B:ℝ)≤1:=by exact_mod_cast sc.parent.2.1
    have hnL:1≤(n.L:ℝ):=by exact_mod_cast sc.parent.2.2.1.le
    have ha1:amp≤1:=by linarith [sc.geometry.a_small]
    have hallow:θ≤(n.allowance:ℝ):=by linarith [sc.loss_small,sc.allowance_pos]
    have hallow1:(n.allowance:ℝ)≤1:=by linarith [sc.geometry.a_allowance,sc.geometry.a_small]
    have hwidthlo:bcell-θ≤∑j,i.w j:=by linarith [hi.cell_lower]
    have homega:frequencyLoss Z 32 ξ+θ≤(n.allowance:ℝ):=by linarith [hguard.2.2.2.2.2,sc.loss_small,sc.allowance_pos]
    have hm0:F.m≠0:=mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R₀ hR₀)
    have hml:goodLambda∣F.m:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
    have hm2:(2:O)∣F.m:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
    have hQMF:F.Q≤M:=inf_le_left.trans hQM
    have hQη:F.Q≤η₀.modulus:=inf_le_right
    have hTsec':∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve 2 N (F.first (G.row u).val.1):=by
      intro u
      change F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
        (3*F.amp (G.row u).val.1.1) θ 2 N (F.first (G.row u).val.1)
      rw [hamps]
      exact hTsec u
    obtain ⟨st,hfixed,keep,select,hdata,hHigh⟩:=SelectedRegularHighPointSome.actual_point_rm
      M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh amp N wmin rmin εslot
      hf hc sc.mesh_nonneg hmesh sc.geometry.a_pos R₀ hR₀ hβ hβhi bound hbound J SH CH Z
      high hB0 hB1 hlam hcap0 hcap1 hparent hAtHigh rows a F second G c rfl rfl rfl rfl sc.xi_pos.le sc.xi_loss
      bcell r t rfl ha1 hamps hN hnB hnL hq hallow hallow1 hi.widths_nonneg hi.widths_mesh hi.face
      hi.r_nonneg hi.long_left hi.long_right hi.reference hwidthlo hi.cell_upper hbcell homega hgaps hinj
      hTsec' hLcap hm0 hQ72 hml hm2 hQMF hQη pool S A depth θ BD Bsource hpool le_rfl
      hdepthamp hS hA hdepth T hT ht hslot Wa H0 mainRadius hH0 (fun l=>(hradius l).1)
      (fun l=>(hradius l).2) hguard.2.1 hguard.2.2.1 hguard.2.2.2.1
    simp only [show F.reflected=reflected from rfl,show F.bin=bin from rfl,
      show F.ξ=ξ from rfl,show c.p=i.p from rfl] at hHigh
    let shared:Shared G M H hH η₀ Q hQM S A (highBuffer 1 1 εslot (θ/16)) (P).τ:={
      states:=st, fixed:=hfixed, keep:=keep, select:=select,
      gates:=fun u=>by
        rcases hdata u with ⟨hc',hp,hw,hbin,_,_,hprof,hkey,_⟩
        exact ⟨hc',hp,hw,hprof,hbin,hkey⟩ }
    have hpair:=High.CorrectedCentered.newton_divisor_pair_good pool S A hS hA hpool.prime
      (fun p hp=>by exact_mod_cast hpool.norm_ge_sixteen p hp)
    have havoid:=regular_original_newton_avoidance F.s pool S A Z amp (amp/2) mesh θ BD Bsource depth
      hpool M H i.w (fun _=>rfl) hi.widths_mesh hS hA
    have hL:=hLow.2 hZ hAtLow i r hi seed 1 1 1 1 (fun _=>1) hs bin reflected second
      F hamps rows G hinj hLcap hTsec pool S A mesh BD Bsource depth hpool hS hA hdepth hdepthamp hpair
      T hT (fun j _ I hI=>havoid j I hI) shared t height hheight hfreq (fun j _=>hslot j)
      Wa H0 mainRadius hH0 hradius
    dsimp only [shared] at hL
    have hfuse:=regular_selected_source_fusion G S A T t (highBuffer 1 1 εslot (θ/16)) (n.q:ℝ) select
      (fun u=>residualWeight F.datum (regularFamilyWeight F Wa (fun _=>pool) H0 mainRadius (amp/2)) (G.row u).val)
      (fun _=>residualWeight_nonneg _ _ _) (by change (9/4:ℝ)≤9/4;rfl) (by change (9/4:ℝ)≤9/4;rfl)
      hpair (regularLowBudget N JL CL Cpref Cslot (forcedProfileCost F.s)
        (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
        ((i.p.control SL)^2) (1+|t|+height) Z (lowExponent n θ εslot N)) _
      (fun side=>by exact hL side) hHigh
    have hpc:=InitialPhysical.initial_cost_bounds M H hH W hW hWs Z (zero_lt_one.trans hZ)
      ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same N hN
    have hpaid:=hpay F.s Z ξ (1+|t|+height) i.p reflected bin hZ (by linarith only [abs_nonneg t,hheight])
      hpc.2 hguard.2.2.2.2.1 hguard.2.2.2.2.2
    exact hfuse.trans (by simpa only [regularLowBudget,←low_loss_eq] using hpaid)
  · letI:IsEmpty rows:=not_nonempty_iff.mp hrows
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    positivity

end
end QRH.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
