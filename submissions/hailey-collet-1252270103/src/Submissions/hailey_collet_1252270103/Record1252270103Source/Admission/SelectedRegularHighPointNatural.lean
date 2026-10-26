/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed pre-slot loss and post-cardinality buffer instantiate the actual
HIGH source with one consistent set of numerical geometry budgets. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighPointSomeGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighPointNatural
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
variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (reserve θ mesh amp:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hm:0≤mesh)(hmesh:100*mesh≤θ)(hamp:0<amp)
variable (R₀:Ideal O)(hR₀:R₀≠0)
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)

def SourceAt
    (hparent:100*mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) θ) (J:ℕ)(τ:ℝ)(P:HighSourceParameters)(control:Finset (ℕ×ℕ))(C Z:ℝ) : Prop :=
  SelectedRegularHighSourceNatural.ActualAt M H hH (α:=α)
    ηanchor η₀ n low setup W
    bRad θ θ θ θ (1/100) 100 rmin 1 θ (highBuffer 1 1 εslot (θ/16))
    (highKappa εslot (θ/16)) (θ/16) εslot (εslot/4)
    (bufferCount (highBuffer 1 1 εslot (θ/16))) le_rfl θ 33 1 wmin hf.positive
    (by norm_num) (by norm_num) hc.wmin_pos hWs hW hbRad hrad
    hf.positive hf.positive hf.positive hf.positive (by norm_num) (by norm_num) hc.rmin_pos (by norm_num)
    hf.positive (hf.small.trans (by norm_num)) hc.buffer_pos hc.buffer_small hc.kappa_pos hc.kappa_le_one
    (div_nonneg hf.positive.le (by norm_num)) hc.density_budget hc.slot_pos (div_nonneg hc.slot_pos.le (by norm_num)) hc.slot_budget hc.slot_gap hβ
    (by linarith only [hβhi])
    (1/50) 2 (100*mesh) (by norm_num) (by norm_num) (by norm_num)
    (by linarith only [hf.positive]) (by linarith only [hf.small]) hc.live_lower
    (mul_nonneg (by norm_num) hm) hparent (hmesh.trans (hf.small.trans (by norm_num)))
    6 θ (by norm_num) (by norm_num) hf.positive 1 (θ/100) (by norm_num) (div_nonneg hf.positive.le (by norm_num))
    1 (1/4) (9/4) θ 2 (by norm_num) hf.positive (by norm_num) N θ hf.positive
    2 2 θ (amp/2) (lowerFactor N 1 (1/4)) 32 θ (by norm_num) (by norm_num) hf.positive
    (div_pos hamp (by norm_num)) (lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)) (by norm_num)
    R₀ hR₀ θ 2 1 1 1 hf.positive (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [SelectedSecondKeyCaps.coarseExponent]) le_rfl le_rfl hβhi J τ P control C Z

variable (bound:ℕ→ℝ)(hbound:∀k,0≤bound k)(J:ℕ)(control:Finset (ℕ×ℕ))(C Z:ℝ)
local notation "P"=>regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hbound

/-- The actual canonical selected family, with internally discharged profile,
coordinate, frozen-ideal and phase gates, enters the genuine fixed HIGH source. -/
theorem actual_point (hparent:100*mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) θ)
    (hs:SourceAt (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh amp
      N wmin rmin εslot hf hc hm hmesh hamp R₀ hR₀ hβ hβhi hparent J (P).τ P control C Z)
    {Label Row:Type}[Fintype Label](rows:Finset Row)[Nonempty rows]
    (a:Anchor α Z)(F:Family a Label)(second:Bool)(G:Selected F Row rows second)
    (c:Canonical M H hH W hW hWs ηanchor η₀ R₀ Z F.hZ F.s)
    (hR:F.R=R₀)(hmod:F.modifier=markedSourceModifier 1 1 1 1 (fun _=>1))
    (hD:F.D=1)(hreserve:F.reserve=θ)(hξ:0≤F.ξ)(hξθ:F.ξ≤θ)
    (bcell r height:ℝ)(hampEq:amp=sourceAReal n low bcell)(hamp1:amp≤1)
    (hamps:∀l,F.amp l=amp)(hN:Fintype.card α≤N)
    (hnodeB:(n.B:ℝ)≤1)(hnodeL:1≤(n.L:ℝ))(hnodeQ:1/2≤(n.q:ℝ))
    (hallow:θ≤(n.allowance:ℝ))(hallow1:(n.allowance:ℝ)≤1)
    (hw:∀i,0≤c.w i)(hwm:∀i,c.w i≤mesh)
    (hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1)
    (hr:0≤r)(hl1:Z^r≤c.X₁)(hl2:Z^r≤c.X₂)(href:c.Y₂=Z^r)
    (hwidthlo:bcell-θ≤∑i,c.w i)(hwidthhi:(∑i,c.w i)≤bcell)(hbcell:bcell≤1)
    (hOmega:frequencyLoss Z 32 F.ξ+θ≤(n.allowance:ℝ))
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps n low (none) bcell ν reserve)
    (hinj:Function.Injective G.key)
    (hTsec:∀l,F.Tsec (G.row l).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
      (3*F.amp (G.row l).val.1.1) F.reserve 2 N (F.first (G.row l).val.1))
    (hLcap:(G.L.absNorm:ℝ)≤Z^(4:ℝ))
    (hm0:F.m≠0)(hQmask:F.Q≤Ideal.span {(72:O)})(hml:goodLambda∣F.m)(hm2:(2:O)∣F.m)
    (hQM:F.Q≤M)(hQη:F.Q≤η₀.modulus)
    (pool Snew Anew:Finset (Ideal O))(depth:ℕ)(poolLoss BD Bsource:ℝ)
    (hpool:FixedCellPoolData pool Z amp (amp/2) mesh poolLoss BD Bsource depth)
    (hpoolLoss:poolLoss≤θ)(hdepthamp:(depth:ℝ)*amp<5)
    (hS:Snew⊆pool)(hA:Anew⊆Snew)(hdepth:Snew.card≤depth)
    (T:Finset α)(hT:∀l,T⊆(G.sel l).full)
    (hheight:|height|≤Z^(P).τ)(hslotheight:∀i,|height+c.v i|≤Z^(P).τ)
    (Wa:𝓢(ℝ,ℂ))(H0 radius:Label→ℝ)
    (hH0:∀l,0<H0 l)(hradius0:∀l,0≤radius l+6*amp)(hradius:∀l,radius l+6*amp≤32)
    (hZlarge:(9/4:ℝ)^2≤Z)(habsorb:(2:ℝ)^N*(9/4)^2*Z≤Z^(2:ℝ))
    (hannular:(2:ℝ)^(3*N)≤Z):
    let e:=highBuffer 1 1 εslot (θ/16)
    let annular:=3*(N:ℝ)*Real.logb Z 2
    let omega:=fun l:rows=>residualWeight F.datum (regularFamilyWeight F Wa (fun _=>pool) H0 radius (amp/2)) (G.row l).val
    ∃st:rows→NaturalState Z (P).Bmask (P).bΦ,
    ∃hfixed:∀l,(st l).fixedModulus=F.Q,
    ∃keep:∀l,(st l).radial.keep (G.z l),
    ∃select:rows→BufferIndex e,
    SharedState F rows second G M H hH η₀ P e (n.q:ℝ) θ annular wmin c.w T Snew Anew hQM hQη st hfixed keep select ∧
    (∑l∈Finset.univ.filter (fun l:rows=>(n.q+1)/2≤bufferValue e (select l)),
      ‖regularSelectedCentered G Snew Anew T height l‖^2*selectedPaidWeight (G.sel l) (omega l))≤
      pointBudget n N J θ reserve εslot wmin C Z P control F.s F.reflected F.bin F.ξ c.p := by
  intro e annular omega
  have hθ1:θ≤1:=hf.small.trans (by norm_num)
  have hz:0<Z:=zero_lt_one.trans F.hZ
  have hη:F.s.η=ηanchor:=c.fields.1
  have hcorn:=c.long_corners n r hnodeB hnodeL hw hadm hr hl1 hl2 href
  have hv:=c.volume_cap n hnodeB hnodeL hw hadm
  have hVlo:0≤Real.logb Z (volume F.s):=Real.logb_nonneg F.hZ hcorn.2.2.2.2.2
  have hVhi:Real.logb Z (volume F.s)≤1:=by
    simpa only [Real.logb_self_eq_one F.hZ] using Real.logb_le_logb_of_le F.hZ (volume_pos F.s) hv
  have hV:|Real.logb Z (volume F.s)|≤1:=by rw [abs_of_nonneg hVlo];exact hVhi
  have hsrc:=c.radius_cap N hN n hnodeB hnodeL hw hadm habsorb
  have hchild:∀l,sourceRadius (F.input (G.row l).val.1.1)≤Z^(2:ℝ):=by
    intro l
    exact (c.child_radius (F.stage (G.row l).val.1.1).common F.R (F.stage (G.row l).val.1.1).B
      (F.stage (G.row l).val.1.1).τ (F.stage (G.row l).val.1.1).t hw).trans hsrc
  have hfreq0:0≤frequencyLoss Z 32 F.ξ:=frequencyLoss_nonneg Z 32 F.ξ F.hZ (by norm_num) hξ
  have hrho:0≤frequencyLoss Z 32 F.ξ+F.reserve-θ:=by rw [hreserve];linarith
  have hFone:sourceFReal n low bcell≤1:=by rw [sourceFReal,←hampEq];linarith only [hamp]
  have hamps':∀l,F.amp (G.row l).val.1.1=sourceAReal n low bcell:=fun l=>(hamps _).trans hampEq
  have hpool0:∀p∈pool,p≠0:=fun p hp=>(hpool.prime p hp).ne_zero
  have hmask:1+(2:ℝ)+2+8+(depth:ℝ)*amp≤(P).Bmask:=by change _≤20;linarith only [hdepthamp]
  have hstate:=hs rows a F second G 1 1 1 1 (fun _=>1) hmod hη hR
    Wa 2 bcell reserve θ T c.w (fun _=>33/50) c.v (fun _=>height) c.ray
    (n.q:ℝ) (reserve/16) θ 256 hnodeQ hf.positive (by linarith only [hf.tiny,hf.positive]) hinj
    hD hξ (hξθ.trans hθ1) hξθ (by rw [hreserve];exact hf.positive.le)
    hamps' (by rw [←hampEq];exact hamp.le) hFone hrho hsrc hchild hTsec hLcap hm0 hQmask hml hm2 hQM hQη
    pool Snew Anew depth amp hS hA hdepth hamp.le hpool0 hpool.norm_upper hmask
  obtain ⟨st,hfixed,keep,select,hdata,henergy⟩:=hstate
  refine ⟨st,hfixed,keep,select,hdata,?_⟩
  let labels:Finset rows:=Finset.univ.filter (fun l=>(n.q+1)/2≤bufferValue e (select l))
  have hann0:0≤annular:=mul_nonneg (by positivity) (Real.logb_nonneg F.hZ (by norm_num))
  have hann1:annular≤1:=by
    have hh:=Real.logb_le_logb_of_le F.hZ (by positivity : (0:ℝ)<2^(3*N)) hannular
    rw [Real.logb_pow,Real.logb_self_eq_one F.hZ] at hh
    simpa only [annular,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hbox:=actual_coordinate_box F rows second G θ annular wmin c.w T hD hf.positive.le hθ1 hreserve
    (fun l=>by rw [hamps _,abs_of_pos hamp];exact hamp1)
    (by rw [abs_of_nonneg (add_nonneg hfreq0 hf.positive.le)];exact hOmega.trans hallow1)
    hV hsrc hchild hLcap hw (hwidthhi.trans hbcell) hann0 hann1
  have hx2:=SelectedRegularGeometryCaps.selected_radial_cap F rows second G n low bcell 1 1 1 1 (fun _=>1) hmod
    θ θ annular c.w wmin T hD hamps' hFone hrho
  have hradial:∀l∈labels,0≤G.x θ θ annular c.w wmin T l 2 ∧ G.x θ θ annular c.w wmin T l 2+θ≤2:=by
    intro l _
    rcases hdata l with ⟨_,_,_,_,_,_,_,_,hr⟩
    exact ⟨radial_nonnegative (G.key l) Z _ F.hZ hr,by linarith only [hx2 l,hθ1]⟩
  have hfrozen(l):=SelectedLowDictionary.actual_frozen_ideal_gates (G.sel l) F.R_ne
  have hpair:=High.CorrectedCentered.newton_divisor_pair_good pool Snew Anew hS hA hpool.prime
    (fun p hp=>by exact_mod_cast hpool.norm_ge_sixteen p hp)
  have havoid:=regular_original_newton_avoidance F.s pool Snew Anew Z amp (amp/2) mesh poolLoss BD Bsource depth
    hpool M H c.w c.fields.2.2.2.2.2.2.2.2.2 hwm hS hA
  have hW1(l):(G.sel l).finalInput.W₁=(c.p.profile 0:ℝ→ℂ):=c.fields.2.2.2.1
  have hW2(l):(G.sel l).finalInput.W₂=(c.p.profile 1:ℝ→ℂ):=c.fields.2.2.2.2.1
  have hrestore(l):(9/4:ℝ)^2*(G.sel l).finalInput.X₁*(G.sel l).finalInput.X₂≤Z^(2:ℝ):=by
    have hh:=(G.sel l).raw_caps F.s.X₁ F.s.X₂ F.s.Y₁ F.s.Y₂ le_rfl le_rfl le_rfl le_rfl
    have hp:(G.sel l).finalInput.X₁*(G.sel l).finalInput.X₂≤Z:=
      (mul_le_mul hh.1 hh.2.1 (G.sel l).finalInput.X₂_pos.le F.s.X₁_pos.le).trans hcorn.2.2.2.2.1
    have hh':(9/4:ℝ)^2*((G.sel l).finalInput.X₁*(G.sel l).finalInput.X₂)≤Z*Z:=
      mul_le_mul hZlarge hp (mul_pos (G.sel l).finalInput.X₁_pos (G.sel l).finalInput.X₂_pos).le hz.le
    simpa only [Real.rpow_two,pow_two,mul_assoc] using hh'
  have hphase(l):=actual_regular_phase F N 1 (1/4) (by norm_num) (by norm_num) hN
    (by rw [c.fields.2.1]) c.ordinary_lower.1 c.ordinary_lower.2
    Wa (fun _=>pool) H0 radius (amp/2) (by positivity)
    (fun l=>by rw [hamps l];exact hradius0 l) rows second G l
  have hvol:=c.source_volume n bcell θ (zero_le_one.trans hnodeL) hallow hwidthlo hwidthhi hadm
  have hout:=henergy (fun l _=>hbox l) hradial
    (by simpa only [CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hV.trans (show (1:ℝ)≤6 by norm_num)) (by rw [c.fields.2.1]) c.ordinary_lower.1 c.ordinary_lower.2
    hw (fun i=>by convert hwm i using 1 <;> ring) (hwidthhi.trans hbcell)
    (fun _=>le_rfl) (fun _=>le_rfl) (fun _ _=>hslotheight) (fun _ _=>hheight)
    (hf.root (100*mesh) (mul_nonneg (by norm_num) hm) hmesh).le hf.bin
    (by norm_num) (by rw [c.fields.2.2.1]) (by rw [c.fields.2.1]) c.fields.2.2.2.2.2.1
    (by simpa only [hD,one_mul] using hwidthlo) (by simpa only [hD,one_mul] using hwidthhi)
    (by rw [hD,one_mul];linarith only [hc.tiny_width,hallow]) (fun l _=>hT l)
    (by norm_num [hD]) (by norm_num [hD]) hf.positive.le
    (by simpa only [hD,one_mul,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hvol) (fun l _=>by rw [hD,one_mul];exact (hamps' l).le)
    (by simpa only [hD,hreserve,one_mul] using hOmega) hgaps
    (fun l=>Selection.frozenLeft (G.sel l)) (fun l=>Selection.frozenRight (G.sel l)) (fun _=>c.p)
    (9/4) ((c.p.control control)^2) hN (by norm_num) le_rfl (sq_nonneg _) hpair
    (fun l _=>(hfrozen l).1) (fun l _=>(hfrozen l).2.1) (fun l _=>(hfrozen l).2.2.2)
    (fun i=>by change c.w i/100≤1;apply (div_le_iff₀ (by norm_num)).mpr;linarith [hwm i,hmesh,hθ1])
    (fun i _ I hI=>havoid i I (by simpa only [c.fields.2.2.2.2.2.2.2.2.2 i] using hI))
    (fun l _=>hW1 l) (fun l _=>hW2 l)
    (hcorn.1.trans (by simpa only [regularParameters,actualPhysicalParameters,highParameters,mul_one,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num : (1:ℝ)≤100)))
    (hcorn.2.1.trans (by simpa only [regularParameters,actualPhysicalParameters,highParameters,mul_one,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num : (1:ℝ)≤100)))
    (hcorn.2.2.1.trans (by simpa only [regularParameters,actualPhysicalParameters,highParameters,mul_one,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num : (1:ℝ)≤100)))
    (hcorn.2.2.2.1.trans (by simpa only [regularParameters,actualPhysicalParameters,highParameters,mul_one,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num : (1:ℝ)≤100)))
    (fun l _=>hrestore l) (fun _ _=>le_rfl)
    (fun _=>pool) (fun l=>H0 (G.row l).val.1.1) (fun l=>radius (G.row l).val.1.1)
    (fun _=>mesh) (fun _=>poolLoss) (fun _=>BD) (fun _=>Bsource) (fun _=>depth) omega
    (fun l _=>by simpa only [hamps] using hpool) (fun l _=>hH0 _) (fun l _=>by simpa only [hamps] using hradius0 (G.row l).val.1.1)
    (fun l _=>by simpa only [hamps] using hradius (G.row l).val.1.1) (fun _ _=>hpoolLoss) (fun l _=>hphase l)
  have hcoeff(i):restoredSlotCoeff F.s i=originalRawCoefficient M H hH η₀ W Z c.w (fun _=>33/50) c.v c.ray i:=by
    funext I
    simp only [restoredSlotCoeff,c.input]
    rfl
  simpa only [regularSelectedCentered,regularSelectedSlots,c.fields.2.2.2.2.2.2.2.2.2,
    c.fields.2.2.2.2.2.1,hcoeff,pointBudget,labels,annular,e,hreserve,hD,one_mul,
    regularParameters,actualPhysicalParameters,highParameters,High.BufferedSelectedPaidSome.highBins,High.BufferedSelectedPaidNatural.highBins] using hout

end
end QRH.Record1252270103Source.Admission.SelectedRegularHighPointNatural
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPointNatural.actual_point
