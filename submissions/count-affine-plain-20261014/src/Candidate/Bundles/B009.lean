/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B005
import Candidate.Bundles.B007
import Candidate.Bundles.B008
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstActualFrequencyBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.StageMargins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.WidthRanges
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionLength

/- BEGIN ORIGINAL Cycle25.Assembly.Count.CertifiedMoments; sha256 9d124c3f3492ea2d981fdc689da256c910c548fd4e7614dfbf086347027c88b7 -/
section
                                         
                                                         
                                                                
                                                                        
                                                                   
namespace OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
theorem weighted_source_moments {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0<mesh)
    (hfine:∀j,D.ell j ≤ mesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0 ≤ J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Cycle25ProbeDetectorInverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
  · constructor
    · intro n hn σ hσ t ht
      exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
        rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
    · intro selected hselected hfirst hsecond n hn σ hσ t ht
      exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands

end
/- END ORIGINAL Cycle25.Assembly.Count.CertifiedMoments -/

/- BEGIN ORIGINAL Cycle25.Energy.FirstSourceParameters; sha256 8e96515a335d4e01dd1dbc32f048e5957f2ebb2adfee90479eb81b044d4a4b75 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/FirstSourceParameters.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                                    
                                                            
                                                     
                                                      

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤Bschedule)(ht:0≤ts)(hem:0≤em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤M)(hA:0≤A)(hB:0≤B)
    (hκ:(7/10:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0<sigma ∧ sigma≤1 ∧ 0<r/4 ∧ r/4≤sigma/4 ∧ r/4≤1 ∧
      0<sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0<maskEpsilon M B ε ∧ 0<mesh M B κ ε ∧
      mesh M B κ ε≤sigma/12 ∧ 0≤sigma/12 ∧ sigma/12<sigma/6 ∧
      0<2*sigma+1 ∧ 0≤A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0<sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(_hP:0≤P)(hB:0≤B)(hready:readyBudget A P≤B)
    (hκ:(7/10:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤M)(hB:0≤Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤Bmask):
    readyBudget A P≤CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.Cycle25CenteredMomentEnergyFirstSourceParameters

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.FirstSourceParameters -/

/- BEGIN ORIGINAL Cycle25.Energy.ReflectionRetainedLength; sha256 210a0fd97646a8c6fa82b64dec23d16055cd96032d1e6f8e618a6457e2fdca82 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Moments/ReflectionRetainedLength.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                           
                                                              

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.Cycle25CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤M/4) (hreflection : reflected≤M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0≤M) (hz : 0≤z) (hk : 7/10≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤37*M/48+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤15*M/16+xi := by
  have hkz : 16/5*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤5*M/96 := by linarith
  constructor <;> nlinarith

end SevenEighths.Cycle25CenteredMomentReflectionRetainedLength

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReflectionRetainedLength -/

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceState; sha256 0c89639bc5b9b258653308da376c5b004951596d230f49dc7dcc68a7bf9bb587 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceState.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                        
                                                       
                                                                 
                                              

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

export CenteredMomentEnergyReferenceState
  (effectiveRadial radialEnergy_effective effectiveState effective_row_norm
    effective_character_nonprincipal effective_character_cap comparisonFirst comparisonSecond
    comparison_positive comparison_same_product comparison_second_power)

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M):
    ell≤5*M/96 ∧
    1≤comparisonFirst Z M ∧
    comparisonFirst Z M≤comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤M:=by
  have hkell:16/5*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤5*M/96:=by linarith
  have hlen:M/2≤Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤37*M/48+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤15*M/16+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=Cycle25CenteredMomentReflectionRetainedLength.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.Cycle25CenteredMomentEnergyReferenceState

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceState -/
