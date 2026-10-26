import Candidate.Cycle63.Assembly.Count.BaselineMoments
import Candidate.Cycle63.Assembly.Low.Probe
import Candidate.Cycle63.Assembly.Transport.PrincipalSignal
import Candidate.Cycle25.Assembly.Continuation
import Candidate.Cycle63.Assembly.Final.Parameters
import Candidate.Cycle63.Assembly.Count.ChosenHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Candidate.Cycle63.Assembly.Geometry
import Candidate.Cycle63.Assembly.Transport.HighApproximation

/- Original module: Candidate.Cycle63.Assembly.Final.SourceProbe. -/
section

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle63DetectorCount PrincipalSignalComparison

def sourceProbe (D : BaselineData) (F : BaselineSourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  Cycle63Low.normalizedProbe F.modulus ⊤ F.S F.maximal D.length 1 2
    (fun _=>F.w) F.W F.W η

theorem sourceProbe_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    sourceProbe D F η=O[atTop](fun Z : ℝ=>Z^(Assembly.signal Arithmetic.theta+loss)) := by
  have hh := Cycle63Low.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  exact hh

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|Arithmetic.theta<s.re} ∧
    (∀s : ℂ,Arithmetic.theta<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    Transport.remainder_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6) (by norm_num) (by norm_num),
    fun s hs=>Transport.PrincipalSignal.sourceCorrection_bound η S hS s hs⟩

theorem fixed_source_contract (D : BaselineData) (F : BaselineSourceData D)
    (loss sigma : ℝ) (hloss : 0<loss)
    (herror : ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-sigma))) :
    Cycle25.PrimitiveProbeContract Arithmetic.theta Assembly.signalShift loss sigma := by
  intro η _
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  simpa only [Assembly.signal] using sourceProbe_low D F loss hloss η
end
end Cycle63.FinalAssembly
end

/- Original module: Candidate.Cycle63.Assembly.Final.Height. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                        
                                          

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter
open OAI.SevenEighths Cycle63DetectorCount HeckeFamily

def HeightAdmissible (D : BaselineData) (P : TransportParameters D) (J τ : ℝ) : Prop :=
  0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ 2*τ≤D.t ∧
    τ*(2+4*P.eps)<D.t ∧ 2*τ*(1+J)≤D.t

theorem choose_height (D : BaselineData) (P : TransportParameters D)
    (J : ℝ) (hJ : 0≤J) : ∃τ : ℝ,HeightAdmissible D P J τ := by
  have ht:=D.t_pos
  have hcost:=D.cost_pos
  have heps:=P.eps_pos
  let τ : ℝ := min ((1/200:ℝ)*D.cost/16)
    (min (1/800) (min (D.t/(8*(J+1))) (D.t/(4*(2+4*P.eps)))))
  have hp : 0<τ := lt_min (by positivity)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hc : τ≤(1/200:ℝ)*D.cost/16 := min_le_left _ _
  have hd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hj : τ≤D.t/(8*(J+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he : τ≤D.t/(4*(2+4*P.eps)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hjm : τ*(8*(J+1))≤D.t := (le_div_iff₀ (by positivity)).mp hj
  have hem : τ*(4*(2+4*P.eps))≤D.t := (le_div_iff₀ (by positivity)).mp he
  refine ⟨τ,hp,by linarith,by linarith,?_,by nlinarith,by nlinarith⟩
  nlinarith [mul_nonneg hp.le hJ]

/-- The common height follows every fixed polynomial degree. -/
theorem height_admissible_mono {D : BaselineData} {P : TransportParameters D}
    {J J' τ : ℝ} (h : HeightAdmissible D P J τ) (hle : J'≤J) :
    HeightAdmissible D P J' τ := by
  rcases h with ⟨ht,hd,hc,hs,he,hJ⟩
  exact ⟨ht,hd,hc,hs,he,(mul_le_mul_of_nonneg_left (by linarith : 1+J'≤1+J)
    (by linarith : 0≤2*τ)).trans hJ⟩

/-- The same height absorbs a genuine count degree and any fixed source degree. -/
theorem actual_joint_height (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200)
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hfineA : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200)
    (Jw : ℝ) (hJw : 0≤Jw) :
    ∀η : Character,∃τ : ℝ,HeightAdmissible D P Jw τ ∧
      ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound D.toData (baselineSource D F) counts η Z τ
          (C*Z^D.t) (Z^(2*τ)) := by
  intro η
  obtain ⟨J,hJ,C,hC,hbound⟩ := actual_baseline_source_moments D F counts hβ hκβ hfine hdet hβhi hfineA η
  obtain ⟨τ,hheight⟩ := choose_height D P (J+Jw) (by positivity)
  have hw : HeightAdmissible D P Jw τ := height_admissible_mono hheight (by linarith)
  have hc : HeightAdmissible D P J τ := height_admissible_mono hheight (by linarith)
  refine ⟨τ,hw,?_⟩
  refine ⟨max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ hc.1 (by linarith [hc.2.1]),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t hC.le hZ hc.1.le hJ
    (by linarith [hc.2.2.2.2.2])).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end Cycle63.FinalAssembly
end

/- Original module: Candidate.Cycle63.Assembly.Final.Baseline. -/
section

set_option autoImplicit false
namespace Cycle63.FinalAssembly
open OAI.SevenEighths

theorem baseline_beta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : Arithmetic.theta<HeckeZeroSupremum.beta) :
    (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 ∧
      2*HeckeZeroSupremum.beta-1≤(3/4:ℝ) ∧ (51/100:ℝ)≤HeckeZeroSupremum.beta := by
  have ht : (85/100:ℝ)<Arithmetic.theta := by norm_num [Arithmetic.theta]
  have hi:=baseline_beta
  constructor
  · linarith
  constructor <;> linarith
end Cycle63.FinalAssembly
end

/- Original module: Candidate.Cycle63.Assembly.Final.FixedHigh. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                         
                                    
                                      
                                                   

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle63DetectorCount PrincipalSignalComparison Cycle63HighTransport

/-- The finite numerator remains the honest analytic integration prerequisite. -/
def FixedFiniteNumeratorInput (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) : Prop :=
  ∀n : ℕ,0<n → ∀η : Character,
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

/-- The finite numerator bound for one character. -/
def FixedFiniteNumeratorInputAt (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀n : ℕ,0<n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

theorem sourceProbe_high_of_finite_numerator (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : Arithmetic.theta≤HeckeZeroSupremum.beta)
    (hfinite : FixedFiniteNumeratorInput D F P τ) :
    ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal Arithmetic.theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)<Assembly.signal Arithmetic.theta := by
      norm_num [Assembly.signal,Assembly.signalShift,Arithmetic.theta,Arithmetic.x,Arithmetic.ell]
    linarith
  have hcap : Arithmetic.h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [Arithmetic.h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Transport.rowExtension]) P.floor_budget hfinite
  simpa only [sourceProbe] using hh
theorem sourceProbe_high_of_finite_numerator_at (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : Arithmetic.theta≤HeckeZeroSupremum.beta)
    (η : Character) (hfinite : FixedFiniteNumeratorInputAt D F P τ η) :
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal Arithmetic.theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)<Assembly.signal Arithmetic.theta := by
      norm_num [Assembly.signal,Assembly.signalShift,Arithmetic.theta,Arithmetic.x,Arithmetic.ell]
    linarith
  have hcap : Arithmetic.h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [Arithmetic.h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator_at F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Transport.rowExtension]) P.floor_budget η hfinite
  simpa only [sourceProbe] using hh
end
end Cycle63.FinalAssembly
end

/- Original module: Candidate.Cycle63.Assembly.Final.CommonProbe. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                       

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Cycle63DetectorCount

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  detector_fine : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t

theorem exists_chosen_data (hβ : Arithmetic.theta<HeckeZeroSupremum.beta) : Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  obtain ⟨D,hκ,hbudget,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1
    (show 0<(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 by positivity)
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  exact ⟨⟨D,hκ,hbudget,hfine,hdet,P,F,counts⟩⟩

/-- Honest intermediate source obligation. Fixed data and polynomial degree precede
height; actual baseline source moments at that height are supplied by the assembly. -/
def FiniteNumeratorAssemblyInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∀A : ChosenData,∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : FiniteNumeratorAssemblyInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A⟩ := exists_chosen_data hβ
  obtain ⟨J,hJ,hfinite⟩ := hinput hβ A
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=>by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Cycle63.FinalAssembly
end
