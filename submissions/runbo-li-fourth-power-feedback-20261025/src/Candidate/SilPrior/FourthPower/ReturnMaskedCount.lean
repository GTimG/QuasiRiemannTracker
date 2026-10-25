/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Masked amplitude-class counting for a common detector and source,
two amplification pairs and seventeen admitted windows.
PR69's original-row count theorem is applied with moments supplied by
UniformUnitFaceSource fullSourceFace. The selected height may depend on
the character after the polynomial degrees have been fixed.
-/
import Candidate.SilPrior.FourthPower.ReturnSourceInputs
import Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MomentMono
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MaskedSourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
import Candidate.SilPrior.FourthPower.ReturnMomentBridge
import Candidate.SilPrior.FourthPower.ReturnCountBridge
import Candidate.SilPrior.FourthPower.OlderIncumbentContract

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnMaskedCount
noncomputable section
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle25DetectorRowCount QRH.Record12518109Count QRH.Record12518109Existence
open ReturnSourceInputs ReturnWindows ReturnSourceFaces ReturnOldCount ReturnEnvelopeBridge

open ProbePhysical (calibrationForSet)

local instance : QRH.Record1252270103Return.Geometry.Parameters := ReturnSourceInputs.parameters
local instance : QRH.Record1252270103Return.CountScheme := ReturnWindows.countScheme

/-- A single height suffices both for the true count input and any fixed
physical degree. The last allowance is user-chosen before eta or the source.
It is an elementary scalar condition, never an analytic energy premise. -/
structure CountHeight (D : Detector) (physicalDegree heightLoss tau : ℝ) : Prop where
  pos : 0<tau
  le_one : tau≤1
  zero_rows : tau<(1/200:ℝ)/2
  detector_cost : 4*tau<(1/200:ℝ)*D.cost
  count_scale : 2*tau≤D.t
  physical_height : 2*tau*(1+physicalDegree)≤heightLoss

private theorem choose_count_height (D : Detector) (J Jw heightLoss : ℝ)
    (hJ : 0≤J) (hJw : 0≤Jw) (hheight : 0<heightLoss) :
    ∃tau : ℝ,CountHeight D Jw heightLoss tau ∧ 2*tau*(1+J)≤D.t := by
  let tau := min (1/1000:ℝ) (min (D.cost/1000)
    (min (D.t/(4*(J+Jw+1))) (heightLoss/(4*(Jw+1)))))
  have htau : 0<tau := by
    dsimp only [tau]
    exact lt_min (by norm_num) (lt_min (div_pos D.cost_pos (by norm_num))
      (lt_min (div_pos D.t_pos (by positivity)) (by positivity)))
  have h1 : tau≤1/1000 := min_le_left _ _
  have hcost : tau≤D.cost/1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hm : tau≤D.t/(4*(J+Jw+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hw : tau≤heightLoss/(4*(Jw+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm' : tau*(4*(J+Jw+1))≤D.t := (le_div_iff₀ (by positivity)).mp hm
  have hw' : tau*(4*(Jw+1))≤heightLoss := (le_div_iff₀ (by positivity)).mp hw
  have htauJ := mul_nonneg htau.le hJ
  have htauJw := mul_nonneg htau.le hJw
  refine ⟨tau,⟨htau,by linarith,by linarith,
    ?_,by nlinarith,by nlinarith⟩,by nlinarith⟩
  nlinarith [D.cost_pos]

variable {sigma affineError extraMesh : ℝ}

/-- This intermediate conclusion is supplied by the actual source moments;
its polynomial height is paid explicitly, including the zero-degree case. -/
theorem actual_moments_at_count_height (hPrior : OlderIncumbentContract.OlderIncumbentInput) (A : JointData sigma affineError extraMesh)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta)
    (Jw heightLoss : ℝ) (hJw : 0≤Jw) (hheight : 0<heightLoss) :
    ∀η : Character,∃tau : ℝ,CountHeight A.D Jw heightLoss tau ∧
      ∃C0 : ℝ,1≤C0 ∧ ∀ᶠZ : ℝ in atTop,
        QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound
          A.D (QRH.Record1252270103Return.GenericPhysical.baselineSource A.D A.F)
          A.counts η Z tau (C0*Z^A.D.t) (Z^(2*tau)) := by
  intro η
  obtain ⟨J,hJ,C,hC,hmom⟩ := actual_count_moments hPrior A hsource hbeta η
  obtain ⟨tau,htau,hJtau⟩ := choose_count_height A.D J Jw heightLoss hJ hJw hheight
  refine ⟨tau,htau,max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hmom tau htau.pos htau.le_one,eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply ReturnMomentBridge.source_moment_mono_constant (by linarith) hm
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z tau J A.D.t
    hC.le hZ htau.pos.le hJ hJtau).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (by linarith) _)

/-- Output notation for the original (unselected) detector rows and their
actual masked amplitude subclasses. The masked mean changes slot selection,
not the family being counted. All floating a,d,rows,bins remain after Z. -/
def ActualMaskedCount (A : JointData sigma affineError extraMesh)
    (η : Character) (tau Ctotal Z : ℝ) (n : ℕ) : Prop :=
  ∀d a : ℝ,(1/200:ℝ)≤d→d≤7/8→51/100<a→a≤7/8→
  ∀rows : Finset FreeRow,
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(d-A.D.t))→
  ∀i : ℕ,i≤n→
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^tau)<a+2*A.D.e)→
    (∀u∈rows,a≤detectorMaximum
      (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u))
      ((3*i:ℕ)*Z^tau))→
  ∀z : ℂ,z.re=17/50→|z.im|≤Z^(2*tau)→
  let Q := QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.canonicalFamily
    A.D (QRH.Record1252270103Return.GenericPhysical.baselineSource A.D A.F) Z z
  ∀main : Finset (Fin A.D.N),
  ∀bin : BinLabel (Finset.univ : Finset (Fin A.D.N)) ((2*a-1)/2) A.D.t,
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos
    (fun j=>A.D.length j/d) Q bin
  let q := weightedMean Finset.univ (fun j=>A.D.length j/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
  rows'.Nonempty→0≤q ∧ q≤(2*a-1)/2 ∧
    (rows'.card:ℝ)≤Ctotal*(Z^d)^
      (variableEnvelope contraryKappa (2*a-1) (q/(2*a-1))+sigma)

/-- Complete original-row count application. No SourceMomentBound is required
from the caller; it is produced from the one unfinished full source theorem.
The final exponent is IDENTICAL to the checked86-box feedback envelope. -/
theorem actual_masked_count (hPrior : OlderIncumbentContract.OlderIncumbentInput) (A : JointData sigma affineError extraMesh)
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hbeta : theta<HeckeZeroSupremum.beta)
    (Jw heightLoss : ℝ) (hJw : 0≤Jw) (hheight : 0<heightLoss) :
    ∀η : Character,∃tau : ℝ,CountHeight A.D Jw heightLoss tau ∧
      ∀n : ℕ,∃Ctotal : ℝ,1≤Ctotal ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ ActualMaskedCount A η tau Ctotal Z n := by
  intro η
  obtain ⟨tau,htau,C0,hC0,hmom⟩ :=
    actual_moments_at_count_height hPrior A hsource hbeta Jw heightLoss hJw hheight η
  refine ⟨tau,htau,?_⟩
  intro n
  obtain ⟨C,hC,hcount⟩ :=
    Candidate.SilPrior.FourthPower.ReturnCountBridge.source_masked_count_with_error
      A.D (QRH.Record1252270103Return.GenericPhysical.baselineSource A.D A.F)
      A.counts tau sigma n htau.pos htau.zero_rows htau.detector_cost
      htau.count_scale A.count_error
  refine ⟨C*C0,one_le_mul_of_one_le_of_one_le hC hC0,?_⟩
  filter_upwards [hmom,hcount η,eventually_gt_atTop (1:ℝ)] with Z hm hc hZ
  refine ⟨hZ,?_⟩
  intro d a hd hd' ha ha' rows hrows i hi hnext hcurrent z hz hzim
  dsimp only
  intro main bin hne
  obtain ⟨hq,hqtop,hcard⟩ :=
    hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim
      hm main bin hne
  refine ⟨hq,hqtop,?_⟩
  have hk := (contrary_gates hbeta).1
  have hdelta : 0<2*a-1 := by linarith
  have hp : (weightedMean Finset.univ (fun j=>A.D.length j/d)
      (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin)))/(2*a-1)
      ∈ Set.Icc (0:ℝ) (1/2) := by
    constructor
    · exact div_nonneg hq hdelta.le
    · apply (div_le_iff₀ hdelta).mpr
      linarith
  rw [A.moment_exact] at hcard
  change _≤C*C0*(Z^d)^(upstreamEnvelope contraryKappa (2*a-1) _+sigma) at hcard
  rw [upstreamEnvelope_eq_variable hk ⟨hdelta.le,by linarith⟩ hp] at hcard
  exact hcard

end
end Candidate.SilPrior.FourthPower.ReturnMaskedCount
