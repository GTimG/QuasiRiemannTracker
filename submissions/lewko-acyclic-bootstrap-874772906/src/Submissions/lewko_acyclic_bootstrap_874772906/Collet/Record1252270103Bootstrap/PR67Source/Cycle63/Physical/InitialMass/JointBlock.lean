import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.JointSourceAssembly
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.Decomposition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.RatioBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstChildBound
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstReduced CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentFirstSourceReduction
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle63Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

structure FirstBlockSource where
  character : Character
  mask : O
  height : ℝ
  pool : Finset (Ideal O)
  beta : Ideal O → ℂ
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  sameSupport : primeSupport C = primeSupport D
  inactive : Finset (CommonIndex C D)
  rows : Finset O
  rows_ne : ∀ h ∈ rows, h ≠ 0
  K : ℝ
  K0 : ℝ
  H0 : ℝ
  A0 : ℝ
  B0 : ℝ
  K_pos : 0 < K
  K0_pos : 0 < K0
  H0_pos : 0 < H0
  A0_pos : 0 < A0
  B0_pos : 0 < B0

abbrev FirstBlockSource.LeftIndex (s : FirstBlockSource) := columns s.C s.C s.hC.1 s.pool
abbrev FirstBlockSource.RightIndex (s : FirstBlockSource) := columns s.C s.D s.hD.1 s.pool
abbrev FirstBlockSource.divisors (s : FirstBlockSource) :=
  divisorPool (Finset.univ : Finset s.RightIndex) (fun i => Ideal.span {element s.C s.D s.hD.1 s.pool i})
def FirstBlockSource.e (s : FirstBlockSource) := primeSubsetGenerator (fun P : CommonIndex s.C s.D => P.val) s.inactive
def FirstBlockSource.r (s : FirstBlockSource) := activeConductor s.C s.D
def FirstBlockSource.sextic (s : FirstBlockSource) := finiteSexticRow (activePrime s.C s.D) (activeGood s.C s.D s.hC) (activeExponent s.C s.D)
def FirstBlockSource.ratio (s : FirstBlockSource) := s.K0*s.H0/(s.A0*s.B0)
def FirstBlockSource.outside (s : FirstBlockSource) := scalar s.C s.D s.hC s.inactive s.K s.A0 s.B0
def FirstBlockSource.value (s : FirstBlockSource) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) :=
  block s.character s.mask 1 s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive s.rows W V s.K s.K0 s.H0 s.A0 s.B0

abbrev FirstSector {Label : Type*} (s : Label → FirstBlockSource) :=
  (l : Label) × (_L : ↥(s l).divisors) × RayCharacter × RayCharacter × ↥(s l).rows

def firstJointLeft {Label : Type*} (s : Label → FirstBlockSource) (weight : Label → ℂ)
    (q : FirstSector s) (i : (s q.1).LeftIndex) : ℂ :=
  weight q.1*(s q.1).outside*
    divisorCoefficient q.2.1.val (element (s q.1).C (s q.1).C (s q.1).hC.1 (s q.1).pool)
      (fun i => coefficient (s q.1).character (s q.1).mask 1 (s q.1).height (s q.1).beta (s q.1).C i*
        leftCoefficient (s q.1).e (s q.1).r (s q.1).sextic (element (s q.1).C (s q.1).C (s q.1).hC.1 (s q.1).pool i)) q.2.2.1 i*
    gaussRow _ (element_supported _ _ _ _ i) q.2.2.2.2.val

def firstJointRight {Label : Type*} (s : Label → FirstBlockSource)
    (q : FirstSector s) (i : (s q.1).RightIndex) : ℂ :=
  divisorCoefficient q.2.1.val (element (s q.1).C (s q.1).D (s q.1).hD.1 (s q.1).pool)
    (fun i => coefficient (s q.1).character (s q.1).mask 1 (s q.1).height (s q.1).beta (s q.1).D i*
      rightCoefficient (s q.1).e (s q.1).r (s q.1).sextic (element (s q.1).C (s q.1).D (s q.1).hD.1 (s q.1).pool i)) q.2.2.2.1⁻¹ i*
    gaussRow _ (element_supported _ _ _ _ i) (-q.2.2.2.2.val)

def firstJointWeight {Label : Type*} (s : Label → FirstBlockSource) (q : FirstSector s) : ℂ :=
  (UniqueFactorizationMonoid.moebius q.2.1.val : ℂ)*pairCoeff firstPhaseTable q.2.2.1 q.2.2.2.1*
    (star ((s q.1).sextic q.2.2.2.2.val)*(s q.1).sextic (s q.1).e)

def firstLeftLog (s : FirstBlockSource) (i : s.LeftIndex) := Real.log (‖eisEmbedding (element s.C s.C s.hC.1 s.pool i)‖^2/s.A0)
def firstRightLog (s : FirstBlockSource) (i : s.RightIndex) := Real.log (‖eisEmbedding (element s.C s.D s.hD.1 s.pool i)‖^2/s.B0)
def firstRho {Label : Type*} (s : Label → FirstBlockSource) (q : FirstSector s) :=
  Real.log ((s q.1).K/‖eisEmbedding (s q.1).e‖^2/‖eisEmbedding (s q.1).r‖^2/(s q.1).K0)
def firstX {Label : Type*} (s : Label → FirstBlockSource) (q : FirstSector s) :=
  Real.log (‖eisEmbedding q.2.2.2.2.val‖^2/(s q.1).H0)

theorem first_joint_weight_norm {Label : Type*} (s : Label → FirstBlockSource) (q : FirstSector s) :
    ‖firstJointWeight s q‖ ≤ 1 := by
  have hp : ‖pairCoeff firstPhaseTable q.2.2.1 q.2.2.2.1‖ ≤ 1 :=
    pairCoeff_norm_le firstPhaseTable 1 (fun u v => by
      unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
      split_ifs <;> norm_num) _ _
  have hh := QuadraticInitialBound.finiteSexticRow_norm_le_one (activePrime (s q.1).C (s q.1).D)
    (activeGood (s q.1).C (s q.1).D (s q.1).hC) (activeExponent (s q.1).C (s q.1).D)
  rw [firstJointWeight, norm_mul, norm_mul, norm_mul, norm_star]
  have hμp := mul_le_mul (CubicEisenstein.norm_ideal_moebius_le_one q.2.1.val) hp (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hρ := mul_le_mul (hh q.2.2.2.2.val) (hh (s q.1).e) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  simpa only [one_mul, FirstBlockSource.sextic] using mul_le_mul hμp hρ (by positivity) (by positivity)

/-- Exact first-transform expansion: the first label, divisor, both rays and
Fourier row all stay in the coordinate. -/
theorem actual_first_block_joint_expression {Label : Type*} [Fintype Label]
    (s : Label → FirstBlockSource) (weight : Label → ℂ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) :
    (∑ l, weight l*(s l).value W V) =
      ∑ q : FirstSector s, firstJointWeight s q*
        (∑ i : (s q.1).LeftIndex, ∑ j : (s q.1).RightIndex,
          (firstJointLeft s weight q i*star (firstJointRight s q j))*
          wholeKernel W V (s q.1).ratio (firstRho s q) (firstX s q)
            (firstLeftLog (s q.1) i) (firstRightLog (s q.1) j)) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [FirstBlockSource.value, block_eq_whole _ _ _ _ _ _ _ _ _ _ (s l).sameSupport _ _ (s l).rows_ne
    _ _ _ _ _ _ _ (s l).K_pos (s l).K0_pos (s l).H0_pos (s l).A0_pos (s l).B0_pos]
  dsimp only
  have hexp := first_row_children (s l).rows (Finset.univ : Finset (s l).LeftIndex)
    (Finset.univ : Finset (s l).RightIndex)
    (element (s l).C (s l).C (s l).hC.1 (s l).pool)
    (element (s l).C (s l).D (s l).hD.1 (s l).pool)
    (element_supported _ _ _ _) (element_supported _ _ _ _)
    (element_primary _ _ _ _) (element_primary _ _ _ _)
    (fun i => coefficient (s l).character (s l).mask 1 (s l).height (s l).beta (s l).C i)
    (fun j => coefficient (s l).character (s l).mask 1 (s l).height (s l).beta (s l).D j)
    (s l).e (s l).r (s l).sextic (finiteSexticRow_mul _ _ _)
    (fun h => star ((s l).sextic h))
    (fun h i j => wholeKernel W V (s l).ratio
      (Real.log ((s l).K/‖eisEmbedding (s l).e‖^2/‖eisEmbedding (s l).r‖^2/(s l).K0))
      (Real.log (‖eisEmbedding h‖^2/(s l).H0)) (firstLeftLog (s l) i) (firstRightLog (s l) j))
  erw [hexp]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.mul_sum]
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun L hL => Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ξ _ => ?_
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [firstJointWeight, firstJointLeft, firstJointRight, firstRho, firstX,
    firstLeftLog, firstRightLog, FirstBlockSource.outside, FirstBlockSource.e,
    FirstBlockSource.r, FirstBlockSource.sextic, FirstBlockSource.ratio, star_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance jointBlockDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Literal source data of an original physical-mass coordinate. -/
def originalFirstBlock (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (q : Cycle63JointSource.SourceCoordinate s R seed K Z ξ) : FirstBlockSource where
  character := s.η
  mask := CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R
  height := s.t
  pool := finiteColumns (Fintype.piFinset s.pools)
  beta := CenteredMomentOriginalCommonHarmonic.coefficient s R seed
  C := q.1.val.1
  D := q.1.val.2
  hC := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ q.1.property).1
  hD := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ q.1.property).2
  sameSupport := (CenteredMomentFirstSectors.commonLabels_data _ _ _ _ q.1.property).2.2
  inactive := q.2.1.val
  rows := retainedRows (CenteredMomentFirstNonexceptionalLocalWeightSum.localRadius s R seed K Z ξ q.1 q.2.1.val) 1
  rows_ne := CenteredMomentFirstPhysicalDyadicAssembly.retained_rows_nonzero _
  K := K
  K0 := dyadicScale (q.2.2 0)
  H0 := dyadicScale (q.2.2 1)
  A0 := dyadicScale (q.2.2 2)
  B0 := dyadicScale (q.2.2 3)
  K_pos := hK
  K0_pos := dyadicScale_pos _
  H0_pos := dyadicScale_pos _
  A0_pos := dyadicScale_pos _
  B0_pos := dyadicScale_pos _

/-- Exact normalized source characters of the two first-transform columns. -/
def originalFirstPair (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s R seed K Z ξ hK)) :=
  let B := originalFirstBlock s R seed K Z ξ hK q.1
  fixedPair s.η B.C B.D B.hC B.inactive q.2.2.1 q.2.2.2.1⁻¹

omit [DecidableEq ι] in
theorem actual_first_left_common_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ → ℂ)
    (q : FirstSector (originalFirstBlock s R seed K Z ξ hK)) (V : ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s R seed K Z ξ hK
    let B := source q.1
    CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft source weight q)
      V (firstLeftLog B) t =
      weight q.1*B.outside*commonWindow (CenteredMomentAmplificationChildInput.original s R seed)
        B.C B.hC (originalFirstPair s R seed K Z ξ hK q).left s.t t B.A0 V q.2.1.val q.2.2.2.2.val := by
  dsimp only
  let B := originalFirstBlock s R seed K Z ξ hK q.1
  let F := originalFirstPair s R seed K Z ξ hK q
  have hc := column_window_common (CenteredMomentAmplificationChildInput.original s R seed)
    B.C B.C B.hC.1 B.hC rfl F.left s.t t B.A0 V q.2.1.val _
    (F.left_column _ s.t q.2.1.val) q.2.2.2.2.val
  rw [←hc]
  simp only [CenteredMomentCauchy.leftColumn, firstJointLeft, firstLeftLog, gaussPolynomial,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let c := divisorCoefficient q.2.1.val (element B.C B.C B.hC.1 B.pool)
    (fun j => coefficient B.character B.mask 1 B.height B.beta B.C j*
      leftCoefficient B.e B.r B.sextic (element B.C B.C B.hC.1 B.pool j)) q.2.2.1 i
  let g := gaussRow (element B.C B.C B.hC.1 B.pool i) (element_supported _ _ _ _ i) q.2.2.2.2.val
  let f := columnPhase V (firstLeftLog B i) t
  change weight q.1*B.outside*c*g*f = weight q.1*B.outside*(c*f*g)
  ring

omit [DecidableEq ι] in
theorem actual_first_right_common_window (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s R seed K Z ξ hK)) (V : ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s R seed K Z ξ hK
    let B := source q.1
    CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight source q)
      V (firstRightLog B) t =
      star (commonWindow (CenteredMomentAmplificationChildInput.original s R seed)
        B.D B.hD (originalFirstPair s R seed K Z ξ hK q).right s.t (-t) B.B0
        (fun x => star (V x)) q.2.1.val (-q.2.2.2.2.val)) := by
  dsimp only
  let B := originalFirstBlock s R seed K Z ξ hK q.1
  let F := originalFirstPair s R seed K Z ξ hK q
  have hc := column_window_common (CenteredMomentAmplificationChildInput.original s R seed)
    B.C B.D B.hC.1 B.hD B.sameSupport F.right s.t (-t) B.B0
    (fun x => star (V x)) q.2.1.val _ (F.right_column B.hD _ s.t q.2.1.val)
    (-q.2.2.2.2.val)
  rw [←hc]
  simp only [CenteredMomentCauchy.rightColumn, firstJointRight, firstRightLog, gaussPolynomial,
    star_sum, star_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [←CenteredMomentConjugateWindow.star_columnPhase, star_star]
  let c := divisorCoefficient q.2.1.val (element B.C B.D B.hD.1 B.pool)
    (fun j => coefficient B.character B.mask 1 B.height B.beta B.D j*
      rightCoefficient B.e B.r B.sextic (element B.C B.D B.hD.1 B.pool j)) q.2.2.2.1⁻¹ i
  let g := gaussRow (element B.C B.D B.hD.1 B.pool i) (element_supported _ _ _ _ i) (-q.2.2.2.2.val)
  let f := columnPhase V (firstRightLog B i) t
  change star g*star c*f = star g*(f*star c)
  ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
