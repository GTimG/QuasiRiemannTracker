import Candidate.Cycle63.Physical.JointSourceAssembly
import Candidate.Cycle63.Physical.InitialMass.Decomposition
import Candidate.Cycle63.Physical.InitialMass.RatioBins
import Candidate.Cycle63.Moment.JointKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource

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
  apply Finset.sum_congr rfl
  intro l _
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
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [firstJointWeight, firstJointLeft, firstJointRight, firstRho, firstX,
    firstLeftLog, firstRightLog, FirstBlockSource.outside, FirstBlockSource.e,
    FirstBlockSource.r, FirstBlockSource.sextic, FirstBlockSource.ratio, star_mul]
  ring

/-- One common dyadic-ratio group is contracted before taking any label supremum. -/
theorem actual_first_joint_contraction (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Label : Type*} [Fintype Label] [DecidableEq Label]
      (s : Label → FirstBlockSource) (weight : Label → ℂ) (R : ℝ),
      0 < R → (∀ l, (s l).ratio = R) →
      (∀ q : FirstSector s, ‖V 0 (firstRho s q)‖ ≤ 1) →
      (∀ q : FirstSector s, ‖V 1 (firstX s q)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ,
        Real.sqrt (∑ q : FirstSector s,
          ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft s weight q)
            (V 2) (firstLeftLog (s q.1)) t‖^2) *
        Real.sqrt (∑ q : FirstSector s,
          ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight s q)
            (V 3) (firstRightLog (s q.1)) t‖^2) ≤ E*(1+‖t‖)^J) →
      (1+R)^A*‖∑ l, weight l*(s l).value W V‖ ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s weight R hR hr hV0 hV1 E hE he
  rw [actual_first_block_joint_expression]
  simp_rw [hr]
  exact hbound R hR (Label := Label) (κ := FirstSector s)
    (α := fun l => (s l).LeftIndex) (β := fun l => (s l).RightIndex)
    Finset.univ (fun q => q.1)
    (firstJointLeft s weight) (firstJointRight s) (fun l => firstLeftLog (s l))
    (fun l => firstRightLog (s l)) (firstRho s) (firstX s) (firstJointWeight s)
    (fun q _ => first_joint_weight_norm s q) (fun q _ => hV0 q) (fun q _ => hV1 q)
    E hE he

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

omit [DecidableEq ι] in
lemma originalFirstBlock_value (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (K Z ξ : ℝ) (hK : 0<K) (q : Cycle63JointSource.SourceCoordinate s R seed K Z ξ) :
    (originalFirstBlock s R seed K Z ξ hK q).value W (fun _ => logAnnulus) =
      Cycle63JointSource.coordinateBlock s R seed W K Z ξ q := rfl

/-- The complete original physical mass is this joint first-sector expression.
The phase aligns the actual blocks and costs at most one. -/
theorem actual_physical_mass_first_sector_expression (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K) :
    let source := originalFirstBlock s R seed K Z ξ hK
    let phase := fun q => normPhase (Cycle63JointSource.coordinateBlock s R seed W K Z ξ q)
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ =
      ‖∑ q : FirstSector source, firstJointWeight source q*
        (∑ i : (source q.1).LeftIndex, ∑ j : (source q.1).RightIndex,
          (firstJointLeft source phase q i*star (firstJointRight source q j))*
          wholeKernel W (fun _ => logAnnulus) (source q.1).ratio
            (firstRho source q) (firstX source q)
            (firstLeftLog (source q.1) i) (firstRightLog (source q.1) j))‖ := by
  dsimp only
  rw [← actual_first_block_joint_expression]
  simp_rw [originalFirstBlock_value]
  exact actual_physical_mass_joint_sum s R seed W K Z ξ

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
  apply Finset.sum_congr rfl
  intro i _
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
  apply Finset.sum_congr rfl
  intro i _
  rw [←CenteredMomentConjugateWindow.star_columnPhase, star_star]
  let c := divisorCoefficient q.2.1.val (element B.C B.D B.hD.1 B.pool)
    (fun j => coefficient B.character B.mask 1 B.height B.beta B.D j*
      rightCoefficient B.e B.r B.sextic (element B.C B.D B.hD.1 B.pool j)) q.2.2.2.1⁻¹ i
  let g := gaussRow (element B.C B.D B.hD.1 B.pool i) (element_supported _ _ _ _ i) (-q.2.2.2.2.val)
  let f := columnPhase V (firstRightLog B i) t
  change star g*star c*f = star g*(f*star c)
  ring

omit [DecidableEq ι] in
/-- The joint left column is the literal Mellin integral of the allocation
polynomials, including their frozen coefficients. -/
theorem actual_first_left_allocation_mellin (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ → ℂ)
    (q : FirstSector (originalFirstBlock s R seed K Z ξ hK))
    (hseed : seed ∣ (originalFirstBlock s R seed K Z ξ hK q.1).C)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (T t : ℝ) :
    let source := originalFirstBlock s R seed K Z ξ hK
    let B := source q.1
    (Real.sqrt T:ℂ)⁻¹*CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft source weight q) V (firstLeftLog B) t =
      weight q.1*B.outside*∫ u : ℝ,
        columnDensity V hc hs u*logPhase (t-u) (Real.log B.A0)*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            B.C q.2.1.val (originalFirstPair s R seed K Z ξ hK q).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val := by
  dsimp only
  rw [actual_first_left_common_window]
  let B := originalFirstBlock s R seed K Z ξ hK q.1
  have h := common_window_original_integral (CenteredMomentAmplificationChildInput.original s R seed)
    s.pools_ne s.prime B.C B.hC hseed (originalFirstPair s R seed K Z ξ hK q).left
    s.t T t B.A0 B.A0_pos V hc hs q.2.1.val q.2.2.2.2.val
  change _ = _*∫u : ℝ, columnDensity V hc hs u*logPhase (t-u) (Real.log B.A0)*
    allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) B.C q.2.1.val
      (originalFirstPair s R seed K Z ξ hK q).left (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val
  simp only [allocatedPolynomial]
  rw [←h]
  ring

omit [DecidableEq ι] in
/-- The right column keeps its actual reflected row and conjugate window. -/
theorem actual_first_right_allocation_mellin (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s R seed K Z ξ hK))
    (hseed : seed ∣ (originalFirstBlock s R seed K Z ξ hK q.1).D)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (T t : ℝ) :
    let source := originalFirstBlock s R seed K Z ξ hK
    let B := source q.1
    (Real.sqrt T:ℂ)⁻¹*CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight source q) V (firstRightLog B) t =
      star (∫ u : ℝ,
        columnDensity (fun x => star (V x)) (CenteredMomentConjugateWindow.conjugate_compact V hc)
          (CenteredMomentConjugateWindow.conjugate_smooth V hs) u*
        logPhase (-t-u) (Real.log B.B0)*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed)
            B.D q.2.1.val (originalFirstPair s R seed K Z ξ hK q).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)) := by
  dsimp only
  rw [actual_first_right_common_window]
  let B := originalFirstBlock s R seed K Z ξ hK q.1
  have h := common_window_original_integral (CenteredMomentAmplificationChildInput.original s R seed)
    s.pools_ne s.prime B.D B.hD hseed (originalFirstPair s R seed K Z ξ hK q).right
    s.t T (-t) B.B0 B.B0_pos (fun x => star (V x))
    (CenteredMomentConjugateWindow.conjugate_compact V hc)
    (CenteredMomentConjugateWindow.conjugate_smooth V hs) q.2.1.val (-q.2.2.2.2.val)
  simp only [allocatedPolynomial]
  rw [←h]
  let c := commonWindow (CenteredMomentAmplificationChildInput.original s R seed) B.D B.hD
    (originalFirstPair s R seed K Z ξ hK q).right s.t (-t) B.B0
    (fun x => star (V x)) q.2.1.val (-q.2.2.2.2.val)
  change (Real.sqrt T:ℂ)⁻¹*star c = star ((Real.sqrt T:ℂ)⁻¹*c)
  simp


def firstJointEnergyPair {Label : Type*} [Fintype Label] (source : Label → FirstBlockSource)
    (weight : Label → ℂ) (V : Fin 4 → ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∑ q : FirstSector source,
    ‖CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft source weight q)
      (V 2) (firstLeftLog (source q.1)) t‖^2)*
  Real.sqrt (∑ q : FirstSector source,
    ‖CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight source q)
      (V 3) (firstRightLog (source q.1)) t‖^2)

omit [DecidableEq ι] in
/-- The outside scalar remains squared inside the joint left energy. -/
theorem actual_first_joint_energy_common_windows (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ → ℂ)
    (V : Fin 4 → ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s R seed K Z ξ hK
    firstJointEnergyPair source weight V t =
      Real.sqrt (∑ q : FirstSector source,
        ‖weight q.1‖^2*‖(source q.1).outside‖^2*
          ‖commonWindow (CenteredMomentAmplificationChildInput.original s R seed)
            (source q.1).C (source q.1).hC
            (originalFirstPair s R seed K Z ξ hK q).left s.t t
            (source q.1).A0 (V 2) q.2.1.val q.2.2.2.2.val‖^2)*
      Real.sqrt (∑ q : FirstSector source,
        ‖commonWindow (CenteredMomentAmplificationChildInput.original s R seed)
          (source q.1).D (source q.1).hD
          (originalFirstPair s R seed K Z ξ hK q).right s.t (-t)
          (source q.1).B0 (fun x => star (V 3 x)) q.2.1.val (-q.2.2.2.2.val)‖^2) := by
  dsimp only
  unfold firstJointEnergyPair
  simp_rw [actual_first_left_common_window, actual_first_right_common_window,
    norm_mul, norm_star, mul_pow]

def ratioFirstSource (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (r : ℤ) (q : SourceRatioFiber s R seed K Z ξ r) :=
  originalFirstBlock s R seed K Z ξ hK q.val

def ratioFirstPhase (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ)
    (r : ℤ) (q : SourceRatioFiber s R seed K Z ξ r) :=
  normPhase (coordinateBlock s R seed W K Z ξ q.val)

/-- Actual physical mass is contracted over each genuine ratio group, with
all first labels inside the matched column energy. -/
theorem actual_physical_mass_joint_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
      (E : ℤ → ℝ), (∀r∈sourceRatioBins s R seed K Z ξ, 0≤E r) →
      (∀r∈sourceRatioBins s R seed K Z ξ, ∀t : ℝ,
        firstJointEnergyPair (ratioFirstSource s R seed K Z ξ hK r)
          (ratioFirstPhase s R seed W K Z ξ r) (fun _ => logAnnulus) t ≤
          E r*(1+‖t‖)^J) →
      physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*∑r∈sourceRatioBins s R seed K Z ξ, E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hbound⟩ := actual_first_joint_contraction W (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ _ hn => CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro s R seed K Z ξ hK E hE he
  rw [actual_physical_mass_ratio_groups,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hh := hbound (ratioFirstSource s R seed K Z ξ hK r)
    (ratioFirstPhase s R seed W K Z ξ r) (dyadicScale r) (dyadicScale_pos r)
    (fun q => actual_source_ratio_fiber s R seed K Z ξ r q)
    (fun q => logAnnulus_norm _) (fun q => logAnnulus_norm _) (E r) (hE r hr) (he r hr)
  have hp : 0<(1+dyadicScale r)^A := pow_pos (by linarith [dyadicScale_pos r]) _
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  have hv (q : SourceRatioFiber s R seed K Z ξ r) :
      (ratioFirstSource s R seed K Z ξ hK r q).value W (fun _ => logAnnulus) =
        coordinateBlock s R seed W K Z ξ q.val := rfl
  simpa only [ratioFirstPhase,hv,mul_comm] using hh

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_block_joint_expression
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_joint_contraction
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_physical_mass_first_sector_expression
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_left_common_window
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_right_common_window
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_left_allocation_mellin
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_right_allocation_mellin
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_joint_energy_common_windows
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_physical_mass_joint_contraction
