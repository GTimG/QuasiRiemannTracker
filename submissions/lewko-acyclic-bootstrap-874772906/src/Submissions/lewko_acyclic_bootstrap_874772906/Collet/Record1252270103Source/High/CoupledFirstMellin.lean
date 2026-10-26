/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal coupled first joint columns and allocation Mellin formulas.
Adapted from pinned OpenAI/Hailey Collet Cycle61 InitialMass JointBlock. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstLabels
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstWindowColumns
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstFixed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
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
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow FourierBridge Cycle61Moment RayFourExpansion CenteredMomentPrimitive CenteredMomentScale
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance coupledFirstMellinDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _
open Cycle61InitialMass

def originalFirstPair (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s modifier R seed K Z ξ hK)) :=
  let B := originalFirstBlock s modifier R seed K Z ξ hK q.1
  fixedPair s.η B.C B.D B.hC B.inactive q.2.2.1 q.2.2.2.1⁻¹

omit [DecidableEq ι] in
theorem actual_first_left_common_window (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : SourceCoordinate s modifier R seed K Z ξ → ℂ)
    (q : FirstSector (originalFirstBlock s modifier R seed K Z ξ hK)) (V : ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    let B := source q.1
    CenteredMomentCauchy.leftColumn Finset.univ (firstJointLeft source weight q)
      V (firstLeftLog B) t =
      weight q.1*B.outside*commonWindow (CenteredMomentAmplificationChildInput.original s R seed) modifier
        B.C B.hC (originalFirstPair s modifier R seed K Z ξ hK q).left s.t t B.A0 V q.2.1.val q.2.2.2.2.val := by
  dsimp only
  let B := originalFirstBlock s modifier R seed K Z ξ hK q.1
  let F := originalFirstPair s modifier R seed K Z ξ hK q
  have hc := column_window_common (CenteredMomentAmplificationChildInput.original s R seed) modifier
    B.C B.C B.hC.1 B.hC rfl F.left s.t t B.A0 V q.2.1.val _
    (fixed_left_column F _ modifier s.t q.2.1.val) q.2.2.2.2.val
  rw [←hc]
  simp only [CenteredMomentCauchy.leftColumn, firstJointLeft, firstLeftLog, gaussPolynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let c := divisorCoefficient q.2.1.val (element B.C B.C B.hC.1 B.pool)
    (fun j => CenteredMomentFirstPhysicalSource.coefficient B.character B.mask 1 B.height B.beta B.C j*
      leftCoefficient B.e B.r B.sextic (element B.C B.C B.hC.1 B.pool j)) q.2.2.1 i
  let g := gaussRow (element B.C B.C B.hC.1 B.pool i) (element_supported _ _ _ _ i) q.2.2.2.2.val
  let f := columnPhase V (firstLeftLog B i) t
  change weight q.1*B.outside*c*g*f = weight q.1*B.outside*(c*f*g)
  ring

omit [DecidableEq ι] in
theorem actual_first_right_common_window (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s modifier R seed K Z ξ hK)) (V : ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    let B := source q.1
    CenteredMomentCauchy.rightColumn Finset.univ (firstJointRight source q)
      V (firstRightLog B) t =
      star (commonWindow (CenteredMomentAmplificationChildInput.original s R seed) modifier
        B.D B.hD (originalFirstPair s modifier R seed K Z ξ hK q).right s.t (-t) B.B0
        (fun x => star (V x)) q.2.1.val (-q.2.2.2.2.val)) := by
  dsimp only
  let B := originalFirstBlock s modifier R seed K Z ξ hK q.1
  let F := originalFirstPair s modifier R seed K Z ξ hK q
  have hc := column_window_common (CenteredMomentAmplificationChildInput.original s R seed) modifier
    B.C B.D B.hC.1 B.hD B.sameSupport F.right s.t (-t) B.B0
    (fun x => star (V x)) q.2.1.val _ (fixed_right_column F B.hD _ modifier s.t q.2.1.val)
    (-q.2.2.2.2.val)
  rw [←hc]
  simp only [CenteredMomentCauchy.rightColumn, firstJointRight, firstRightLog, gaussPolynomial,
    star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [←CenteredMomentConjugateWindow.star_columnPhase, star_star]
  let c := divisorCoefficient q.2.1.val (element B.C B.D B.hD.1 B.pool)
    (fun j => CenteredMomentFirstPhysicalSource.coefficient B.character B.mask 1 B.height B.beta B.D j*
      rightCoefficient B.e B.r B.sextic (element B.C B.D B.hD.1 B.pool j)) q.2.2.2.1⁻¹ i
  let g := gaussRow (element B.C B.D B.hD.1 B.pool i) (element_supported _ _ _ _ i) (-q.2.2.2.2.val)
  let f := columnPhase V (firstRightLog B i) t
  change star g*star c*f = star g*(f*star c)
  ring

omit [DecidableEq ι] in
/-- The joint left column is the literal Mellin integral of the allocation
polynomials, including their frozen coefficients. -/
theorem actual_first_left_allocation_mellin (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : SourceCoordinate s modifier R seed K Z ξ → ℂ)
    (q : FirstSector (originalFirstBlock s modifier R seed K Z ξ hK))
    (hseed : seed ∣ (originalFirstBlock s modifier R seed K Z ξ hK q.1).C)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (T t : ℝ) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    let B := source q.1
    (Real.sqrt T:ℂ)⁻¹*CenteredMomentCauchy.leftColumn Finset.univ
      (firstJointLeft source weight q) V (firstLeftLog B) t =
      weight q.1*B.outside*∫ u : ℝ,
        columnDensity V hc hs u*logPhase (t-u) (Real.log B.A0)*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) modifier
            B.C q.2.1.val (originalFirstPair s modifier R seed K Z ξ hK q).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val := by
  dsimp only
  rw [actual_first_left_common_window]
  let B := originalFirstBlock s modifier R seed K Z ξ hK q.1
  have h := common_window_original_integral (CenteredMomentAmplificationChildInput.original s R seed) modifier
    s.pools_ne s.prime B.C B.hC hseed (originalFirstPair s modifier R seed K Z ξ hK q).left
    s.t T t B.A0 B.A0_pos V hc hs q.2.1.val q.2.2.2.2.val
  change _ = _*∫u : ℝ, columnDensity V hc hs u*logPhase (t-u) (Real.log B.A0)*
    allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) modifier B.C q.2.1.val
      (originalFirstPair s modifier R seed K Z ξ hK q).left (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val
  simp only [allocatedPolynomial]
  rw [←h]
  ring

omit [DecidableEq ι] in
/-- The right column keeps its actual reflected row and conjugate window. -/
theorem actual_first_right_allocation_mellin (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (q : FirstSector (originalFirstBlock s modifier R seed K Z ξ hK))
    (hseed : seed ∣ (originalFirstBlock s modifier R seed K Z ξ hK q.1).D)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (T t : ℝ) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    let B := source q.1
    (Real.sqrt T:ℂ)⁻¹*CenteredMomentCauchy.rightColumn Finset.univ
      (firstJointRight source q) V (firstRightLog B) t =
      star (∫ u : ℝ,
        columnDensity (fun x => star (V x)) (CenteredMomentConjugateWindow.conjugate_compact V hc)
          (CenteredMomentConjugateWindow.conjugate_smooth V hs) u*
        logPhase (-t-u) (Real.log B.B0)*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) modifier
            B.D q.2.1.val (originalFirstPair s modifier R seed K Z ξ hK q).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)) := by
  dsimp only
  rw [actual_first_right_common_window]
  let B := originalFirstBlock s modifier R seed K Z ξ hK q.1
  have h := common_window_original_integral (CenteredMomentAmplificationChildInput.original s R seed) modifier
    s.pools_ne s.prime B.D B.hD hseed (originalFirstPair s modifier R seed K Z ξ hK q).right
    s.t T (-t) B.B0 B.B0_pos (fun x => star (V x))
    (CenteredMomentConjugateWindow.conjugate_compact V hc)
    (CenteredMomentConjugateWindow.conjugate_smooth V hs) q.2.1.val (-q.2.2.2.2.val)
  simp only [allocatedPolynomial]
  rw [←h]
  let c := commonWindow (CenteredMomentAmplificationChildInput.original s R seed) modifier B.D B.hD
    (originalFirstPair s modifier R seed K Z ξ hK q).right s.t (-t) B.B0
    (fun x => star (V x)) q.2.1.val (-q.2.2.2.2.val)
  change (Real.sqrt T:ℂ)⁻¹*star c = star ((Real.sqrt T:ℂ)⁻¹*c)
  simp


omit [DecidableEq ι] in
/-- The outside scalar remains squared inside the joint left energy. -/
theorem actual_first_joint_energy_common_windows (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K)
    (weight : SourceCoordinate s modifier R seed K Z ξ → ℂ)
    (V : Fin 4 → ℝ → ℂ) (t : ℝ) :
    let source := originalFirstBlock s modifier R seed K Z ξ hK
    firstJointEnergyPair source weight V t =
      Real.sqrt (∑ q : FirstSector source,
        ‖weight q.1‖^2*‖(source q.1).outside‖^2*
          ‖commonWindow (CenteredMomentAmplificationChildInput.original s R seed) modifier
            (source q.1).C (source q.1).hC
            (originalFirstPair s modifier R seed K Z ξ hK q).left s.t t
            (source q.1).A0 (V 2) q.2.1.val q.2.2.2.2.val‖^2)*
      Real.sqrt (∑ q : FirstSector source,
        ‖commonWindow (CenteredMomentAmplificationChildInput.original s R seed) modifier
          (source q.1).D (source q.1).hD
          (originalFirstPair s modifier R seed K Z ξ hK q).right s.t (-t)
          (source q.1).B0 (fun x => star (V 3 x)) q.2.1.val (-q.2.2.2.2.val)‖^2) := by
  dsimp only
  unfold firstJointEnergyPair
  simp_rw [actual_first_left_common_window, actual_first_right_common_window,
    norm_mul, norm_star, mul_pow]


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_left_common_window
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_right_common_window
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_left_allocation_mellin
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_right_allocation_mellin
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_first_joint_energy_common_windows
