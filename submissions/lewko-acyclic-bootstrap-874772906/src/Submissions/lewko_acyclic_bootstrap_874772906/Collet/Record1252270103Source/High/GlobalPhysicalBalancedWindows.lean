/- Adapted from Zhongpai Gao, gao-balanced-marked-20261017, Apache-2.0;
upstream math snapshot 9c0e14f985041e397f71c574028193ee595a0f98.
Underlying Cycle61: Hailey Collet; original analytic interfaces: OpenAI, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalWindow

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy FourierBridge
local notation "O" => HeckeFamily.O

open Cycle61InitialMass QRH.Record12518109Assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def geometryOriginalSector (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s modifier R seed K Z ξ hK key)) :
    FirstSector (originalFirstBlock s modifier R seed K Z ξ hK) := ⟨q.1.val,q.2⟩

def balancedLeftScalar (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (q : FirstSector (geometryFirstSource s modifier R seed K Z ξ hK key)) : ℂ :=
  weight q.1.val*(geometryFirstSource s modifier R seed K Z ξ hK key q.1).outside/
    (Real.sqrt (Z^(2*outsideExponent M A (geometryExponents s modifier R seed K Z ξ q.1.val)+
      balancedLeft A (geometryExponents s modifier R seed K Z ξ q.1.val))):ℂ)

omit [DecidableEq ι] in
/-- Specialization to the actual normalized left Hilbert energy in one
geometry group. The original outside scalar, source volume and every
first-sector coordinate are preserved through the Mellin integral. -/
theorem actual_balanced_left_window_energy (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (hseed : ∀q : CommonGeometryFiber s modifier R seed K Z ξ key,
      seed∣(geometryFirstSource s modifier R seed K Z ξ hK key q).C)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 2)) (hs : ContDiff ℝ ∞ (V 2))
    (t T : ℝ) (hT : 0<T) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s modifier R seed K Z ξ hK key) V,
        ‖balancedLeftScalar s modifier R seed K Z ξ M A hK key weight q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) modifier
            (geometryFirstSource s modifier R seed K Z ξ hK key q.1).C q.2.1.val
            (originalFirstPair s modifier R seed K Z ξ hK
              (geometryOriginalSector s modifier R seed K Z ξ hK key q)).left
            (s.t+2*Real.pi*(u-t)) T q.2.2.2.2.val‖^2)≤E*(1+‖u‖)^(2*J)) :
    balancedLeftEnergy s modifier R seed K Z ξ M A hK key (fun q=>weight q.val) V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (V 2) hc hs u‖)^2 := by
  let src := geometryFirstSource s modifier R seed K Z ξ hK key
  let lift := geometryOriginalSector s modifier R seed K Z ξ hK key
  have hh := GlobalPhysical.actual_modified_joint_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=>s) (fun _=>modifier) (fun _=>R) (fun _=>seed)
    (fun q=>(src q.1).C) (fun q=>q.2.1.val) (fun q=>(src q.1).hC)
    (fun q=>hseed q.1)
    (fun q=>(originalFirstPair s modifier R seed K Z ξ hK (lift q)).left)
    (fun _=>s.t) (fun _=>T) (fun _=>t) (fun q=>(src q.1).A0)
    (fun q=>(src q.1).A0_pos) (fun q=>q.2.2.2.2.val)
    (fun q=>balancedLeftScalar s modifier R seed K Z ξ M A hK key weight q) (V 2) hc hs J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [balancedLeftEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_left_common_window s modifier R seed K Z ξ hK weight (lift q) (V 2) t
  change CenteredMomentCauchy.leftColumn Finset.univ
    (firstJointLeft src (fun q=>weight q.val) q) (V 2) (firstLeftLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [balancedLeftScalar]
  simp only [norm_mul,norm_div,norm_inv,mul_pow,div_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

def balancedRightScalar (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (q : FirstSector (geometryFirstSource s modifier R seed K Z ξ hK key)) : ℂ :=
  (Real.sqrt (Z^(balancedRight A (geometryExponents s modifier R seed K Z ξ q.1.val))):ℂ)⁻¹

omit [DecidableEq ι] in
/-- The matching right energy uses the reflected row and conjugate window;
its Mellin height is independent of the left one. -/
theorem actual_balanced_right_window_energy (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (hseed : ∀q : CommonGeometryFiber s modifier R seed K Z ξ key,
      seed∣(geometryFirstSource s modifier R seed K Z ξ hK key q).D)
    (V : Fin 4→ℝ→ℂ) (hc : HasCompactSupport (V 3)) (hs : ContDiff ℝ ∞ (V 3))
    (t T : ℝ) (hT : 0<T) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑q∈firstActiveSectors (geometryFirstSource s modifier R seed K Z ξ hK key) V,
        ‖balancedRightScalar s modifier R seed K Z ξ A hK key q*
          allocatedPolynomial (CenteredMomentAmplificationChildInput.original s R seed) modifier
            (geometryFirstSource s modifier R seed K Z ξ hK key q.1).D q.2.1.val
            (originalFirstPair s modifier R seed K Z ξ hK
              (geometryOriginalSector s modifier R seed K Z ξ hK key q)).right
            (s.t+2*Real.pi*(u-(-t))) T (-q.2.2.2.2.val)‖^2)≤E*(1+‖u‖)^(2*J)) :
    balancedRightEnergy s modifier R seed K Z ξ A hK key V t/T≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (V 3 x))
        (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
        (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) u‖)^2 := by
  let src := geometryFirstSource s modifier R seed K Z ξ hK key
  let lift := geometryOriginalSector s modifier R seed K Z ξ hK key
  have hh := GlobalPhysical.actual_modified_joint_window_energy (firstActiveSectors src V)
    (fun _ : FirstSector src=>s) (fun _=>modifier) (fun _=>R) (fun _=>seed)
    (fun q=>(src q.1).D) (fun q=>q.2.1.val) (fun q=>(src q.1).hD)
    (fun q=>hseed q.1)
    (fun q=>(originalFirstPair s modifier R seed K Z ξ hK (lift q)).right)
    (fun _=>s.t) (fun _=>T) (fun _=>-t) (fun q=>(src q.1).B0)
    (fun q=>(src q.1).B0_pos) (fun q=>-q.2.2.2.2.val)
    (fun q=>balancedRightScalar s modifier R seed K Z ξ A hK key q) (fun x=>star (V 3 x))
    (CenteredMomentConjugateWindow.conjugate_compact (V 3) hc)
    (CenteredMomentConjugateWindow.conjugate_smooth (V 3) hs) J E hE henergy
  apply le_trans (le_of_eq ?_) hh
  rw [balancedRightEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  have hcol := actual_first_right_common_window s modifier R seed K Z ξ hK (lift q) (V 3) t
  change CenteredMomentCauchy.rightColumn Finset.univ
    (firstJointRight src q) (V 3) (firstRightLog (src q.1)) t=_ at hcol
  rw [hcol]
  dsimp only [balancedRightScalar]
  simp only [norm_mul,norm_inv,norm_star,mul_pow,inv_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),Real.sq_sqrt hT.le]
  dsimp [src,lift,geometryOriginalSector,geometryFirstSource]
  ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_left_window_energy
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_right_window_energy
