/- Adapted from Zhongpai Gao, gao-balanced-marked-20261017, Apache-2.0;
upstream math snapshot 9c0e14f985041e397f71c574028193ee595a0f98.
Underlying Cycle61: Hailey Collet; original analytic interfaces: OpenAI, Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedColumns

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

open Cycle61InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic


variable {ι : Type*} [Fintype ι]
/-- The literal left child budget supplies the source premise of the
Mellin-window theorem, with original source volume as normalization. -/
theorem actual_balanced_left_budget_window (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, balancedLiveBudget false s modifier R seed K Z ξ M A hK key weight
      (s.t+2*Real.pi*(u-t))≤E*(1+‖u‖)^(2*J)) :
    balancedLeftEnergy s modifier R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        logAnnulus hc hsm u‖)^2 := by
  apply actual_balanced_left_window_energy s modifier R seed K Z ξ M A hK hZ key weight
    (fun q=>(actual_geometry_seed s modifier R seed K Z ξ hK key hs hz₁ hz₂ q).1)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_balanced_source_budget false s modifier R seed K Z ξ M A hK key weight
    (s.t+2*Real.pi*(u-t))
  simp only [balancedColumnScalar,
    Bool.false_eq_true,ite_false] at hh
  exact le_trans hh (hbudget u)

/-- The reflected right budget passes through its independent Mellin
height, retaining the conjugate window from the actual first transform. -/
theorem actual_balanced_right_budget_window (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 0<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : SourceCoordinate s modifier R seed K Z ξ→ℂ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (hbudget : ∀u : ℝ, balancedLiveBudget true s modifier R seed K Z ξ M A hK key weight
      (s.t+2*Real.pi*(u-(-t)))≤E*(1+‖u‖)^(2*J)) :
    balancedRightEnergy s modifier R seed K Z ξ A hK key (fun _=>logAnnulus) t/volume s≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
        (fun x=>star (logAnnulus x))
        (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
        (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖)^2 := by
  apply actual_balanced_right_window_energy s modifier R seed K Z ξ A hK hZ key
    (fun q=>(actual_geometry_seed s modifier R seed K Z ξ hK key hs hz₁ hz₂ q).2)
    (fun _=>logAnnulus) hc hsm t (volume s) (volume_pos s) J E hE
  intro u
  have hh := actual_balanced_source_budget true s modifier R seed K Z ξ M A hK key weight
    (s.t+2*Real.pi*(u-(-t)))
  simp only [balancedColumnScalar,
    ite_true] at hh
  exact le_trans hh (hbudget u)

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_left_budget_window
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_right_budget_window
