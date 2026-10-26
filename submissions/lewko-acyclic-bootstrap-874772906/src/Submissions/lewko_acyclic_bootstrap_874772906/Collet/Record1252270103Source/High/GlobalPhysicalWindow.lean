/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modified full-label allocation energy passes through one common Mellin window.
Adapted from pinned Cycle61 JointWindowEnergy; full Hilbert indices retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstMellin
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.JointWindowEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy FourierBridge Cycle61InitialMass
local notation "O" => HeckeFamily.O
/-- The full first-column Hilbert index is retained through Mellin
integration. The source estimate is joint before integration; no individual
label energy envelope or label-count factor is introduced. -/
theorem actual_modified_joint_window_energy {Label ι : Type*} [Fintype Label] [Fintype ι]
    (labels : Finset Label) (s : Label→Input ι)
    (modifier : Label→CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed C L : Label→Ideal O) (hC : ∀l,Supported (C l))
    (hseed : ∀l,seed l∣C l) (τ : Label→Character) (t T θ X : Label→ℝ)
    (hX : ∀l,0<X l) (z : Label→O) (scalar : Label→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑l∈labels,‖scalar l*CoupledFirst.allocatedPolynomial
        (CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l)) (modifier l)
        (C l) (L l) (τ l) (t l+2*Real.pi*(u-θ l)) (T l) (z l)‖^2)≤
          E*(1+‖u‖)^(2*J)) :
    (∑l∈labels,‖scalar l*(Real.sqrt (T l):ℂ)⁻¹*CoupledFirst.commonWindow
      (CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l)) (modifier l)
      (C l) (hC l) (τ l) (t l) (θ l) (X l) V (L l) (z l)‖^2)≤
        E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  let src (l : Label) := CenteredMomentAmplificationChildInput.original (s l) (R l) (seed l)
  let φ (l : Label) (u : ℝ) := logPhase (θ l-u) (Real.log (X l))*
    (scalar l*CoupledFirst.allocatedPolynomial (src l) (modifier l) (C l) (L l) (τ l)
      (t l+2*Real.pi*(u-θ l)) (T l) (z l))
  have hi (l : Label) : Integrable (fun u=>columnDensity V hc hs u*φ l u) := by
    have hh := (CoupledFirst.common_window_original_integrable (src l) (modifier l) (s l).pools_ne (s l).prime
      (C l) (hC l) (hseed l) (τ l) (t l) (T l) (θ l) (X l) (hX l)
      V hc hs (L l) (z l)).const_mul (scalar l)
    convert hh using 1
    funext u
    dsimp [φ,CoupledFirst.allocatedPolynomial]
    ring
  have hb (u : ℝ) : (∑l∈labels,‖φ l u‖^2)≤E*((1+‖u‖)^J)^2 := by
    simpa only [φ,norm_mul,logPhase_norm,one_mul,src,←pow_mul,Nat.mul_comm] using henergy u
  have hbound := finite_set_weighted_integral_energy labels (columnDensity V hc hs) φ
    (fun u=>(1+‖u‖)^J) (fun _=>by positivity) E hE
    (columnDensity_moments V hc hs J) hi hb
  have he (l : Label) : (∫u : ℝ,columnDensity V hc hs u*φ l u)=
      scalar l*(Real.sqrt (T l):ℂ)⁻¹*
        CoupledFirst.commonWindow (src l) (modifier l) (C l) (hC l) (τ l) (t l) (θ l) (X l) V (L l) (z l) := by
    have hh := CoupledFirst.common_window_original_integral (src l) (modifier l) (s l).pools_ne (s l).prime
      (C l) (hC l) (hseed l) (τ l) (t l) (T l) (θ l) (X l) (hX l)
      V hc hs (L l) (z l)
    rw [mul_assoc,hh,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [φ,CoupledFirst.allocatedPolynomial]
    ring
  simpa only [he,src] using hbound

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_joint_window_energy
