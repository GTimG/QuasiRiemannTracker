/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Joint second Mellin energy for the literal modified finite columns.
Adapted from the pinned Cycle61 JointWindowFamily; every coefficient and
row scalar remains inside the same finite Hilbert sum. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondWindow
import Submissions.hailey_collet_1252270103.Cycle61.Moment.JointWindowFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentHeckeWindowEnergy
local notation "O"=>HeckeFamily.O

theorem actual_modified_second_joint_window_energy {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→Finset α) (s : (k : κ)→Input (slots k))
    (modifier : ∀k,Tuple (slots k)→ℂ)
    (C R seed L : κ→Ideal O) (hC : ∀k,Supported (C k)) (η : κ→Character)
    (t θ X : κ→ℝ) (hX : ∀k,0<X k) (z : κ→O) (scalar : κ→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑k∈rows,‖scalar k*modifiedPlainColumn (s k) (modifier k)
        (C k) (hC k) (R k) (seed k) (L k) (η k) (t k+2*Real.pi*(u-θ k)) (z k)‖^2)
        ≤E*(1+‖u‖)^(2*J)) :
    (∑k∈rows,‖scalar k*modifiedWindowColumn (s k) (modifier k)
      (C k) (hC k) (R k) (seed k) (L k) (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  let φ (k : κ) (u : ℝ):=logPhase (θ k-u) (Real.log (X k))*
    (scalar k*modifiedPlainColumn (s k) (modifier k) (C k) (hC k) (R k) (seed k)
      (L k) (η k) (t k+2*Real.pi*(u-θ k)) (z k))
  have hi (k : κ) : Integrable (fun u=>columnDensity V hc hs u*φ k u) := by
    have hh:=(modified_window_integrable (s k) (modifier k) (C k) (hC k) (R k)
      (seed k) (L k) (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k)).const_mul (scalar k)
    convert hh using 1
    funext u
    dsimp [φ]
    ring
  have hb (u : ℝ) : (∑k : rows,‖φ k.val u‖^2)≤E*((1+‖u‖)^J)^2 := by
    rw [Finset.sum_coe_sort rows (fun k=>‖φ k u‖^2)]
    simpa only [φ,norm_mul,logPhase_norm,one_mul,←pow_mul,Nat.mul_comm] using henergy u
  have hh:=finite_weighted_integral_energy (columnDensity V hc hs)
    (fun k : rows=>φ k.val) (fun u=>(1+‖u‖)^J) (fun _=>by positivity)
    E hE (columnDensity_moments V hc hs J) (fun k=>hi k.val) hb
  have he (k : κ) : (∫u : ℝ,columnDensity V hc hs u*φ k u)=
      scalar k*modifiedWindowColumn (s k) (modifier k) (C k) (hC k) (R k)
        (seed k) (L k) (η k) (t k) (θ k) (X k) V (z k) := by
    rw [modified_window_integral (s k) (modifier k) (C k) (hC k) (R k) (seed k)
      (L k) (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [φ]
    ring
  simp only [he] at hh
  rw [Finset.sum_coe_sort rows (fun k=>‖scalar k*modifiedWindowColumn (s k) (modifier k)
    (C k) (hC k) (R k) (seed k) (L k) (η k) (t k) (θ k) (X k) V (z k)‖^2)] at hh
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_second_joint_window_energy
