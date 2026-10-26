/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal first frozen coefficient and child volume are paid together, then
the declared Fourier scale and prime-average prefactor give the counted cost. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalMainPrefactor
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstSum
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalAllocationCost

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst
open Record1252270103Second
open CenteredMomentSectorLocalization Cycle61Moment Cycle61InitialMass
local notation "O"=>HeckeFamily.O

theorem frozen_first_payment {ι : Type}[Fintype ι](s : Input ι)
    (reflected : Bool)(l : FirstSourceLabel)(hC : Supported l.1.1)(hD : Supported l.1.2)
    (R : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ : Character)(t : ℝ)(scalar : ℂ)(N : ℕ)(Z r amp ξ reserve extra lower A loss : ℝ)
    (hZ : 0<Z)(he : 0≤extra)(hlower : 0<lower)(hA : 0≤A)
    (hextra : extra/lower≤A*Z^(-amp+loss)) :
    let C : Ideal O:=if reflected then l.1.2 else l.1.1
    let H:=firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve l
    let radial:=frequencyRadius
      (firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N l) Z ξ
    (‖scalar‖^2*extra*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/volume s)*
      (H/lower)*(max 1 (Z^r/(C.absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
      volume (child s C R B τ t)*(4*radial)^(1/6:ℝ)≤
      (forcedProfileCost s*A*((4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ)))*
        (‖scalar‖^2/(C.absNorm:ℝ))*
        firstRadialFactor reflected l Z (volume s) r amp ξ reserve (loss+ξ/12) := by
  intro C H radial
  have hc : C≠0 := by cases reflected <;> first | exact hC.1 | exact hD.1
  have hnc : (0:ℝ)<C.absNorm := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hc)
  have hV:=volume_pos s
  have hH : 0<H:=first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve hZ l
  have hr : 0≤radial := by dsimp only [radial,frequencyRadius,firstMainFourierScale];positivity
  have hp:=forcedProfileCost_nonneg s
  have hv:=frozen_child_volume_cost s C R hc B τ t
  let center:=(max 1 (Z^r/(C.absNorm:ℝ)))^(-(2*(499/1000:ℝ)))
  have hcenter : 0≤center:=by dsimp only [center];positivity
  have hh:=mul_le_mul_of_nonneg_left hv
    (show 0≤(‖scalar‖^2*extra/volume s)*(H/lower)*center*(4*radial)^(1/6:ℝ) by positivity)
  have hbase : (‖scalar‖^2*extra*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/volume s)*
      (H/lower)*center*volume (child s C R B τ t)*(4*radial)^(1/6:ℝ)≤
      forcedProfileCost s*(‖scalar‖^2/(C.absNorm:ℝ))*(extra/lower)*
        (H*(4*radial)^(1/6:ℝ))*center := by
    convert hh using 1
    · ring
    · field_simp [hV.ne']
      <;> ring
  have hfour:=actual_first_fourier_payment reflected l hC hD N Z (volume s) ξ amp reserve hZ hV
  change H*(4*radial)^(1/6:ℝ)=_ at hfour
  rw [hfour] at hbase
  have hbound:=mul_le_mul_of_nonneg_left hextra
    (show 0≤forcedProfileCost s*(‖scalar‖^2/(C.absNorm:ℝ))*
      (((4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ))*(volume s/(C.absNorm:ℝ))^(1/3:ℝ)*
        H^(5/6:ℝ)*Z^(ξ/12))*center by positivity)
  apply hbase.trans
  unfold firstRadialFactor
  change _≤(forcedProfileCost s*A*((4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ)))*
    (‖scalar‖^2/(C.absNorm:ℝ))*((volume s/(C.absNorm:ℝ))^(1/3:ℝ)*H^(5/6:ℝ)*center*
      Z^(-amp+(loss+ξ/12)))
  rw [show -amp+(loss+ξ/12)=(-amp+loss)+ξ/12 by ring,Real.rpow_add hZ]
  convert hbound using 1 <;> ring

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.frozen_first_payment
