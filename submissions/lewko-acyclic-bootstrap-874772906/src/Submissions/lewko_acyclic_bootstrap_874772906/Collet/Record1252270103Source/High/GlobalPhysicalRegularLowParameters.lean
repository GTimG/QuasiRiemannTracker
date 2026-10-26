/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The earlier global source fixes the LOW mesh before the original slot type.
The actual buffered supplier is then instantiated at the staged slot losses. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularLowSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularSetup
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open Cycle61Moment Record1252270103Finite Record1252270103StepScalar
open CenteredMomentNaturalFixedRaySource
open QRH.Record1252270103Low QRH.Record1252270103Graph PhysicalAnalytic
open Set Admission.SelectedRegularLowSource
local notation "O"=>HeckeFamily.O
variable (K:ℚ)(n low:Source)(b θ:ℝ)
variable (hg:RealGeometry K n low b)(hn:ParentGood n)(hlow:ParentGood low)
variable (ha:0<(n.allowance:ℝ))(hqhalf:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
variable (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hθ:0<θ)

def regularLowMesh:ℝ:=Classical.choose
  (global_selected_regular_low_buffered_positive_family K n low b θ hg hn hlow ha hqhalf hq1 hG hθ)

theorem regular_low_mesh_positive:0<regularLowMesh K n low b θ hg hn hlow ha hqhalf hq1 hG hθ:=
  (Classical.choose_spec
    (global_selected_regular_low_buffered_positive_family K n low b θ hg hn hlow ha hqhalf hq1 hG hθ)).1

variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (Mslot:α→ℝ)(hMslot:∀i,0≤Mslot i)
variable (mesh:ℝ)(hmesh:mesh≤regularLowMesh K n low b θ hg hn hlow ha hqhalf hq1 hG hθ)
variable (N:ℕ)(wmin rmin εslot τ:ℝ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hτ:0<τ)(hτheight:2*τ<100*(εslot/4))
variable (ηanchor η₀:Character)(Q:Ideal O)(hQM:Q≤M)
variable (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
local instance regularLowParametersQuotientFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Proof-valued specialization: its exact result still chooses Cslot before
the paid degree/control/constant and before every moving physical row. -/
def regular_low_slot_supply :=
  (Classical.choose_spec
    (global_selected_regular_low_buffered_positive_family K n low b θ hg hn hlow ha hqhalf hq1 hG hθ)).2
    mesh hmesh α M H hH Mslot hMslot 6 θ (θ/100) (by norm_num) hθ (by positivity)
    W hWs hW 1 100 τ εslot (highBuffer 1 1 εslot (θ/16)) (highKappa εslot (θ/16))
    (εslot/4) 2 40 20 1 100 (by norm_num) (by norm_num) hτ hc.slot_pos hc.buffer_pos hc.buffer_small
    hc.kappa_pos (div_nonneg hc.slot_pos.le (by norm_num)) hc.slot_budget (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl hτheight ηanchor η₀ Q hQM hQ hQt hQ72

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_low_mesh_positive
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_low_slot_supply
