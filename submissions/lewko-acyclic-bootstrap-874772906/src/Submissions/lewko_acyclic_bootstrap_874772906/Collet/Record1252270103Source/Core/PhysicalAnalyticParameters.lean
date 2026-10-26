/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Analytic losses chosen in the order used by the actual cofactor suppliers:
source loss, parent mesh, original cardinality, density degree, then height. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighParameters
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalAnalytic
noncomputable section
open OAI.SevenEighths.Cycle61Moment

structure FixedBudget (reserve dmax d Smax θ : ℝ) : Prop where
  positive : 0<θ
  small : θ≤1/100000
  tiny : 16*θ<reserve/16
  bin : θ≤1/4
  root : ∀mesh : ℝ,0≤mesh→mesh≤θ→
    dmax*(155*θ+mesh+θ+(3/4)*θ+θ)+θ+2*θ*Smax<reserve/16
  plain : 2*(θ/16)*d+θ/8<reserve/16

theorem fixed_loss_exists (reserve dmax d Smax : ℝ)
    (hr : 0<reserve) (hdmax : 0≤dmax) (hd : 0≤d) (hS : 0≤Smax) :
    ∃θ : ℝ,FixedBudget reserve dmax d Smax θ := by
  let A:=dmax+d+Smax+1
  have hA : 0<A := by dsimp [A];linarith
  let θ:=min (1/100000) (reserve/(100000*A))
  have hθ : 0<θ:=lt_min (by norm_num) (div_pos hr (by positivity))
  have hθsmall : θ≤1/100000:=min_le_left _ _
  have hpaid : θ*(100000*A)≤reserve:=
    (le_div_iff₀ (by positivity : 0<100000*A)).mp (min_le_right _ _)
  have hθd:=mul_nonneg hθ.le hd
  have hθmax:=mul_nonneg hθ.le hdmax
  have hθS:=mul_nonneg hθ.le hS
  dsimp only [A] at hpaid
  refine ⟨θ,hθ,hθsmall,?_,by linarith,?_,?_⟩
  · nlinarith only [hpaid,hθd,hθmax,hθS,hr]
  · intro mesh hm hm'
    have hmesh:=mul_le_mul_of_nonneg_left hm' hdmax
    nlinarith only [hpaid,hmesh,hθd,hθmax,hθS,hθ,hr]
  · nlinarith only [hpaid,hθd,hθmax,hθS,hr]

structure CardinalityBudget (θ dmax d Rwidth Rplain : ℝ) (N : ℕ)
    (wmin rmin εslot : ℝ) : Prop where
  wmin_pos : 0<wmin
  rmin_pos : 0<rmin
  slot_pos : 0<εslot
  live_lower : rmin≤wmin/dmax
  tiny_width : (N:ℝ)*wmin≤θ
  slot_gap : εslot<rmin*θ
  slot_cost : 2*εslot*d*(N:ℝ)≤θ/8
  buffer_pos : 0<highBuffer Rwidth Rplain εslot (θ/16)
  buffer_small : highBuffer Rwidth Rplain εslot (θ/16)<1/1000
  kappa_pos : 0<highKappa εslot (θ/16)
  kappa_le_one : highKappa εslot (θ/16)≤1
  density_budget : 288*highBuffer Rwidth Rplain εslot (θ/16)+
    8*highKappa εslot (θ/16)+2*(θ/16)≤θ/2
  slot_budget : 8*highBuffer Rwidth Rplain εslot (θ/16)*Rwidth+
    highKappa εslot (θ/16)≤εslot

theorem cardinality_loss_exists (θ dmax d Rwidth Rplain : ℝ)
    (hθ : 0<θ) (hdmax : 0<dmax) (hd : 0<d)
    (hRw : 0≤Rwidth) (hRp : 0≤Rplain) (N : ℕ) :
    ∃wmin rmin εslot : ℝ,CardinalityBudget θ dmax d Rwidth Rplain N wmin rmin εslot := by
  let wmin:=θ/((N:ℝ)+1)
  let rmin:=wmin/(2*dmax)
  let εslot:=min (θ/(16*d*((N:ℝ)+1))) (rmin*θ/2)
  have hw : 0<wmin:=div_pos hθ (by positivity)
  have hr : 0<rmin:=div_pos hw (by positivity)
  have hes : 0<εslot:=lt_min (div_pos hθ (by positivity)) (by positivity)
  have hep : 0<θ/16:=by positivity
  have he:=high_buffer_pos hRw hRp hes hep
  have hk:=high_kappa_pos hes hep
  have hrw : rmin≤wmin/dmax:=div_le_div_of_nonneg_left hw.le hdmax (by linarith)
  have hww : wmin*((N:ℝ)+1)=θ:=div_mul_cancel₀ _ (by positivity)
  have hesgap : εslot≤rmin*θ/2:=min_le_right _ _
  have hescost : εslot*(16*d*((N:ℝ)+1))≤θ:=
    (le_div_iff₀ (by positivity : 0<16*d*((N:ℝ)+1))).mp (min_le_left _ _)
  have hbuf : highBuffer Rwidth Rplain εslot (θ/16)≤(θ/16)/(48*(Rplain+2)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbuf' : highBuffer Rwidth Rplain εslot (θ/16)*(48*(Rplain+2))≤θ/16:=
    (le_div_iff₀ (by positivity : 0<48*(Rplain+2))).mp hbuf
  have hκ : highKappa εslot (θ/16)≤(θ/16)/32:=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨wmin,rmin,εslot,hw,hr,hes,hrw,?_,?_,?_,he,?_,hk,min_le_left _ _,?_,
    (high_buffer_budgets hRw hRp hes hep).1⟩
  · nlinarith only [hww,hw]
  · nlinarith only [hesgap,mul_pos hr hθ]
  · nlinarith only [hescost,mul_pos hes hd]
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · nlinarith only [hbuf',hκ,mul_nonneg he.le hRp,hθ]

/-- The source loss is chosen before receiving the parent's source mesh.
The common root mesh is chosen before every possible slot cardinality. -/
theorem staged_physical_losses (reserve dmax d Rwidth Rplain Smax : ℝ)
    (hr : 0<reserve) (hdmax : 0<dmax) (hd : 0<d)
    (hRw : 0<Rwidth) (hRp : 0≤Rplain) (hS : 0≤Smax) :
    ∃θ : ℝ,FixedBudget reserve dmax d Smax θ ∧
      ∀sourceMesh : ℝ,0<sourceMesh→∃meshMax : ℝ,0<meshMax ∧
        meshMax≤sourceMesh ∧ meshMax≤Rwidth ∧ meshMax≤θ ∧
        ∀N : ℕ,∃wmin rmin εslot : ℝ,
          CardinalityBudget θ dmax d Rwidth Rplain N wmin rmin εslot := by
  obtain ⟨θ,hθ⟩:=fixed_loss_exists reserve dmax d Smax hr hdmax.le hd.le hS
  refine ⟨θ,hθ,?_⟩
  intro sourceMesh hmesh
  refine ⟨min sourceMesh (min Rwidth θ),lt_min hmesh (lt_min hRw hθ.positive),
    min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  exact cardinality_loss_exists θ dmax d Rwidth Rplain hθ.positive hdmax hd hRw.le hRp

end
end QRH.Record1252270103Source.PhysicalAnalytic
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.fixed_loss_exists
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.cardinality_loss_exists
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.staged_physical_losses
