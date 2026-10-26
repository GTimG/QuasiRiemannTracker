import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighAdmission
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointAllocationEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentCommonPairedSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope

/-- A finite family is reduced to one maximizing representative per joint
key. The complete cost is selected, so its physical scalar stays inside the
joint sum. This statement supplies no analytic bound on that sum. -/
theorem high_family_max_selection {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→Key)(cost : Row→ℝ)(W : ℝ)(hW : 0≤W)
    (hc : ∀r,0≤ cost r)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W) :
    ∃pick : (k : Finset.univ.image key)→Row,
      (∀k,key (pick k)=k.val) ∧ Function.Injective (fun k=>key (pick k)) ∧
      (∑r,cost r)≤W*(∑k : Finset.univ.image key,cost (pick k)) := by
  let keys:=Finset.univ.image key
  let fiber:=fun k : Key=>Finset.univ.filter (fun r=>key r=k)
  have hn (k : keys) : (fiber k.val).Nonempty := by
    obtain ⟨r,hr,he⟩:=Finset.mem_image.mp k.property
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩
  choose pick hp hm using (fun k : keys=>Finset.exists_max_image (fiber k.val) cost (hn k))
  have hk : ∀k,key (pick k)=k.val:=fun k=>(Finset.mem_filter.mp (hp k)).2
  refine ⟨pick,hk,?_,?_⟩
  · intro k l he
    apply Subtype.ext
    exact (hk k).symm.trans (he.trans (hk l))
  · apply joint_fiber_selection key cost W _ hW hc (fun k _=>hfiber k)
    intro other hother
    refine Finset.sum_le_sum fun k _ => ?_
    exact hm k (other k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hother k⟩)

/-- The physical second normalized column, with its source character and
reflection inherited from the literal retained row. -/
def highNormalizedRowCost {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) : ℝ :=
  let v:=d r.val.1
  let E:=if second then v.D else v.C
  let hE : Supported E:=by dsimp only [E]; split <;> first | exact v.hD | exact v.hC
  let ψ:=if second then r.val.2.2.1⁻¹ else r.val.2.1
  let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
  ∑L∈Ds,‖normalizedColumn (withHeight v.input (v.τ ψ) t) E hE v.R v.seed L z‖^2

lemma high_normalized_row_cost_nonneg {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) :
    0≤highNormalizedRowCost second d r t Ds := by
  dsimp only [highNormalizedRowCost]
  exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
