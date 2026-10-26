import Candidate.Cycle63.Physical.InitialMass.GeometryAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryMainRadius
import Candidate.Cycle63.Physical.InitialMass.SecondSourceBudget

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSecondLocalization
open CenteredMomentCommonProfile CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic CenteredMomentSupportedTailAggregate

/-- The amplified main branch of the actual first geometry budget splits
into zero/tail costs and one retained sum across all original columns and
supported common allocations. Its main scale is tied to the arithmetic label. -/
theorem actual_geometry_main_second_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A sigma reserve b t : ℝ) (N : ℕ) (hK : 0<K) (hZ : 0<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) :
    let Live := ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus))
    let C := fun j : Live=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
    let χ := fun j : Live=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
    let g := fun j : Live=>geometryBranch reflected s R seed K Z ξ hK key j.val
    let w := fun j : Live=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
    let Label := (j : Live) × actualAllocations s.pools (C j)
    let source := fun q : Label=>child s (C q.1) R q.2 (χ q.1) t
    let radius := fun q : Label=>firstMainRadius reflected K (volume s) Z ξ sigma reserve
      (geometryFirstLabel s R seed K Z ξ hK key q.1.val)
    let c := fun q : Label=>w q.1 q.2/volume (source q)
    ∀Tsec : Label→ℝ,
    (∑j : Live,∑B : actualAllocations s.pools (C j),
      w j B*actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)≤
      (∑q : Label,c q*(‖originalSecondZero (source q) (R*C q.1) q.1.val.2.1.val ballProfile (radius q)‖+
        ‖secondDiscardedEnergy (source q).η (source q).t
          (original (source q) (R*C q.1) q.1.val.2.1.val).columns
          (original (source q) (R*C q.1) q.1.val.2.1.val).beta
          ballProfile (radius q) (Tsec q) Z ξ‖))+
      ‖∑q : Label,(c q:ℂ)*secondRetainedEnergy (source q).η (source q).t
        (original (source q) (R*C q.1) q.1.val.2.1.val).columns
        (original (source q) (R*C q.1) q.1.val.2.1.val).beta
        ballProfile (radius q) (Tsec q) Z ξ‖ := by
  intro Live C χ g w Label source radius c Tsec
  have hh := actual_joint_normalized_source_budget (α:=ι) (Label:=Label)
    (fun q=>liveIndices q.2.val) source (fun q=>R*C q.1) (fun q=>q.1.val.2.1.val)
    ballProfile radius Tsec Z ξ
    (fun q=>first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hZ _)
    (fun q=>w q.1 q.2)
    (fun q=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b q.1.val q.2)
  apply le_trans (le_of_eq ?_) hh
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun B hB => ?_
  rw [actual_geometry_main_source_radius]

end
end OAI.SevenEighths.Cycle63InitialMass
