import Candidate.Cycle63.Moment.JointHighDensity
import Candidate.Cycle63.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

/-- Actual two-stage source multiplicity lifts an arbitrary nonnegative
weighted bound on distinct encoded frequencies. The chosen representative
may retain every row-dependent height and allocation parameter. -/
theorem actual_joint_weighted_row_bound (B loss : ℝ) (hB : 0≤B) (hloss : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→O,
      ∀Z : ℝ,2≤Z→∀m E : ℝ,
      ∀labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀cost : NonzeroJointSourceLabel left u₀ unit→ℝ,
      (∀l∈labels,0≤ cost l)→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow l)≤Z^B)→
      (∀l∈labels,Supported l.val.1.1.1 ∧ l.val.1.1.2≠0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2≠0)→
      (∀l∈labels,primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1=primeSupport l.val.2.1.2)→
      (∀l∈labels,((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^B)→
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧
        (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.2.absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^m)→
      (∀selected : Finset (NonzeroJointSourceLabel left u₀ unit),selected⊆labels→
        Set.InjOn (fun l : NonzeroJointSourceLabel left u₀ unit=>nonzeroJointSourceRow l)
          (↑selected:Set (NonzeroJointSourceLabel left u₀ unit))→(∑l∈selected,cost l)≤E)→
      (∑l∈labels,cost l)≤C*Z^(m+loss)*E := by
  obtain ⟨C,hC,hcount⟩:=nonzero_joint_source_fiber_count B loss hB hloss
  refine ⟨C,hC,?_⟩
  intro left u₀ unit Z hZ m E labels cost hcost hnormRow hnonzero heq hsupportnorm hnorm hmissing hselected
  let row : NonzeroJointSourceLabel left u₀ unit→NonzeroFrequency:=nonzeroJointSourceRow
  have hZ0 : 0<Z:=by linarith
  have hfiber (w : NonzeroFrequency) (_ : w ∈ labels.image row) :
      ((labels.filter (fun label => row label = w)).card:ℝ) ≤ C*Z^(m+loss) :=
    hcount left u₀ unit Z hZ m labels hnormRow hnonzero heq hsupportnorm hnorm hmissing w
  let keys:=labels.image row
  let fiber (k : NonzeroFrequency):=labels.filter (fun l=>row l=k)
  have hnonempty (k : keys):(fiber k.val).Nonempty:=by
    obtain ⟨l,hl,he⟩:=Finset.mem_image.mp k.property
    exact ⟨l,Finset.mem_filter.mpr ⟨hl,he⟩⟩
  choose pick hpick hmax using (fun k : keys=>
    Finset.exists_max_image (fiber k.val) cost (hnonempty k))
  have hpickmem (k : keys):pick k∈labels:=(Finset.mem_filter.mp (hpick k)).1
  have hpickrow (k : keys):row (pick k)=k.val:=(Finset.mem_filter.mp (hpick k)).2
  have hpinj : Function.Injective pick:=by
    intro k l h
    apply Subtype.ext
    rw [←hpickrow k,←hpickrow l,h]
  let selected:=(Finset.univ : Finset keys).image pick
  have hsubset : selected⊆labels:=by
    intro l hl
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hl
    exact hpickmem k
  have hselinj : Set.InjOn (fun l : NonzeroJointSourceLabel left u₀ unit=>nonzeroJointSourceRow l)
          (↑selected:Set (NonzeroJointSourceLabel left u₀ unit)):=by
    intro a ha b hb he
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hb
    have h : k=l:=Subtype.ext (by change row (pick k)=row (pick l) at he; simpa [hpickrow] using he)
    rw [h]
  have hsum : (∑k : keys,cost (pick k))≤E:=by
    have hs:=hselected selected hsubset hselinj
    simpa [selected,Finset.sum_image,Function.Injective.injOn hpinj] using hs
  have hsplit : (∑k : keys,∑l∈fiber k.val,cost l)=∑l∈labels,cost l:=by
    rw [Finset.sum_coe_sort keys (fun k=>∑l∈fiber k,cost l)]
    exact Finset.sum_fiberwise_of_maps_to (fun l hl=>Finset.mem_image_of_mem row hl) cost
  rw [←hsplit]
  calc
    _≤∑k : keys,(C*Z^(m+loss))*cost (pick k):=by
      refine Finset.sum_le_sum fun k hk => ?_
      calc
        _≤∑_l∈fiber k.val,cost (pick k):=Finset.sum_le_sum (fun l hl=>hmax k l hl)
        _=(fiber k.val).card*cost (pick k):=by simp
        _≤_:=mul_le_mul_of_nonneg_right (hfiber k.val k.property) (hcost _ (hpickmem k))
    _=(C*Z^(m+loss))*(∑k : keys,cost (pick k)):=(Finset.mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left hsum (by positivity)

end
end OAI.SevenEighths.Cycle63Moment
