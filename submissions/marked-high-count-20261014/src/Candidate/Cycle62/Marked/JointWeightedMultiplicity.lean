import Candidate.Cycle62.Moment.JointHighDensity
import Candidate.Cycle62.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle62Moment
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
      (∀l∈labels,0≤cost l)→
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
  obtain ⟨C,hC,hcount⟩:=actual_joint_source_row_count B loss hB hloss
  refine ⟨C,hC,?_⟩
  intro left u₀ unit Z hZ m E labels cost hcost hnormRow hnonzero heq hsupportnorm hnorm hmissing hselected
  let row : NonzeroJointSourceLabel left u₀ unit→NonzeroFrequency:=nonzeroJointSourceRow
  have hZ0 : 0<Z:=by linarith
  have hfiber (w : NonzeroFrequency) (hw : w ∈ labels.image row) :
      ((labels.filter (fun label => row label = w)).card:ℝ) ≤ C*Z^(m+loss) := by
    let fibre := labels.filter (fun label => row label = w)
    have mem_fibre (v : NonzeroJointSourceLabel left u₀ unit) (hv : v ∈ fibre) :
        v ∈ labels ∧ row v = w := by
      simpa only [fibre, Finset.mem_filter] using hv
    have hc := hcount left u₀ unit Z hZ w.val w.property
      (by
        obtain ⟨label,hl,hrow⟩ := Finset.mem_image.mp hw
        have hn := hnormRow label hl
        change ((Ideal.span {jointSourceRow left u₀ unit label.val}).absNorm:ℝ) ≤ Z^B at hn
        have he : jointSourceRow left u₀ unit label.val = w.val := congrArg Subtype.val hrow
        rw [he] at hn
        exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) le_rfl))
      m (fibre.image Subtype.val)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        exact congrArg Subtype.val (mem_fibre v hv).2)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnonzero v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact heq v (mem_fibre v hv).1)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        have he : jointSourceRow left u₀ unit v.val = w.val :=
          congrArg Subtype.val (mem_fibre v hv).2
        simpa only [he] using hsupportnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hmissing v (mem_fibre v hv).1)
    have hinj : Set.InjOn (fun v : NonzeroJointSourceLabel left u₀ unit => v.val)
        (↑fibre : Set (NonzeroJointSourceLabel left u₀ unit)) :=
      fun v _ r _ h => Subtype.ext h
    have hcard : fibre.card ≤ (fibre.image Subtype.val).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv
        exact Finset.mem_image_of_mem _ hv
      · exact hinj
    change (fibre.card:ℝ) ≤ C*Z^(m+loss)
    exact (show (fibre.card:ℝ) ≤ ((fibre.image Subtype.val).card:ℝ) by exact_mod_cast hcard).trans hc
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
      apply Finset.sum_le_sum
      intro k hk
      calc
        _≤∑_l∈fiber k.val,cost (pick k):=Finset.sum_le_sum (fun l hl=>hmax k l hl)
        _=(fiber k.val).card*cost (pick k):=by simp
        _≤_:=mul_le_mul_of_nonneg_right (hfiber k.val k.property) (hcost _ (hpickmem k))
    _=(C*Z^(m+loss))*(∑k : keys,cost (pick k)):=(Finset.mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left hsum (by positivity)

end
end OAI.SevenEighths.Cycle62Moment
#print axioms OAI.SevenEighths.Cycle62Moment.actual_joint_weighted_row_bound
