import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.JointWeightedMultiplicity
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.OriginalSlotPartition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource

/-- The actual joint multiplicity theorem retains the original row labels,
so every row-dependent height and geometric allocation survives selection. -/
theorem actual_joint_weighted_family_bound (B loss : ℝ) (hB : 0≤B) (hloss : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→O,
      ∀Z : ℝ,2≤Z→∀m E : ℝ,
      ∀{κ : Type}[Nonempty κ](key : κ→NonzeroJointSourceLabel left u₀ unit),
      Function.Injective key→∀labels : Finset κ,∀cost : κ→ℝ,
      (∀l∈labels,0≤ cost l)→
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^B)→
      (∀l∈labels,Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2≠0 ∧
        Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2≠0)→
      (∀l∈labels,primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 ∧
        primeSupport (key l).val.2.1.1=primeSupport (key l).val.2.1.2)→
      (∀l∈labels,((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.2.1.2.absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^m)→
      (∀selected : Finset κ,selected⊆labels→
        Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑selected:Set κ)→
        (∑l∈selected,cost l)≤E)→
      (∑l∈labels,cost l)≤C*Z^(m+loss)*E := by
  obtain ⟨C,hC,hbound⟩:=actual_joint_weighted_row_bound B loss hB hloss
  refine ⟨C,hC,?_⟩
  intro left u₀ unit Z hZ m E κ _ key hinj labels cost hcost hraw hsupp heq hsupport hnorm hmissing hselected
  let back:=Function.invFun key
  have hback (l : κ) : back (key l)=l:=Function.leftInverse_invFun hinj l
  have hkey (l : NonzeroJointSourceLabel left u₀ unit) (hl : l∈labels.image key) : key (back l)=l := by
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hl
    rw [hback]
  have hmem (l : NonzeroJointSourceLabel left u₀ unit) (hl : l∈labels.image key) : back l∈labels := by
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hl
    simpa only [hback] using hv
  have he:=hbound left u₀ unit Z hZ m E (labels.image key) (fun l=>cost (back l))
    (fun l hl=>hcost _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using hraw _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using hsupp _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using heq _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using hsupport _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using hnorm _ (hmem l hl))
    (fun l hl=>by simpa only [hkey l hl] using hmissing _ (hmem l hl)) ?_
  · simpa only [Finset.sum_image hinj.injOn,hback] using he
  · intro selected hs hrawinj
    have hb : Set.InjOn back (↑selected:Set (NonzeroJointSourceLabel left u₀ unit)) := by
      intro l hl k hk heq
      rw [←hkey l (hs hl),←hkey k (hs hk),heq]
    have hh:=hselected (selected.image back)
      (by intro l hl;obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hl;exact hmem v (hs hv)) (by
        intro l hl k hk heq
        obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hl
        obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hk
        change nonzeroJointSourceRow (key (back v))=nonzeroJointSourceRow (key (back u)) at heq
        rw [hkey v (hs hv),hkey u (hs hu)] at heq
        rw [hrawinj hv hu heq])
    simpa only [Finset.sum_image hb] using hh

/-- A finite fixed dictionary and a varying surviving original slot subset
only cost fixed cardinalities after actual raw-frequency selection. -/
theorem fixed_dictionary_slot_partition {κ α Dict : Type} [Fintype α] [DecidableEq α]
    [Fintype Dict] (labels : Finset κ) (index : κ→Dict) (slots : κ→Finset α)
    (cost : κ→ℝ) (E : ℝ)
    (hE : ∀j s,(∑l∈labels.filter (fun l=>index l=j ∧ slots l=s),cost l)≤E) :
    (∑l∈labels,cost l)≤(Fintype.card Dict:ℝ)*(2:ℝ)^(Fintype.card α)*E := by
  have hsplit : (∑l∈labels,cost l)=∑j : Dict,∑l∈labels.filter (fun l=>index l=j),cost l := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun _ _=>Finset.mem_univ _) cost
  rw [hsplit]
  calc
    _≤∑_j : Dict,(2:ℝ)^(Fintype.card α)*E := by
      refine Finset.sum_le_sum fun j _ => ?_
      apply Cycle63CommonSupply.slot_partition_bound
      intro s
      simpa only [Finset.filter_filter] using hE j s
    _=_ := by simp [mul_assoc]

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
