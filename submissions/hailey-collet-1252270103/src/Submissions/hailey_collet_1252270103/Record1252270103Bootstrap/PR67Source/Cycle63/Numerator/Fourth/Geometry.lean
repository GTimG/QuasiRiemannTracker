import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Capacity.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorBoxGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Damping
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Imported.NumeratorPacketMellin
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Holder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Parameters
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace Cycle63.Numerator.Fourth
open Cycle63.Arithmetic
open Cycle25.Numerator

lemma physical_y_range {d : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) :
    1/2≤ y/d ∧ y/d<1 := by
  have hs:=Physical.shiftBase_bounds hd
  have hp:=Physical.physical_d_pos hd.1
  refine ⟨by unfold Physical.shiftBase at hs;rw [mul_div_assoc] at hs;linarith,?_⟩
  apply (div_lt_one hp).mpr
  exact y_lt_half.trans (half_lt_dMinus.trans_le hd.1)

lemma coefficient_box_geometry {d xi slack : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus)
    (hx : 0<xi) (_hs : 0≤ slack) (hsmall : 2*xi+slack≤1/2)
    (j : ℕ) (hj : j∈Finset.range (WeightedQRH.Numerator.coefficientBoxCount xi+1)) :
    0≤1-y/d+(j:ℝ)*xi+xi ∧ (1-y/d+(j:ℝ)*xi+xi)+slack≤2 := by
  have hy:=physical_y_range hd
  have hv:=WeightedQRH.Numerator.coefficient_box_index_range xi hx j hj
  constructor <;> linarith

/-- A physical logarithmic conductor shift v enters the two-plain budget as
2v. This exact factor is retained in the public selected-capacity argument. -/
lemma scheduled_capacity_or_empty {α : Type*} (T : Finset α) (width : T→ℝ)
    {d t κ : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) (ht : 0≤ t) (hk : κ≤3/4)
    (hw : ∀i,0<width i)
    (hselected : (∑i,width i)≤ Capacity.scheduledCapacity d (2*t)) :
    (∃d' t':ℝ,dMinus≤ d' ∧ d'≤ dPlus ∧ 0≤ t' ∧ t'≤ t0 ∧
      Physical.plainScale d t=Physical.plainScale d' t' ∧
      (∑i,width i)≤ Physical.affineCapacity d' t') ∨
      (2*Physical.plainScale d t+6*κ*(∑i,width i)≤1 ∨ T=∅) := by
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>(hw i).le)
  by_cases hsmall:t≤ t0
  · left
    refine ⟨d,t,hd.1,hd.2,ht,hsmall,rfl,?_⟩
    simpa [Capacity.scheduledCapacity,show 2*t≤2*t0 by linarith] using hselected
  · right
    have hlarge:¬2*t≤2*t0:=by linarith
    have hselected':(∑i,width i)≤ Physical.oldCapacity (Physical.shiftBase d) t:=by
      simpa [Capacity.scheduledCapacity,hlarge] using hselected
    by_cases hraw:0≤(Physical.shiftBase d-2*t)/(9/2)
    · left
      have hs:(∑i,width i)≤(Physical.shiftBase d-2*t)/(9/2):=by
        simpa [Physical.oldCapacity,max_eq_right hraw] using hselected'
      have hbudget:2*Physical.plainScale d t+(9/2)*(∑i,width i)≤1:=by
        unfold Physical.plainScale Physical.shiftBase at *
        rw [mul_div_assoc] at hs
        linarith
      nlinarith
    · right
      have hs:(∑i,width i)≤0:=by
        simpa [Physical.oldCapacity,max_eq_left (le_of_not_ge hraw)] using hselected'
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hs':width ⟨i,hi⟩≤∑i,width i:=Finset.single_le_sum
        (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
      linarith [hw ⟨i,hi⟩]

end Cycle63.Numerator.Fourth

end
end Record1252270103Bootstrap.PR67
