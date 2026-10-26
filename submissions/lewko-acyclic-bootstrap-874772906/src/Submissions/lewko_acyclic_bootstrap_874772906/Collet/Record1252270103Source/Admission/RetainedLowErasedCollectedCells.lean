/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowScaleCollection
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.LowErasure.Partition
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open scoped Classical BigOperators
variable {Key Slot : Type*}

def originalKeyCarrier (labels : Finset Key) (rows : Finset labels) : Finset Key :=
  rows.image Subtype.val

def originalKeyInclusion (labels : Finset Key) (rows : Finset labels)
    (l : originalKeyCarrier labels rows) : labels :=
  ⟨l.val,by obtain ⟨r,_,he⟩:=Finset.mem_image.mp l.property;exact he ▸ r.property⟩

lemma originalKeyInclusion_mem (labels : Finset Key) (rows : Finset labels)
    (l : originalKeyCarrier labels rows) : originalKeyInclusion labels rows l∈rows := by
  obtain ⟨r,hr,he⟩:=Finset.mem_image.mp l.property
  have h : originalKeyInclusion labels rows l=r:=Subtype.ext he.symm
  rwa [h]

lemma originalKeyCarrier_sum (labels : Finset Key) (rows : Finset labels) (g : labels→ℝ) :
    (∑l : originalKeyCarrier labels rows,g (originalKeyInclusion labels rows l))=
      ∑r∈rows,g r := by
  symm
  apply Finset.sum_bij (fun r hr=>⟨r.val,Finset.mem_image.mpr ⟨r,hr,rfl⟩⟩)
  · intro r hr;exact Finset.mem_univ _
  · intro r₁ _ r₂ _ he
    exact Subtype.ext (congrArg (fun l : originalKeyCarrier labels rows=>l.val) he)
  · intro l _
    obtain ⟨r,hr,he⟩:=Finset.mem_image.mp l.property
    exact ⟨r,hr,Subtype.ext he⟩
  · intro r _;rfl

theorem selected_scale_partition [DecidableEq Slot] {Row : Type*} (rows : Finset Row) (T : Finset Slot)
    (select : Row→Finset Slot) (hs : ∀r∈rows,select r⊆T)
    (tag : Row→Fin 3→ℤ) (value : Row→ℂ) (weight : Row→ℝ) :
    let live:=rows.filter (fun r=>value r≠0)
    (∑r∈rows,‖value r‖^2*weight r)=
      ∑F∈T.powerset,∑k∈(live.filter (fun r=>select r=F)).image tag,
        ∑r∈(live.filter (fun r=>select r=F)).filter (fun r=>tag r=k),
          ‖value r‖^2*weight r := by
  intro live
  have he : (∑r∈rows,‖value r‖^2*weight r)=∑r∈live,‖value r‖^2*weight r := by
    dsimp only [live]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs with hn
    · rfl
    · simp only [not_ne_iff.mp hn,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
  rw [he]
  calc
    (∑r∈live,‖value r‖^2*weight r) =
        ∑F∈T.powerset,∑r∈live.filter (fun r=>select r=F),‖value r‖^2*weight r := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      have hm : select r∈T.powerset:=Finset.mem_powerset.mpr
        (hs r (Finset.mem_filter.mp hr).1)
      simp only [Finset.sum_ite_eq,hm,ite_true]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro F _
      exact (Finset.sum_fiberwise_of_maps_to
        (fun r hr=>Finset.mem_image.mpr ⟨r,hr,rfl⟩) (fun r=>‖value r‖^2*weight r)).symm
theorem selected_scale_sum_le [DecidableEq Slot] {Row : Type*} (rows : Finset Row) (T : Finset Slot)
    (select : Row→Finset Slot) (hs : ∀r∈rows,select r⊆T)
    (tag : Row→Fin 3→ℤ) (value : Row→ℂ) (weight : Row→ℝ)
    (budget : Finset Slot→(Fin 3→ℤ)→ℝ)
    (hc : ∀F∈T.powerset,∀k∈((rows.filter (fun r=>value r≠0)).filter (fun r=>select r=F)).image tag,
      (∑r∈((rows.filter (fun r=>value r≠0)).filter (fun r=>select r=F)).filter
        (fun r=>tag r=k),‖value r‖^2*weight r)≤budget F k) :
    (∑r∈rows,‖value r‖^2*weight r)≤
      ∑F∈T.powerset,∑k∈((rows.filter (fun r=>value r≠0)).filter (fun r=>select r=F)).image tag,
        budget F k := by
  rw [selected_scale_partition rows T select hs tag value weight]
  exact Finset.sum_le_sum (fun F hF=>Finset.sum_le_sum (fun k hk=>hc F hF k hk))

end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.originalKeyCarrier_sum
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.selected_scale_partition

#print axioms QRH.Record1252270103Source.Admission.RetainedLow.selected_scale_sum_le
