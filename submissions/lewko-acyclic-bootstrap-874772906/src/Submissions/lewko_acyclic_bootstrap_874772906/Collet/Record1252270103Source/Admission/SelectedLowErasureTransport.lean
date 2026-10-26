/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCofactorFamilyData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowErasure
noncomputable section
open scoped Classical BigOperators

variable {α κ : Type*} [Fintype κ] [DecidableEq α] [DecidableEq κ]

def originalPullback (f : κ↪α) (T : Finset α) : Finset κ :=
  Finset.univ.filter (fun i=>f i∈T)

lemma originalPullback_map (f : κ↪α) (T : Finset α) (hT : T⊆Finset.univ.map f) :
    (originalPullback f T).map f=T := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    obtain ⟨j,_,hji⟩:=Finset.mem_map.mp (hT hi)
    exact Finset.mem_map.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji ▸ hi⟩,hji⟩

lemma originalPullback_member (f : κ↪α) (T : Finset α) (i : κ)
    (hi : i∈originalPullback f T) : f i∈T := (Finset.mem_filter.mp hi).2

omit [Fintype κ] in
theorem original_erasure_transport (f : κ↪α) (S : Finset κ) (T : Finset α) (hmap : S.map f=T)
    (E : Finset κ) (hE : E⊆S) (w : α→ℝ) :
    let select:=(S\E).map f
    select⊆T ∧ T\select=E.map f ∧
      (∑j∈T,w j)=(∑i∈S,w (f i)) ∧
      (∑j∈select,w j)=(∑i∈S\E,w (f i)) ∧
      (∑j∈T\select,w j)=(∑i∈E,w (f i)) := by
  intro select
  have hsub : select⊆T := by
    rw [←hmap]
    exact Finset.map_subset_map.mpr Finset.sdiff_subset
  have herase : T\select=E.map f := by
    change T\(S\E).map f=E.map f
    rw [←hmap,←Finset.map_sdiff,Finset.sdiff_sdiff_eq_self hE]
  refine ⟨hsub,herase,?_,?_,?_⟩
  · rw [←hmap];exact Finset.sum_map _ _ _
  · exact Finset.sum_map _ _ _
  · rw [herase];exact Finset.sum_map _ _ _
end
end QRH.Record1252270103Source.Admission.SelectedLowErasure
#print axioms QRH.Record1252270103Source.Admission.SelectedLowErasure.originalPullback_map
#print axioms QRH.Record1252270103Source.Admission.SelectedLowErasure.original_erasure_transport
