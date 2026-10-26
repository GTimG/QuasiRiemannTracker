/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowSourceReindex
noncomputable section
open scoped Classical BigOperators

def keyImageEquiv {κ Key : Type} [DecidableEq κ] [DecidableEq Key]
    (rows : Finset κ) (key : κ → Key)
    (hinj : Function.Injective (fun r : rows => key r.val)) : rows ≃ rows.image key :=
  Equiv.ofBijective (fun r => ⟨key r.val, Finset.mem_image.mpr ⟨r.val,r.property,rfl⟩⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h), by
      intro j
      obtain ⟨r,hr,he⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨r,hr⟩,Subtype.ext he⟩⟩

@[simp] theorem keyImageEquiv_apply {κ Key : Type} [DecidableEq κ] [DecidableEq Key]
    (rows : Finset κ) (key : κ → Key)
    (hinj : Function.Injective (fun r : rows => key r.val)) (r : rows) :
    (keyImageEquiv rows key hinj r).val = key r.val := rfl

@[simp] theorem keyImageEquiv_symm_key {κ Key : Type} [DecidableEq κ] [DecidableEq Key]
    (rows : Finset κ) (key : κ → Key)
    (hinj : Function.Injective (fun r : rows => key r.val)) (j : rows.image key) :
    key ((keyImageEquiv rows key hinj).symm j).val = j.val :=
  congrArg Subtype.val ((keyImageEquiv rows key hinj).apply_symm_apply j)

theorem sum_keyImageEquiv {κ Key : Type} [DecidableEq κ] [DecidableEq Key]
    (rows : Finset κ) (key : κ → Key)
    (hinj : Function.Injective (fun r : rows => key r.val)) (f : rows → ℝ) :
    (∑r : rows,f r) = ∑j : rows.image key,f ((keyImageEquiv rows key hinj).symm j) := by
  exact (Equiv.sum_comp (keyImageEquiv rows key hinj).symm f).symm
end
end QRH.Record1252270103Source.Admission.SelectedLowSourceReindex
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSourceReindex.sum_keyImageEquiv
