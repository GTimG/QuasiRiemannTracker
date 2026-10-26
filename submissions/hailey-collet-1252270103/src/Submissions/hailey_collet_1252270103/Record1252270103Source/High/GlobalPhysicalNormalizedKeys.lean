/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The entire residual cost is selected on original second-row keys before
fixing a residual ideal. All residual ideals remain in the padded union. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalCorrectedResidual
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.ModifiedFibersSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentExceptionalAmplitudePair
open Record1252270103Second SecondRemainder Admission.ModifiedFibers
local notation "O"=>HeckeFamily.O
variable {α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]

theorem corrected_residual_term_nonneg
    (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
    (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u:ℝ)
    (r:SecondRow (fun l=>modifiedDatumBlock (d l)
      (correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1))))(L:Ideal O):
    0≤correctedResidualTerm reflected d P A₁ A₂ D K w t u r L := by
  unfold correctedResidualTerm fixedPlainEnergy
  exact mul_nonneg (sq_nonneg _) (mul_nonneg
    (mul_nonneg (norm_nonneg _) (second_outside_pos (d r.1).block).le)
    (volume_pos (d r.1).input.toData).le)

/-- The representative maximizes the complete residual cost. Its key is
unchanged, and only afterwards is L fixed across the resulting family. -/
theorem corrected_normalized_key_selection
    (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
    (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u:ℝ)
    {Key:Type*}[DecidableEq Key](W:ℝ):
    let modifier:=fun l=>correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1)
    let blocks:=fun l=>modifiedDatumBlock (d l) (modifier l)
    let rows:=secondLiveRows blocks
    ∀(key:rows→Key)(transform:Key→Key),FullCostSelection key transform W→
    let labels:=Finset.univ.image key
    ∃pick:labels→ rows,
      (∀j,key (pick j)=j.val) ∧ Function.Injective (fun j=>transform (key (pick j))) ∧
      modifiedSecondNormalizedSum reflected d modifier w t u≤
        W*(∑L∈Finset.univ.biUnion (fun j:labels=>secondResidualIdeals blocks (pick j).val),
          ∑j∈Finset.univ.filter (fun j:labels=>L∈secondResidualIdeals blocks (pick j).val),
            correctedResidualTerm reflected d P A₁ A₂ D K w t u (pick j).val L) := by
  classical
  intro modifier blocks rows key transform hselect labels
  let cost:=fun r:rows=>∑L∈secondResidualIdeals blocks r.val,
    correctedResidualTerm reflected d P A₁ A₂ D K w t u r.val L
  have hc (r:rows):0≤cost r:=Finset.sum_nonneg (fun L _=>
    corrected_residual_term_nonneg reflected d P A₁ A₂ D K w t u r.val L)
  obtain ⟨pick,hpick,_,htransform,hbound⟩:=hselect Finset.univ (fun r=>cost r.val) (fun r=>hc r.val)
  have himage:Finset.univ.image (fun r:(Finset.univ:Finset rows)=>key r.val)=labels := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and,labels]
    constructor
    · rintro ⟨r,hr⟩;exact ⟨r.val,hr⟩
    · rintro ⟨r,hr⟩;exact ⟨⟨r,Finset.mem_univ _⟩,hr⟩
  let castKey : labels ≃ Finset.univ.image (fun r:(Finset.univ:Finset rows)=>key r.val) :=
    { toFun:=fun j=>⟨j.val,by rw [himage];exact j.property⟩
      invFun:=fun j=>⟨j.val,by rw [←himage];exact j.property⟩
      left_inv:=fun j=>Subtype.ext rfl
      right_inv:=fun j=>Subtype.ext rfl }
  let pick':labels→ rows:=fun j=>(pick (castKey j)).val
  refine ⟨pick',fun j=>hpick _,?_,?_⟩
  · intro j k h
    exact castKey.injective (htransform h)
  · have he:(∑r:rows,cost r)≤W*∑j:labels,cost (pick' j) := by
      have hs:(∑j:labels,cost (pick' j))=∑j,cost (pick j).val :=
        castKey.sum_comp (fun j=>cost (pick j).val)
      rw [hs]
      simpa only [Finset.sum_coe_sort] using hbound
    have hsum:modifiedSecondNormalizedSum reflected d modifier w t u=∑r:rows,cost r := by
      rw [corrected_normalized_residual_reassembly,←residual_union_reassembly]
      exact (Finset.sum_coe_sort rows _).symm
    rw [hsum]
    apply he.trans_eq
    congr 1
    exact residual_union_reassembly Finset.univ
      (fun j:labels=>secondResidualIdeals blocks (pick' j).val)
      (fun j L=>correctedResidualTerm reflected d P A₁ A₂ D K w t u (pick' j).val L)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_residual_term_nonneg
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_normalized_key_selection
