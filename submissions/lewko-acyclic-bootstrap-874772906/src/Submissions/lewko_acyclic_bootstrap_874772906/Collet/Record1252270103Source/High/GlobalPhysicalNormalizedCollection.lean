/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original second-row keys are counted once. The fixed-L estimates are then
summed with the full padded inverse-norm mass. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalNormalizedKeys
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open Record1252270103Second SecondRemainder Admission.ModifiedFibers
local notation "O"=>HeckeFamily.O

theorem normalized_fixed_key_collection (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label Key:Type}[Fintype α][DecidableEq α][Fintype Label][DecidableEq Key]
      (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
      (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u W ε E:ℝ),
    0≤W→0≤ε→0≤E→
    let modifier:=fun l=>correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1)
    let blocks:=fun l=>modifiedDatumBlock (d l) (modifier l)
    let rows:=secondLiveRows blocks
    ∀(key:rows→Key)(transform:Key→Key),FullCostSelection key transform W→
    (∀r∈rows,∀L∈secondResidualIdeals blocks r,(L.absNorm:ℝ)≤Z^B)→
    let labels:=Finset.univ.image key
    (∀pick:labels→ rows,(∀j,key (pick j)=j.val)→
      Function.Injective (fun j=>transform (key (pick j)))→
      ∀L∈Finset.univ.biUnion (fun j:labels=>secondResidualIdeals blocks (pick j).val),
        (∑j∈Finset.univ.filter (fun j:labels=>L∈secondResidualIdeals blocks (pick j).val),
          correctedResidualTerm reflected d P A₁ A₂ D K w t u (pick j).val L)≤
            ((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*E)→
    modifiedSecondNormalizedSum reflected d modifier w t u≤W*C*Z^(δ+B*ε)*E := by
  obtain ⟨C,hC,hcollect⟩:=uniform_fixed_residual_collection B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hcollect] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label Key _ _ _ _ reflected d P A₁ A₂ D K w t u W ε E hW hε hE
    modifier blocks rows key transform hselect hcap labels hfixed
  obtain ⟨pick,hpick,hinj,hbound⟩:=corrected_normalized_key_selection
    reflected d P A₁ A₂ D K w t u W key transform hselect
  have hc:=hZ.2 ε E hε hE (Finset.univ:Finset labels)
    (fun j=>secondResidualIdeals blocks (pick j).val)
    (fun j L=>correctedResidualTerm reflected d P A₁ A₂ D K w t u (pick j).val L)
    (fun j _ L hL=>((mem_second_residual_ideals blocks (pick j).val L).mp hL).2)
    (fun j _ L hL=>hcap (pick j).val (pick j).property L hL)
    (hfixed pick hpick hinj)
  rw [residual_union_reassembly] at hc
  exact hbound.trans ((mul_le_mul_of_nonneg_left hc hW).trans_eq (by ring))

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_fixed_key_collection
