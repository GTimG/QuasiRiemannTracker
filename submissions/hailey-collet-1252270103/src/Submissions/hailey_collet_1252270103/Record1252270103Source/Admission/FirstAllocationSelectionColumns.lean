/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual first-column dyads and rays are paid before an injective key is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstAllocationSelectionFinite
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryHighFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstAllocationSelection
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentDyadicCount
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
section ColumnFamilies
variable {ι:Type*} [Fintype ι] (s:Input ι) (modifier:Tuple ι→ℂ)
  (R seed:Ideal O) (K Z ξ:ℝ) (hK:0<K) (bin:ℤ×(Fin 5→ℤ))
local notation "Columns"=>FirstColumnIndex (source s modifier R seed K Z ξ hK bin)

def columnKey (j:Columns) : FirstSourceLabel×Ideal O :=
  (FirstFamily.firstLabel s modifier R seed K Z ξ hK bin j,j.2.1.val)

def columnAux (j:Columns) : (Fin 4→ℤ)×RayCharacter×RayCharacter :=
  ((fun i=>(j.1.val.2.2 i:ℤ)),j.2.2.1,j.2.2.2)

/-- The true code includes all four dyads and both rays. The geometry bin
alone does not assert these are determined by the arithmetic key. -/
theorem column_key_aux_injective : Function.Injective (fun j:Columns=>
    (columnKey s modifier R seed K Z ξ hK bin j,columnAux s modifier R seed K Z ξ hK bin j)) := by
  intro j k h
  apply FirstFamily.column_code_injective s modifier R seed K Z ξ hK bin
  exact congrArg (fun x:(FirstSourceLabel×Ideal O)×((Fin 4→ℤ)×RayCharacter×RayCharacter)=>
    (x.1.1,x.1.2,x.2)) h

theorem fixed_column_aux_key_injective (a:(Fin 4→ℤ)×RayCharacter×RayCharacter) :
    Function.Injective (fun j:{j:Columns // columnAux s modifier R seed K Z ξ hK bin j=a}=>
      columnKey s modifier R seed K Z ξ hK bin j.val) := by
  intro j k h
  apply Subtype.ext
  exact column_key_aux_injective s modifier R seed K Z ξ hK bin
    (Prod.ext h (j.property.trans k.property.symm))

/-- An arbitrary original-column restriction retains its exact fiber count.
Only the actual dyad box and the finite pair of rays are paid. -/
theorem column_key_fiber_card (rows:Finset Columns) (N:Finset (Fin 4→ℤ))
    (hN:∀j:rows,(fun i=>(j.val.1.val.2.2 i:ℤ))∈N) (k:FirstSourceLabel×Ideal O) :
    (Finset.univ.filter (fun j:rows=>columnKey s modifier R seed K Z ξ hK bin j.val=k)).card≤
      N.card*(Fintype.card RayCharacter)^2 := by
  let fiber:=Finset.univ.filter (fun j:rows=>columnKey s modifier R seed K Z ξ hK bin j.val=k)
  let target:=N×ˢ((Finset.univ:Finset RayCharacter)×ˢ(Finset.univ:Finset RayCharacter))
  have hc:fiber.card≤target.card:=Finset.card_le_card_of_injOn
    (fun j:rows=>columnAux s modifier R seed K Z ξ hK bin j.val)
    (by intro j _;exact Finset.mem_product.mpr ⟨hN j,by simp⟩)
    (by
      intro j hj l hl he
      apply Subtype.ext
      exact column_key_aux_injective s modifier R seed K Z ξ hK bin
        (Prod.ext ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hl).2.symm) he))
  simpa only [target,Finset.card_product,Finset.card_univ,pow_two] using hc
end ColumnFamilies

/-- Complete-cost selection over the genuine missing first dyads and rays.
The constant precedes all finite types and actual modified source data.
No energy estimate is assumed for the selected family. -/
theorem actual_first_full_cost_selection (A D B ξ ε:ℝ)
    (hA:0≤A) (hD:0≤D) (hB:0≤B) (hξ:0≤ξ) (hε:0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,1≤Z ∧
      ∀{ι:Type*} [Fintype ι] (s:Input ι) (modifier:Tuple ι→ℂ)
        (R seed:Ideal O) (K:ℝ) (hK:0<K) (bin:ℤ×(Fin 5→ℤ)),
      Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→
      0<sourceRadius s→sourceRadius s≤Z^B→volume s≤Z^A→K⁻¹≤Z^D→
      ∀(rows:Finset (FirstColumnIndex (source s modifier R seed K Z ξ hK bin)))
        (cost:rows→ℝ), (∀j,0≤cost j)→
      let key:=fun j:rows=>columnKey s modifier R seed K Z ξ hK bin j.val
      ∃ pick : (k : Finset.univ.image key) → rows,
        (∀k,key (pick k)=k.val) ∧ Function.Injective (fun k=>key (pick k)) ∧
        (∑j:rows,cost j)≤(C₀*Z^ε)*(∑k:Finset.univ.image key,cost (pick k)) := by
  have hL:0≤3*max A D+ξ/2:=by positivity
  obtain ⟨C,hC,hbox⟩:=source_dyadic_envelope_subpower B (3*max A D+ξ/2) ε hB hL hε
  have hray:(0:ℝ)<Fintype.card RayCharacter:=by exact_mod_cast Fintype.card_pos
  refine ⟨C*(Fintype.card RayCharacter:ℝ)^2,by positivity,?_⟩
  filter_upwards [hbox,eventually_ge_atTop (1:ℝ)] with Z hbox hZ
  refine ⟨hZ,?_⟩
  intro ι inst s modifier R seed K hK bin hs hz₁ hz₂ hpos hsource hvolume hKi rows cost hc key
  let box:Finset (Fin 4→ℤ):=Fintype.piFinset (fun i=>
    indices (![K/Z^(2*B),1,1,1] i) (![K,Z^(3*max A D+ξ/2),Z^B,Z^B] i))
  have hcard:(box.card:ℝ)≤C*Z^ε:=by
    have hh:=hbox K hK
    simpa only [box,SourceDyadicEnvelope,Fintype.card_piFinset,Fintype.card_pi,Fintype.card_coe] using hh
  have hmem (j:rows):(fun i=>(j.val.1.val.2.2 i:ℤ))∈box:=
    Fintype.mem_piFinset.mpr (High.CoupledFirst.actual_dyads_in_envelope s modifier R seed K Z ξ A D B
      hK hZ hB hA hD hξ hs hz₁ hz₂ hpos hsource hvolume hKi j.val.1.val)
  apply high_family_max_selection key cost _ (by positivity) hc
  intro k
  have hh:((Finset.univ.filter (fun j:rows=>key j=k)).card:ℝ)≤
      (box.card:ℝ)*(Fintype.card RayCharacter:ℝ)^2:=by
    exact_mod_cast column_key_fiber_card s modifier R seed K Z ξ hK bin rows box hmem k
  exact hh.trans ((mul_le_mul_of_nonneg_right hcard (sq_nonneg _)).trans_eq (by ring))

end
end QRH.Record1252270103Source.Admission.FirstAllocationSelection
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.column_key_aux_injective
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.fixed_column_aux_key_injective
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.column_key_fiber_card
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.actual_first_full_cost_selection
