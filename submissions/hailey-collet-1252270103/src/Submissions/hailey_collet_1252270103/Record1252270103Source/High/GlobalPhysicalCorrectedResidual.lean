/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal corrected second normalized sum is collected with one residual
ideal fixed across the original rows. No row divisor truncation is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondContraction
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalFixedSecondAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalResidualUnion
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Correction
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentHeckeColumnWindow CenteredMomentExceptionalAmplitudePair
open CenteredMomentHeckeExpansion CenteredMomentCommonProfile
open OAI.SevenEighths.Record1252270103Source
open OAI.SevenEighths.Record1252270103Source.Collision
open Record1252270103Second SecondRemainder
local notation "O"=>HeckeFamily.O

/-- Before the second extraction the correction counts the unfrozen column.
The first common ideal belongs to the puncture, not to this correction mask. -/
theorem corrected_one_modifier {ι:Type*}[Fintype ι]
    (P:Finset (Ideal O))(A₁ A₂ D K:Ideal O):
    correctedModifier (ι:=ι) P A₁ A₂ D K (fun _=>1)=
      markedSourceModifier A₁ A₂ 1 K (poolCorrection P) := by
  unfold correctedModifier
  congr 1
  funext I
  simp only [mul_one,poolCorrection,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_natCast]

def correctedResidualTerm {α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
    (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
    (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u:ℝ)
    (r:SecondRow (fun l=>modifiedDatumBlock (d l)
      (correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1))))(L:Ideal O):ℝ :=
  let η:=if reflected then (d r.1).τ r.2.2.1⁻¹ else (d r.1).τ r.2.1
  let height:=(d r.1).input.t+2*Real.pi*(u-(if reflected then -t else t))
  let z:=if reflected then -r.2.2.2.val else r.2.2.2.val
  let common:=if reflected then (d r.1).D else (d r.1).C
  let hcommon:Supported common:=by
    cases reflected
    · exact (d r.1).hC
    · exact (d r.1).hD
  fixedPlainEnergy (d r.1).input (A₁ r.1) (A₂ r.1) 1 (K r.1) common
    (d r.1).R (d r.1).seed L (poolCorrection P) hcommon η height z*
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)

theorem corrected_normalized_residual_reassembly {α Label:Type*}
    [Fintype α][DecidableEq α][Fintype Label]
    (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
    (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u:ℝ):
    let modifier:=fun l=>correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1)
    let blocks:=fun l=>modifiedDatumBlock (d l) (modifier l)
    let rows:=secondLiveRows blocks
    modifiedSecondNormalizedSum reflected d modifier w t u=
      ∑L∈rows.biUnion (secondResidualIdeals blocks),
        ∑r∈rows.filter (fun r=>L∈secondResidualIdeals blocks r),
          correctedResidualTerm reflected d P A₁ A₂ D K w t u r L := by
  intro modifier blocks rows
  rw [←residual_union_reassembly]
  unfold modifiedSecondNormalizedSum
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro L hL
  cases reflected <;> simp only [correctedResidualTerm,fixedPlainEnergy,modifier,
    corrected_one_modifier,Bool.false_eq_true,ite_false,ite_true,mul_comm]

/-- This final scalar collection uses the whole padded union. The fixed-L
joint estimate is supplied before the harmonic mass is taken. -/
theorem modified_second_normalized_fixed_residual (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃H:ℝ,0<H ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected:Bool)(d:Label→SecondInputDatum α)(P:Finset (Ideal O))
      (A₁ A₂ D K:Label→Ideal O)(w:Label→ℂ)(t u ε E:ℝ),0≤ε→0≤E→
    let modifier:=fun l=>correctedModifier P (A₁ l) (A₂ l) (D l) (K l) (fun _=>1)
    let blocks:=fun l=>modifiedDatumBlock (d l) (modifier l)
    let rows:=secondLiveRows blocks
    (∀r∈rows,∀L∈secondResidualIdeals blocks r,(L.absNorm:ℝ)≤Z^B)→
    (∀L∈rows.biUnion (secondResidualIdeals blocks),
      (∑r∈rows.filter (fun r=>L∈secondResidualIdeals blocks r),
        correctedResidualTerm reflected d P A₁ A₂ D K w t u r L)≤
        ((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*E)→
    modifiedSecondNormalizedSum reflected d modifier w t u≤H*Z^(δ+B*ε)*E := by
  obtain ⟨H,hH,hcollect⟩:=uniform_fixed_residual_collection B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hcollect] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label _ _ _ reflected d P A₁ A₂ D K w t u ε E hε hE modifier blocks rows hcap hfixed
  rw [corrected_normalized_residual_reassembly]
  rw [←residual_union_reassembly]
  exact hZ.2 ε E hε hE rows (secondResidualIdeals blocks)
    (correctedResidualTerm reflected d P A₁ A₂ D K w t u)
    (fun r _ L hL=>((mem_second_residual_ideals blocks r L).mp hL).2) hcap hfixed

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_one_modifier
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_normalized_residual_reassembly
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_normalized_fixed_residual
