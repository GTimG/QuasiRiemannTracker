/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal joint second normalized sum has a height-independent finite
absolute envelope. This supplies the large Mellin-height branch. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalPlainAbsolute
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondContraction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondPhysicalBlock Cycle61InitialMass
local notation "O"=>HeckeFamily.O
local instance normalizedAbsoluteSumDecidable {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- The padded residual pool and original block weights remain visible. -/
def secondAbsoluteBudget {α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
    (d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)(w:Label→ℂ):ℝ :=
  ∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),
    ‖w r.1‖*(d r.1).block.outside*
      ((secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r).card:ℝ)*
      (∑I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),
        ‖CoupledFirst.coefficient (d r.1).input (modifier r.1) (d r.1).R (d r.1).seed I‖)^2

theorem modified_second_normalized_absolute {α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
    (reflected:Bool)(d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
    (w:Label→ℂ)(t u:ℝ):
    modifiedSecondNormalizedSum reflected d modifier w t u≤secondAbsoluteBudget (α:=α) (Label:=Label) d modifier w := by
  unfold modifiedSecondNormalizedSum secondAbsoluteBudget
  apply Finset.sum_le_sum
  intro r hr
  have hv:=volume_pos (d r.1).input.toData
  have ho:0≤(d r.1).block.outside:=(second_outside_pos (d r.1).block).le
  let mass:=∑I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),
    ‖CoupledFirst.coefficient (d r.1).input (modifier r.1) (d r.1).R (d r.1).seed I‖
  have hpoint (L:Ideal O):
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        (if reflected then
          ‖modifiedPlainColumn (d r.1).input (modifier r.1) (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L
            ((d r.1).τ r.2.2.1⁻¹) ((d r.1).input.t+2*Real.pi*(u-(-t))) (-r.2.2.2.val)‖^2
         else
          ‖modifiedPlainColumn (d r.1).input (modifier r.1) (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L
            ((d r.1).τ r.2.1) ((d r.1).input.t+2*Real.pi*(u-t)) r.2.2.2.val‖^2)≤
      ‖w r.1‖*(d r.1).block.outside*mass^2 := by
    have hb : (if reflected then
          ‖modifiedPlainColumn (d r.1).input (modifier r.1) (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L
            ((d r.1).τ r.2.2.1⁻¹) ((d r.1).input.t+2*Real.pi*(u-(-t))) (-r.2.2.2.val)‖^2
         else
          ‖modifiedPlainColumn (d r.1).input (modifier r.1) (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L
            ((d r.1).τ r.2.1) ((d r.1).input.t+2*Real.pi*(u-t)) r.2.2.2.val‖^2)≤mass^2/volume (d r.1).input.toData := by
      cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact modified_plain_absolute_sq (d r.1).input (modifier r.1) (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L ((d r.1).τ r.2.1) ((d r.1).input.t+2*Real.pi*(u-t)) r.2.2.2.val
      · exact modified_plain_absolute_sq (d r.1).input (modifier r.1) (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L ((d r.1).τ r.2.2.1⁻¹) ((d r.1).input.t+2*Real.pi*(u-(-t))) (-r.2.2.2.val)
    apply (mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg (norm_nonneg _) ho) hv.le)).trans_eq
    field_simp [hv.ne']
  have hh:=Finset.sum_le_sum (fun L (_:L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r)=>hpoint L)
  apply hh.trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul,mass]
  ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_normalized_absolute
