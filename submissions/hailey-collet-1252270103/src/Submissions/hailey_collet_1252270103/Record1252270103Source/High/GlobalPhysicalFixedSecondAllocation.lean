/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed residual ideal is kept outside the genuine original-row allocation
selection. This is the ordering used by the earlier ordinary source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondAllocationSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open Record1252270103Source Record1252270103Second Collision Admission.JointForced
local notation "O"=>HeckeFamily.O
universe u v

def fixedPlainEnergy {ι:Type u}[Fintype ι] (s:Input ι)
    (A₁ A₂ D K C R seed L:Ideal O)(F:Ideal O→ℂ)(hC:Supported C)
    (τ:Character)(t:ℝ)(z:O) : ℝ :=
  ‖modifiedPlainColumn s (markedSourceModifier A₁ A₂ D K F) C hC R seed L τ t z‖^2

/-- Both allocation-card factors remain: one is from the exact Cauchy
reduction and the other from choosing a maximum. The selected family is a
subset of the original rows, with one fixed residual ideal throughout. -/
theorem fixed_residual_original_allocation_family
    {Row:Type v}(rows:Finset Row)(ι:Row→Type u)[∀r,Fintype (ι r)]
    (s:∀r,Input (ι r))(A₁ A₂ D K C R seed:Row→Ideal O)(L:Ideal O)
    (F:Row→Ideal O→ℂ)(hC:∀r,Supported (C r))(hseed:∀r,seed r∣C r)
    (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(weight:Row→ℝ)
    (hw:∀r∈rows,0≤weight r) :
    let energy:=fun r=>fixedPlainEnergy (s r) (A₁ r) (A₂ r) (D r) (K r) (C r) (R r) (seed r) L
      (F r) (hC r) (τ r) (t r) (z r)
    let live:=rows.filter (fun r=>energy r≠0)
    ∃alloc:∀r:live,actualAllocations (s r).pools (C r),
      (∀r,frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P≠0) ∧
      let s':=fun r:live=>child (s r) (C r) (R r) (alloc r) (τ r) (t r)
      let modifier':=fun r:live=>markedSourceModifier
        (A₁ r*(alloc r).val (Sum.inr 0)) (A₂ r*(alloc r).val (Sum.inr 1))
        (D r*C r) (K r*markedProduct (alloc r).val) (F r)
      (∀r:live,normalizedRow (s' r) (modifier' r) (R r*C r) L (τ r) (t r) (z r)≠0) ∧
      (∑r∈rows,energy r*weight r)≤
        ∑r:live,((actualAllocations (s r).pools (C r)).card:ℝ)^2*
          ‖frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P‖^2*
            (volume (s' r)/volume (s r))*
              ‖normalizedRow (s' r) (modifier' r) (R r*C r) L (τ r) (t r) (z r)‖^2*weight r := by
  classical
  intro energy live
  have hex (r:live):=marked_plain_residual_selected_allocation (s r)
    (A₁ r) (A₂ r) (D r) (K r) (C r) (R r) (seed r) (F r) (hC r) (hseed r)
    {L} (τ r) (t r) (z r) (by simpa only [Finset.sum_singleton,energy,fixedPlainEnergy] using (Finset.mem_filter.mp r.property).2)
  choose alloc hf hpos hbound using hex
  refine ⟨alloc,hf,?_⟩
  intro s' modifier'
  refine ⟨?_,?_⟩
  · intro r hn
    have h:=hpos r
    simp only [secondAllocatedResidualNorm,Finset.sum_singleton] at h
    change 0<‖normalizedRow (s' r) (modifier' r) (R r*C r) L (τ r) (t r) (z r)‖^2 at h
    rw [hn,norm_zero,zero_pow (by decide)] at h
    exact (lt_irrefl 0 h)
  · have he:(∑r∈rows,energy r*weight r)=∑r:live,energy r*weight r := by
      rw [Finset.sum_coe_sort live (fun r:Row=>energy r*weight r)]
      simp only [live,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hn:energy r=0 <;> simp [hn]
    rw [he]
    apply Finset.sum_le_sum
    intro r hr
    have hh:=mul_le_mul_of_nonneg_right (hbound r) (hw r (Finset.mem_filter.mp r.property).1)
    simpa only [Finset.sum_singleton,secondAllocatedResidualNorm,energy,fixedPlainEnergy,s',modifier'] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.fixed_residual_original_allocation_family
