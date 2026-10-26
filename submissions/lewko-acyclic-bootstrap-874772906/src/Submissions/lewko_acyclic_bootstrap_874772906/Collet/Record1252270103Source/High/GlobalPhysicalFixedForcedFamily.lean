/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed residual ideal is kept outside the genuine original-row allocation
selection. This is the ordering used by the earlier ordinary source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalFixedSecondAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.JointForcedFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentAmplificationChildSourceCaps
open Record1252270103Source Record1252270103Second Collision Admission.JointForced
local notation "O"=>HeckeFamily.O
universe u v

theorem uniform_fixed_residual_original_forced_family (N:ℕ)(ε:ℝ)(hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀{Row:Type v}(rows:Finset Row)(ι:Row→Type u)[∀r,Fintype (ι r)]
    (s:∀r,Input (ι r)),
    (∀r∈rows,Fintype.card (ι r)≤N)→
    ∀(A₁ A₂ D K C R seed:Row→Ideal O)(L:Ideal O),Squarefree L→∀
    (F:Row→Ideal O→ℂ)(hC:∀r,Supported (C r))(hseed:∀r,seed r∣C r)
    (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(weight:Row→ℝ)
    (hw:∀r∈rows,0≤weight r),
    let energy:=fun r=>fixedPlainEnergy (s r) (A₁ r) (A₂ r) (D r) (K r) (C r) (R r) (seed r) L
      (F r) (hC r) (τ r) (t r) (z r)
    let live:=rows.filter (fun r=>energy r≠0)
    ∃alloc:∀r:live,actualAllocations (s r).pools (C r),
      (∀r,frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P≠0) ∧
      let s':=fun r:live=>child (s r) (C r) (R r) (alloc r) (τ r) (t r)
      let modifier':=fun r:live=>markedSourceModifier
        (A₁ r*(alloc r).val (Sum.inr 0)) (A₂ r*(alloc r).val (Sum.inr 1))
        (D r*C r) (K r*markedProduct (alloc r).val) (F r)
      ∃pick:∀r:live,ChildIndex (s' r) (modifier' r) (R r*C r) L,
      (∀r:live,frozenCoefficient (pick r).2 (pick r).1 (R r*C r) (s' r).ν (s' r).W (s' r).P≠0 ∧
        0<childValue (s' r) (modifier' r) (R r*C r) L (τ r) (t r) (z r) (pick r) ∧
        L∣((pick r).1:Ideal O) ∧ ((pick r).1:Ideal O)∣L^2) ∧
      (∑r∈rows,energy r*weight r)≤
        K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*∑r:live,((actualAllocations (s r).pools (C r)).card:ℝ)^2*
          ‖frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P‖^2*
            (volume (s' r)/volume (s r))*
              forcedProfileCost (s' r)*childValue (s' r) (modifier' r) (R r*C r) L (τ r) (t r) (z r) (pick r)*weight r := by
  classical
  obtain ⟨K₀,hK₀,hforced⟩:=uniform_selected_child.{u} N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro Row rows ι inst s hcard A₁ A₂ D K C R seed L hL F hC hseed τ t z weight hw energy live
  obtain ⟨alloc,hf,hn,hbound⟩:=fixed_residual_original_allocation_family rows ι s A₁ A₂ D K C R seed L
    F hC hseed τ t z weight hw
  refine ⟨alloc,hf,?_⟩
  intro s' modifier'
  have hex (r:live):=hforced ((live_card_le (alloc r).val).trans (hcard r (Finset.mem_filter.mp r.property).1))
    (s' r) (A₁ r*(alloc r).val (Sum.inr 0)) (A₂ r*(alloc r).val (Sum.inr 1))
    (D r*C r) (K r*markedProduct (alloc r).val) (R r*C r) L (F r) hL (τ r) (t r) (z r) (hn r)
  choose pick hp using hex
  refine ⟨pick,(fun r=>⟨(hp r).1,(hp r).2.1,(hp r).2.2.1,(hp r).2.2.2.1⟩),hbound.trans ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hweight:=hw r (Finset.mem_filter.mp r.property).1
  have hwgt:0≤((actualAllocations (s r).pools (C r)).card:ℝ)^2*
      ‖frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P‖^2*
        (volume (s' r)/volume (s r))*weight r := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (volume_pos _).le (volume_pos _).le)) hweight
  have hh:=mul_le_mul_of_nonneg_right (hp r).2.2.2.2 hwgt
  convert hh using 1 <;> ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.uniform_fixed_residual_original_forced_family
