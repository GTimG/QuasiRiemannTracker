/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete-cost finite allocation selection, including exact zero fibers. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.ModifiedFibersBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstAllocationSelection
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def weightedTotal {β:Type*} [Fintype β] (frozen:β→ℂ) (cost:β→ℝ) : ℝ :=
  ∑B,‖frozen B‖^2*cost B

lemma weighted_total_nonneg {β:Type*} [Fintype β] (frozen:β→ℂ) (cost:β→ℝ)
    (hc:∀B,0≤cost B) : 0≤weightedTotal frozen cost :=
  Finset.sum_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (hc B))

/-- Empty fibers and fibers whose complete weighted costs all vanish are
exactly zero. No inhabited-allocation hypothesis is introduced. -/
lemma weighted_total_eq_zero_iff {β:Type*} [Fintype β] (frozen:β→ℂ) (cost:β→ℝ)
    (hc:∀B,0≤cost B) : weightedTotal frozen cost=0 ↔ ∀B,frozen B=0 ∨ cost B=0 := by
  rw [weightedTotal,Finset.sum_eq_zero_iff_of_nonneg (fun B _=>mul_nonneg (sq_nonneg _) (hc B))]
  simp only [Finset.mem_univ,forall_const,mul_eq_zero,pow_eq_zero_iff (by decide:2≠0),norm_eq_zero]

/-- The maximizing value contains BOTH the actual frozen coefficient and
the complete child cost. No physical weight is discarded. -/
theorem weighted_full_cost_max {β:Type*} [Fintype β] (frozen:β→ℂ) (cost:β→ℝ)
    (hc:∀B,0≤cost B) (hne:weightedTotal frozen cost≠0) :
    ∃B,frozen B≠0 ∧ 0<cost B ∧
      (∀A,‖frozen A‖^2*cost A≤‖frozen B‖^2*cost B) ∧
      weightedTotal frozen cost≤(Fintype.card β:ℝ)*(‖frozen B‖^2*cost B) := by
  have hex:∃A,‖frozen A‖^2*cost A≠0 := by
    by_contra h
    apply hne
    exact Finset.sum_eq_zero (fun A _=>not_ne_iff.mp (not_exists.mp h A))
  obtain ⟨A,hA⟩:=hex
  obtain ⟨B,_,hmax⟩:=Finset.exists_max_image (Finset.univ:Finset β)
    (fun B=>‖frozen B‖^2*cost B) ⟨A,Finset.mem_univ _⟩
  have hp:0<‖frozen B‖^2*cost B:=
    (lt_of_le_of_ne (mul_nonneg (sq_nonneg _) (hc A)) (Ne.symm hA)).trans_le (hmax A (Finset.mem_univ _))
  have hf:frozen B≠0:=by intro h;simpa [h] using hp
  have hcB:0<cost B:=lt_of_le_of_ne (hc B) (by intro h;simpa [←h] using hp)
  refine ⟨B,hf,hcB,(fun A=>hmax A (Finset.mem_univ _)),?_⟩
  calc
    _≤∑_A:β,‖frozen B‖^2*cost B:=Finset.sum_le_sum (fun A _=>hmax A (Finset.mem_univ _))
    _=_:=by simp

/-- Uniform allocation payment for every live slot type of cardinality at
most N. The constant precedes all source data and complete child costs. -/
theorem actual_allocation_full_cost_small_power (N:ℕ) (Bcap ε:ℝ) (hB:0≤Bcap) (hε:0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀Z:ℝ,1≤Z→∀{ι:Type*} [Fintype ι],Fintype.card ι≤N→
      ∀(s:Input ι) (C R:Ideal O) (cost:actualAllocations s.pools C→ℝ),
      C≠0→(C.absNorm:ℝ)≤Z^Bcap→(∀B,0≤cost B)→
      weightedTotal (fun B=>frozenCoefficient B.val C R s.ν s.W s.P) cost≠0→
      ∃B,frozenCoefficient B.val C R s.ν s.W s.P≠0 ∧ 0<cost B ∧
        weightedTotal (fun B=>frozenCoefficient B.val C R s.ν s.W s.P) cost≤
          (C₀*Z^ε)*(‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*cost B) := by
  obtain ⟨C₀,hC₀,hcard⟩:=ModifiedFibers.allocation_auxiliary_small_power N Bcap ε hB hε
  refine ⟨C₀,hC₀,?_⟩
  intro Z hZ ι inst hι s C R cost hC hnorm hc hne
  obtain ⟨B,hf,hcB,_,hmax⟩:=weighted_full_cost_max _ cost hc hne
  refine ⟨B,hf,hcB,hmax.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by simpa only [Fintype.card_coe] using hcard Z hZ hι s.pools C hC hnorm)
    (mul_nonneg (sq_nonneg _) hcB.le)

/-- All positive allocation fibers are selected simultaneously, once per
original row. The complete weighted sum and any outer weight stay on that row. -/
theorem weighted_family_selection {Row:Type*} [Fintype Row]
    (Alloc:Row→Type*) [∀r,Fintype (Alloc r)] (frozen:∀r,Alloc r→ℂ) (cost:∀r,Alloc r→ℝ)
    (hc:∀r B,0≤cost r B) (outer:Row→ℝ) (ho:∀r,0≤outer r) :
    let live:=Finset.univ.filter (fun r=>0<weightedTotal (frozen r) (cost r))
    ∃pick:∀r:live,Alloc r.val,
      (∀r,frozen r.val (pick r)≠0 ∧ 0<cost r.val (pick r)) ∧
      (∑r,weightedTotal (frozen r) (cost r)*outer r)=
        ∑r:live,weightedTotal (frozen r.val) (cost r.val)*outer r.val ∧
      (∑r,weightedTotal (frozen r) (cost r)*outer r)≤
        ∑r:live,(Fintype.card (Alloc r.val):ℝ)*
          (‖frozen r.val (pick r)‖^2*cost r.val (pick r))*outer r.val := by
  intro live
  have hp (r:live):0<weightedTotal (frozen r.val) (cost r.val):=(Finset.mem_filter.mp r.property).2
  choose pick hf hcost hmax hbound using (fun r:live=>weighted_full_cost_max
    (frozen r.val) (cost r.val) (hc r.val) (ne_of_gt (hp r)))
  have he:(∑r,weightedTotal (frozen r) (cost r)*outer r)=
      ∑r:live,weightedTotal (frozen r.val) (cost r.val)*outer r.val := by
    calc
      _=∑r∈live,weightedTotal (frozen r) (cost r)*outer r := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r _
        by_cases h:0<weightedTotal (frozen r) (cost r)
        · simp only [h,ite_true]
        · have hz:weightedTotal (frozen r) (cost r)=0:=
            le_antisymm (le_of_not_gt h) (weighted_total_nonneg _ _ (hc r))
          simp [hz]
      _=_:=Finset.sum_subtype live (by intro r;rfl) _
  refine ⟨pick,(fun r=>⟨hf r,hcost r⟩),he,?_⟩
  rw [he]
  exact Finset.sum_le_sum (fun r _=>mul_le_mul_of_nonneg_right (hbound r) (ho r.val))

end
end QRH.Record1252270103Source.Admission.FirstAllocationSelection
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.weighted_total_nonneg
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.weighted_total_eq_zero_iff
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.weighted_full_cost_max
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.actual_allocation_full_cost_small_power
#print axioms QRH.Record1252270103Source.Admission.FirstAllocationSelection.weighted_family_selection
