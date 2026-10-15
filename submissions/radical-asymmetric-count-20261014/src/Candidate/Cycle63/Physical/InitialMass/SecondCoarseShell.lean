import Candidate.Cycle63.Physical.InitialMass.SecondCoarseRows

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw Cycle63Moment
local notation "O" => HeckeFamily.O
variable {ι : Type*}[Fintype ι][DecidableEq ι]

def coarseAllocationControl (s : Data ι)(B₁ B₂ : ℝ) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*(coarseRowControl s B₁ B₂)^2*
    (coarseRowSize s false+coarseRowSize s true)

lemma coarse_allocation_control_nonneg (s : Data ι)(B₁ B₂ : ℝ) :
    0≤coarseAllocationControl s B₁ B₂ := by
  unfold coarseAllocationControl
  exact mul_nonneg (by positivity)
    (add_nonneg (coarse_row_size_nonneg s false) (coarse_row_size_nonneg s true))

/-- The diagonal extraction sum is dominated by the already proved paired
projector sum. This costs no assertion that the projector divides a row. -/
theorem actual_reciprocal_diagonal (s : Data ι)(Ds : Finset (Ideal O)) :
    (∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      ∑D∈Ds,∑a∈s.toSource.active D,∑b∈s.toSource.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b s.P) := by
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro a ha
  have hh := Finset.single_le_sum (s:=s.toSource.active D)
    (f:=fun b=>1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b s.P))
    (fun b _=>by positivity) ha
  simpa only [←pow_two,Real.sqrt_sq (s.reduction_pos D a).le] using hh

/-- All-height coarse energy of the literal residual-projector shell.
The fixed factor precedes source data; the bound retains the original
support allowance and coefficient/profile controls. -/
theorem actual_second_coarse_shell (N : ℕ)(hι : Fintype.card ι≤N)(ε : ℝ)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(z : (D : Ideal O)→Allocation D (Finset.univ : Finset (ι⊕Fin 2))→O)
        (B₁ B₂ : ℝ),0≤B₁ → 0≤B₂ → (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) →
      (∑D∈Ds,∑a∈s.toSource.active D,retainedAllocationCost s D a (z D a))≤
        coarseAllocationControl s B₁ B₂*C*(2*T)^(2*ε)*Z^(s.toSource.allowance Z) := by
  obtain ⟨C,hC,hshell⟩ := paired_all_active_shell (ι:=ι) (κ:=ι) N hι hι ε hε
  refine ⟨C,hC,?_⟩
  intro s Ds hDs T Z hT hZ hlo hhi z B₁ B₂ hB₁ hB₂ hW₁ hW₂
  have hs := (actual_reciprocal_diagonal s Ds).trans (hshell s.toSource s.toSource Ds hDs T Z hT hZ hlo hhi)
  have hcost := coarse_allocation_control_nonneg s B₁ B₂
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,coarseAllocationControl s B₁ B₂/formalReductionFactor D a s.P :=
      Finset.sum_le_sum (fun D _=>Finset.sum_le_sum (fun a _=>
        actual_second_allocation_coarse s D a (z D a) B₁ B₂ hB₁ hB₂ hW₁ hW₂))
    _=coarseAllocationControl s B₁ B₂*(∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P) := by
      simp only [Finset.mul_sum,mul_one_div]
    _≤coarseAllocationControl s B₁ B₂*(C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+s.toSource.allowance Z)/2)) :=
      mul_le_mul_of_nonneg_left hs hcost
    _=_ := by rw [show (s.toSource.allowance Z+s.toSource.allowance Z)/2=s.toSource.allowance Z by ring]; ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_reciprocal_diagonal
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_coarse_shell
