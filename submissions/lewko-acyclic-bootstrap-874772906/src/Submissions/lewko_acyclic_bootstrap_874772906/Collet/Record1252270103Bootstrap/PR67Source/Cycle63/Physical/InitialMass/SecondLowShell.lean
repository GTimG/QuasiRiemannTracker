import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FinalDictionary
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentPositiveSummability ConcreteTraceCRT Cycle63Moment
open Cycle63Moment.LowBranch
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual clipped positive daughter has a summable radial energy.
Only the source's existing compact support and a positive radial scale are used. -/
theorem actual_final_positive_summable (s : Data ι) (second : Bool)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => if keep z then
      ‖Cycle63.Physical.sourcePositiveRow s.toSource second D a z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hX (j : Fin 2) : 0<Cycle63.Physical.sourcePlainScales s.toSource second j := by
    cases second <;> fin_cases j
    · exact s.X₁_pos
    · exact s.X₂_pos
    · exact s.Y₁_pos
    · exact s.Y₂_pos
  exact allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂
    _ _ s.support₁ s.support₂ (hX 0) (hX 1) s.slots s.coefficient s.P D a keep Φ K hK

/-- A finite weighted row sum is paid by the literal final positive energy.
The keep predicate and radial profile remain the ones used by the low estimate. -/
theorem actual_finite_final_positive (s : Data ι) (second : Bool)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O, keep z → 0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (zs : Finset O) (weight : O→ℝ) (hkeep : ∀z∈zs,keep z)
    (hweight : ∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z∈zs,weight z*‖Cycle63.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤
      finalPositiveEnergy s second D a keep Φ K := by
  have hs := actual_final_positive_summable s second D a keep Φ K hK
  apply le_trans _ (hs.sum_le_tsum zs (fun z _ => by
    split_ifs with hz
    · exact mul_nonneg (sq_nonneg _) (hΦ z hz)
    · exact le_rfl))
  refine Finset.sum_le_sum fun z hz => ?_
  rw [ite_eq_left (hkeep z hz),mul_comm (weight z)]
  exact mul_le_mul_of_nonneg_left (hweight z hz) (sq_nonneg _)

/-- Integrate the two positive rectangles before summing residual allocations. -/
theorem actual_low_allocation_energy (s : Data ι)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (zs : Finset O) (weight : O→ℝ) (E : ℝ) (hE : 0≤E)
    (hrows : ∀second : Bool,
      (∑z∈zs,weight z*‖Cycle63.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤E) :
    (∑z∈zs,weight z*retainedAllocationCost s D a z)≤
      ((4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E)/formalReductionFactor D a s.P := by
  have hprod : (∏i∈frozenIndices D a,s.M i)≤∏i,s.M i :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hfp : 0≤∏i∈frozenIndices D a,s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  let F := (2*(max 1 s.b₁*max 1 s.b₂))*(∏i∈frozenIndices D a,s.M i)^2/
    formalReductionFactor D a s.P
  have hF : 0≤F := div_nonneg (by positivity) (s.reduction_pos D a).le
  have hexact : (∑z∈zs,weight z*retainedAllocationCost s D a z)=
      F*((∑z∈zs,weight z*‖Cycle63.Physical.sourcePositiveRow s.toSource false D a z‖^2)+
         (∑z∈zs,weight z*‖Cycle63.Physical.sourcePositiveRow s.toSource true D a z‖^2)) := by
    simp only [retainedAllocationCost,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> dsimp [F] <;> ring
  rw [hexact]
  calc
    _≤F*(E+E) := mul_le_mul_of_nonneg_left (add_le_add (hrows false) (hrows true)) hF
    _=((4*(max 1 s.b₁*max 1 s.b₂))*(∏i∈frozenIndices D a,s.M i)^2*E)/
        formalReductionFactor D a s.P := by dsimp [F]; ring
    _≤_ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hfp hprod 2) (by positivity)) hE) (s.reduction_pos D a).le

/-- Low energy summed over the actual residual projector shell. The constant
precedes all moving sources, rows and allocations. -/
theorem actual_second_low_shell (N : ℕ) (hι : Fintype.card ι≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(zs : (D : Ideal O)→Allocation D (Finset.univ : Finset (ι⊕Fin 2))→Finset O)
        (weight : (D : Ideal O)→Allocation D (Finset.univ : Finset (ι⊕Fin 2))→O→ℝ)
        (E : ℝ),0≤E →
      (∀D∈Ds,∀a∈s.toSource.active D,∀second : Bool,
        (∑z∈zs D a,weight D a z*‖Cycle63.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤E) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑z∈zs D a,weight D a z*retainedAllocationCost s D a z)≤
        ((4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E)*C*(2*T)^(2*ε)*Z^(s.toSource.allowance Z) := by
  obtain ⟨C,hC,hshell⟩ := paired_all_active_shell (ι:=ι) (κ:=ι) N hι hι ε hε
  refine ⟨C,hC,?_⟩
  intro s Ds hDs T Z hT hZ hlo hhi zs weight E hE hrows
  have hs := (actual_reciprocal_diagonal s Ds).trans (hshell s.toSource s.toSource Ds hDs T Z hT hZ hlo hhi)
  let Q := (4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E
  have hQ : 0≤Q := by dsimp [Q]; positivity
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,Q/formalReductionFactor D a s.P :=
      Finset.sum_le_sum (fun D hD=>Finset.sum_le_sum (fun a ha=>
        actual_low_allocation_energy s D a (zs D a) (weight D a) E hE (hrows D hD a ha)))
    _=Q*(∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P) := by
      simp only [Finset.mul_sum,mul_one_div]
    _≤Q*(C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+s.toSource.allowance Z)/2)) :=
      mul_le_mul_of_nonneg_left hs hQ
    _=_ := by rw [show (s.toSource.allowance Z+s.toSource.allowance Z)/2=s.toSource.allowance Z by ring]; ring

/-- The shell estimate with its finite-row premise discharged by the actual
low positive energies, including the original radial keep predicate. -/
theorem actual_second_low_energy_shell (N : ℕ) (hι : Fintype.card ι≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),0<K →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      ∀(zs : (D : Ideal O)→Allocation D (Finset.univ : Finset (ι⊕Fin 2))→Finset O)
        (weight : (D : Ideal O)→Allocation D (Finset.univ : Finset (ι⊕Fin 2))→O→ℝ)
        (E : ℝ),0≤E →
      (∀D∈Ds,∀a∈s.toSource.active D,∀z∈zs D a,keep z) →
      (∀D∈Ds,∀a∈s.toSource.active D,∀z∈zs D a,weight D a z≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀D∈Ds,∀a∈s.toSource.active D,∀second : Bool,finalPositiveEnergy s second D a keep Φ K≤E) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑z∈zs D a,weight D a z*retainedAllocationCost s D a z)≤
        ((4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E)*C*(2*T)^(2*ε)*Z^(s.toSource.allowance Z) := by
  obtain ⟨C,hC,hbound⟩ := actual_second_low_shell (ι:=ι) N hι ε hε
  refine ⟨C,hC,?_⟩
  intro s Ds hDs T Z hT hZ hlo hhi keep Φ K hK hΦ zs weight E hE hkeep hw henergy
  apply hbound s Ds hDs T Z hT hZ hlo hhi zs weight E hE
  intro D hD a ha second
  exact (actual_finite_final_positive s second D a keep Φ K hK hΦ (zs D a) (weight D a)
    (hkeep D hD a ha) (hw D hD a ha)).trans (henergy D hD a ha second)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
