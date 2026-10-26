import Candidate.Cycle63.Physical.InitialMass.SecondCoarseShell
import Candidate.Cycle63.Moment.LowBranch.FinalDictionary
import Candidate.Cycle63.Moment.JointAllocationEnergy

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondLowShell. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentPositiveSummability ConcreteTraceCRT Cycle63Moment
open Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
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
  apply Finset.sum_le_sum
  intro z hz
  rw [if_pos (hkeep z hz),mul_comm (weight z)]
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
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_final_positive_summable
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_finite_final_positive
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_low_allocation_energy
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_low_shell
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_low_energy_shell
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondLowCommon. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
open Cycle63Moment Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Common allocations are summed after each entire finite row sum has
been estimated. In particular, the chosen allocation does not vary with the row. -/
theorem actual_common_low_cost_from_shell (s : Input ι) (C R : Ideal O)
    (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O→ℝ) (E : ℝ)
    (hshell : ∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
      (∑D∈Ds,∑a∈(commonData s C R B).toSource.active D,∑z∈zs,
        weight z*retainedAllocationCost (commonData s C R B) D a z)≤E) :
    (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost s C R D z)≤
      (((actualAllocations s.pools C).card:ℝ)*
        ∑B : actualAllocations s.pools C,‖commonScalar s C R B‖^2)*E := by
  have he : (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost s C R D z)=
      ((actualAllocations s.pools C).card:ℝ)*
        ∑B : actualAllocations s.pools C,‖commonScalar s C R B‖^2*
          (∑D∈Ds,∑a∈(commonData s C R B).toSource.active D,∑z∈zs,
            weight z*retainedAllocationCost (commonData s C R B) D a z) := by
    simp only [commonRetainedCost,Finset.mul_sum]
    rw [Finset.sum_comm (s:=Finset.univ) (t:=Ds)]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [he,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro B hB
  by_cases hn : commonScalar s C R B=0
  · simp [hn]
  · exact mul_le_mul_of_nonneg_left (hshell B hn) (sq_nonneg _)

/-- Actual low positive energies pay the residual and common allocations.
The finite menu of surviving slot sets is fixed before the source; no row
cardinality or row-dependent allocation selection is introduced. -/
theorem actual_common_low_energy (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(s : Input ι),s.upper≤b → ∀C R : Ideal O,C≠0 →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1≤T → 1<Z → 0≤E →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0<rad →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,keep z) → (∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z≤pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad≤E) →
      (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost s C R D z)≤
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*(2*T)^(2*ε)*Z^pad := by
  choose K hK hbound using fun J : Finset ι=>actual_second_low_energy_shell
    (ι:=↥J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  let Kall := 1+∑J : Finset ι,K J
  have hKall : 0<Kall := by
    dsimp [Kall]
    have hh : 0≤∑J : Finset ι,K J := Finset.sum_nonneg (fun J _=>(hK J).le)
    linarith
  have hKle (J : Finset ι) : K J≤Kall := by
    have hh := Finset.single_le_sum (fun J (_ : J∈Finset.univ)=>(hK J).le) (Finset.mem_univ J)
    dsimp [Kall]; linarith
  obtain ⟨Km,hKm,hmass⟩ := uniform_common_scalar_mass (Fintype.card ι) b ε hε
  refine ⟨2*Kall*Km,by positivity,?_⟩
  intro s hb C R hC Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ hkeep hw hallow henergy
  let Q := 2*s.toData.profileFactor*E*Kall*(2*T)^(2*ε)*Z^pad
  have hQ : 0≤Q := by dsimp [Q]; have hp:=s.toData.profile_nonneg; positivity
  have hshell (B : actualAllocations s.pools C)(hn : commonScalar s C R B≠0) :
      (∑D∈Ds,∑a∈(commonData s C R B).toSource.active D,∑z∈zs,
        weight z*retainedAllocationCost (commonData s C R B) D a z)≤Q := by
    have hh := hbound (liveIndices B.val) (commonData s C R B) Ds
      (fun D hD=>(hDs D hD).1) T Z hT hZ
      (fun D hD=>(hDs D hD).2.1) (fun D hD=>(hDs D hD).2.2)
      keep Φ rad hrad hΦ (fun _ _=>zs) (fun _ _=>weight) E hE
      (fun _ _ _ _=>hkeep) (fun _ _ _ _=>hw) (henergy B hn)
    have hp := common_profile_le s C R B
    have hp0 := (commonData s C R B).profile_nonneg
    have heq : (4*(max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂))*
        (∏i,(commonData s C R B).M i)^2*E = 2*(commonData s C R B).profileFactor*E := by
      unfold Data.profileFactor; ring
    rw [heq] at hh
    apply hh.trans
    dsimp [Q]
    have hpall := s.toData.profile_nonneg
    have hk0 := (hK (liveIndices B.val)).le
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hE)
        (hKle _) hk0 (by positivity)
    · exact Real.rpow_le_rpow_of_exponent_le hZ.le (hallow B hn)
    · exact Real.rpow_nonneg (by linarith) _
    · positivity
  have hs := actual_common_low_cost_from_shell s C R Ds zs weight Q hshell
  have hm := hmass (ι:=ι) le_rfl s hb C R hC
  apply hs.trans
  apply (mul_le_mul_of_nonneg_right hm hQ).trans_eq
  dsimp [Q]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_common_low_cost_from_shell
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_common_low_energy
end
