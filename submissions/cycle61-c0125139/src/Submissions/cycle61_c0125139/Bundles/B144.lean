/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B095
import Submissions.cycle61_c0125139.Bundles.B110
import Submissions.cycle61_c0125139.Bundles.B113
import Submissions.cycle61_c0125139.Bundles.B123
import Submissions.cycle61_c0125139.Bundles.B143

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowShell; sha256 6ca0741eb8165fb888e87a53c9f60f3ff68586a74ca1ae0ca694e77cf4c344f0 -/
section
                                                     
                                               

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentPositiveSummability ConcreteTraceCRT Cycle61Moment
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual clipped positive daughter has a summable radial energy.
Only the source's existing compact support and a positive radial scale are used. -/
theorem actual_final_positive_summable (s : Data ι) (second : Bool)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (keep : O→ Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z : O => if keep z then
      ‖Cycle61.Physical.sourcePositiveRow s.toSource second D a z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hX (j : Fin 2) : 0< Cycle61.Physical.sourcePlainScales s.toSource second j := by
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
    (keep : O→ Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hΦ : ∀z : O, keep z → 0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (zs : Finset O) (weight : O→ℝ) (hkeep : ∀z∈zs,keep z)
    (hweight : ∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z∈zs,weight z*‖Cycle61.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤
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
    (zs : Finset O) (weight : O→ℝ) (E : ℝ) (hE : 0≤ E)
    (hrows : ∀second : Bool,
      (∑z∈zs,weight z*‖Cycle61.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤ E) :
    (∑z∈zs,weight z*retainedAllocationCost s D a z)≤
      ((4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E)/formalReductionFactor D a s.P := by
  have hprod : (∏i∈frozenIndices D a,s.M i)≤∏i,s.M i :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hfp : 0≤∏i∈frozenIndices D a,s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  let F := (2*(max 1 s.b₁*max 1 s.b₂))*(∏i∈frozenIndices D a,s.M i)^2/
    formalReductionFactor D a s.P
  have hF : 0≤ F := div_nonneg (by positivity) (s.reduction_pos D a).le
  have hexact : (∑z∈zs,weight z*retainedAllocationCost s D a z)=
      F*((∑z∈zs,weight z*‖Cycle61.Physical.sourcePositiveRow s.toSource false D a z‖^2)+
         (∑z∈zs,weight z*‖Cycle61.Physical.sourcePositiveRow s.toSource true D a z‖^2)) := by
    simp only [retainedAllocationCost,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> dsimp [F] <;> ring
  rw [hexact]
  calc
    _≤ F*(E+E) := mul_le_mul_of_nonneg_left (add_le_add (hrows false) (hrows true)) hF
    _=((4*(max 1 s.b₁*max 1 s.b₂))*(∏i∈frozenIndices D a,s.M i)^2*E)/
        formalReductionFactor D a s.P := by dsimp [F]; ring
    _≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hfp hprod 2) (by positivity)) hE) (s.reduction_pos D a).le

/-- Low energy summed over the actual residual projector shell. The constant
precedes all moving sources, rows and allocations. -/
theorem actual_second_low_shell (N : ℕ) (hι : Fintype.card ι≤ N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(zs : (D : Ideal O)→ Allocation D (Finset.univ : Finset (ι⊕Fin 2))→ Finset O)
        (weight : (D : Ideal O)→ Allocation D (Finset.univ : Finset (ι⊕Fin 2))→ O→ℝ)
        (E : ℝ),0≤ E →
      (∀D∈Ds,∀a∈s.toSource.active D,∀second : Bool,
        (∑z∈zs D a,weight D a z*‖Cycle61.Physical.sourcePositiveRow s.toSource second D a z‖^2)≤ E) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑z∈zs D a,weight D a z*retainedAllocationCost s D a z)≤
        ((4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E)*C*(2*T)^(2*ε)*Z^(s.toSource.allowance Z) := by
  obtain ⟨C,hC,hshell⟩ := paired_all_active_shell (ι:=ι) (κ:=ι) N hι hι ε hε
  refine ⟨C,hC,?_⟩
  intro s Ds hDs T Z hT hZ hlo hhi zs weight E hE hrows
  have hs := (actual_reciprocal_diagonal s Ds).trans (hshell s.toSource s.toSource Ds hDs T Z hT hZ hlo hhi)
  let Q := (4*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*E
  have hQ : 0≤ Q := by dsimp [Q]; positivity
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,Q/formalReductionFactor D a s.P :=
      Finset.sum_le_sum (fun D hD=>Finset.sum_le_sum (fun a ha=>
        actual_low_allocation_energy s D a (zs D a) (weight D a) E hE (hrows D hD a ha)))
    _=Q*(∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P) := by
      simp only [Finset.mul_sum,mul_one_div]
    _≤ Q*(C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+s.toSource.allowance Z)/2)) :=
      mul_le_mul_of_nonneg_left hs hQ
    _=_ := by rw [show (s.toSource.allowance Z+s.toSource.allowance Z)/2=s.toSource.allowance Z by ring]; ring

/-- The shell estimate with its finite-row premise discharged by the actual
low positive energies, including the original radial keep predicate. -/
theorem actual_second_low_energy_shell (N : ℕ) (hι : Fintype.card ι≤ N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(keep : O→ Prop)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),0< K →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      ∀(zs : (D : Ideal O)→ Allocation D (Finset.univ : Finset (ι⊕Fin 2))→ Finset O)
        (weight : (D : Ideal O)→ Allocation D (Finset.univ : Finset (ι⊕Fin 2))→ O→ℝ)
        (E : ℝ),0≤ E →
      (∀D∈Ds,∀a∈s.toSource.active D,∀z∈zs D a,keep z) →
      (∀D∈Ds,∀a∈s.toSource.active D,∀z∈zs D a,weight D a z≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀D∈Ds,∀a∈s.toSource.active D,∀second : Bool,finalPositiveEnergy s second D a keep Φ K≤ E) →
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_final_positive_summable
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finite_final_positive
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_allocation_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_low_shell
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_low_energy_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowCommon; sha256 6d303a729a5312b0b479aa854ec814c923ff07a9500df584d7a94be7d9806480 -/
section
                                                  
                                           

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
open Cycle61Moment Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Common allocations are summed after each entire finite row sum has
been estimated. In particular, the chosen allocation does not vary with the row. -/
theorem actual_common_low_cost_from_shell (s : Input ι) (C R : Ideal O)
    (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O→ℝ) (E : ℝ)
    (hshell : ∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
      (∑D∈Ds,∑a∈(commonData s C R B).toSource.active D,∑z∈zs,
        weight z*retainedAllocationCost (commonData s C R B) D a z)≤ E) :
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
    ∃K : ℝ,0< K ∧ ∀(s : Input ι),s.upper≤ b → ∀C R : Ideal O,C≠0 →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1≤ T → 1< Z → 0≤ E →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀(keep : O→ Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0< rad →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,keep z) → (∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z≤ pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad≤ E) →
      (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost s C R D z)≤
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*(2*T)^(2*ε)*Z^pad := by
  choose K hK hbound using fun J : Finset ι=>actual_second_low_energy_shell
    (ι:=↥J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  let Kall := 1+∑J : Finset ι,K J
  have hKall : 0< Kall := by
    dsimp [Kall]
    have hh : 0≤∑J : Finset ι,K J := Finset.sum_nonneg (fun J _=>(hK J).le)
    linarith
  have hKle (J : Finset ι) : K J≤ Kall := by
    have hh := Finset.single_le_sum (fun J (_ : J∈Finset.univ)=>(hK J).le) (Finset.mem_univ J)
    dsimp [Kall]; linarith
  obtain ⟨Km,hKm,hmass⟩ := uniform_common_scalar_mass (Fintype.card ι) b ε hε
  refine ⟨2*Kall*Km,by positivity,?_⟩
  intro s hb C R hC Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ hkeep hw hallow henergy
  let Q := 2*s.toData.profileFactor*E*Kall*(2*T)^(2*ε)*Z^pad
  have hQ : 0≤ Q := by dsimp [Q]; have hp:=s.toData.profile_nonneg; positivity
  have hshell (B : actualAllocations s.pools C)(hn : commonScalar s C R B≠0) :
      (∑D∈Ds,∑a∈(commonData s C R B).toSource.active D,∑z∈zs,
        weight z*retainedAllocationCost (commonData s C R B) D a z)≤ Q := by
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_low_cost_from_shell
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_low_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowCommon -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfileCommon; sha256 f8d38d29e1cd7d3d2935a4ed813f6ee449a24226cb3e98ef686e43a8882e0584 -/
section
                                                     
                                     
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The genuine low analytic bound through both allocation layers.
Each common allocation stays fixed across the complete frequency sum. -/
theorem actual_live_main_low_profile_common
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤ pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0≤ Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1≤ Z^L) →
    let hQM' : st.fixedModulus≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z)≤
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(2*εshell)*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad := by
  obtain ⟨degree,Sp,hprofiles⟩ := actual_live_main_low_profiles (α:=α) M H hH W A B a b Bmask L lo hi Mcap εold
    hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin
  choose Ks hKs hcommon using fun J : Finset α=>actual_common_low_energy (ι:=↥J) bs εshell heshell
  let Kall := 1+∑J : Finset α,Ks J
  have hKall : 0< Kall := by
    dsimp [Kall]
    have hh : 0≤∑J : Finset α,Ks J := Finset.sum_nonneg (fun J _=>(hKs J).le)
    linarith
  have hKle (J : Finset α) : Ks J≤ Kall := by
    have hh := Finset.single_le_sum (fun J (_ : J∈Finset.univ)=>(hKs J).le) (Finset.mem_univ J)
    dsimp [Kall]; linarith
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hprofiles η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kall*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
    hQM' hQη low zs weight hkeep hweight
  let exponent : ℝ := nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
    (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh
  let E := C*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*Z^exponent
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hE : 0≤ E := by dsimp [E]; positivity
  have henergy (B₂ : actualAllocations src.pools q.E₂)(hn : commonScalar src q.E₂ q.R₂ B₂≠0)
      (D : Ideal O)(hD : D∈Ds)
      (alloc : Allocation D (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
      (halloc : alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D)(second : Bool) :
      finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
        (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤ E := by
    let q' : Chain s := { q with B₂:=B₂ }
    have hB₂ : frozenCoefficient B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0 :=
      right_ne_zero_of_mul hn
    let g' : LiveMainGeometry s q' Z Mrow amp omega ξ bs (Fintype.card α) :=
      { reflected:=g.reflected, C₀:=g.C₀, D₀:=g.D₀, hC₀:=g.hC₀, hD₀:=g.hD₀,
        heq₀:=g.heq₀, selected:=g.selected, E₀:=g.E₀, hmod:=g.hmod,
        δ:=g.δ, reserve:=g.reserve, homega:=g.homega, datum:=g.datum,
        parent:=g.parent, row:=g.row, radius_eq:=g.radius_eq, label:=g.label,
        first_nonzero:=g.first_nonzero, second_nonzero:=hB₂ }
    exact hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q' g' χ hP hPN second D alloc p₀ hp₁ hp₂
      (hcaps B₂ hn D hD alloc halloc second).1 (hcaps B₂ hn D hD alloc halloc second).2
  have hC₂ : q.E₂≠0 := CenteredMomentAllocatedNaturalRadial.common_nonzero q.first q.E₂ q.B₂
  have hh := hcommon (liveIndices q.B₁.val) src hsupper q.E₂ q.R₂ hC₂ Ds zs weight
    T Z pad E hT hZone hE hDs (fun z=>st.radial.keep z ∧ low z)
    st.radial.profile st.radial.scale st.radial.scale_pos (fun z _=>st.radial.nonneg z)
    hkeep hweight hallow henergy
  apply hh.trans
  have hp:=src.toData.profile_nonneg
  have hn:=CenteredMomentFirstScale.norm_pos q.E₂ hC₂
  calc
    _≤ Kall*src.toData.profileFactor*(∏j,src.M j)^2*E*(q.E₂.absNorm:ℝ)^(εshell-1)*
        (2*T)^(2*εshell)*Z^pad := by
      gcongr
      exact hKle _
    _=_ := by dsimp [E,exponent]; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_live_main_low_profile_common

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfileCommon -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfileColumn; sha256 8540b9d497471040aab355c9a008982aa131bddbef14d11426643460d8b012fd -/
section
                                                          
                                                    
                                     
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)


open CenteredMomentCommonPairedSource
/-- The actual low analytic estimate for normalized columns, after both
common and residual allocations, with the original radial row majorant. -/
theorem actual_live_main_low_profile_column
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤ pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0≤ Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1≤ Z^L) →
    let hQM' : st.fixedModulus≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤ weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad := by
  obtain ⟨degree,Sp,hcommon⟩ := actual_live_main_low_profile_common (α:=α) M H hH W A B a b Bmask L lo hi Mcap εold
    hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  obtain ⟨K,hK,hpoint⟩ := actual_uniform_second_column_extraction (α:=α) εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hcommon η₀ Q hQM hQ0 hQt hQ72
  refine ⟨K*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
    hQM' hQη low zs weight hnonneg hkeep hweight
  have hh := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps zs weight hkeep hweight
  have hT0 : 0<2*T := by linarith
  have hmajor : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      K*(2*T)^εshell*(∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro z hz
    have hp:=mul_le_mul_of_nonneg_left
      (hpoint (liveIndices q.B₁.val) src q.E₂ hE₂ q.R₂ seed D hseed (hDs D hD).1 z) (hnonneg z hz)
    apply hp.trans
    have hd:=Real.rpow_le_rpow (Nat.cast_nonneg D.absNorm) (hDs D hD).2.2.le heshell.le
    have hc:=common_retained_cost_nonneg src q.E₂ q.R₂ D z
    have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK.le)
      (mul_nonneg (hnonneg z hz) hc)
    convert hbnd using 1 <;> ring
  apply hmajor.trans
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤ K*(2*T)^εshell)).trans_eq
  rw [show 3*εshell=εshell+2*εshell by ring,Real.rpow_add hT0 εshell (2*εshell)]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_live_main_low_profile_column

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfileColumn -/
