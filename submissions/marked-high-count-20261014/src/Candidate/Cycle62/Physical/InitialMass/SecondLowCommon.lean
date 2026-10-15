import Candidate.Cycle62.Physical.InitialMass.SecondLowShell
import Candidate.Cycle62.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
open Cycle62Moment Cycle62Moment.LowBranch
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
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_common_low_cost_from_shell
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_common_low_energy
