import Candidate.Cycle63.Physical.InitialMass.FirstLowLabelCount
import Candidate.Cycle63.Physical.InitialMass.LowOneSidedHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorBoundary

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentDivisorBoundary Cycle63Moment
local notation "O" => HeckeFamily.O

/-- One-sided reciprocal mass of actual equal-support labels, including their inactive
subsets. The seed saving is retained for the first-projector shell. -/
theorem actual_low_label_reciprocal_mass (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀second : Bool, ∀Z : ℝ,2≤Z → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∑l∈labels,1/((if second then l.1.2 else l.1.1).absNorm:ℝ))≤C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := LowOneSided.one_sided_harmonic_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro second Z hZ seed hs hs0 labels hsup heq hseed hnorm
  have hh := hbound second Z hZ seed hs hs0 (labels.image firstPartitionCode) ?_ ?_
  · rw [Finset.sum_image] at hh
    · exact hh
    · exact first_partition_code_injective.injOn
  · intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨(hsup l hl).1.1,(hsup l hl).2.1,heq l hl,(hseed l hl).1,(hseed l hl).2,?_⟩
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [commonRadical_support]
    exact Q.property
  · intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    exact hnorm l hl

/-- The one-sided seed saving pays the entire first-projector dyad. No
condition that this projector divides an encoded row is used here. -/
theorem actual_low_reciprocal_projector_shell (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀second : Bool, ∀Z T : ℝ,2≤Z → 1≤T → ∀Ds : Finset (Ideal O),
      (∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀labels : Ideal O→Finset FirstSourceLabel,
      (∀D∈Ds,∀l∈labels D,Supported l.1.1 ∧ Supported l.1.2) →
      (∀D∈Ds,∀l∈labels D,primeSupport l.1.1=primeSupport l.1.2) →
      (∀D∈Ds,∀l∈labels D,D∣l.1.1 ∧ D∣l.1.2) →
      (∀D∈Ds,∀l∈labels D,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∑D∈Ds,∑l∈labels D,1/((if second then l.1.2 else l.1.1).absNorm:ℝ))≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := actual_low_label_reciprocal_mass B ε hB hε
  refine ⟨256*C,by positivity,?_⟩
  intro second Z T hZ hT Ds hDs hdyad labels hsup heq hseed hnorm
  have hT0 : 0<T := zero_lt_one.trans_le hT
  have hcard := divisor_dyad_card Ds T hT (fun D hD=>(hDs D hD).ne_zero)
    (fun D hD=>(hdyad D hD).2)
  calc
    _≤∑_D∈Ds,C*Z^ε/T := by
      refine Finset.sum_le_sum fun D hD => ?_
      exact (hbound second Z hZ D (hDs D hD) (hDs D hD).ne_zero (labels D)
        (hsup D hD) (heq D hD) (hseed D hD) (hnorm D hD)).trans
        (div_le_div_of_nonneg_left (by positivity) hT0 (hdyad D hD).1)
    _=(Ds.card:ℝ)*(C*Z^ε/T) := by simp
    _≤(256*T)*(C*Z^ε/T) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _=(256*C)*Z^ε := by field_simp

end
end OAI.SevenEighths.Cycle63InitialMass
