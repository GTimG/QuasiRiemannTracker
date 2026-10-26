import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRetainedAssembly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61Moment RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentOriginalChildEnergy
open CenteredMomentSourceRow CenteredMomentSecondSectorColumns
open CenteredMomentSourceLiveColumn
open CenteredMomentChildAssembly CenteredMomentSecondScaled
local notation "O" => HeckeFamily.O
local instance secondLiveAllocationSumDecidable {ι : Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- A nonzero full physical block has a nonzero original coefficient on
both sides of its actual sector expansion. No ordinary-row restriction is used. -/
theorem actual_second_nonzero_coefficients (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (hne : s.value W≠0) :
    (∃I : s.LeftIndex,s.beta (s.C*I.val)≠0) ∧
      (∃J : s.RightIndex,s.beta (s.D*J.val)≠0) := by
  rw [SecondBlockSource.value,actual_second_physical_block_expression] at hne
  have hs := right_ne_zero_of_mul hne
  obtain ⟨L,hL,hLne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨χ,hχ,hχne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLne
  obtain ⟨ψ,hψ,hψne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hχne
  obtain ⟨z,hz,hzne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hψne
  unfold secondSectorTerm at hzne
  have hi := right_ne_zero_of_mul hzne
  obtain ⟨I,hI,hIne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  obtain ⟨J,hJ,hIJne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hIne
  constructor
  · refine ⟨I,?_⟩
    intro hzero
    apply hIJne
    simp only [CanonicalSectorSource.leftCoefficient,SecondBlockSource.sector,
      divisorCoefficient,movingCoefficient,hzero,zero_mul,ite_self]
  · refine ⟨J,?_⟩
    intro hzero
    apply hIJne
    simp only [CanonicalSectorSource.rightCoefficient,SecondBlockSource.sector,
      divisorCoefficient,movingCoefficient,hzero,zero_mul,ite_self,star_zero,mul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original punctured source-coefficient identity forces a live
common allocation. The allocation does not depend on a Fourier row. -/
theorem actual_second_coefficient_live_allocation (s : Input ι) (R seed C : Ideal O)
    (hC : Supported C) (hseed : seed∣C)
    (I : sectorPool C hC.1 (finiteColumns (Fintype.piFinset s.pools)))
    (hne : coefficient s R seed (C*I.val)≠0) :
    ∃B : actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 := by
  have hc := original_source_punctured_column s.pools s.pools_ne
    (fun i J hJ=>s.prime i J hJ) C R seed I.val hC.1
    (sectorPool_supported C hC.1 _ I).1 hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  have hcop := (Finset.mem_filter.mp I.property).2
  rw [ite_eq_left hcop] at hc
  change coefficient s R seed (C*I.val)=_ at hc
  rw [hc] at hne
  obtain ⟨B,hB,hBne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨B,left_ne_zero_of_mul hBne⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Either selected common ideal of the literal original input admits a
nonzero frozen coefficient when its full physical block is nonzero. -/
theorem actual_second_input_live_allocation (d : SecondInputDatum α) (second : Bool)
    (hseed : d.seed∣(if second then d.D else d.C)) (W : 𝓢(ℝ,ℂ))
    (hne : d.block.value W≠0) :
    ∃B : actualAllocations d.input.pools (if second then d.D else d.C),
      frozenCoefficient B.val (if second then d.D else d.C)
        d.R d.input.ν d.input.W d.input.P≠0 := by
  have hc := actual_second_nonzero_coefficients d.block W hne
  cases second with
  | false =>
    obtain ⟨I,hI⟩ := hc.1
    exact actual_second_coefficient_live_allocation d.input d.R d.seed d.C d.hC hseed I hI
  | true =>
    obtain ⟨J,hJ⟩ := hc.2
    exact actual_second_coefficient_live_allocation d.input d.R d.seed d.D d.hD hseed J hJ

/-- Concrete live second allocation for the actual retained block datum.
It is chosen once from the full original block, before the full row-column sum. -/
theorem actual_second_block_live_allocation (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (second : Bool) (W : 𝓢(ℝ,ℂ))
    (hne : (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0) :
    let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    ∃B : actualAllocations s.pools (if second then d.D else d.C),
      frozenCoefficient B.val (if second then d.D else d.C) R s.ν s.W s.P≠0 := by
  let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  have hg := actual_retained_block_gates slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  have hs : d.seed∣(if second then d.D else d.C) := by
    cases second
    · exact hg.1
    · exact hg.2.1
  exact actual_second_input_live_allocation d second hs W hne

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_nonzero_coefficients
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_coefficient_live_allocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_input_live_allocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_live_allocation
