import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondRetainedAssembly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockCount

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondActiveDyadic CenteredMomentSecondBlockAggregate
open CenteredMomentSecondDyadicPartition CenteredMomentDyadicCount
open CenteredMomentSectorLocalization CenteredMomentSecondBlockCount
local notation "O" => HeckeFamily.O

def secondDyadEnvelope (C D : Ideal O) (U : Finset (CommonIndex C D))
    (K R H : ℝ) : Finset (Fin 4→ℤ) :=
  Fintype.piFinset (fun i=>indices
    (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K i)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H i))

theorem second_dyad_envelope_card (C D : Ideal O) (U : Finset (CommonIndex C D))
    (K R H : ℝ) :
    (secondDyadEnvelope C D U K R H).card=Fintype.card (SourceBlocks C D U K R H) := by
  simp only [secondDyadEnvelope,Fintype.card_piFinset,SourceBlocks,Blocks,Fintype.card_pi,
    Fintype.card_coe]

/-- Enlarging the original source cap gives a common dyad envelope. It
leaves the effective scale and retained frequency cutoff fixed. -/
theorem second_dyad_envelope_mono (C D : Ideal O) (U : Finset (CommonIndex C D))
    (K R H H' : ℝ) (hH : H≤H') :
    secondDyadEnvelope C D U K R H⊆secondDyadEnvelope C D U K R H' := by
  intro n hn
  have hn' := Fintype.mem_piFinset.mp hn
  apply Fintype.mem_piFinset.mpr
  intro i
  have hu : sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H i≤
      sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H' i := by
    fin_cases i
    · exact le_rfl
    · exact le_rfl
    · exact max_le_max_left 1 (div_le_div_of_nonneg_right hH (Nat.cast_nonneg _))
    · exact max_le_max_left 1 (div_le_div_of_nonneg_right hH (Nat.cast_nonneg _))
  by_cases hi : i=0
  · subst i
    exact hn' 0
  have hup : 1≤sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H i := by
    fin_cases i
    · exact (hi rfl).elim
    all_goals exact le_max_left _ _
  have hni := hn' i
  rw [indices,Finset.mem_Icc] at hni ⊢
  refine ⟨hni.1,hni.2.trans (Int.floor_mono ?_)⟩
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)

/-- Every actual retained block lies in the envelope at any valid larger
source cap; no independent source-label count is introduced. -/
theorem actual_second_dyad_envelope {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ H : ℝ)
    (hH : sourceRadius s≤H) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    (fun i=>(q.2.2 i:ℤ))∈secondDyadEnvelope q.1.val.val.1 q.1.val.val.2 q.2.1
      K (frequencyRadius Tsec Z ξ) H := by
  apply second_dyad_envelope_mono _ _ _ _ _ _ _ hH
  exact Fintype.mem_piFinset.mpr (fun i=>(q.2.2 i).property)

/-- The common dyad envelope is uniformly subpower, even when its
absolute position shifts with the physical radius. -/
theorem second_dyad_envelope_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃D₀ : ℝ,0<D₀ ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      ∀(C D : Ideal O),Supported C → Supported D →
      ∀(U : Finset (CommonIndex C D))(K R H : ℝ),0<K →
      R≤Cr*Z^L → H≤Z^B → (secondDyadEnvelope C D U K R H).card≤D₀*Z^ε := by
  obtain ⟨D₀,hD,hbound⟩ := sourceBlocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨D₀,hD,?_⟩
  filter_upwards [hbound] with Z hz
  intro C D hC hD U K R H hK hR hH
  rw [second_dyad_envelope_card]
  exact hz C D hC hD U K R H hK hR hH

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.second_dyad_envelope_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_dyad_envelope_mono
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_dyad_envelope
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_dyad_envelope_subpower
