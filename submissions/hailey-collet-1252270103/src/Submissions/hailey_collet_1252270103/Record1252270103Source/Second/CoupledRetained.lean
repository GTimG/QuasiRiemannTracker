/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained second-source energy with the complete tuple modifier.
Reuses pinned OpenAI/Hailey Collet finite sector and dyadic identities. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLocalization CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev BlockIndex (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (K Tsec Z ξ : ℝ) :=
  (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)) ×
    (U : Finset (CommonIndex p.val.val.1 p.val.val.2)) ×
      SourceBlocks p.val.val.1 p.val.val.2 U K (frequencyRadius Tsec Z ξ) (sourceRadius s)

def blockRows (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) : Finset O :=
  liveRows C D U R (retainedRows R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

def originalBlock (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (q : BlockIndex s modifier R seed K Tsec Z ξ) : ℂ :=
  physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)
    q.1.val.val.1 q.1.val.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ q.1.val.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ q.1.val.property).2 q.2.1
    (frequencyRadius Tsec Z ξ) (blockRows _ _ q.2.1 (frequencyRadius Tsec Z ξ))
    W K (fun i=>(q.2.2 i:ℤ))

def blockWeight (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (K Tsec Z ξ : ℝ) (q : BlockIndex s modifier R seed K Tsec Z ξ) : ℂ :=
  heightCoeff s.η s.t q.1.val.val.1*star (heightCoeff s.η s.t q.1.val.val.2)

/-- The complete coupled coefficient enters the generic second transform.
The physical block retains the original finite column pools. -/
theorem actual_retained_assembly (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed) W K Tsec Z ξ=
      ∑q : BlockIndex s modifier R seed K Tsec Z ξ,
        blockWeight s modifier R seed K Tsec Z ξ q*originalBlock s modifier R seed W K Tsec Z ξ q := by
  rw [original_live_blocks s.η s.t _ _ W K Tsec Z ξ (sourceRadius s) hK
    (fun I _ hI=>(QRH.Record1252270103Source.High.CoupledFirst.original_column_norm
      s modifier R seed I hz₁ hz₂ hI).2)]
  rw [Fintype.sum_sigma]
  conv_lhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  apply congrArg (fun x : ℂ=>heightCoeff s.η s.t p.val.val.1*
    star (heightCoeff s.η s.t p.val.val.2)*x)
  exact (physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _).symm

/-- Original complete-zero removal happens before any later row split. -/
theorem actual_retained_original_nonzero (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed) W K Tsec Z ξ=
      ∑q ∈ (Finset.univ : Finset (BlockIndex s modifier R seed K Tsec Z ξ)).filter
        (fun q=>originalBlock s modifier R seed W K Tsec Z ξ q≠0),
        blockWeight s modifier R seed K Tsec Z ξ q*originalBlock s modifier R seed W K Tsec Z ξ q := by
  rw [actual_retained_assembly s modifier R seed hz₁ hz₂ W K Tsec Z ξ hK,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with h
  · rfl
  · simp only [not_not] at h
    rw [h,mul_zero]

theorem original_block_seed_and_caps (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (q : BlockIndex s modifier R seed K Tsec Z ξ) :
    seed∣q.1.val.val.1 ∧ seed∣q.1.val.val.2 ∧
      (q.1.val.val.1.absNorm:ℝ)≤sourceRadius s ∧
      (q.1.val.val.2.absNorm:ℝ)≤sourceRadius s := by
  have h := QRH.Record1252270103Source.High.CoupledFirst.actual_common_gates
    s modifier R seed hs hz₁ hz₂ _ _ q.1.val.property
  exact ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

/-- An arbitrary row selector is retained after the original block exists;
the complete original-zero filter above is unchanged by this decomposition. -/
theorem physical_block_keep_split (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) (keep : O→Prop) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter keep) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬keep z)) W K n :=
  physicalBlock_row_split η t S β C D hC hD U R rows W K n keep

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.actual_retained_assembly
#print axioms OAI.SevenEighths.Record1252270103Second.actual_retained_original_nonzero
#print axioms OAI.SevenEighths.Record1252270103Second.original_block_seed_and_caps
