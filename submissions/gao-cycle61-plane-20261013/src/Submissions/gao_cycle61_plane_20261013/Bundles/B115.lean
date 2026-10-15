/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B110
import Submissions.gao_cycle61_plane_20261013.Bundles.B114
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondActualSources; sha256 21a82169309d7ae9468c55567077d9214ba753ffab3eade8fde5792628119523 -/
section
                                                  
                                                         
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentCanonicalFirst
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondActiveCount
local notation "O" => HeckeFamily.O
local instance secondActualSourcesDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev ActualSecondPair {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O) :=
  ↥(commonLabels
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))))

/-- A second input is constructed from actual active common labels. Its
character family is supplied by the proved finite-character construction. -/
def actualSecondInputDatum (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ActualSecondPair s R seed) (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (dyad : Fin 4→ℤ) : SecondInputDatum α :=
  let hp := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))
      _ _ p.property
  let hg := actual_common_gates s R seed hseed hz₁ hz₂ _ _ p.property
  let hf := exists_row_budgeted_second_family s.η _ _ hp.1 hp.2 hg.2.2.1 U
  {slots:=slots,input:=s,R:=R,seed:=seed,C:=p.val.1,D:=p.val.2,
    hC:=hp.1,hD:=hp.2,sameSupport:=hg.2.2.1,inactive:=U,
    radius:=radius,rows:=rows,rows_ne:=hrows,K:=K,K_pos:=hK,dyad:=dyad,
    τ:=Classical.choose hf,family:=(Classical.choose_spec hf).1,
    rowBudget:=(Classical.choose_spec hf).2}

/-- The first projector divides both actual second common ideals; these
hypotheses no longer have to be supplied at the encoding boundary. -/
theorem actual_second_input_seed (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ActualSecondPair s R seed) (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (dyad : Fin 4→ℤ) :
    let d := actualSecondInputDatum slots s R seed hseed hz₁ hz₂ p U radius rows hrows K hK dyad
    d.seed∣d.C ∧ d.seed∣d.D := by
  have h := actual_common_gates s R seed hseed hz₁ hz₂ _ _ p.property
  exact ⟨h.2.2.2.1,h.2.2.2.2.1⟩

theorem actual_second_input_common_norm (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ActualSecondPair s R seed) (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0< K) (dyad : Fin 4→ℤ) :
    let d := actualSecondInputDatum slots s R seed hseed hz₁ hz₂ p U radius rows hrows K hK dyad
    (d.C.absNorm:ℝ)≤ sourceRadius s ∧ (d.D.absNorm:ℝ)≤ sourceRadius s := by
  exact (actual_common_gates s R seed hseed hz₁ hz₂ _ _ p.property).2.2.2.2.2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_input_seed
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_input_common_norm

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondActualSources -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRetainedAssembly; sha256 d51ca3da563852614a87ffdef529af6c3c733efb2146ab3e96f5e64d6a831ff5 -/
section
                                                       
                                                            

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance secondRetainedAssemblyDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev ActualSecondBlockIndex {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ) :=
  (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)) ×
    (U : Finset (CommonIndex p.val.val.1 p.val.val.2)) ×
      SourceBlocks p.val.val.1 p.val.val.2 U K (frequencyRadius Tsec Z ξ) (sourceRadius s)

variable {α : Type*} [Fintype α] [DecidableEq α]

def actualSecondBlockDatum (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    SecondInputDatum α :=
  actualSecondInputDatum slots s R seed hseed hz₁ hz₂ q.1.val q.2.1
    (frequencyRadius Tsec Z ξ)
    (sourceRows q.1.val.val.1 q.1.val.val.2 q.2.1 (frequencyRadius Tsec Z ξ))
    (sourceRows_nonzero _ _ _ _) K hK (fun i=>(q.2.2 i:ℤ))

def actualSecondBlockWeight {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : ℂ :=
  heightCoeff s.η s.t q.1.val.val.1*star (heightCoeff s.η s.t q.1.val.val.2)

/-- Exact retained-energy expansion into the original-input blocks. The
source cap follows from the actual coefficients, and active-pool removal
preserves the polynomial used by the allocation extraction. -/
theorem actual_original_retained_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ=
      ∑q : ActualSecondBlockIndex s R seed K Tsec Z ξ,
        actualSecondBlockWeight s R seed K Tsec Z ξ q*
          (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W := by
  rw [original_live_blocks s.η s.t _ _ W K Tsec Z ξ (sourceRadius s) hK
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)]
  rw [Fintype.sum_sigma]
  conv_lhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [actualSecondBlockWeight,actualSecondBlockDatum,actualSecondInputDatum,
    SecondInputDatum.block,originalSecondBlock,SecondBlockSource.value]
  apply congrArg (fun x : ℂ=>heightCoeff s.η s.t p.val.val.1*
    star (heightCoeff s.η s.t p.val.val.2)*x)
  exact (physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _).symm

/-- Heterogeneous original sources retain a single joint block sum. The
outer weights may include the first allocation and amplification scalars. -/
theorem actual_joint_retained_assembly {Label : Type*} [Fintype Label]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0< K l)
    (weight : Label→ℂ) :
    (∑l,weight l*secondRetainedEnergy (s l).η (s l).t
      (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ)=
      ∑q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
        (weight q.1*actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)*
          (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
            (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2).block.value W := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_original_retained_assembly (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) W (K l) (Tsec l) Z ξ (hK l),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (mul_assoc _ _ _).symm

/-- Seed and source-size gates for every block in the actual expansion. -/
theorem actual_retained_block_gates (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    d.seed∣d.C ∧ d.seed∣d.D ∧
      (d.C.absNorm:ℝ)≤ sourceRadius s ∧ (d.D.absNorm:ℝ)≤ sourceRadius s := by
  have h := actual_common_gates s R seed hseed hz₁ hz₂ _ _ q.1.val.property
  exact ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_retained_assembly

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_retained_assembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_retained_block_gates

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRetainedAssembly -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondDyadEnvelope; sha256 a881e318ad6e5089ef55652c64e34beec4c122ac8bb4a96b3358e7658b2b60e9 -/
section
                                                          
                                                           

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
    (K R H H' : ℝ) (hH : H≤ H') :
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
  have hup : 1≤ sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H i := by
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
    (hH : sourceRadius s≤ H) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    (fun i=>(q.2.2 i:ℤ))∈secondDyadEnvelope q.1.val.val.1 q.1.val.val.2 q.2.1
      K (frequencyRadius Tsec Z ξ) H := by
  apply second_dyad_envelope_mono _ _ _ _ _ _ _ hH
  exact Fintype.mem_piFinset.mpr (fun i=>(q.2.2 i).property)

/-- The common dyad envelope is uniformly subpower, even when its
absolute position shifts with the physical radius. -/
theorem second_dyad_envelope_subpower (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃D₀ : ℝ,0< D₀ ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      ∀(C D : Ideal O),Supported C → Supported D →
      ∀(U : Finset (CommonIndex C D))(K R H : ℝ),0< K →
      R≤ Cr*Z^L → H≤ Z^B → (secondDyadEnvelope C D U K R H).card≤ D₀*Z^ε := by
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondDyadEnvelope -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRowFibres; sha256 263d95ca1d6e9bba436c96c49822a87eb47b9a71e2fa46cd93123832eb197764 -/
section
                                                          
                                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCommonRadialData IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

abbrev SecondBlockCode := (p : Ideal O × Ideal O) ×
  Finset (CommonIndex p.1 p.2) × (Fin 4→ℤ)

def secondBlockCode (s : SecondBlockSource) : SecondBlockCode :=
  ⟨(s.C,s.D),s.inactive,s.dyad⟩

/-- Once the source's remaining auxiliary labels are fixed, the joint
encoding loses only the two finite ray labels and the dyadic block. -/
theorem actual_second_row_key_injective {Label Aux : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel) (aux : Label→ Aux)
    (hlabel : Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l)))) :
    Function.Injective (fun r : secondLiveRows s=>
      (secondEncodedRow s first r,aux r.val.1,(s r.val.1).dyad,r.val.2.1,r.val.2.2.1)) := by
  intro r t h
  have hj := congrArg Prod.fst h
  have ha := congrArg (fun x=>x.2.1) h
  have hn := congrArg (fun x=>x.2.2.1) h
  have hχ := congrArg (fun x=>x.2.2.2.1) h
  have hψ := congrArg (fun x=>x.2.2.2.2) h
  dsimp only at hj ha hn hχ hψ
  have hf : first r.val.1=first t.val.1 := congrArg Sigma.fst hj
  have hc : secondBlockCode (s r.val.1)=secondBlockCode (s t.val.1) := by
    have he := congrArg (fun x : JointSourceLabel=>
      (⟨x.2.1,x.2.2.val.1,(s r.val.1).dyad⟩ : SecondBlockCode)) hj
    exact he.trans (by dsimp only [secondBlockCode,secondEncodedRow]; rw [hn])
  have hl : r.val.1=t.val.1 := hlabel (Prod.ext hf (Prod.ext ha hc))
  have hz := congrArg (fun x : JointSourceLabel=>x.2.2.val.2) hj
  apply Subtype.ext
  rcases r with ⟨⟨l,χ,ψ,z⟩,hr⟩
  rcases t with ⟨⟨m,χ',ψ',z'⟩,ht⟩
  dsimp only at hl hχ hψ
  cases hl
  cases hχ
  cases hψ
  have hz' : z=z' := Subtype.ext hz
  cases hz'
  rfl


def actualSecondBlockCode {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    SecondBlockCode := ⟨q.1.val.val,q.2.1,fun i=>(q.2.2 i:ℤ)⟩

/-- Actual common labels and block intervals have no further hidden
multiplicity after their ideal pair, partition and four dyads are recorded. -/
theorem actual_second_block_code_injective {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ) :
    Function.Injective (actualSecondBlockCode s R seed K Tsec Z ξ) := by
  rintro ⟨p,U,n⟩ ⟨p',U',n'⟩ h
  have hp : p.val.val=p'.val.val := congrArg Sigma.fst h
  have hp' : p=p' := Subtype.ext (Subtype.ext hp)
  cases hp'
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hU : U=U' := congrArg Prod.fst ht
  cases hU
  have hn := congrArg Prod.snd ht
  have hn' : n=n' := funext (fun i=>Subtype.ext (congrFun hn i))
  cases hn'
  rfl

/-- Selecting the other first-stage choices at each first-label/projector
pair leaves just the displayed divisor as auxiliary source information. -/
theorem actual_second_joint_block_code_injective {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (first : Label→ FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex
        (s l) (R l) (seed l) (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,actualSecondBlockCode (s q.1) (R q.1) (seed q.1)
        (K q.1) (Tsec q.1) Z ξ q.2)) := by
  rintro ⟨l,q⟩ ⟨m,v⟩ h
  have hf : first l=first m := congrArg Prod.fst h
  have hs : seed l=seed m := congrArg (fun x=>x.2.1) h
  have hl : l=m := hfirst (Prod.ext hf hs)
  cases hl
  have hq : q=v := actual_second_block_code_injective (s l) (R l) (seed l)
    (K l) (Tsec l) Z ξ (congrArg (fun x=>x.2.2) h)
  cases hq
  rfl



/-- The injective source code applies to the literal heterogeneous block
family, including the character witness used in its window columns. -/
theorem actual_second_joint_source_keys {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0< K l)
    (first : Label→ FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex
        (s l) (R l) (seed l) (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,secondBlockCode
        (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
          (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2).block)) :=
  actual_second_joint_block_code_injective slots s R seed K Tsec Z ξ first hfirst

/-- The fiber of the joint encoding is bounded by its actual auxiliary
projectors, four dyads and two ray characters. The residual projector is
absent: its sum has already been contracted inside the row energy. -/
theorem actual_second_row_fiber_card {Label Aux : Type*} [Fintype Label]
    [DecidableEq Aux] (s : Label→ SecondBlockSource)
    (first : Label→ FirstSourceLabel) (aux : Label→ Aux)
    (hlabel : Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l))))
    (j : JointSourceLabel) (A : Finset Aux) (N : Finset (Fin 4→ℤ))
    (haux : ∀r : secondLiveRows s,secondEncodedRow s first r=j → aux r.val.1∈A)
    (hdyad : ∀r : secondLiveRows s,secondEncodedRow s first r=j → (s r.val.1).dyad∈N) :
    ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j)).card)≤
      A.card*N.card*(Fintype.card RayCharacter)^2 := by
  let fiber := Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j)
  let target := A ×ˢ (N ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ (Finset.univ : Finset RayCharacter)))
  have hk := actual_second_row_key_injective s first aux hlabel
  have hc : fiber.card≤ target.card := Finset.card_le_card_of_injOn
    (fun r : secondLiveRows s=>(aux r.val.1,(s r.val.1).dyad,r.val.2.1,r.val.2.2.1))
    (by
      intro r hr
      have hj := (Finset.mem_filter.mp hr).2
      exact Finset.mem_product.mpr ⟨haux r hj,Finset.mem_product.mpr
        ⟨hdyad r hj,Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩⟩⟩)
    (by
      intro r hr t ht he
      apply hk
      exact Prod.ext ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm) he)
  calc
    _≤ target.card := hc
    _=_ := by simp only [target,Finset.card_product,Finset.card_univ];ring


/-- In a fixed joint row the first projector costs a divisor small power,
not the size of the first-stage source pool. The dyads and ray labels are
kept explicit for their separate finite summation. -/
theorem actual_second_projector_fiber_bound (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (j : NonzeroJointSourceLabel left u₀ unit) (N : Finset (Fin 4→ℤ)),
      ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤ Z^B →
      (∀r : secondLiveRows s,secondEncodedRow s first r=j.val → (s r.val.1).dyad∈N) →
      ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
        (K*Z^ε)*N.card*(Fintype.card RayCharacter:ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := first_projector_small_power B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit j N hnorm hdyad
  let A := (idealDivisors (Ideal.span {jointSourceRow left u₀ unit j.val})).filter Squarefree
  have hI : Ideal.span {jointSourceRow left u₀ unit j.val}≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr j.property
  have hcard := actual_second_row_fiber_card s first seed hinj j.val A N
    (by
      intro r hr
      have hd := actual_second_encoded_first_projector s first r left u₀ unit
        (seed r.val.1) (hseed r.val.1) (hdiv r.val.1).1 (hdiv r.val.1).2
      rw [hr] at hd
      exact Finset.mem_filter.mpr ⟨(mem_idealDivisors hI).mpr hd,hseed r.val.1⟩) hdyad
  have hsmall : (A.card:ℝ)≤ K*Z^ε := hbound Z hZ _ j.property hnorm A
    (fun L hL=>(Finset.mem_filter.mp hL).2)
    (fun L hL=>(mem_idealDivisors hI).mp (Finset.mem_filter.mp hL).1)
  have hc : ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
      (A.card:ℝ)*N.card*(Fintype.card RayCharacter:ℝ)^2 := by exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)) (sq_nonneg _))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_row_key_injective

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_code_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_block_code_injective

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_row_fiber_card

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_projector_fiber_bound

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_source_keys

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRowFibres -/
