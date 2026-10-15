import Candidate.Cycle62.Physical.InitialMass.Decomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentFirstAnnularInput CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization
open CenteredMomentPrimeElements CenteredMomentAmplificationErrorEnergy RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Removing zero slot-profile values only removes pool elements. Plain
ideal pools are unchanged. -/
theorem error_active_pools_subset (s : Input ι) :
    ∀j,(activeInput s).pools j⊆s.pools j := by
  intro j
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

/-- Actual allocations are monotone in the literal source pools. -/
theorem error_actual_allocations_mono {κ : Type*} [Fintype κ]
    (S T : κ→Finset (Ideal O)) (C : Ideal O) (hST : ∀j,S j⊆T j) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hlabel
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨v,?_,he⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun j=>hST j (Fintype.mem_piFinset.mp hv j))

/-- An active extracted allocation is the same tuple in the unpruned
source. No equality of the two allocation pools is asserted. -/
def errorActiveAllocation (s : Input ι) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,error_actual_allocations_mono _ _ C (error_active_pools_subset s) B.property⟩

@[simp] theorem errorActiveAllocation_val (s : Input ι) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) :
    (errorActiveAllocation s C B).val=B.val := rfl

theorem errorActiveAllocation_injective (s : Input ι) (C : Ideal O) :
    Function.Injective (errorActiveAllocation s C) := by
  intro B D h
  apply Subtype.ext
  exact congrArg (fun A : actualAllocations s.pools C=>A.val) h

/-- Extraction and zero-profile pruning commute for a lifted allocation.
The surviving slot filter remains present on the right. -/
theorem error_active_child (s : Input ι) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (errorActiveAllocation s C B) τ t) := by
  rfl

/-- Literal active extracted source equals the unpruned lifted source.
Zero slot coefficients are removed using the actual Gaussian identity. -/
theorem error_active_child_source (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (radius : ℝ) :
    childNormalizedGaussSource (activeInput s) C R seed B τ t W radius=
      childNormalizedGaussSource s C R seed (errorActiveAllocation s C B) τ t W radius := by
  unfold childNormalizedGaussSource
  dsimp only [errorActiveAllocation]
  rw [error_active_child]
  exact active_normalized _ _ _ _ _

/-- The extraction index is the literal amplification index plus one. -/
theorem error_extracted_index_cases (i : Fin 3) :
    errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7 := by
  rcases errorIndex_cases i with h|h|h <;> simp [h]

/-- Exact rewrite of all three error branches into unpruned children.
The active allocation domain, both scalar factors and the radius stay
literal; no extra unpruned allocations or positivity assumption are added. -/
theorem actual_error_sources_lifted (s : Input ι) (g : FirstBranchGeometry)
    (Z sigma Csec ξ reserve : ℝ) (P : Finset (Ideal O))
    (τ : elementPool P→Fin 3→RayCharacter→Character) :
    actualErrorSources s g Z sigma Csec ξ reserve P τ=
      ∑p : elementPool P,∑i : Fin 3,
        (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
          ∑χ : RayCharacter,∑B : actualAllocations (activeInput s).pools
            ((Ideal.span {p.val})^(errorIndex i+1)),
            childNormalizedGaussSource s ((Ideal.span {p.val})^(errorIndex i+1))
              g.R g.seed (errorActiveAllocation s _ B) (τ p i χ) s.t ballProfile
              (errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z)
                g.cLog sigma (frequencyLoss Z (32*Csec) ξ) reserve p (errorIndex i+1)) := by
  unfold actualErrorSources
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun x : ℝ=>(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  exact error_active_child_source s _ g.R g.seed B (τ p i χ) s.t ballProfile _

/-- Specialize the exact source identity to the first actual common child.
The target is precisely the unpruned `twiceChild` dictionary. -/
theorem error_active_twice_source (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (η : Character) (t : ℝ)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput (child s C R B η t)).pools
      ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v : ℝ) (W : 𝓢(ℝ,ℂ)) (radius : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B η t))
      ((Ideal.span {p})^(errorIndex i+1)) (R*C) seed Bp υ v W radius=
    normalizedGaussSource
      (twiceChild s C R B η t (Ideal.span {p}) (errorIndex i+1)
        (errorActiveAllocation (child s C R B η t) _ Bp) υ v)
      ((R*C)*(Ideal.span {p})^(errorIndex i+1)) seed W radius := by
  exact error_active_child_source (child s C R B η t) _ (R*C) seed Bp υ v W radius

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_active_pools_subset
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_actual_allocations_mono
#print axioms OAI.SevenEighths.Cycle62InitialMass.errorActiveAllocation_injective
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_active_child
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_active_child_source
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_extracted_index_cases
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_sources_lifted
#print axioms OAI.SevenEighths.Cycle62InitialMass.error_active_twice_source
