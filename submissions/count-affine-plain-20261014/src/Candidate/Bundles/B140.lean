/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B080
import Candidate.Bundles.B109
import Candidate.Bundles.B126
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePrimeGates; sha256 37dcfc422de14af29194c2b42f612240e78fde03afbb8b6b03f38a024565b64c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        
                                       
                                                        

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationSlotGap CenteredMomentPrimeElements
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance affinePrimeGatesFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- One threshold separates every amplifier cell from all stored slots.
It does not discard entries whose smooth profile happens to vanish. -/
theorem eventual_geometry_affine_prime_coprime
    (S : Finset (Ideal O)) (hS : fixedBadPrimes⊆S) (b mesh : ℝ)
    (hmesh : mesh<(62485051/9854400000:ℝ)/2) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀beta : ℝ,3401/100000≤ beta → beta≤1/25 →
      let P:=CenteredMomentPrimePool.primePool M H S (1/2) 1
        (Z^(Cycle61.Arithmetic.amp beta))
      ∀{α : Type*}[Fintype α][DecidableEq α]
        (s : Input α)(η₀ : Character)(θ : α→ RayQuotient.Characters M H)
        (w σ v : α→ℝ)(W : ℝ→ℂ),
        Matches M H hH s η₀ θ w σ v W b Z → (∀i,w i≤ mesh) →
        ∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I := by
  let ell : ℝ:=(62485051/9854400000)/2
  have hell : 0< ell := by norm_num [ell]
  filter_upwards [eventually_scale_gap (max 1 b) mesh ell hmesh,
    (tendsto_rpow_atTop hell).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hgap hlarge hZ
  refine ⟨hZ,?_⟩
  intro beta hlo hhi P α _ _ s η₀ θ w σ v W hm hw q i I hI
  have hz : 0< Z:=zero_lt_one.trans hZ
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).1
  have hbad : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hbad q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz _) (Finset.mem_sdiff.mp hq.2.1).1
  have hlow : Z^ell≤(1/2:ℝ)*Z^(Cycle61.Arithmetic.amp beta) := by
    have ha : ell+ell≤ Cycle61.Arithmetic.amp beta := by
      have h:=(Cycle61.Arithmetic.amp_bounds ⟨hlo,hhi⟩).1
      dsimp only [ell]
      linarith
    have hr:=Real.rpow_le_rpow_of_exponent_le hZ.le ha
    rw [Real.rpow_add hz] at hr
    have hnonneg:=Real.rpow_nonneg hz.le ell
    have hx : 2 * Z^ell ≤ Z^(Cycle61.Arithmetic.amp beta) :=
      (mul_le_mul_of_nonneg_right hlarge hnonneg).trans hr
    calc
      Z^ell = (1/2:ℝ) * (2 * Z^ell) := by ring
      _ ≤ (1/2:ℝ) * Z^(Cycle61.Arithmetic.amp beta) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
  exact actual_full_slot_coprime M H hH s η₀ θ w σ v W b Z mesh ell hZ.le hm hw
    (Ideal.span {q.val}) (hp _ hq.2.1)
    (hlow.trans (by simpa only [mul_comm] using hn.1.le)) hgap.2 i I hI

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_affine_prime_coprime

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePrimeGates -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorActiveInput; sha256 4ba8e089c50deb71db3d1b1e8fe646b18aa5704a66ccb6ccb5c23ab9d513d729 -/
section
                                                 
                                                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
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
    (S T : κ→ Finset (Ideal O)) (C : Ideal O) (hST : ∀j,S j⊆T j) :
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
    (τ : elementPool P→ Fin 3→ RayCharacter→ Character) :
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_active_pools_subset
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_actual_allocations_mono
#print axioms OAI.SevenEighths.Cycle61InitialMass.errorActiveAllocation_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_active_child
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_active_child_source
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_extracted_index_cases
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_sources_lifted
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_active_twice_source

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorActiveInput -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalErrorCapacity.Capacity; sha256 b0a79ee9e3d5424cbc52c71d29d9edf780d4ccc3fd28a06afc5c1f1b8d6f9a4b -/
section
                                              
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61FinalErrorCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCanonicalFirst Cycle61FinalCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem extraction_max_loss (c d w wo : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (hwo : wo ≤ w) :
    max (c-d+2*w-wo) 0-c-w ≤ w-wo := by
  have hm : max (c-d+2*w-wo) 0 ≤ c+2*w-wo :=
    max_le (by linarith) (by linarith)
  linarith

omit [DecidableEq ι] in
theorem extracted_final_volume_log (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools C₂) (Z : ℝ) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    Real.logb Z (preVolume (commonData e C₂ R₂ B₂)) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-
      Real.logb Z (rawReduction B₂.val e.P) := by
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  dsimp only
  rw [common_preVolume,Real.logb_div (preVolume_pos e.toData).ne'
    (rawReduction_pos B₂.val (alloc_ne e C₂ B₂) e.P e.P_pos).ne']
  have he := twice_volume s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v
  change preVolume e.toData = preVolume s.toData / _ at he
  rw [he,Real.logb_div (preVolume_pos s.toData).ne'
    (mul_pos (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos)
      (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)).ne',
    Real.logb_mul (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne'
      (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k).ne',Real.logb_pow]
  ring

/-- Extraction contributes its exact prime power, rather than a third
 common-allocation support loss. -/
theorem extracted_supported_capacity (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (hP : ∀i,1 ≤ s.P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v)
      C₂ R₂ B₂).X₁*(commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) C₂ R₂ B₂).X₂)
    (z : O) (hne : let f := commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) C₂ R₂ B₂
      allocatedPositiveRow f.η f.m f.A z f.t f.slots f.coefficient f.P L a
        f.W₁ f.W₂ X₁ X₂ ≠ 0) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    let f := commonData e C₂ R₂ B₂
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z f.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-Real.logb Z (rawReduction B₂.val e.P)+
        (7/2)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hpe : ∀i,1 ≤ e.P i := fun i => hp₁ i.val
  have hpf : ∀i,1 ≤ f.P i := fun i => hpe i.val
  have hb := supported_residual_capacity f L a Z hZ hpf X₁ X₂ hX₁ hX₂ hprod z hne
  have hv : Real.logb Z (preVolume f) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-
      Real.logb Z (rawReduction B₂.val e.P) :=
    extracted_final_volume_log s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v C₂ R₂ B₂ Z
  have hl₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hlp := common_slot_logs_le first (Q^k) Bp Z hZ hp₁
  have hl₂ := common_slot_logs_le e C₂ B₂ Z hZ hpe
  change (∑i,Real.logb Z (first.P i)) ≤ ∑i,Real.logb Z (s.P i) at hl₁
  change (∑i,Real.logb Z (e.P i)) ≤ ∑i,Real.logb Z (first.P i) at hlp
  change (∑i,Real.logb Z (f.P i)) ≤ ∑i,Real.logb Z (e.P i) at hl₂
  rw [hv] at hb
  change _ ≤ _ at hb ⊢
  change _ ≤ Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
    (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-Real.logb Z (rawReduction B₂.val e.P)+
    (7/2)*(∑i,Real.logb Z (f.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  linarith

def errorNominal (M Z amp omega w wo : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (U : Finset (CommonIndex C₂ D₂)) : ℝ :=
  M-max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)+2*w-wo) 0-
    3*amp-omega-Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)

#print axioms extraction_max_loss
#print axioms extracted_final_volume_log
#print axioms extracted_supported_capacity
end
end OAI.SevenEighths.Cycle61FinalErrorCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalErrorCapacity.Capacity -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalErrorCapacity.Physical; sha256 5fb0208f8ebc7b2798767e04bda3933e22afddc7371f4d7ef19b74ab8ce6d2d9 -/
section
                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61FinalErrorCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCanonicalFirst Cycle61FinalCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both actual second-label allocations share the same generator/unit
 cancellation. Prime extraction pays its exact removed width. -/
theorem actual_error_source_capacity (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (χ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ D₂ H R₂ : Ideal O) (hH : H=C₂ ∨ H=D₂)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools H)
    (hf₂ : let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
      frozenCoefficient B₂.val H R₂ e.ν e.W e.P ≠ 0)
    (D₁ : Ideal O) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z M amp omega wo : ℝ) (hZ : 1 < Z) (hM : 0 < M) (hP : ∀i,1 ≤ s.P i)
    (hwo : wo ≤ (k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hz : (17/500)*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ (1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle61.Arithmetic.B*M)
    (second : Bool) (z : O)
    (hne : Cycle61.Physical.sourcePositiveRow
      (commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) H R₂ B₂).toSource second L a z ≠ 0) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    let f := commonData e H R₂ B₂
    let w := (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    let cell := Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    length Z (Cycle61Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle61Moment.LowBranch.finalPlain f second L a 1)+
        (9/2)*remainingLogs L a Z f.P-
      errorNominal M Z amp omega w wo C₁ D₁ C₂ D₂ U ≤
        M*Cycle61.Arithmetic.g cell+3*amp+(w-wo)+omega+supportPadding N b s.b₁ s.b₂ Z := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e H R₂ B₂
  let X := Cycle61.Physical.sourcePlainScales f.toSource second
  have hx₁ := Cycle61Moment.LowBranch.source_plain_positive f second 0
  have hx₂ := Cycle61Moment.LowBranch.source_plain_positive f second 1
  have hprod : X 0*X 1=f.X₁*f.X₂ := by
    cases second
    · rfl
    · exact f.same_product
  have htotal := extracted_supported_capacity s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v
    H R₂ B₂ L a Z hZ hP (X 0) (X 1) hx₁ hx₂ hprod z hne
  have he : length Z (Cycle61Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle61Moment.LowBranch.finalPlain f second L a 1) =
        plainLogs L a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 0) 0)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 1) 1))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  have hc₁ := Real.logb_nonneg hZ (norm_ge_one C₁ (allocation_ne s C₁ B₁))
  have hd₁ := Real.logb_nonneg hZ (norm_ge_one D₁ hD₁)
  have hw : 0 ≤ (k:ℝ)*Real.logb Z (Q.absNorm:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg hZ (norm_ge_one Q hQ))
  have hmax := extraction_max_loss _ _ _ wo hc₁ hd₁ hw hwo
  have hshift : Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) ≤ Real.logb Z (H.absNorm:ℝ) := by
    rcases hH with hh|hh
    · rw [hh]
      exact actual_common_shift_le C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
    · rw [hh]
      exact actual_common_shift_le_right C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hce : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val) ≤ N :=
    (live_card_le Bp.val).trans ((live_card_le B₁.val).trans hcard)
  have hr₂ := common_reduction_log_lower N b hb e hce hs H R₂ B₂ hf₂ Z hZ
  have hcell := original_affine_capacity s Z M hZ hM hz haffine
  dsimp only at htotal hcell ⊢
  rw [he]
  change Real.logb Z (preVolume s.toData)+(7/2)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
  unfold errorNominal supportPadding
  linarith

#print axioms actual_error_source_capacity

/-- A residual branch with no surviving literal row contributes zero for
 every retained mask and every radial profile. -/
theorem no_surviving_row_energy_zero {α : Type*} [Fintype α] [DecidableEq α]
    (src : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : SchwartzMap ℝ ℂ) (K : ℝ)
    (hz : ∀z,Cycle61.Physical.sourcePositiveRow src.toSource second L a z=0) :
    Cycle61Moment.LowBranch.finalPositiveEnergy src second L a keep Φ K=0 := by
  unfold Cycle61Moment.LowBranch.finalPositiveEnergy
  simp only [hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,ite_self,tsum_zero]

#print axioms no_surviving_row_energy_zero
end
end OAI.SevenEighths.Cycle61FinalErrorCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalErrorCapacity.Physical -/
