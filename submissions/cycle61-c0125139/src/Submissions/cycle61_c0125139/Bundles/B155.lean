/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B114
import Submissions.cycle61_c0125139.Bundles.B115
import Submissions.cycle61_c0125139.Bundles.B134
import Submissions.cycle61_c0125139.Bundles.B148
import Submissions.cycle61_c0125139.Bundles.B149
import Submissions.cycle61_c0125139.Bundles.B152
import Submissions.cycle61_c0125139.Bundles.B153
import Submissions.cycle61_c0125139.Bundles.B154
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLiveAllocation; sha256 1f64a88d3ae525692d1d627a15c3de2e220010a64db62c7febeb6786cc487699 -/
section
                                                          
                                                              

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
    (K Tsec Z ξ : ℝ) (hK : 0< K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLiveAllocation -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLiveWitness; sha256 fd0f554e223eac71d01ae0c97ceaf2bdabf8d8e1f7ee89eb4dd19694dbc5d452 -/
section
                                              

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap

/-- Nonvanishing of the original full block supplies a live row before any
ordinary/exceptional split or positive column majorant. -/
theorem actual_second_nonzero_live_row (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (hne : s.value W ≠ 0) : (secondLiveRows (fun _ : Unit => s)).Nonempty := by
  have hex := actual_second_batch_active_expression (fun _ : Unit => s)
    (fun _ => (1 : ℂ)) W
  simp only [Fintype.sum_unique, one_mul] at hex
  rw [hex] at hne
  obtain ⟨q,hq,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h := (Finset.mem_filter.mp hq).2
  refine ⟨⟨q.1,q.2.2⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,h.2.1,h.2.2.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_nonzero_live_row

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLiveWitness -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainNormalized; sha256 acb7733f2ae5d6844f085ea0fb8adfb2c097fc0f419abd390ec0ceb11357b74d -/
section
                                                      
                                                       
                                                             
                                                         
                                                              
                                                            
                                                        
                                                     
                                                             

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle61FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate
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
open Cycle61Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainNormalizedPhysicalDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The actual physical weight is paid before the complete live-column sum.
The selected ideal is not made squarefree and the right row remains negated. -/
theorem actual_main_effective_normalized_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ ap≤ x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*((d l).K/lowerFactor N a ap)*
              normalizer (d l).C (d l).D (d l).inactive)*
            (if reflected then
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z.val)‖^2
             else
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z.val‖^2) := by
  let cost := fun (r : SecondRow (fun l=>(d l).block)) (D : Ideal O)=>
    if reflected then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
  have hc : ∀r D,0≤ cost r D := by
    intro r D
    dsimp only [cost]
    split_ifs <;> exact sq_nonneg _
  calc
    _≤∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          (‖w r.1‖*((d r.1).K/lowerFactor N a ap)*
            normalizer (d r.1).C (d r.1).D (d r.1).inactive)*cost r D := by
      unfold secondNormalizedSum
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_right
        (actual_effective_physical_weight N a ap ha hap d w W
          hcard hlower hW₁ hW₂ r) (hc r D)
    _=_ := actual_second_column_reindex (fun l=>(d l).block) _


/-- The ordinary physical filter supplies the literal natural keep mask
for both orientations. The actual radial cutoff majorizes unit row weight. -/
theorem actual_main_ordinary_row_admission {α : Type*} [Fintype α] [DecidableEq α]
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (z : O) (hz : z∈(ordinarySecondDatum d χ₀ Q m).rows) :
    let τ:=if second then d.τ (ψ⁻¹) else d.τ χ
    let row:=if second then -z else z
    let st:=retainedState Z Bmask hZ τ Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    st.radial.keep row ∧
      1≤(st.radial.profile (normValue row/st.radial.scale)).re := by
  have hk := geometry_nonexceptional_reduced_pair d.input.η χ₀ χ ψ Q hQ m hm hml hm2
    d.C d.D d.hC d.hD d.inactive d.τ d.family d.radius z hz
  have hp := actual_partRows_majorized Z Bmask hZ
    (if second then d.τ (ψ⁻¹) else d.τ χ) Q
    (d.R*(if second then d.D else d.C)) hP hPN d.input.η χ₀ m
    d.radius d.C d.D d.inactive z hz
  dsimp only
  constructor
  · rw [retainedState_keep]
    cases second
    · exact hk.1
    · exact hk.2
  · cases second
    · exact hp
    · simpa only [ite_true,normValue,Ideal.span_singleton_neg] using hp

/-- The literal moving-height coefficient has norm at most one. The
first source weight is therefore retained without a label multiplicity. -/
theorem actual_main_block_weight_norm {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) (c : ℝ) (hc : 0≤ c) :
    ‖(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ q‖≤ c := by
  have hs := commonLabels_supported _ _ _ q.1.val.property
  have hh := common_height_norm_le_one s.η s.t _ _ hs.1.1 hs.2.1
  unfold actualSecondBlockWeight
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc hh

section PhysicalLow
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The uniform low-column estimate pays the literal source radius and
second normalizer inside the complete column sum. Its allocation is fixed
before every retained frequency; no individual norm bound is an input. -/
theorem actual_main_low_physical_family_columns
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
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
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
    ∀(reflected : Bool)(R seed : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t Mprice Aprice : ℝ)
      (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ),
    ∀{Label : Type*}[Fintype Label][DecidableEq Label],
    ∀firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin,
    ∀q : Label→ Chain s,
    (∀l,(q l).C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).R₁=R) → (∀l,HEq (q l).B₁ (firstIndex l).2) →
    (∀l,(q l).η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).t₁=t) →
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : (l : Label)→ LiveMainGeometry s (q l) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀l,(g l).reflected=reflected) →
    (∀l,(g l).C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).C) →
    (∀l,(g l).D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).D) →
    ∀(χ : Label→ RayFourExpansion.RayCharacter)(hP : ∀l,(q l).R₂*(q l).E₂≠0)
      (hPN : ∀l,(((q l).R₂*(q l).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun l=>retainedState Z Bmask hZ ((g l).datum.τ (χ l)) (internalQ Q η₀)
      ((q l).R₂*(q l).E₂) (hP l) (hPN l) (g l).datum.radius (g l).datum.C (g l).datum.D (g l).datum.inactive
    let src := fun l=>withHeight (q l).first ((g l).datum.τ (χ l)) v
    let nominal := fun l=>secondNominal Mrow Z amp omega (q l).C₁ (g l).D₁
      (g l).datum.C (g l).datum.D (g l).datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(divisorSeed : Label→ Ideal O)(hE₂ : ∀l,Supported (q l).E₂),(∀l,divisorSeed l∣(q l).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      (commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.allowance Z≤ pad) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      ∀D∈Ds,∀alloc∈(commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.active D,∀second : Bool,
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 0≤ Z^L ∧
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 1≤ Z^L) →
    let low := fun l=>ActualLow M H hH (st l) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Label→ Finset O)(weight : Label→ O→ℝ),(∀l,∀z∈zs l,0≤ weight l z) →
      (∀l,∀z∈zs l,(st l).radial.keep z ∧ low l z) →
      (∀l,∀z∈zs l,weight l z≤((st l).radial.profile (‖eisEmbedding z‖^2/(st l).radial.scale)).re) →
    let c := fun l=>geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l)*
      ((g l).datum.K/lowerFactor Nweight slotlo plainlo)*
      normalizer (g l).datum.C (g l).datum.D (g l).datum.inactive
    (∑l,c l*(∑D∈Ds,∑z∈zs l,weight l z*
      ‖normalizedColumn (src l) (q l).E₂ (hE₂ l) (q l).R₂ (divisorSeed l) D z‖^2))≤
      Cg*∑l,c l*((src l).toData.profileFactor*(∏j,(src l).M j)^2*
        QuadraticInitialBound.diagonalControl (st l).radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*((q l).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal l+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad) := by
  obtain ⟨degree,Sp,hcolumn⟩ := actual_live_main_low_profile_column (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hzslot haff
    reflected R seed bin t Mprice Aprice sourceWeight Label _ _ firstIndex q hCq hRq hBq hηq htq
    cell amp g hgref hgC hgD χ hP hPN st src nominal δwidth padding divisorSeed hE₂ hseed
    Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hzslot haff (q l) (g l) (χ l) (hP l) (hPN l)
    (divisorSeed l) (hE₂ l) (hseed l) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow l) (hcaps l)
    (zs l) (weight l) (hnonneg l) (hkeep l) (hweight l)
  have hc : 0≤ c l := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg
      (geometry_low_first_weight_nonneg reflected s R seed (Z^Mrow) Z ξ
        Mprice Aprice (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l))
      (div_nonneg (g l).datum.K_pos.le (lowerFactor_pos Nweight slotlo plainlo hslot hplain).le))
      (normalizer_pos (g l).datum.C (g l).datum.D (g l).datum.hC (g l).datum.inactive).le
  apply (mul_le_mul_of_nonneg_left hh hc).trans_eq
  ring

universe u v
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option linter.defProp false in
/-- Literal first and second geometry constructor specialization of the
physical scalar-weighted low kernel. All profile, capacity and detector
gates remain those of the actual retained state. -/
def actual_geometry_main_low_physical_columns {α : Type u} [Fintype α] [DecidableEq α]
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
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo) :=
  let hbase := actual_main_low_physical_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell Nweight slotlo plainlo hslot hplain
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc := hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose hc
    let hg := Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1< Z) (s : Input α) (θ : α→ RayQuotient.Characters M H)
        (w σ freq : α→ℝ) (heightV height mesh aLow : ℝ) (i : ℕ)
        hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
        hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap'
        hzslot haff (reflected : Bool) (R seed : Ideal O) (bin : ℤ×(Fin 5→ℤ))
        (t Mprice Aprice : ℝ)
        (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        {Label : Type v} [Fintype Label] [DecidableEq Label]
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let cell := Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
        (n : (l : Label)→ GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l))=>
        let datum := fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l)
        let firstChild := fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        fun (second : Label→ Bool)
          (B₂ : (l : Label)→ actualAllocations (firstChild l).pools
            (if second l then (datum l).D else (datum l).C))
          (r : (l : Label)→ secondLiveRows (fun _:Unit=>(datum l).block))
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hf₂ : ∀l,frozenCoefficient (B₂ l).val
            (if second l then (datum l).D else (datum l).C) (datum l).R
            (firstChild l).ν (firstChild l).W (firstChild l).P≠0)=>
        let q : Label→ Chain s := fun l=>geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l)
        let g : (l : Label)→ LiveMainGeometry s (q l) Z Mrow amp
          (frequencyLoss Z 32 ξ+reserve) ξ bs (Fintype.card α) := fun l=>geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        let hfields := fun l=>actual_geometry_low_admission_fields reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        hz.2 hZ s θ w σ freq heightV height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
          hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow (frequencyLoss Z 32 ξ+reserve) ξ
          hMmin hω hξ hMcap' hzslot haff reflected R seed bin t Mprice Aprice sourceWeight firstIndex q
          (fun l=>(hfields l).1) (fun l=>(hfields l).2.1) (fun l=>(hfields l).2.2.1)
          (fun l=>(hfields l).2.2.2.1) (fun l=>(hfields l).2.2.2.2.1) g
          (fun l=>(hfields l).2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.2.1)))))))

end PhysicalLow

/-- Original zero blocks and zero source coefficients are removed before
any decomposition into ordinary and exceptional rows. -/
theorem actual_original_nonzero_block_sum {Label : Type*} [Fintype Label]
    (d : Label→ SecondBlockSource) (w : Label→ℂ) (live : Label→ Prop)
    (hw : ∀l,¬live l→ w l=0) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(d l).value W)=
      ∑l : Finset.univ.filter (fun l=>live l ∧ (d l).value W≠0),
        w l.val*(d l.val).value W := by
  classical
  rw [Finset.sum_coe_sort (Finset.univ.filter (fun l=>live l ∧ (d l).value W≠0))
    (fun l=>w l*(d l).value W),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  split_ifs with h
  · rfl
  · by_cases hlive : live l
    · have hz : (d l).value W=0 := by
        by_contra hn
        exact h ⟨hlive,hn⟩
      rw [hz,mul_zero]
    · rw [hw l hlive,zero_mul]

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainNormalizedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))

/-- Every actual first column/allocation and every original second label and
four-coordinate dyadic block remain in the normalized family. -/
abbrev GeometryMainSecondIndex :=
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) ×
  GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key q

variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)

/-- Only the inducing branch is removed; all actual second dyads and rows
remain those of the original retained decomposition. -/
def geometryMainOrdinaryDatum (χ : RayCharacter) (Q : Ideal O) (m : O)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    SecondInputDatum α :=
  ordinarySecondDatum
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2) χ Q m

/-- The physical first allocation weight is retained inside every literal
second source weight, including canceled and unsupported blocks. -/
def geometryMainSecondWeight (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) : ℂ :=
  (geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1:ℂ)*
  actualSecondBlockWeight
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)
    j.1.1.val.2.1.val
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)) Z ξ j.2

/-- Selection takes place on the unrestricted original physical block,
before the ordinary split or any positive column majorant. -/
def geometryMainNonzeroBlocks : Finset
    (GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :=
  Finset.univ.filter (fun j=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0 ∧
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block.value ballProfile≠0)

set_option linter.defProp false in
/-- Exact original-block selection on the literal main geometry family. -/
def actual_geometry_main_nonzero_sum (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) :=
  let datum := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block
  let w := geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight
  let live := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0
  actual_original_nonzero_block_sum datum w live
    (fun j hf=>by
      simp only [w,geometryMainSecondWeight,geometryLowFirstWeight,geometryAllocationWeight,
        live] at hf ⊢
      simp only [hf,ite_false,zero_div,Complex.ofReal_zero,zero_mul]) ballProfile

/-- The full original block supplies a live second common allocation
once, independently of all subsequent row and shifted-height choices. -/
theorem actual_geometry_main_live_common_allocation
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      frozenCoefficient B₂.val (if second then d.D else d.C) d.R
        d.input.ν d.input.W d.input.P≠0 := by
  intro d
  have hs := actual_geometry_low_column_seed reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    j.val.1 hz₁ hz₂ j.val.2
  have hseed : d.seed∣(if second then d.D else d.C) := by
    cases second
    · exact hs.1
    · exact hs.2
  exact actual_second_input_live_allocation d second hseed ballProfile
    (Finset.mem_filter.mp j.property).2.2

/-- The original nonzero block supplies both a genuine row witness and
a valid canonical inactive partition before the ordinary restriction. -/
theorem actual_geometry_main_original_admission
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    (secondLiveRows (fun _:Unit=>d.block)).Nonempty ∧
      d.inactive∈inactiveSubsets d.C d.D := by
  intro d
  have hn : d.block.value ballProfile≠0 := (Finset.mem_filter.mp j.property).2.2
  exact ⟨actual_second_nonzero_live_row d.block ballProfile hn,
    second_block_nonzero_inactive d.block ballProfile hn⟩

omit [DecidableEq α] in
/-- Original first-source weights bound the literal second block weights;
the radius and second normalizer are paid by the physical low kernel. -/
theorem actual_geometry_main_block_weight_norm
    (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1 := by
  exact actual_main_block_weight_norm _ _ _ _ _ Z ξ j.2 _
    (geometry_low_first_weight_nonneg reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1)

set_option linter.defProp false in
/-- Literal normalized physical columns on original nonzero blocks.
Ordinary blocks may vanish; no positivity enlargement drops those blocks. -/
def actual_geometry_main_normalized_columns
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤ N) (hlower : slotlo≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ plainlo≤ x) (hW₂ : ∀x,s.W₂ x≠0→ plainlo≤ x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :=
  let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
    geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
  let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
    geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
  actual_main_effective_normalized_columns N slotlo plainlo hslot hplain datum w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) second t₀ u

end Literal

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_effective_normalized_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_normalized_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_ordinary_row_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_family_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_physical_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_nonzero_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_live_common_allocation

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_nonzero_block_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_block_weight_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_original_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_block_weight_norm

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainNormalized -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalized; sha256 22a73d17e243074168aa8ad91e205b4c702cc7d4f37b98ef3738dc3487b1b93e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                       
                                                          
                                                            
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss ActualEisensteinCubic
open Cycle61Moment Cycle61FinalError CenteredMomentPrimeElements
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedRows ConcretePrimeRowBridge
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondInputCapacitySource
open CenteredMomentFirstScale CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon Cycle61FinalErrorCapacity
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open CenteredMomentCommonProfile CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic
open CenteredMomentAmplificationErrorEnergy CenteredMomentSecondBlockAggregate
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open Filter CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationActiveFactor
local notation "O" => HeckeFamily.O
local instance errorNormalizedDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Negation preserves the actual retained source disk and radial filter. -/
theorem actual_error_source_rows_neg (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (R : ℝ) (z : O) :
    -z∈sourceRows C D U R ↔ z∈sourceRows C D U R := by
  have hn (w : O) : normValue (-w)=normValue w := by
    rw [normValue_eq_embedding,normValue_eq_embedding]
    simp
  unfold sourceRows liveRows retainedRows
  simp only [Finset.mem_filter,mem_rowNormDisk,mul_neg,hn,Ideal.span_singleton_neg]

/-- The right physical column uses the same complete ordinary set after
negating its row; the fixed inducing filter retains both ray characters. -/
theorem actual_error_ordinary_rows_neg (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (z : O) :
    -z∈partRows false η ψ Q fixedBadMask C D U R ↔
      z∈partRows false η χ Q fixedBadMask C D U R := by
  constructor
  · intro hz
    have hn := geometry_nonexceptional_pair η ψ χ⁻¹ χ⁻¹ Q hQ fixedBadMask
      (dvd_mul_right _ _)
      (dvd_mul_left _ _) C D U R (-z) hz
    apply Finset.mem_filter.mpr
    refine ⟨(actual_error_source_rows_neg C D U R z).mp (Finset.mem_filter.mp hz).1,?_⟩
    simpa only [Bool.false_eq_true,ite_false,inv_inv,neg_neg] using hn.2
  · intro hz
    have hn := geometry_nonexceptional_pair η χ ψ⁻¹ ψ⁻¹ Q hQ fixedBadMask
      (dvd_mul_right _ _)
      (dvd_mul_left _ _) C D U R z hz
    apply Finset.mem_filter.mpr
    refine ⟨(actual_error_source_rows_neg C D U R z).mpr (Finset.mem_filter.mp hz).1,?_⟩
    simpa only [Bool.false_eq_true,ite_false,inv_inv] using hn.2

/-- Complete ordinary columns dominate the full positive live-row sum.
Residual projectors and both rays remain inside the label sum. -/
theorem actual_error_ordinary_normalized_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ ap≤ x)
    (χ₀ : Label→ RayCharacter) (Q : Ideal O) (reflected : Bool) (t u : ℝ) :
    let datum := fun l=>ordinarySecondDatum (d l) (χ₀ l) Q fixedBadMask
    secondNormalizedSum reflected datum
      (secondEffectiveWeight (fun l=>(datum l).block) w W) t u≤
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        (‖w l‖*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈partRows false (d l).input.η (χ₀ l) Q fixedBadMask
            (d l).C (d l).D (d l).inactive (d l).radius,
            (if reflected then
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z‖^2) := by
  intro datum
  apply (actual_main_effective_normalized_columns N a ap ha hap datum w W
    hcard hlower hW₁ hW₂ reflected t u).trans
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ψ hψ
  let c := ‖w l‖*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive
  have hc : 0≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (div_nonneg (d l).K_pos.le (lowerFactor_pos N a ap ha hap).le))
      (normalizer_pos (d l).C (d l).D (d l).hC (d l).inactive).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D hD
  let f := fun z : O=>
    if reflected then
      ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
        ((d l).input.t+2*Real.pi*(u-(-t))))
        (d l).D (d l).hD (d l).R (d l).seed D (-z)‖^2
    else
      ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
        ((d l).input.t+2*Real.pi*(u-t)))
        (d l).C (d l).hC (d l).R (d l).seed D z‖^2
  have hf : ∀z,0≤ f z := by intro z; dsimp only [f]; split_ifs <;> exact sq_nonneg _
  change (∑z∈secondLiveColumnRows (datum l).block,c*f z.val)≤ c*∑z∈(datum l).block.rows,f z
  rw [←Finset.sum_coe_sort (datum l).block.rows f,Finset.mul_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun z _ _=>mul_nonneg hc (hf z.val))

/-- The actual extracted-prime coefficient, before either common norm
payment or prime cardinality cancellation. -/
def errorNormalizedCoefficient (P : Finset (Ideal O)) (weight V : ℝ)
    (p : O) (i : Fin 3) : ℝ :=
  (56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i)/V

theorem error_normalized_coefficient_nonneg (P : Finset (Ideal O)) (weight V : ℝ)
    (hw : 0≤ weight) (hV : 0< V) (p : O) (i : Fin 3) :
    0≤ errorNormalizedCoefficient P weight V p i := by
  unfold errorNormalizedCoefficient
  have hcost := localErrorCost_nonneg p (errorIndex i)
  positivity

/-- The actual moving height weight costs no arithmetic label factor. -/
theorem actual_error_block_weight_norm {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) (c : ℝ) (hc : 0≤ c) :
    ‖(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ q‖≤ c := by
  have hs := commonLabels_supported _ _ _ q.1.val.property
  have hh := common_height_norm_le_one s.η s.t _ _ hs.1.1 hs.2.1
  unfold actualSecondBlockWeight
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc hh

/-- Literal positive normalized error columns for a fixed first source.
The full physical row sum is taken before common allocation selection.
The exact prime coefficient remains inside every selected block weight. -/
theorem actual_error_full_normalized_to_columns {α : Type*} [Fintype α] [DecidableEq α]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤ weight) (p : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (hcard : Fintype.card α≤ N) (hlower : a≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x) (hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : rows→ RayCharacter) (Q : Ideal O)
    (reflected : Bool) (t u : ℝ) :
    let d := fun n : rows=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK n.val
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) p i
    let w := fun n : rows=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ n.val
    secondNormalizedSum reflected datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      (c*(K/lowerFactor N a ap))*
      ∑n : rows,∑χ : RayCharacter,∑ψ : RayCharacter,
        normalizer (d n).C (d n).D (d n).inactive*
        ∑D∈(d n).block.divisors.filter Squarefree,
          ∑z∈partRows false s.η (χ₀ n) Q fixedBadMask
            (d n).C (d n).D (d n).inactive (d n).radius,
            (if reflected then
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹)
                (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight s ((d n).τ χ)
                (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
  intro d datum c w
  have hc : 0≤ c := error_normalized_coefficient_nonneg P weight (volume s) hw (volume_pos s) p i
  have hdatum := actual_error_ordinary_normalized_columns N a ap ha hap d w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) χ₀ Q reflected t u
  apply hdatum.trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ψ hψ
  have hnorm := actual_error_block_weight_norm s R seed K Tsec Z ξ n.val c hc
  have hfactor : 0≤ K/lowerFactor N a ap := div_nonneg hK.le (lowerFactor_pos N a ap ha hap).le
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro z hz
  have he (r : Bool) : 0≤
    (if r then
      ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
        (d n).D (d n).hD R seed D (-z)‖^2
     else
      ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
        (d n).C (d n).hC R seed D z‖^2) := by
    split_ifs <;> exact sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hfactor)
      (normalizer_pos (d n).C (d n).D (d n).hC (d n).inactive).le) (he reflected)
  convert hm using 1 <;> dsimp only [d,w,actualSecondBlockDatum,actualSecondInputDatum] <;> (ring_nf; try rfl)


variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Choose the actual live common allocation from the original physical
block, once before the full ordinary column and all shifted heights. -/
theorem actual_geometry_error_live_common_allocation (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      frozenCoefficient B₂.val (if second then d.D else d.C) d.R
        d.input.ν d.input.W d.input.P≠0 := by
  intro d
  have hs := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve b t N
    hZ bin q p i Bp υ v hw₁ hw₂ n.val
  have hseed : d.seed∣(if second then d.D else d.C) := by
    cases second
    · exact hs.1
    · exact hs.2
  have hne : d.block.value ballProfile≠0 := (Finset.mem_filter.mp n.property).2
  exact actual_second_input_live_allocation d second hseed ballProfile hne

set_option linter.defProp false in
/-- Literal specialization to the lifted active extracted source. The
inferred result retains every original first key and error-radius parameter. -/
def actual_geometry_error_full_normalized_to_columns
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤ weight)
    (a ap : ℝ) (ha : 0< a) (hap : 0< ap) (hcard : Fintype.card α≤ N)
    (hlower : a≤ s.lower) (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x) (hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ))
    (χ₀ : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂→ RayCharacter)
    (Q : Ideal O) (second : Bool) (θ u : ℝ) :=
  actual_error_full_normalized_to_columns
    (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
    ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    (geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂)
    P weight hw p i N a ap ha hap
    ((Fintype.card_subtype_le _).trans hcard) hlower hW₁ hW₂ W χ₀ Q second θ u


/-- A different finite extraction menu may be chosen at each first
projector. Unioning its second labels pays that menu's cardinality once. -/
theorem actual_error_dependent_projector_reciprocal (B ε : ℝ)
    (hB : 0≤ B) (he : 0<ε) :
    ∃Ks : ℝ,0< Ks ∧ ∀(second : Bool)(Z T : ℝ),2≤ Z → 1≤ T →
    ∀(Ds : Finset (Ideal O)),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(β : Ds→ Type*)[∀D,Fintype (β D)](children : (D : Ds)→β D→ Finset FirstSourceLabel)
      (n : ℕ),
      (∀D,Fintype.card (β D)≤ n) →
      (∀D b,∀v∈children D b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀D b,∀v∈children D b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀D b,∀v∈children D b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀D b,∀v∈children D b,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑D : Ds,∑b : β D,∑v∈children D b,
        1/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤(n:ℝ)*(Ks*Z^ε) := by
  obtain ⟨Ks,hKs,hpay⟩ := actual_low_reciprocal_projector_shell B ε hB he
  refine ⟨Ks,hKs,?_⟩
  intro second Z T hZ hT Ds hDs hdyad β _ children n hcard hsup heq hdiv hnorm
  let union : Ideal O→ Finset FirstSourceLabel := fun D=>
    if h : D∈Ds then Finset.univ.biUnion (children ⟨D,h⟩) else ∅
  have hmem (D : Ds)(v : FirstSourceLabel) :
      v∈union D.val ↔ ∃b : β D,v∈children D b := by
    simp only [union,dite_eq_left D.property,Finset.mem_biUnion,Finset.mem_univ,true_and]
  have hh := hpay second Z T hZ hT Ds hDs hdyad union
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hsup ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact heq ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hdiv ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hnorm ⟨D,hD⟩ b v hb)
  have hpoint (D : Ds) :
      (∑b : β D,∑v∈children D b,1/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
        (n:ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
    have hn : 0≤∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by positivity
    calc
      _ ≤ ∑_b : β D,∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
        apply Finset.sum_le_sum
        intro b _
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun v hv=>(hmem D v).mpr ⟨b,hv⟩)
        intro v _ _
        positivity
      _ = (Fintype.card (β D):ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard D) hn
  calc
    _ ≤ ∑D : Ds,(n:ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) :=
      Finset.sum_le_sum (fun D _=>hpoint D)
    _ = (n:ℝ)*(∑D∈Ds,∑v∈union D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
      rw [←Finset.sum_coe_sort Ds (fun D : Ideal O=>
        ∑v∈union D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)),Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)


/-- Genuine extracted payment with the first allocation chosen separately
at every first residual projector. The original seed is not replaced by
that projector; its saving is provided by the second-label shell sum. -/
theorem eventual_actual_error_projector_dependent_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (he : 0<ε) :
    ∃Ks : ℝ,0< Ks ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool)(l : FirstSourceLabel),
      Supported l.1.1 → Supported l.1.2 → primeSupport l.1.1=primeSupport l.1.2 →
    ∀(T error εcommon M a δ reserve : ℝ),1≤ T → 0≤εcommon →
    ∀(Ds : Finset (Ideal O)),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : Ds→ actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Ds→ Character)(t : ℝ),
      (∀D,frozenCoefficient (alloc D).val (if reflected then l.1.2 else l.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u := fun D=>child s (if reflected then l.1.2 else l.1.1) Rfirst (alloc D) (χ D) t
    ∀(p : O)(k : ℕ),p≠0 → Prime (Ideal.span {p}) →
      (∀D,∀j I,I∈(u D).slots j→ IsCoprime (Ideal.span {p}) I) →
    let Bps := fun D=>errorLiftedActiveAllocations (u D) (Ideal.span {p}) k
    ∀(υ : (D : Ds)→ Bps D→ Character)(vheight : ℝ)
      (children : (D : Ds)→ Bps D→ Finset FirstSourceLabel),
      (∀D b,∀v∈children D b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀D b,∀v∈children D b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀D b,∀v∈children D b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀D b,∀v∈children D b,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
          (volume s) (volume (child (u D) ((Ideal.span {p})^k)
            (Rfirst*(if reflected then l.1.2 else l.1.1))
            Bp.val (υ D Bp) vheight)) p k)≤
      Ks*(k+1:ℝ)*Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon+ε-M*branchReserve k) := by
  obtain ⟨Ks,hKs,hpay⟩ := actual_error_dependent_projector_reciprocal B ε hB he
  refine ⟨Ks,hKs,?_⟩
  filter_upwards [eventual_actual_twice_error_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq T error εcommon M a δ reserve
    hT hecommon Ds hDs hdyad Rfirst alloc χ t halloc u p k hp hprime hslot Bps υ vheight
    children hsup heq₂ hdiv hnorm
  have hZ : 0< Z := by linarith
  have halloccount (D : Ds) : Fintype.card (Bps D)≤ k+1 := by
    have hh := actual_amplification_allocations_card (u D).pools (Ideal.span {p}) hprime k
      (by intro j I hI; exact ⟨(u D).pools_ne _ _ hI,hslot D j I hI⟩)
    have hsub : (errorLiftedActiveAllocations (u D) (Ideal.span {p}) k).card≤
        (actualAllocations (u D).pools ((Ideal.span {p})^k)).card :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
    dsimp only [Bps]
    rw [Fintype.card_coe]
    exact hsub.trans hh
  let exponent := lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
    error+εv+B*εcommon-M*branchReserve k
  have hpoint (D : Ds)(Bp : Bps D)(v : FirstSourceLabel)(hv : v∈children D Bp) :
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
        (volume s) (volume (child (u D) ((Ideal.span {p})^k)
          (Rfirst*(if reflected then l.1.2 else l.1.1)) Bp.val (υ D Bp) vheight)) p k≤
      Z^exponent/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    have hm := hz.2 s hcard hlow reflected second l hC hD heq Rfirst (alloc D) (χ D) t
      (halloc D) p hp k (hslot D) Bp.val (υ D Bp) vheight
      v.1.1 v.1.2 (hsup D Bp v hv).1 (hsup D Bp v hv).2 v.2.val
      M a δ reserve (error-M*branchReserve k) εcommon B hecommon (by
        cases second
        · exact (hnorm D Bp v hv).1
        · exact (hnorm D Bp v hv).2)
    convert hm using 1 <;>
      (dsimp only [extractedErrorLabelScalar,exponent,u,CenteredMomentAmplificationChildSourceCaps.twiceChild]; try ring_nf)
  have hsum := hpay second Z T hZ2 hT Ds hDs hdyad (fun D=>↥(Bps D)) children (k+1)
    halloccount hsup heq₂ hdiv hnorm
  simp only [Nat.cast_add,Nat.cast_one] at hsum
  calc
    _ ≤ ∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        Z^exponent/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro Bp _
      exact Finset.sum_le_sum (fun v hv=>hpoint D Bp v hv)
    _ = Z^exponent*(∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
      simp only [Finset.mul_sum,mul_one_div]
    _ ≤ Z^exponent*((k+1:ℝ)*(Ks*Z^ε)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hZ.le _)
    _ = _ := by
      rw [show lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon+ε-M*branchReserve k=exponent+ε by dsimp [exponent]; ring,
        Real.rpow_add hZ]
      ring


set_option backward.isDefEq.respectTransparency false in
/-- Original first-label counting and exact prime averaging after the
projector-dependent extraction payment. The two seeds remain distinct. -/
theorem eventual_actual_error_dependent_full_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (he : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ),
      1≤ T → p≤ B → 0≤εcommon →
    ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤ exponent) →
    ∀(Ds : labels→ Finset (Ideal O)),(∀l D,D∈Ds l→ Squarefree D) →
      (∀l D,D∈Ds l→ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : labels)→ Ds l→ actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1))
      (χ : (l : labels)→ Ds l→ Character)(t : ℝ),
      (∀l D,frozenCoefficient (alloc l D).val (if reflected then l.val.1.2 else l.val.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc l D).val) := fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l D) (χ l D) t
    ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→ IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l D q i→ Character)
      (vheight : ℝ)
      (children : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l D q i→ Finset FirstSourceLabel),
      (∀l D q i ψ b,∀v∈children l D q i ψ b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        ∑l : labels,∑ψ : RayCharacter,∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
            q.val (errorIndex i+1))≤
      K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ)*
        ∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*Z^(-M*branchReserve (errorIndex i+1)) := by
  obtain ⟨Kf,hKf,hfirst⟩ := actual_first_low_label_count B (ε/2) hB (half_pos he)
  obtain ⟨Ks,hKs,hsecond⟩ := eventual_actual_error_projector_dependent_payment N lo εv B (ε/2)
    hlo hev hB (half_pos he)
  let Kray : ℝ := Fintype.card RayCharacter
  have hKray : 0< Kray := by dsimp [Kray]; exact_mod_cast Fintype.card_pos
  refine ⟨56*Kray*Kf*Ks,by positivity,?_⟩
  filter_upwards [hsecond] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a δ reserve hT hp hecommon
    seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Ds hDs hdyad Rfirst alloc χ t halloc
    u P hne hprime hbad hslot Bps υ vheight children hsup₂ heq₂ hdiv hnorm₂
  have hZ : 0< Z := by linarith [hz.1]
  have hcount := hfirst Z (by linarith [hz.1]) p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpair (l : labels)(q : elementPool P)(i : Fin 3)(ψ : RayCharacter) :
      (∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
        extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
          (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
          q.val (errorIndex i+1))≤
      Ks*(errorIndex i+2:ℝ)*Z^(exponent+error+εv+B*εcommon+ε/2-M*branchReserve (errorIndex i+1)) := by
    have hq := elementPool_data P hprime hbad q.val q.property
    have hh := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1
      (hsup l.val l.property).2 (heq l.val l.property) T error εcommon M a δ reserve hT hecommon
      (Ds l) (hDs l) (hdyad l) Rfirst (alloc l) (χ l) t (halloc l)
      q.val (errorIndex i+1) hq.1.ne_zero (hprime _ hq.2.1) (fun D=>hslot l D q)
      (fun D=>υ l D q i ψ) vheight (fun D=>children l D q i ψ)
      (fun D=>hsup₂ l D q i ψ) (fun D=>heq₂ l D q i ψ) (fun D=>hdiv l D q i ψ)
      (fun D=>hnorm₂ l D q i ψ)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [show (errorIndex i:ℝ)+1+1=(errorIndex i:ℝ)+2 by ring] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hz.1])
    linarith [hgeom l.val l.property]
  have htotal (q : elementPool P)(i : Fin 3) :
      (∑l : labels,∑ψ : RayCharacter,∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
        extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
          (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
          q.val (errorIndex i+1))≤
      Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
        Z^(-M*branchReserve (errorIndex i+1)) := by
    let E := Ks*(errorIndex i+2:ℝ)*Z^(exponent+error+εv+B*εcommon+ε/2-M*branchReserve (errorIndex i+1))
    calc
      _ ≤ ∑_l : labels,∑_ψ : RayCharacter,E :=
        Finset.sum_le_sum (fun l _=>Finset.sum_le_sum (fun ψ _=>hpair l q i ψ))
      _ = (labels.card:ℝ)*(Kray*E) := by simp [Kray]
      _ ≤ (Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Kray*E) :=
        mul_le_mul_of_nonneg_right hcount (by dsimp [E]; positivity)
      _ = _ := by
        dsimp [E]
        simp only [Real.rpow_add hZ,Real.rpow_sub hZ]
        have heps : Z^ε=Z^(ε/2)*Z^(ε/2) := by rw [←Real.rpow_add hZ,add_halves]
        rw [heps,neg_mul,Real.rpow_neg hZ.le]
        ring
  have hpcount : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hprime hbad]
  have hpc : (0:ℝ)< P.card := by exact_mod_cast hne.card_pos
  calc
    _ ≤ (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        (Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-M*branchReserve (errorIndex i+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun q _=>Finset.sum_le_sum
        (fun i _=>mul_le_mul_of_nonneg_left (htotal q i) (by positivity)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hpcount,Finset.mul_sum]
      field_simp
      apply Finset.sum_congr rfl
      intro i hi
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_source_rows_neg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_ordinary_rows_neg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_ordinary_normalized_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.error_normalized_coefficient_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_block_weight_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_full_normalized_to_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_live_common_allocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_full_normalized_to_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_dependent_projector_reciprocal

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_projector_dependent_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_dependent_full_label_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalized -/
