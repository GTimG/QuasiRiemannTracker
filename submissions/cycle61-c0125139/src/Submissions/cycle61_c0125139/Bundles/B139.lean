/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B078
import Submissions.cycle61_c0125139.Bundles.B090
import Submissions.cycle61_c0125139.Bundles.B108
import Submissions.cycle61_c0125139.Bundles.B135
import Submissions.cycle61_c0125139.Bundles.B138

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryChosenAffine; sha256 c62049edad019c05bdaf344b5dfc3932df5699cac3b53cad5af6136c1f090548 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          
                                    

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle61InitialMass
open scoped SchwartzMap

/-- The chosen-source interface is exactly the literal geometry budget
followed by the proved physical-mass and affine assembly. The budget remains
an explicit analytic obligation; this adapter does not assert it. -/
theorem actual_affine_input_of_geometry (A : ChosenData) (bΦ δ τ ξ : ℝ)
    (hbΦ : 0< bΦ) (hδ : 0<δ) (hτ : 0<τ) (hξ : 0<ξ)
    (hδgap : δ≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000)
    (hsΦ : Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (hmesh : A.P.mesh≤ Cycle61FirstActual.comparisonMesh 1 1 (δ/2))
    (hbudget : SourceLiteralAffineGeometryBudget A.F bΦ A.P.mesh (δ/4) τ ξ) :
    Numerator.Source.ActualAffineInput A := by
  have hgap : Arithmetic.theta< HeckeZeroSupremum.beta := by linarith
  have hβ:=moment_parameter_gates hgap
  obtain ⟨degree,S,C,hC,hbound⟩:=weighted_source_affine_from_geometry A.F
    bΦ A.P.mesh δ τ ξ hbΦ A.P.mesh_pos hδ hτ hξ hmesh hβ.2.2 hβ.2.1 hbudget
  exact ⟨bΦ,δ,hδ,hδgap,hsΦ,degree,S,C,hC,hbound⟩

end
end Cycle61.FinalAssembly
#print axioms Cycle61.FinalAssembly.actual_affine_input_of_geometry

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryChosenAffine -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryChosenSetup; sha256 c0a8a1258037fb73d23ce1d50ae0246685a13113c2272c858ad15de76f31d743 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        
                                                      

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Cycle61.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle61InitialMass

/-- This cap depends only on the outer error, before any dictionary is chosen. -/
def geometryChosenMesh (ε : ℝ) : ℝ :=
  min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle61FirstActual.comparisonMesh 1 1 (ε/2))

theorem geometry_chosen_mesh_admission (ε : ℝ) (hε : 0<ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0< geometryChosenMesh ε ∧
    geometryChosenMesh ε≤ Cycle61FirstActual.comparisonMesh 1 1 (ε/2) ∧
    geometryChosenMesh ε≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    geometryChosenMesh ε≤μ/8 ∧
    geometryChosenMesh ε<(902420521/120632400000:ℝ)/2 := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle61FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hle : geometryChosenMesh ε≤ geometryAnalyticMesh 1 1 (ε/4) 2 28 1 :=
    min_le_left _ _
  refine ⟨lt_min ha.1 hc,min_le_right _ _,hle.trans ha.2.2.1,
    hle.trans ha.2.2.2.1,?_⟩
  simpa only [one_mul] using hle.trans_lt ha.2.2.2.2

/-- Fix the loss and mesh before the chosen dictionary; enlarge only the
radial support bound to meet the high-family admission gate. No analytic
moment estimate is assumed or asserted here. -/
theorem exists_chosen_geometry_setup
    (hgap : Arithmetic.theta< HeckeZeroSupremum.beta) :
    ∃ ε : ℝ,0<ε ∧ ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 ∧
    ∃ A : ChosenData,A.P.mesh≤ geometryChosenMesh ε ∧
    ∃ bΦ : ℝ,2≤ bΦ ∧ Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
  let ε:=(HeckeZeroSupremum.beta-Arithmetic.theta)/20000
  have hε : 0<ε := by dsimp [ε];positivity
  have hεgap : ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 := by
    dsimp [ε];linarith
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hgap
    (geometry_chosen_mesh_admission ε hε).1
  obtain ⟨b,hb,hs⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  refine ⟨ε,hε,hεgap,A,hA,max 2 b,le_max_left _ _,?_⟩
  intro x hx
  exact (show x≤ b from hs hx).trans (le_max_right _ _)

/-- A uniform source geometry estimate supplies the genuine chosen affine
input, with the mesh fixed before the dictionary and the support bound fixed
before its analytic height. The source estimate remains explicit here. -/
theorem chosen_affine_of_source_geometry
    (hsource : ∀{D : Cycle25.Weighted.MomentData}
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (εaffine mesh bΦ : ℝ),0<εaffine →
      mesh < (902420521/120632400000:ℝ)/2 → 0 ≤ mesh →
      mesh ≤ geometryLossUnit 1 εaffine/8 →
      mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8) →
      2≤ bΦ → 51/100≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta≤7/8 →
      ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
        SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ
          (geometryLossUnit 1 εaffine/64)) : ChosenAffineInput := by
  intro hgap
  obtain ⟨ε,hε,hεgap,A,hA,bΦ,hbΦ,hsΦ⟩:=exists_chosen_geometry_setup hgap
  have hm:=geometry_chosen_mesh_admission ε hε
  obtain ⟨τ,hτ,_hτcap,hbudget⟩:=hsource A.F (ε/4) A.P.mesh bΦ (by positivity)
    (hA.trans_lt hm.2.2.2.2) A.P.mesh_pos.le
    (hA.trans hm.2.2.2.1) (hA.trans hm.2.2.1) hbΦ
    (moment_parameter_gates hgap).2.2 baseline_beta
  refine ⟨A,actual_affine_input_of_geometry A bΦ ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hε hτ ?_ hεgap hsΦ (hA.trans hm.2.1) hbudget⟩
  exact div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) (by positivity))
    (by norm_num)

end
end Cycle61.FinalAssembly
#print axioms Cycle61.FinalAssembly.geometry_chosen_mesh_admission
#print axioms Cycle61.FinalAssembly.exists_chosen_geometry_setup
#print axioms Cycle61.FinalAssembly.chosen_affine_of_source_geometry

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryChosenSetup -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineAmplification; sha256 28c5faff9ef40a91992849a38bc6e31f007841055ec4cad858c6f494b76e5dd5 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                         
                                                      
                                  

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O

open Cycle61InitialSource CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyReferenceState
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance affineAmplificationSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable (rayM : Ideal O) [NeZero rayM]
local instance affineAmplificationFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

/-- One scale threshold works for every live subset and all 600 possible
original-width cells. The literal affine source supplies all amplification
gates; no main or error energy estimate is a premise. -/
theorem actual_affine_geometry_amplification
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (loss mesh ξ reserve : ℝ) (hloss : 0< loss)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (hξ : 0≤ξ) (hξcap : ξ≤1) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(hZ : 1< Z)
      (T : Finset α) (η₀ : Character) (θ : T→ RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta:=Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))
      let amp:=Cycle61.Arithmetic.amp beta
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      P.Nonempty ∧ Z^(amp-loss)≤(P.card:ℝ) ∧
      ∀(reflected : Bool) (key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate inp 1 1 Z Z ξ→ℂ) (N : ℕ) (height : ℝ),
      let hK:=zero_lt_one.trans hZ
      let Label:=↥(firstLiveColumns (geometryFirstSource inp 1 1 Z Z ξ hK key) (fun _=>logAnnulus))
      let C:=fun j : Label=>geometryColumnIdeal reflected inp 1 1 Z Z ξ hK key j.val
      let χ:=fun j : Label=>geometryColumnCharacter reflected inp 1 1 Z Z ξ hK key j.val
      let g:=fun j : Label=>geometryBranch reflected inp 1 1 Z Z ξ hK key j.val
      let mass:=fun j : Label=>geometryAllocationWeight reflected inp 1 1 Z Z ξ 1
        (Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)) hK key weight N (9/4) j.val
      ∃τ : (j : Label)→ actualAllocations inp.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
        (∀j B q i ψ,(τ j B q i ψ).modulus.absNorm≤
          radicalBound (childCharacter (χ j) ψ) fixedBadMask q.val
            (errorMovingExponent (errorIndex i))) ∧
        geometryLiveBudget reflected inp 1 1 Z Z ξ 1
          (Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)) hK key weight N (9/4) height≤
        (56/(P.card:ℝ))*
          (((amplifierCap 2 0 1+6*amp)/(amp/2))*
            (∑j,∑B,mass j B*actualMainSource (child inp (C j) 1 B (χ j) height)
              (g j) Z (3*amp) 1 ξ reserve)+
            ∑j,∑B,mass j B*actualErrorSources (child inp (C j) 1 B (χ j) height)
              (g j) Z (3*amp) 1 ξ reserve P (τ j B)) := by
  have hdata (T : Finset α) (j : ↥(Finset.Icc 1 600)) :=
    actual_geometry_budget_amplification (ι:=T) rayM H hH Sbad hbad
      (3*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper j.val)) loss
      0 3 2 0 1 3 (9/4) mesh ξ reserve
      (by have hh:=Cycle61.Arithmetic.amp_pos
            (Cycle61.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2);positivity)
      hloss (by norm_num [amplifierCap]) (by norm_num)
      (by have hh:=(Cycle61.Arithmetic.amp_bounds
            (Cycle61.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2)).1
          linarith)
      hξ hξcap hreserve
  have hu := Filter.eventually_all.mpr (fun T : Finset α=>
    Filter.eventually_all.mpr (fun j : ↥(Finset.Icc 1 600)=>hdata T j))
  have hcaps:=eventual_affine_polynomial_caps (α:=α) rayM H hH W hW 1 2
    (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hu,hcaps] with Z hu hc
  refine ⟨hc.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi inp beta amp P
  have hcell:=Cycle61.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  let j : ↥(Finset.Icc 1 600):=⟨Cycle61.Moment.originalCell (∑i,w i),Finset.mem_Icc.mpr ⟨hcell.1,hcell.2.1⟩⟩
  have hg:=hu T j
  have hdiv : ∀x : ℝ,3*x/3=x := by intro x;ring
  have hp : Z^(amp-loss)≤(P.card:ℝ) := by
    simpa only [P,amp,beta,j,hdiv] using hg.2.2.1
  refine ⟨?_,hp,?_⟩
  · simpa only [P,amp,beta,j,hdiv] using hg.2.1
  intro reflected key weight N height hK Label C χ g mass
  have hcap:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa using hlo₁) (by simpa using hlo₂)
    (by simpa using hhi₁) (by simpa using hhi₂) (by simpa using hwhi)
  have hz₁ : inp.W₁ 0=0:=CenteredMomentDetectorPlainSource.support_zero
    (p.profile 0) (1/4) (9/4) (by norm_num) (p.support 0)
  have hz₂ : inp.W₂ 0=0:=CenteredMomentDetectorPlainSource.support_zero
    (p.profile 1) (1/4) (9/4) (by norm_num) (p.support 1)
  have hsupp : ∀i,Function.support (inp.W i)⊆Set.Iic (9/4:ℝ) := by
    intro i x hx
    have hh:=CenteredMomentEnergyNaturalInputMatches.profile_support W 1 2 hWs (σ i) (freq i) hx
    change x≤9/4
    linarith [hh.2]
  have hh:=hg.2.2.2 reflected inp 1 1 Z 1
    (Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)) hK key weight N height
    (by simpa only [CenteredMomentExceptionalAmplitudePair.volume,
      CenteredMomentAmplificationChildInput.volume,inp,show (1:ℝ)+1=2 by norm_num] using hcap.2.2.1)
    (by simpa using inv_le_one_of_one_le₀ hZ.le)
    one_ne_zero (by simp) squarefree_one hz₁ hz₂
    (by simpa only [show (1:ℝ)+2=3 by norm_num] using hcap.2.2.2.1)
    (by
      have hh := hcap.2.2.2.2
      norm_num only [show (2:ℝ)*1+1=3 by norm_num] at hh
      intro I hI
      apply hh I
      simpa only [finiteColumns,Finset.mem_image,Fintype.mem_piFinset,inp] using hI)
    hsupp w hwm (fun _=>rfl)
  have hf : ∀a : ℝ,(amplifierCap 2 0 1+2*(3*a))/(3*a/6)=
      (amplifierCap 2 0 1+6*a)/(a/2) := by intro a;ring
  have hd : 3*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper j.val)/3=amp := by
    dsimp only [amp,beta,j];ring
  rw [hd] at hh
  simp only [hf] at hh
  exact hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_geometry_amplification

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineAmplification -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePoolCaps; sha256 7fc16814c21f14f30454e94b8e847998ffbf1478ec4d641b6ce336b23383dc04 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                      

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle61InitialSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
section Affine
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryAffinePoolCapsFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
local notation "V" => CenteredMomentAmplificationChildInput.volume inp


omit [DecidableEq ι] in
/-- Every stored prime or plain factor obeys one fixed polynomial cap,
including when another pool is empty. The threshold absorbs only fixed
support endpoints and precedes all live source parameters. -/
theorem affine_individual_pool_cap (Mmax : ℝ) (hZ : 1< Z)
    (hM : 0≤ M) (hmax : M≤ Mmax) (hb : 0≤ b)
    (hbsZ : max 1 bslot≤ Z) (hbZ : b≤ Z)
    (hw : ∀i,0≤ w i) (hslots : (∑i,w i)≤ M/25)
    (hhi₁ : length Z X₁≤(44/100)*M) (hhi₂ : length Z X₂≤(44/100)*M) :
    ∀j I,I∈(inp).pools j→(I.absNorm:ℝ)≤ Z^(Mmax+1) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hscale := affine_plain_caps rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ Mmax hZ hM hmax hhi₁ hhi₂
  have hpay (X : ℝ) (hx : X≤ Z^Mmax) : b*X≤ Z^(Mmax+1) := by
    calc
      _≤ b*Z^Mmax := mul_le_mul_of_nonneg_left hx hb
      _≤ Z*Z^Mmax := mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg hz.le _)
      _=Z^(Mmax+1) := by
        calc
          Z*Z^Mmax=Z^(1:ℝ)*Z^Mmax := by rw [Real.rpow_one]
          _=Z^(1+Mmax) := (Real.rpow_add hz _ _).symm
          _=Z^(Mmax+1) := by congr 1;ring
  apply actual_completed_pool_cap inp (Z^(Mmax+1))
  · intro i I hI
    change I∈CenteredMomentPrimeSlot.primePool rayM H bslot (Z^(w i)) at hI
    have hn := (Nat.cast_le.mpr (mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1).2).trans
      (Nat.floor_le (by positivity : 0≤ max 1 bslot*Z^(w i)))
    have hi : w i≤∑j,w j := Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)
    have hi' : w i≤ Mmax := by linarith
    calc
      (I.absNorm:ℝ)≤ max 1 bslot*Z^(w i) := hn
      _≤ Z*Z^Mmax := mul_le_mul hbsZ
        (Real.rpow_le_rpow_of_exponent_le hZ.le hi')
        (Real.rpow_nonneg hz.le _) hz.le
      _=Z^(Mmax+1) := by
        calc
          Z*Z^Mmax=Z^(1:ℝ)*Z^Mmax := by rw [Real.rpow_one]
          _=Z^(1+Mmax) := (Real.rpow_add hz _ _).symm
          _=Z^(Mmax+1) := by congr 1;ring
  · rfl
  · rfl
  · exact hpay _ (hscale false 0)
  · exact hpay _ (hscale true 0)
  · exact hpay _ (hscale false 1)
  · exact hpay _ (hscale true 1)
end Affine

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_individual_pool_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePoolCaps -/
