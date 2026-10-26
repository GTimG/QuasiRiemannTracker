/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineCaps
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
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

open Cycle63InitialSource CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyReferenceState
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance affineAmplificationSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable (rayM : Ideal O) [NeZero rayM]
local instance affineAmplificationFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- One scale threshold works for every live subset and all 600 possible
original-width cells. The literal affine source supplies all amplification
gates; no main or error energy estimate is a premise. -/
theorem actual_affine_geometry_amplification
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (loss mesh ξ reserve : ℝ) (hloss : 0<loss)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (hξ : 0≤ξ) (hξcap : ξ≤1) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(hZ : 1<Z)
      (T : Finset α) (η₀ : Character) (θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤mesh) →
      (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta:=Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
      let amp:=Cycle63.Arithmetic.amp beta
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      P.Nonempty ∧ Z^(amp-loss)≤(P.card:ℝ) ∧
      ∀(reflected : Bool) (key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate inp 1 1 Z Z ξ→ℂ) (N : ℕ) (height : ℝ),
      let hK:=zero_lt_one.trans hZ
      let Label:=↥(firstLiveColumns (geometryFirstSource inp 1 1 Z Z ξ hK key) (fun _=>logAnnulus))
      let C:=fun j : Label=>geometryColumnIdeal reflected inp 1 1 Z Z ξ hK key j.val
      let χ:=fun j : Label=>geometryColumnCharacter reflected inp 1 1 Z Z ξ hK key j.val
      let g:=fun j : Label=>geometryBranch reflected inp 1 1 Z Z ξ hK key j.val
      let mass:=fun j : Label=>geometryAllocationWeight reflected inp 1 1 Z Z ξ 1
        (Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)) hK key weight N (9/4) j.val
      ∃τ : (j : Label)→actualAllocations inp.pools (C j)→elementPool P→Fin 3→RayCharacter→Character,
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
      (3*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper j.val)) loss
      0 3 2 0 1 3 (9/4) mesh ξ reserve
      (by have hh:=Cycle63.Arithmetic.amp_pos
            (Cycle63.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2);positivity)
      hloss (by norm_num [amplifierCap]) (by norm_num)
      (by have hh:=(Cycle63.Arithmetic.amp_bounds
            (Cycle63.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2)).1
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
  have hcell:=Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  let j : ↥(Finset.Icc 1 600):=⟨Cycle63.Moment.originalCell (∑i,w i),Finset.mem_Icc.mpr ⟨hcell.1,hcell.2.1⟩⟩
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
  have hd : 3*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper j.val)/3=amp := by
    dsimp only [amp,beta,j];ring
  rw [hd] at hh
  simp only [hf] at hh
  exact hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_geometry_amplification
