/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B109
import Submissions.gao_cycle61_plane_20261013.Bundles.B136
import Submissions.gao_cycle61_plane_20261013.Bundles.B141
import Submissions.gao_cycle61_plane_20261013.Bundles.B142
import Submissions.gao_cycle61_plane_20261013.Bundles.B143
import Submissions.gao_cycle61_plane_20261013.Bundles.B144
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLowFamily; sha256 66e0e5f1e379bf710bf45aa0be183e1f564a130e5b601b8b3aa2f01ef0f9e1a7 -/
section
                                                          
                                               
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _


abbrev GeometryLowFirstIndex (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ)) :=
  (j : firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus)) ×
    actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK bin j.val)

def geometryLowFirstChild (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    Input (liveIndices q.2.val) :=
  child s (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val) t

def geometryLowFirstWeight (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) : ℝ :=
  geometryAllocationWeight reflected s R seed K Z ξ M A hK bin weight (Fintype.card α) b q.1.val q.2/
    volume (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q)

omit [DecidableEq α] in
theorem geometry_low_first_weight_nonneg (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (b t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    0≤ geometryLowFirstWeight reflected s R seed K Z ξ M A hK bin weight b t q :=
  div_nonneg (geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK bin weight
    (Fintype.card α) b q.1.val q.2) (volume_pos _).le


variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Literal first-column/allocation weights contract complete retained low
row sums; common allocations are selected only after the row sum. -/
theorem actual_geometry_low_family_columns
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
    (εshell : ℝ) (heshell : 0<εshell) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
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
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l)
    (∑l,c l*(∑D∈Ds,∑z∈zs l,weight l z*
      ‖normalizedColumn (src l) (q l).E₂ (hE₂ l) (q l).R₂ (divisorSeed l) D z‖^2))≤
      Cg*∑l,c l*((src l).toData.profileFactor*(∏j,(src l).M j)^2*
        QuadraticInitialBound.diagonalControl (st l).radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*((q l).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal l+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
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
  have hc : 0≤ c l := geometry_low_first_weight_nonneg reflected s R seed (Z^Mrow) Z ξ
    Mprice Aprice (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l)
  apply (mul_le_mul_of_nonneg_left hh hc).trans_eq
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_family_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_low_first_weight_nonneg

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLowFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorAdmission; sha256 ae064ae1943cb8e30e7116fbc687f24982ea4163e885a3fd6b1d5881cd200054 -/
section
                                                     
                                                            
                                                        
                                                        
                                                         
                                           
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstMixedRightTransport
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentCompleteCommon
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily RayFourExpansion
open CenteredMomentCommonRawScale CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildSourceCaps CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

section First
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (K Z ξ : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ))
  (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
local notation "src" => geometryFirstSource s R seed K Z ξ hK bin j.1

def geometryErrorOtherIdeal : Ideal O := if reflected then (src).C else (src).D

/-- Reflection transports the actual subset, preserving its prime labels. -/
def geometryErrorInactive : Finset (CommonIndex
    (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
    (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)) :=
  match reflected with
  | false => (src).inactive
  | true => swapSubset (src).C (src).D (src).inactive

omit [DecidableEq α] in
theorem actual_geometry_error_first_support :
    Supported (geometryColumnIdeal reflected s R seed K Z ξ hK bin j) ∧
    Supported (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j) ∧
    primeSupport (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)=
      primeSupport (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j) := by
  cases reflected
  · exact ⟨(src).hC,(src).hD,(src).sameSupport⟩
  · exact ⟨(src).hD,(src).hC,(src).sameSupport.symm⟩

omit [DecidableEq α] in
theorem actual_geometry_error_first_modulus :
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus=
      s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator
        (fun P : CommonIndex (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
          (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)=>P.val)
        (geometryErrorInactive reflected s R seed K Z ξ hK bin j)*
          activeConductor (geometryColumnIdeal reflected s R seed K Z ξ hK bin j)
            (geometryErrorOtherIdeal reflected s R seed K Z ξ hK bin j)} := by
  have hm := actual_geometry_column_modulus reflected s R seed K Z ξ hK bin j
  cases reflected
  · exact hm
  · change _=_*Ideal.span {primeSubsetGenerator (fun P : CommonIndex (src).D (src).C=>P.val)
      (swapSubset (src).C (src).D (src).inactive)*activeConductor (src).D (src).C}
    rw [swapped_modulus_factor]
    exact hm

end First

/-- Full padded-pool coprimality is obtained before extraction. This
gate includes every stored slot, including zero smooth-profile entries. -/
theorem actual_geometry_error_child_coprime
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (s : Input α) (η₀ : Character) (θ : α→ RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z eta ell : ℝ) (hZ : 1≤ Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (hw : ∀j,w j≤ eta)
    (p : O) (hprime : Prime (Ideal.span {p}))
    (hpn : Z^ell≤((Ideal.span {p}).absNorm:ℝ))
    (hgap : max 1 bslot*Z^eta< Z^ell)
    (reflected : Bool) (R seed : Ideal O) (K ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin) :
    ∀j I,I∈(geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).slots j→
      IsCoprime (Ideal.span {p}) I :=
  actual_child_full_slot_coprime s (Ideal.span {p})
    (actual_full_slot_coprime M H hH s η₀ θ w σ freq W bslot Z eta ell hZ hm hw
      (Ideal.span {p}) hprime hpn hgap)
    (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val) t

/-- Literal Chain constructor, with the active extracted allocation lifted
once and the final allocation typed in that exact unpruned dictionary. -/
def errorAdmissionChain (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (η : Character) (t : ℝ)
    (p : O) (hp : p≠0) (i : Fin 3)
    (hc : ∀j I,I∈(child s C R B η t).slots j→ IsCoprime (Ideal.span {p}) I)
    (Bp : actualAllocations (activeInput (child s C R B η t)).pools
      ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations
      (twiceChild s C R B η t (Ideal.span {p}) (errorIndex i+1)
        (errorActiveAllocation (child s C R B η t) _ Bp) υ v).pools E₂) :
    Cycle61FinalError.Chain s :=
  {C₁:=C,R₁:=R,B₁:=B,η₁:=η,t₁:=t,p:=p,hp:=hp,k:=errorIndex i+1,
    hk:=Nat.succ_le_succ (Nat.zero_le (errorIndex i)),coprime:=hc,
    Bp:=errorActiveAllocation (child s C R B η t) _ Bp,υ:=υ,t₂:=v,
    E₂:=E₂,R₂:=R₂,B₂:=B₂}

section Extracted
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (p : O) (i : Fin 3)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
local notation "firstIdeal" => geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
local notation "firstEta" => geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
local notation "firstSrc" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK bin t q
local notation "Qp" => Ideal.span {p}
local notation "errorPower" => errorIndex i+1
variable (Bp : actualAllocations (activeInput
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1)))
  (υ : Character) (v : ℝ)

/-- The extracted child uses the active allocation lifted to the original
first child; it retains the exact prime and one of the three error indices. -/
def geometryErrorChild (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :
    Input (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val) :=
  twiceChild s
    (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t (Ideal.span {p}) (errorIndex i+1)
    (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp) υ v

/-- The literal source radius from the amplification error sum. -/
def geometryErrorSourceRadius : ℝ :=
  let g := geometryBranch reflected s R seed (Z^Mrow) Z ξ hK bin q.1.val
  errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z)
    g.cLog (3*amp) (frequencyLoss Z 32 ξ) reserve p errorPower

def geometryErrorFourierScale : ℝ :=
  (b^N*volume s/(((firstIdeal).absNorm:ℝ)*(normValue p)^errorPower))^2/
    geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i

local notation "extracted" => geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
local notation "rad" => geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
local notation "fourier" => geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i

omit [DecidableEq α] in
theorem actual_geometry_error_source_radius_pos : 0< rad :=
  Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _


/-- All three allocations are the actual tuples. The error extraction
never enlarges the active allocation summation domain. -/
def geometryErrorChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) (hp : p≠0)
    (hc : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v).pools E₂) :
    Cycle61FinalError.Chain s :=
  errorAdmissionChain s
    (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t p hp i hc Bp υ v E₂ R₂ B₂

omit [DecidableEq α] in
theorem actual_geometry_error_chain_fields (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow ξ t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools E₂) :
    let chain:=geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop E₂ R₂ B₂
    chain.C₁=(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ∧ chain.R₁=R ∧ HEq chain.B₁ q.2 ∧ chain.η₁=(geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ∧
      chain.t₁=t ∧ chain.first=(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) ∧ chain.p=p ∧ chain.k=(errorIndex i+1) ∧
      HEq chain.Bp (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp) ∧ chain.υ=υ ∧ chain.t₂=v ∧
      HEq chain.extracted (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ∧ chain.E₂=E₂ ∧ chain.R₂=R₂ ∧ HEq chain.B₂ B₂ :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,HEq.rfl,rfl,rfl,HEq.rfl⟩

/-- The original actual error-source summand equals the exact unpruned
extracted dictionary used by the geometry constructor. -/
theorem actual_geometry_error_active_source (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :
    childNormalizedGaussSource (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)) ((Ideal.span {p})^(errorIndex i+1)) (R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
      q.1.val.2.1.val Bp υ v ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)=
      normalizedGaussSource (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) := by
  exact error_active_twice_source s (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R q.1.val.2.1.val q.2 (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) t
    p i Bp υ v ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)

omit [DecidableEq α] in
theorem actual_geometry_error_radius (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools E₂) :
    Cycle61FinalError.errorRadius
      (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop E₂ R₂ B₂)
      (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val)
      (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val)
      Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N=frequencyRadius (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ := by
  cases reflected
  · rfl
  · let src := geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1
    let A := (b^N*volume s/((src.D.absNorm:ℝ)*(normValue p)^(errorIndex i+1)))^2
    change frequencyRadius (A/errorCommonRadius Z (Real.logb Z (src.C.absNorm:ℝ))
      (nominalLog src.D src.C
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.D src.C=>P.val)
          (swapSubset src.C src.D src.inactive)}) (Z^Mrow) (volume s) Z)
      (Real.logb Z (src.D.absNorm:ℝ)) (3*amp) (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1)) Z ξ=
      frequencyRadius (A/errorCommonRadius Z (Real.logb Z (src.C.absNorm:ℝ))
        (nominalLog src.C src.D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
          (Z^Mrow) (volume s) Z)
        (Real.logb Z (src.D.absNorm:ℝ)) (3*amp) (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1)) Z ξ
    rw [swapSubset_generator,nominalLog_swap]

abbrev GeometryErrorSecondIndex (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ) :=
  ActualSecondBlockIndex (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ

/-- Actual retained second-transform datum, with its finite character
family, original polynomial and exact extracted cutoff. -/
def geometryErrorSecondDatum (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :
    SecondInputDatum (liveIndices q.2.val) :=
  actualSecondBlockDatum (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) n


/-- Blocks canceled by the actual sum are removed before absolute values. -/
def geometryErrorNonzeroBlocks (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) : Finset
    (GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :=
  Finset.univ.filter (fun n=>((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) n).block.value ballProfile≠0)

set_option linter.defProp false in
/-- Literal specialization of the proved nonzero-block filter identity.
The inferred result retains the original dependent finite sum. -/
def actual_geometry_error_nonzero_retained_assembly (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0) :=
  actual_nonzero_retained_assembly
    (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val) (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ ballProfile (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)


def geometryErrorActualChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C)) : Cycle61FinalError.Chain s :=
  geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
    (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R B₂

/-- The admitted geometry is assembled from one actual nonzero physical
block, two supported allocations and the amplification conductor receipt. -/
def geometryErrorActualGeometry (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C))
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).ν ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).W ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).P≠0) :
    Cycle61FinalError.Geometry s
      (geometryErrorActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂)
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b (fixedFactor:ℝ) N :=
  let datum := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val
  {D₁:=geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    hC₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).1,
    hD₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).2.1,
    heq₁:=(actual_geometry_error_first_support reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val).2.2,
    E:=geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    hmod:=actual_geometry_error_first_modulus reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin q.1.val,
    moving_modulus:=actual_error_moving_modulus (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) υ ψ p hp Z hZ i hυ,
    δ:=frequencyLoss Z 32 ξ,reserve:=reserve,homega:=rfl,
    C:=datum.C,D:=datum.D,hC:=datum.hC,hD:=datum.hD,heq:=datum.sameSupport,U:=datum.inactive,
    τ:=datum.τ,family:=datum.family,label:=by
      cases second
      · exact Or.inl rfl
      · exact Or.inr rfl,
    first_nonzero:=hf₁,second_nonzero:=hf₂,
    cols:=datum.block.pool,coefficient:=datum.block.beta,frequencies:=datum.rows,
    profile:=ballProfile,scale:=datum.K,scale_pos:=datum.K_pos,bin:=datum.dyad,
    block_nonzero:=by
      change physicalBlock υ v datum.block.pool datum.block.beta datum.C datum.D
        datum.hC datum.hD datum.inactive
        (Cycle61FinalError.errorRadius
          (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
            (if second then datum.D else datum.C) datum.R B₂)
          (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
          (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
          Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N)
        datum.rows ballProfile datum.K datum.dyad≠0
      rw [actual_geometry_error_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop
        (if second then datum.D else datum.C) datum.R B₂]
      exact (Finset.mem_filter.mp n.property).2}

end Extracted
end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_first_support
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_first_modulus
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_child_coprime
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorChild
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorChain
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_chain_fields
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_active_source
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSecondDatum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_nonzero_retained_assembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorActualChain
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorActualGeometry

#print axioms OAI.SevenEighths.Cycle61InitialMass.errorAdmissionChain
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorNonzeroBlocks
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSourceRadius
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorFourierScale

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorAdmission -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalError.Payment; sha256 4e56afbe961a50ba64aed74a031429e8988712a0558f368d2d72bca5a3738f34 -/
section
                                           
                                                                  

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalError
noncomputable section
open Cycle61.Arithmetic
open HeckeFamily CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open Cycle61FinalErrorCapacity
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
local notation "O" => HeckeFamily.O

def branchReserve (k : ℕ) : ℝ :=
  if k=1 then 32653211/39417600000 else
    if k=6 then 782473823/39417600000 else 60620561/2463600000

theorem paid_branch_exponent {b M width nominal allowance total padding primeWidth : ℝ}
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hb : 3401/100000≤ b ∧ b≤1/25) (hM : 0≤ M)
    (hwidth : width-nominal≤ allowance) (hallow : 0≤ allowance)
    (hprime : 3*(M*amp b)/4≤ primeWidth) (hpadding : 0≤ padding)
    (hcap : total-nominal≤ M*g b+3*(M*amp b)+
      ((k:ℝ)*primeWidth-(if k=6 then 0 else primeWidth))+padding) :
    width+(1/6)*max (total-width) 0 ≤
      nominal+allowance+(k:ℝ)*primeWidth-M*branchReserve k+padding/6 := by
  have he : total-nominal-(width-nominal)=total-width := by ring
  rcases hk with rfl|rfl|rfl
  · have hp := first_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp := sixth_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith
  · have hp := seventh_paid_error_reserve hb hM hwidth hallow hprime hpadding
      (F:=total-nominal) (by norm_num at hcap; linarith)
    rw [he] at hp
    norm_num [branchReserve]
    linarith

#print axioms paid_branch_exponent

theorem normalize_error_energy (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1< Z)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) (E D exponent : ℝ) (hD : 0≤ D)
    (hE : E≤ D*Z^(exponent+errorRemoval p Z k)) :
    localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*E≤ D*Z^exponent := by
  have hz := zero_lt_one.trans hZ
  have hc := localErrorCost_nonneg p (k-1)
  have hs := mul_le_mul_of_nonneg_right (actual_error_weight p hp Z hZ k hk)
    (Real.rpow_nonneg hz.le (errorMoving p Z k))
  rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hs
  calc
    _ ≤ localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*
        (D*Z^(exponent+errorRemoval p Z k)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = D*(localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^exponent := by
      calc
        _ = D*localErrorCost p (k-1)*(Z^(-errorRemoval p Z k+errorMoving p Z k)*
            Z^(exponent+errorRemoval p Z k)) := by ring
        _ = _ := by rw [←Real.rpow_add hz,show -errorRemoval p Z k+errorMoving p Z k+
          (exponent+errorRemoval p Z k)=errorMoving p Z k+exponent by ring,Real.rpow_add hz]; ring
    _ ≤ D*Z^exponent := by nlinarith [mul_le_mul_of_nonneg_left hs hD,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hD) (Real.rpow_nonneg hz.le exponent)]

#print axioms normalize_error_energy
end
end OAI.SevenEighths.Cycle61FinalError

end
/- END ORIGINAL Cycle61.Physical.FinalError.Payment -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalError.Main; sha256 45a5875c39fd493bf9546047d6da090bafa836279765c4d6f5b8e2a4e4f89ba8 -/
section
                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61FinalError
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAmplificationErrorEnergy
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity Cycle61FinalErrorCapacity
open Cycle61Physical.ExtractedBranches
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The genuine extracted retained positive energy, with both common
 allocations and prime extraction paid in the original ambient family.
 Profiles and all moment constants precede the moving physical labels. -/
theorem actual_paid_error_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hJ : 0< J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^L) →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    q.k=1 ∨ q.k=6 ∨ q.k=7 → 3*amp/4≤ Real.logb Z (normValue q.p) →
    ∀g : Geometry s q Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) ∧
    localErrorCost q.p (q.k-1)*Z^(-errorRemoval q.p Z q.k+errorMoving q.p Z q.k)*
      finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth-Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) := by
  have hapret : 0< ap/max 1 bp := div_pos hap (by positivity)
  have hapret' : ap/max 1 bp≤1/4 := (div_le_self hap.le (le_max_left _ _)).trans hap'
  obtain ⟨degree,S,hmain⟩ := actual_global_main_uniform (α:=α) M H hH W A B (ap/max 1 bp) bp
    2 Bmask L lo hi Mcap εold loss margin hA hWs hW hB hapret hapret' hbp (by norm_num)
    hBmask hMcap hεold hloss hmargin hbeta
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := Cycle61FinalProfiles.clipped_pair_control ap bp hap S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg*Cp^2,by positivity,?_⟩
  filter_upwards [hbound,Cycle61FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs J εwidth Mmin (zero_lt_one.trans_le hbs) hJ hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp bp εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp hk hprime g χ hP hPN second L₂ alloc st src δwidth padding p hp₁ hp₂
  dsimp only
  suffices henergy : finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      (Cg*Cp^2)*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) by
    refine ⟨henergy,?_⟩
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    apply normalize_error_energy q.p q.hp Z hZone q.k hk _ _ _ (by positivity)
    have hExp : (g.nominal+δwidth-Mrow*branchReserve q.k+εold+
        loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh)+errorRemoval q.p Z q.k =
      g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
        εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh := by ring
    simpa only [hExp] using henergy
  have hM : 0< Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle61.Moment.originalCell_mem
    (show (17/500:ℝ)≤(∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow≤1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle61.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (Cycle61.Arithmetic.amp_pos hcell)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.C g.D g.hC g.U Z hZone
  have hnominal : g.nominal≤ Mrow := by
    have hm0 := le_max_right (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)+
      2*errorRemoval q.p Z q.k-errorMoving q.p Z q.k) (0:ℝ)
    unfold Geometry.nominal errorNominal
    linarith
  have hwidth : st.width-g.nominal≤δwidth := by
    have ht := error_state_width g Bmask hZone (zero_lt_one.trans_le hbs) hJ χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    dsimp [δwidth]; linarith
  have hδ : 0≤δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0≤ padding := by dsimp [padding]; positivity
  have hs : st.width≤ Mcap := by dsimp [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    let X := Cycle61.Physical.sourcePlainScales src.toSource second
    let U := fun j : Fin 2=>X j/(Ideal.absNorm (selectedPlain L₂ alloc j):ℝ)
    have hU : ∀j,0< U j := fun j=> div_pos (source_plain_positive src second j)
      (zero_lt_one.trans_le (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _
        (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j))))
    have hsurv := allocated_survives src L₂ alloc z (X 0) (X 1)
      (source_plain_positive src second 0) (source_plain_positive src second 1) hzrow
    have hret : ∀j,1≤ U j*bp := by
      intro j; fin_cases j
      · change 1≤ _/ _*bp
        have hs0 := hsurv.1
        change 1≤ _/ _*s.b₁ at hs0
        rw [hsb₁] at hs0
        exact hs0
      · change 1≤ _/ _*bp
        have hs1 := hsurv.2
        change 1≤ _/ _*s.b₂ at hs1
        rw [hsb₂] at hs1
        exact hs1
    let pret := retainedPair ap bp hap p U hU 0
    have hprofile (j : Fin 2) := Cycle61FinalProfiles.actual_clipped_pair ap bp hap p U hU hret j
    have hp0 : dilated s.W₁ (clipDilation (U 0))=pret.profile 0 := by rw [hp₁]; exact (hprofile 0).symm
    have hp1 : dilated s.W₂ (clipDilation (U 1))=pret.profile 1 := by rw [hp₂]; exact (hprofile 1).symm
    have hXcap₁ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 0
    have hXcap₂ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 1
    have htotal := error_source_capacity g hbs hsupper hZone hM
      (fun j=>by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [hsb₁,hsb₂] at htotal
    have hcap : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (9/2)*(∑j∈q.indices L₂ alloc,w j)-g.nominal≤ Mrow*Cycle61.Arithmetic.g cell+3*amp+
        ((q.k:ℝ)*Real.logb Z (normValue q.p)-(if q.k=6 then 0 else Real.logb Z (normValue q.p)))+padding := by
      change _≤ _ at htotal
      dsimp [padding]; unfold errorRemoval errorMoving at htotal; linarith
    have hpaid := paid_branch_exponent q.k hk hcell hM.le hwidth hδ hprime hpadding hcap
    have he := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh hw hwL hmesh (fun j _=>hwm j)
      hσlo hσhi hheight hfreq st rfl hs pret _ _
      (zero_lt_one.trans_le (clippedScale_ge_one _)) (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂
    have hcoef := hcontrol p U hU
    have hpn := Profiles.control_nonneg p Sp
    have hpretn := Profiles.control_nonneg pret S
    have hsq : (pret.control S)^2≤ Cp^2*(p.control Sp)^2 := by nlinarith
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    rw [original_positive_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.τ χ) v
      (internalQ Q η₀) hP hPN g.radius g.C g.D g.U second L₂ alloc,hp0,hp1]
    apply he.trans
    have hpow := Real.rpow_le_rpow_of_exponent_le hZone.le
      (show st.width+εold+loss*(Fintype.card α:ℝ)+(1/6)*max
        (length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
          (9/2)*(∑j∈q.indices L₂ alloc,w j)-st.width) 0+(3/4)*mesh ≤
          g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
            εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh by
        unfold errorRemoval; linarith)
    calc
      _ ≤ Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p.control Sp)^2)*
        (1+|v|+height)^degree*Z^_ := mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity))
          hpow (Real.rpow_nonneg (zero_le_one.trans hZone.le) _) (by positivity)
      _ = _ := by ring
  · have hzrow : ∀z,Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [no_surviving_row_energy_zero src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms actual_paid_error_uniform
end
end OAI.SevenEighths.Cycle61FinalError

end
/- END ORIGINAL Cycle61.Physical.FinalError.Main -/
