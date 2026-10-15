/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B090
import Submissions.gao_cycle61_plane_20261013.Bundles.B108
import Submissions.gao_cycle61_plane_20261013.Bundles.B109
import Submissions.gao_cycle61_plane_20261013.Bundles.B135
import Submissions.gao_cycle61_plane_20261013.Bundles.B139
import Submissions.gao_cycle61_plane_20261013.Bundles.B140
import Submissions.gao_cycle61_plane_20261013.Bundles.B149
import Submissions.gao_cycle61_plane_20261013.Bundles.B165
import Submissions.gao_cycle61_plane_20261013.Bundles.B166
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected; sha256 be241fbb522f224b5369ce0bac86646f5ea5951f8b16ac38076337fcfb4385e4 -/
section
                                                            
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowSelectedDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The literal child and all Mellin height shifts retain a fixed four-power
profile bound, chosen before the source labels and allocations. -/
theorem actual_child_low_profile_factor {ι : Type*}[Fintype ι]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤ Cs)(hbp : 1≤ bp)
    (s : Input ι)(hn : Fintype.card ι≤ N)(hM : ∀i,s.M i≤ Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)
    (C R : Ideal O)(alloc : actualAllocations s.pools C)(χ τ : Character)(t v : ℝ) :
    let src := withHeight (child s C R alloc χ t) τ v
    src.toData.profileFactor*(∏i,src.M i)^2≤2*bp^2*Cs^(4*N) := by
  intro src
  have hm : mass s≤ Cs^N := by
    apply le_trans (Finset.prod_le_prod₀
      (fun i (_ : i∈Finset.univ)=>zero_le_one.trans (s.M_ge_one i)) (fun i _=>hM i))
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hCs hn
  have hc : mass (child s C R alloc χ t)≤ Cs^N := (child_mass s C R alloc χ t).trans hm
  have hc0 := mass_nonneg (child s C R alloc χ t)
  have hp := pow_le_pow_left₀ hc0 hc 4
  have heq : src.toData.profileFactor*(∏i,src.M i)^2=
      2*bp^2*mass (child s C R alloc χ t)^4 := by
    change (2*(max 1 s.b₁*max 1 s.b₂))*(∏i:liveIndices alloc.val,s.M i.val)^2*
      (∏i:liveIndices alloc.val,s.M i.val)^2=_
    rw [hb₁,hb₂,max_eq_right hbp]
    dsimp only [mass,child,commonData]
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*bp^2)
  simpa only [←pow_mul,Nat.mul_comm] using hh

/-- Fixed source-profile factors are extracted from the genuine low analytic estimate. -/
theorem actual_low_fixed_profile_columns
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
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤ pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0≤ Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1≤ Z^L) →
    let hQM' : st.fixedModulus≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤ weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*(2*b^2*Cs^(4*N))*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad := by
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
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
    hMmin hω hξ hMcap' hzslot haff q cell amp g χ hP hPN st src nominal δwidth padding
    seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps hQM' hQη low zs weight hnonneg hkeep hweight
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
    hMmin hω hξ hMcap' hzslot haff q g χ hP hPN seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps zs weight hnonneg hkeep hweight
  have hprofile : src.toData.profileFactor*(∏j,src.M j)^2≤2*b^2*Cs^(4*N) :=
    actual_child_low_profile_factor N Cs b hCs hb s hcard hmass hsb₁ hsb₂ q.C₁ q.R₁ q.B₁
      q.η₁ (g.datum.τ χ) q.t₁ v
  let R := QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
    Z^(nominal+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hR : 0≤ R := by dsimp only [R]; positivity
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprofile hCg.le) hR
  apply hh.trans
  convert hbnd using 1 <;> dsimp only [R] <;> ring

theorem actual_low_label_normalizer (C D : Ideal O)(U : Finset (CommonIndex C D))
    (l : FirstSourceLabel)(hc : C=l.1.1)(hd : D=l.1.2)(hu : HEq U l.2.val) :
    normalizer C D U=normalizer l.1.1 l.1.2 l.2.val := by
  subst C; subst D
  rw [eq_of_heq hu]

theorem actual_low_label_nominal (Mrow Z amp omega : ℝ)(C₁ D₁ C D : Ideal O)
    (U : Finset (CommonIndex C D))(l : FirstSourceLabel)
    (hc : C=l.1.1)(hd : D=l.1.2)(hu : HEq U l.2.val) :
    secondNominal Mrow Z amp omega C₁ D₁ C D U=
      secondNominal Mrow Z amp omega C₁ D₁ l.1.1 l.1.2 l.2.val := by
  subst C; subst D
  rw [eq_of_heq hu]

/-- The selected scalar is the original first-column mass. Its physical
D factor is retained on both orientations, before any second-row sum. -/
theorem actual_geometry_low_uniform_mass {ι : Type}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(N : ℕ)(lo ap : ℝ)(hlo : 0< lo)(hap : 0< ap)
    (s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D Z ξ B ε side : ℝ)
    (hZ : 1< Z)(hK : 0< Z^D)(hε : 0≤ε)(hcard : Fintype.card ι≤ N)(hlower : lo≤ s.lower)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
    (hside : side≤ geometryHighSide reflected (Real.logb Z (volume s))
      (geometryExponents s R seed (Z^D) Z ξ j.1.val)) :
    geometryFirstHighMass reflected s R seed W D Z ξ ε hK bin j≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*ε-side) := by
  have hz : 0< Z:=zero_lt_one.trans hZ
  have hh:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z ξ B ε
    hZ hK hε hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  have hfactor : 0≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin := by
    cases reflected <;> simp only [geometryHighFactor,ite_true,ite_false]
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
    · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
  apply hh.trans
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le hside
  have hm:=div_le_div_of_nonneg_left
    (mul_nonneg hfactor (Real.rpow_nonneg hz.le (B*ε))) (Real.rpow_pos_of_pos hz side) hp
  simpa only [Real.rpow_sub hz,div_eq_mul_inv,mul_assoc,
    CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hm


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_low_profile_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_fixed_profile_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_uniform_mass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected -/
