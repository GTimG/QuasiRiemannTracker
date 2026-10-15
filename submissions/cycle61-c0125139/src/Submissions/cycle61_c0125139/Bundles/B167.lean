/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B090
import Submissions.cycle61_c0125139.Bundles.B108
import Submissions.cycle61_c0125139.Bundles.B109
import Submissions.cycle61_c0125139.Bundles.B135
import Submissions.cycle61_c0125139.Bundles.B139
import Submissions.cycle61_c0125139.Bundles.B140
import Submissions.cycle61_c0125139.Bundles.B149
import Submissions.cycle61_c0125139.Bundles.B165
import Submissions.cycle61_c0125139.Bundles.B166
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
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤21/25 →
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
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
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
    Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
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

private theorem low_scalar_product_transport
    (coef base diagonal control height norm shell power padding : ℝ)
    (coef' diagonal' norm' power' : ℝ)
    (hc : coef=coef')(hd : diagonal=diagonal')(hn : norm=norm')
    (hp : power*padding=power') :
    coef*(base*diagonal*control*height*norm*shell*power*padding)=
      base*diagonal'*control*height*shell*coef'*norm'*power' := by
  rw [hc,hd,hn]
  calc
    _=(base*diagonal'*control*height*shell*coef'*norm')*(power*padding) := by ring
    _=_ := congrArg (fun x : ℝ=>(base*diagonal'*control*height*shell*coef'*norm')*x) hp

set_option maxHeartbeats 200000 in
/-- Complete selected low frequency columns are paid by the actual finite supported label budget. -/
theorem actual_selected_low_paid_columns {α : Type} [Fintype α] [DecidableEq α]
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
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→ FirstSourceLabel)
      (hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→ actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤ Tfirst → p≤ Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤ Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→ LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→ RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤ pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤ Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤ Z^L) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→ Finset O)(weight : rows→ O→ℝ),(∀r,∀z∈zs r,0≤ weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0≤ physical → (∀l,0≤ mass l) →
      (∀l,mass l≤ physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*Mrow+ξ/2-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) := by
  let hbase := actual_low_fixed_profile_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  let hpbase := eventual_actual_selected_low_second_paid
    N supply εv Bnorm εlabels hsupply hev hBnorm hel
  let K₀ := Classical.choose hpbase
  let hpspec := Classical.choose_spec hpbase
  have hK₀ : 0< K₀ := hpspec.1
  let hpaid := hpspec.2
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hcbase := hcolumn η₀ Q hQM hQ0 hQt hQ72
  let C := Classical.choose hcbase
  let hcspec := Classical.choose_spec hcbase
  have hC : 0< C := hcspec.1
  let hbound := hcspec.2
  refine ⟨C*K₀,mul_pos hC hK₀,?_⟩
  filter_upwards [hbound,hpaid] with Z hz hzpaid
  refine ⟨hzpaid.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
    hMmin hω hξ hMcap' hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight mass physical loss hphysical hmass0 hmasscap c error
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  let pay := fun r : rows=>Z^(-amp)*
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
    (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
      ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
    Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val+amp+error)
  let fixed := (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(2*T)^(3*εshell)
  have hfixed : 0≤ fixed := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
    dsimp only [fixed]; positivity
  have hpoint (r : rows) : c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)≤
      C*fixed*(physical*Z^(loss+amp))*pay r := by
    have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
      hMmin hω hξ hMcap' hzslot haff (q r) (g r) (χ r) (hP r) (hPN r)
      (divisorSeed r) (hE₂ r) (hdivisor r) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow r) (hcaps r)
      (zs r) (weight r) (hnonneg r) (hkeep r) (hweight r)
    have hc : 0≤ c r := by
      dsimp only [c]
      exact mul_nonneg (mul_nonneg (div_nonneg (hmass0 _) (CenteredMomentAmplificationChildInput.volume_pos _).le)
        (g r).datum.K_pos.le) (normalizer_pos _ _ (g r).datum.hC _).le
    have h := mul_le_mul_of_nonneg_left hh hc
    have hcancel : Z^amp*Z^(-amp)=(1:ℝ) := by rw [←Real.rpow_add hZ0]; simp
    have hscale : mass r.val.1*Z^amp≤ physical*Z^(loss+amp) := by
      simpa only [Real.rpow_add hZ0,mul_assoc] using mul_le_mul_of_nonneg_right (hmasscap r.val.1)
        (Real.rpow_nonneg hZ0.le amp)
    have hpay0 : 0≤ pay r := by
      dsimp only [pay]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (div_nonneg (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _).le (CenteredMomentAmplificationChildInput.volume_pos _).le))
        (mul_nonneg (normalizer_pos _ _ ((hC₂ r) ▸ (g r).datum.hC) _).le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ0.le _)
    have heq' : c r*(C*(2*b^2*Cs^(4*N))*
      QuadraticInitialBound.diagonalControl (st r).radial.profile*(p₀.control Sp)^2*
      (1+|v|+height)^degree*((q r).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
      Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
        (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-Mrow*(7/30000000)+εold+
        2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)*Z^pad)=
      C*fixed*(mass r.val.1*Z^amp)*pay r := by
      have hpayeq : (mass r.val.1*Z^amp)*pay r=
          mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error) := by
        dsimp only [pay]
        calc
          _=(Z^amp*Z^(-amp))*(mass r.val.1*
              (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
              (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
                ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
              Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
                (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
                (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
                (label r).1.1 (label r).1.2 (label r).2.val+amp+error)) := by ring
          _=_ := by rw [hcancel]; ring
      have hnom : secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive=
          secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val := by
        have hback:=actual_low_label_nominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive (label r) (hC₂ r) (hD₂ r) (hU₂ r)
        have hfront:=congrArg₂ (fun C₁ D₁ : Ideal O=>
          secondNominal Mrow Z amp omega C₁ D₁ (label r).1.1 (label r).1.2 (label r).2.val)
          (hC₁ r) (hD₁ r)
        have homega:=congrArg (fun omega : ℝ=>secondNominal Mrow Z amp omega
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val) hωeq
        exact hback.trans (hfront.trans homega)
      have hnormal := actual_low_label_normalizer _ _ _ _ (hC₂ r) (hD₂ r) (hU₂ r)
      have hnorm := congrArg (fun I : Ideal O=>(I.absNorm:ℝ)^(εshell-1)) (hEeq r)
      have hrad : (st r).radial.profile=ballProfile := rfl
      have hexp : secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*Mrow+ξ/2)+amp-Mrow*(7/30000000)+εold+
        2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*
        (omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad=
        secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+amp+
        (εwidth*Mrow+ξ/2-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
        (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad) := by ring
      have hpower := (Real.rpow_add hZ0
        (secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*Mrow+ξ/2)+amp-Mrow*(7/30000000)+εold+
          2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*
          (omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh) pad).symm
      have hpowerExact := hpower.trans (congrArg (fun exponent : ℝ=>Z^exponent) hexp)
      have hnomPower:=congrArg (fun nominal : ℝ=>Z^(nominal+(εwidth*Mrow+ξ/2)+amp-
        Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
        (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)) hnom
      have hpowerSource: Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-
          Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)*Z^pad=
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error) :=
        (congrArg (fun x : ℝ=>x*Z^pad) hnomPower).trans hpowerExact
      have hcoef : c r=mass r.val.1/volume (childSrc r.val.1)*
          firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)*
          normalizer (label r).1.1 (label r).1.2 (label r).2.val :=
        congrArg₂ (fun K normal : ℝ=>mass r.val.1/volume (childSrc r.val.1)*K*normal)
          (hKeq r) hnormal
      have hdiag:=congrArg QuadraticInitialBound.diagonalControl hrad
      have htrans:=low_scalar_product_transport (c r) (C*(2*b^2*Cs^(4*N)))
        (QuadraticInitialBound.diagonalControl (st r).radial.profile) ((p₀.control Sp)^2)
        ((1+|v|+height)^degree) (((q r).E₂.absNorm:ℝ)^(εshell-1)) ((2*T)^(3*εshell))
        (Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
          (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-Mrow*(7/30000000)+εold+
          2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh))
        (Z^pad) _ _ _ _ hcoef hdiag hnorm hpowerSource
      calc
        _=_ := htrans
        _=C*fixed*(mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error)) := by dsimp only [fixed]; ring
        _=_ := (congrArg (fun x : ℝ=>C*fixed*x) hpayeq).symm.trans (by ring)
    have hfull := h.trans_eq heq'
    exact hfull.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (mul_nonneg hC.le hfixed)) hpay0)
  have hpays := hzpaid.2 s hcard hsupply' reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    R seed K Tsec ξ Mrow amp reserve error εshell hseed hw₁ hw₂ heshell.le hsource
    Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
    rows hU box hbox
  calc
    _≤∑r,C*fixed*(physical*Z^(loss+amp))*pay r := Finset.sum_le_sum (fun r _=>hpoint r)
    _=(C*fixed*(physical*Z^(loss+amp)))*(∑r,pay r) := by rw [Finset.mul_sum]
    _≤(C*fixed*(physical*Z^(loss+amp)))*
      ((box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ))) :=
      mul_le_mul_of_nonneg_left hpays (by positivity)
    _=_ := by
      have hzproduct:=Real.rpow_add hZ0 (loss+amp) (p+exponent+error+εv+Bnorm*εshell+εlabels)
      have headd : (loss+amp)+(p+exponent+error+εv+Bnorm*εshell+εlabels)=
          loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels := by ring
      rw [headd] at hzproduct
      have hscalar:=congrArg (fun x : ℝ=>
        C*fixed*(box.card:ℝ)*physical*K₀*x/(seed₀.absNorm:ℝ)) hzproduct
      calc
        _=C*fixed*(box.card:ℝ)*physical*K₀*
            (Z^(loss+amp)*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels))/(seed₀.absNorm:ℝ) := by ring
        _=C*fixed*(box.card:ℝ)*physical*K₀*
            Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) := hscalar.symm
        _=_ := by dsimp only [fixed]; ring

/-- The payment dictionary uses the literal first label and original second
block, independently of any frequency in its low column sum. -/
theorem actual_geometry_low_paid_fields
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1< Z)(bin : ℤ×(Fin 5→ℤ))
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j)
    (hU : n.2.1∈inactiveSubsets n.1.val.val.1 n.1.val.val.2)
    (second : Bool)
    (B₂ : actualAllocations
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t j).pools
      (if second then (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).D
        else (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).C))
    (r : secondLiveRows (fun _:Unit=>
      (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).block))
    (hf₁ : frozenCoefficient j.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.val) R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val
      (if second then (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).D
        else (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).C)
      (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n).R
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t j).ν
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t j).W
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t j).P≠0) :
    let q:=geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n second B₂
    let g:=geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n second B₂ r hf₁ hf₂
    let first:=geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.val
    let label:=actualSecondSupportedLabel
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t j)
      (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.val) j.1.val.2.1.val
      (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve first)
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first)
      Z ξ n hU
    q.C₁=(if reflected then first.1.2 else first.1.1) ∧
    g.D₁=(if reflected then first.1.1 else first.1.2) ∧
    g.datum.C=label.1.1 ∧ g.datum.D=label.1.2 ∧ HEq g.datum.inactive label.2.val ∧
    q.E₂=(if second then label.1.2 else label.1.1) ∧
    g.datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve first := by
  intro q g first label
  exact ⟨rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl⟩

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option maxHeartbeats 400000 in
set_option linter.defProp false in
def actual_geometry_selected_low_paid_columns {α : Type} [Fintype α] [DecidableEq α]
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
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass) :=
  let hbase := actual_selected_low_paid_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
    supply εv Bnorm εlabels hsupply hev hBnorm hel
  let degree:=Classical.choose hbase
  let hd:=Classical.choose_spec hbase
  let Sp:=Classical.choose hd
  let hcolumn:=Classical.choose_spec hd
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc:=hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg:=Classical.choose hc
    let hg:=Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (heightV height mesh aLow : ℝ)(i : ℕ) hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
        hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
        (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap' hzslot haff
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        fun hf heq
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          hsource (Tfirst p exponent : ℝ) hTfirst hp hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
          (rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (Rchild l) (seed l)
            (K l) (Tsec l) Z ξ))
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ℤ)) hbox=>
        let datum:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        fun (B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0)=>
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        let fields:=fun r : rows=>actual_geometry_low_paid_fields reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 (hU r.val r.property)
          second (B₂ r) (rwitness r) (hf₁ r.val.1) (hf₂ r)
        let hrow:=hz.2 hZ s θ w σ freq heightV height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
          hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
          Mrow (frequencyLoss Z 32 ξ+reserve) ξ hMmin hω hξ hMcap' hzslot haff
          reflected second first hf heq R (fun l=>(firstIndex l).2)
          (fun l=>geometryColumnCharacter reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
          (fun _=>t) hf₁ Rchild seed K Tsec reserve
          (fun l=>actual_first_live_squarefree
            (geometryFirstSource s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
            (fun _=>logAnnulus) (firstIndex l).1.val (firstIndex l).1.property)
          (fun _=>hw₁) (fun _=>hw₂) hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed
          hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
          (fun r=>(fields r).1) (fun r=>(fields r).2.1) (fun r=>(fields r).2.2.1)
          (fun r=>(fields r).2.2.2.1) (fun r=>(fields r).2.2.2.2.1)
          (fun r=>(fields r).2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2) rfl
        fun χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
          zs weight hnonneg hkeep hweight (Ψ : 𝓢(ℝ,ℂ)) hsourceOriginal hplain₁ hplain₂
          (sideLower : ℝ)
          (hside : ∀l,sideLower≤ geometryHighSide reflected (Real.logb Z (volume s))
            (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))=>
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let hphysical : 0≤ physical := by
          cases reflected <;> simp only [physical,geometryHighFactor,ite_true,ite_false]
          · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
          · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
        hrow χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
          zs weight hnonneg hkeep hweight firstMass physical (Bmass*εmass-sideLower) hphysical
          (fun l=>geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
          (fun l=>actual_geometry_low_uniform_mass reflected N supply ap hsupply hap s R seed₀ Ψ
            Mrow Z ξ Bmass εmass sideLower hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hemass
            hcard hsupply' hs₀ hw₁ hw₂ hsourceOriginal hplain₁ hplain₂ bin (firstIndex l).1.val (hside l))))))))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_low_profile_factor

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_fixed_profile_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_low_paid_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_paid_fields

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_low_paid_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_uniform_mass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalPayment; sha256 120f2436be1c84fdf2bbfb54db732694f1d5cdc48ec8123695a27d0aae5157c5 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                
                                                          
                                                                   
                                                           
                                                        

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open Cycle61Moment CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentRankinRadical ActualEisensteinCubic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance errorPhysicalPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The extracted scalar is positive before any ordinary-row restriction. -/
theorem extracted_error_label_scalar_nonneg (reflected second : Bool)(l v : FirstSourceLabel)
    (Z M a δ reserve error εcommon V Vextract : ℝ)(p : O)(k : ℕ)
    (hZ : 0≤ Z)(hV : 0< Vextract)(hv : Supported v.1.1) :
    0≤ extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V Vextract p k := by
  unfold extractedErrorLabelScalar
  apply mul_nonneg
  · apply mul_nonneg
    · unfold firstErrorTailRadius errorCommonRadius
      exact div_nonneg (Real.rpow_nonneg hZ _) hV.le
    · exact mul_nonneg (normalizer_pos _ _ hv _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact Real.rpow_nonneg hZ _

private theorem error_actual_label_scalar_sum_nonneg {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(hs : Squarefree seed)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(reflected second : Bool)(l : FirstSourceLabel)
    (Z M a δ reserve error εcommon V : ℝ)(p : O)(k : ℕ)(hZ : 0≤ Z) :
    0≤∑v∈actualSecondLabels s R seed,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V (volume s) p k := by
  apply Finset.sum_nonneg
  intro v hv
  exact extracted_error_label_scalar_nonneg reflected second l v Z M a δ reserve error εcommon
    V (volume s) p k hZ (volume_pos s)
    (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).1

private theorem error_menu_nonneg {Menu : Type*}[Fintype Menu]
    (cost : Menu→ℝ)(hc : ∀m,0≤ cost m) : 0≤∑m,cost m :=
  Finset.sum_nonneg (fun m _=>hc m)

private theorem error_weighted_prime_cost {Label PrimeIndex : Type*}
    [Fintype Label][Fintype PrimeIndex]
    (mass : Label→ℝ)(cost : PrimeIndex→ Fin 3→ RayCharacter→ Label→ℝ)
    (outside F : ℝ)(branch : Fin 3→ℝ)
    (hout : 0≤ outside)(hb : ∀i,0≤ branch i)
    (hc : ∀q i ψ j,0≤ cost q i ψ j)(hm : ∀j,mass j≤ F) :
    outside*(∑q,∑i,branch i*∑j,∑ψ,mass j*cost q i ψ j)≤
      F*(outside*(∑q,∑i,branch i*∑j,∑ψ,cost q i ψ j)) := by
  calc
    _≤ outside*(∑q,∑i,branch i*∑j,∑ψ,F*cost q i ψ j) := by
      apply mul_le_mul_of_nonneg_left _ hout
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hb i)
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun ψ _=>mul_le_mul_of_nonneg_right (hm j) (hc q i ψ j))
    _=_ := by
      have h (q : PrimeIndex)(i : Fin 3) :
          branch i*(∑j,∑ψ,F*cost q i ψ j)=F*(branch i*∑j,∑ψ,cost q i ψ j) := by
        simp only [←Finset.mul_sum]
        ring
      simp_rw [h]
      simp only [←Finset.mul_sum]
      ring

/-- The first-bin mismatch is a fixed factor sixteen, not a new power loss. -/
theorem error_physical_bin_exponent_payment (Z F K seedNorm B εmass p exponent side M : ℝ)
    (hZ : 1< Z)(hF : 0≤ F)(hK : 0≤ K)(hs : 0≤ seedNorm)
    (hbin : p+exponent-side≤4*Real.logb Z 2) :
    (F*Z^(B*εmass-side))*(K*Z^(p+exponent-M*(7/60000000))/seedNorm)≤
      16*F*K*Z^(B*εmass-M*(7/60000000))/seedNorm := by
  have hz : 0< Z:=zero_lt_one.trans hZ
  have he : B*εmass-side+(p+exponent-M*(7/60000000))≤
      4*Real.logb Z 2+(B*εmass-M*(7/60000000)) := by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(F*K/seedNorm)*Z^(B*εmass-side+(p+exponent-M*(7/60000000))) := by
      rw [Real.rpow_add hz];ring
    _≤(F*K/seedNorm)*Z^(4*Real.logb Z 2+(B*εmass-M*(7/60000000))) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg (mul_nonneg hF hK) hs)
    _=_ := by rw [Real.rpow_add hz,geometry_low_bin_slack_payment Z hZ];ring

/-- Actual first columns provide all support, seed, and norm gates. -/
theorem actual_error_first_label_gates {ι : Type}[Fintype ι][DecidableEq ι]
    (s : Input ι)(R seed : Ideal O)(K Z ξ B : ℝ)(hK : 0< K)
    (hs : Squarefree seed)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    (Supported l.1.1 ∧ Supported l.1.2) ∧
      primeSupport l.1.1=primeSupport l.1.2 ∧
      (seed∣l.1.1 ∧ seed∣l.1.2) ∧
      ((l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) := by
  intro l
  have hc:=actual_common_gates s R seed hs hw₁ hw₂ j.1.val.1.val.1 j.1.val.1.val.2 j.1.val.1.property
  have hh:=commonLabels_supported
    (CenteredMomentActiveSource.activeSource
      (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ j.1.val.1.property
  exact ⟨hh,hc.2.2.1,⟨hc.2.2.2.1,hc.2.2.2.2.1⟩,
    ⟨hc.2.2.2.2.2.1.trans hsource,hc.2.2.2.2.2.2.trans hsource⟩⟩

/-- One literal extracted packet before its prime/ray/first-column sum.
The first allocation is stored on the original first index. -/
def geometryErrorPhysicalScalarPacket {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(υ : Character)(vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ) : ℝ :=
  let C:=if reflected then l.1.2 else l.1.1
  let u:=child s C R B₁ χ t
  let Q:=Ideal.span {q}
  let R₂:=(R*C)*Q^k
  ∑Bp : errorLiftedActiveAllocations u Q k,
    let source:=child u (Q^k) (R*C) Bp.val υ vheight
    ∑v∈actualSecondLabels source R₂ L,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
        (volume s) (volume source) q k

/-- Inverse-key selection is exactly the original packet when the actual
extracted character is independent of the active Bp allocator. -/
theorem selected_error_physical_scalar_packet_at {ι Label : Type}[Fintype ι][Fintype Label]
    (s : Input ι)(reflected second : Bool)(first : Label→ FirstSourceLabel)
    (projector : Label→ Ideal O)(hinj : Function.Injective (fun j=>(first j,projector j)))
    (alloc : (j : Label)→ actualAllocations s.pools
      (if reflected then (first j).1.2 else (first j).1.1))
    (R : Ideal O)(χ υ : Label→ Character)(t vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ)(j : Label) :
    let e:=selectedLowFirstPairEquiv first projector hinj
    let pair:=e j
    geometryErrorPhysicalScalarPacket s reflected second pair.1.val pair.2.val R
      (selectedErrorAllocation s reflected first projector hinj alloc pair)
      (χ (e.symm pair)) t (υ (e.symm pair)) vheight q k Z M a δ reserve error εcommon=
    geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R (alloc j)
      (χ j) t (υ j) vheight q k Z M a δ reserve error εcommon := by
  intro e pair
  change geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R
    (selectedErrorAllocation s reflected first projector hinj alloc (selectedLowFirstPair first projector j))
    (χ (e.symm (e j))) t (υ (e.symm (e j))) vheight q k Z M a δ reserve error εcommon=_
  rw [Equiv.symm_apply_apply,selected_error_allocation_at]

/-- Literal mass-weighted extracted scalar sum on a common FIRST-projector
shell. Its source menu retains the original occupied-key allocator. -/
def ErrorPhysicalShellBound (N : ℕ)(lo ap εv B ε b bs Mmin εaffine K Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(_hcard : Fintype.card ι≤ N)(_hlower : lo≤ s.lower)
      (_hend : Endpoints b bs bs s)(_hvolume : volume s≤ Z^B)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (_hM : Mmin≤ M)(_hecommon : 0≤εcommon)(_hemass : 0≤εmass)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)(_hsource : sourceRadius s≤ Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(_hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→ FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
        (column j).2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
      (_hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
      (χ : Label→ Character)(t T : ℝ)(_hT : 1≤ T)
      (_hprojector : ∀j,Squarefree (column j).2.1.val)
      (_hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T),
    let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
    let projector:=fun j=>(column j).2.1.val
    let labels:=selectedLowFirstLabels first
    let Ds : labels→ Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→ Ds l→ actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→ Ds l→ Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    ∀(P : Finset (Ideal O))(_hP : P.Nonempty)(_hprime : ∀Q∈P,Prime Q)
      (_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I),
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→ Bps l D q i→ Character)(vheight : ℝ),
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (R*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (R*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
      let pair:=e j
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
    let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)
    (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,mass j*cost q i ψ j)≤
      16*F*K*Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ)

private def error_eventual_predicate {P : ℝ→ Prop} (_ : ∀ᶠZ : ℝ in atTop,P Z) : ℝ→ Prop := P

set_option maxHeartbeats 1200000 in
set_option linter.defProp false in
/-- Saved extracted-prime payment with literal original first-column mass.
The inverse occupied-key map retains each selected allocation. The FIRST
projector is the SECOND seed; the original outer seed is unchanged. -/
def eventual_actual_error_physical_shell_payment
    (N : ℕ)(lo ap εv B ε b bs : ℝ)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(Mmin εaffine : ℝ)(hMmin : 0< Mmin) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
      2≤ Z ∧ ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z :=
  let hBplus : 0≤ B+1:=by linarith
  let data:=eventual_actual_error_dependent_saved_payment N lo εv (B+1) ε
    hlo hev hBplus he Mmin εaffine hMmin
  let K:=Classical.choose data
  let hKscalar : 0< K:=(Classical.choose_spec data).1
  let saved:=eventual_actual_selected_error_saved_payment N lo εv (B+1) ε
    hlo hev hBplus he Mmin εaffine hMmin
  let cap:=eventual_geometry_error_child_source_cap N b bs (1/2) hb hbs (by norm_num)
  let combined:=saved.2.and cap
  let pointwise : ∀Z,error_eventual_predicate combined Z →
      2≤ Z ∧ ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z :=
    fun (Z : ℝ)(hz : error_eventual_predicate combined Z)=>And.intro hz.1.1 (
    fun {ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(hcard : Fintype.card ι≤ N)(hlower : lo≤ s.lower)
      (hend : Endpoints b bs bs s)(hvolume : volume s≤ Z^B)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (hM : Mmin≤ M)(hecommon : 0≤εcommon)(hemass : 0≤εmass)
      (hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hsource : sourceRadius s≤ Z^B)
      (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→ FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
        (column j).2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
      (hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
      (χ : Label→ Character)(t T : ℝ)(hT : 1≤ T)
      (hprojector : ∀j,Squarefree (column j).2.1.val)
      (hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T)=>
    let hZ : 1< Z:=by linarith [hz.1.1]
    let hZ0 : 0< Z:=zero_lt_one.trans hZ
    let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
    let projector:=fun j=>(column j).2.1.val
    let A:=Real.logb Z (volume s)
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let pBin:=((bin.2 2:ℝ)+1)*w
    let p:=min (B+1) pBin
    let exponent:=A-(bin.2 c:ℝ)*w+((bin.2 3:ℝ)+1)*w+((bin.2 4:ℝ)+1)*w
    let side:=(bin.2 2:ℝ)*w+A-((bin.2 c:ℝ)+1)*w+(bin.2 3:ℝ)*w+(bin.2 4:ℝ)*w
    let hbin : p+exponent-side≤4*Real.logb Z 2:=by
      have hp : p≤ pBin:=min_le_right _ _
      have hg : pBin+exponent-side=4*w:=by dsimp only [pBin,exponent,side];ring
      linarith
    let gates:=actual_geometry_low_bin_scalar_gates s R seed (Z^M) Z ξ B A hK hZ hs hw₁ hw₂ hsource bin reflected
    let firstG:=fun j=>actual_error_first_label_gates s R seed (Z^M) Z ξ B hK hs hw₁ hw₂ hsource bin (column j)
    let hnplus : ∀j,((first j).1.1.absNorm:ℝ)≤ Z^(B+1) ∧ ((first j).1.2.absNorm:ℝ)≤ Z^(B+1):=
      fun j=>And.intro ((firstG j).2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
        ((firstG j).2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
    let hrad : ∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤ Z^p:=by
      intro j
      rcases le_total (B+1) pBin with hp | hp
      · dsimp only [p]
        rw [min_eq_left hp]
        have h:=actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hw₁ hw₂ hsource (column j).1.val 2
        exact h.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      · dsimp only [p]
        rw [min_eq_right hp]
        exact (gates.2 (column j)).1
    let pay:=hz.1.2 s hcard hlower reflected second T p exponent error εcommon M a δ reserve
      hT (min_le_left _ _) hecommon hM hloss seed hs hs0 first projector hinj
      (fun j=>(firstG j).1) (fun j=>(firstG j).2.1) (fun j=>(firstG j).2.2.1)
      hnplus hrad (fun j=>(gates.2 (column j)).2.1) hprojector hdyad R alloc χ t hf hw₁ hw₂
    let labels:=selectedLowFirstLabels first
    let Ds : labels→ Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→ Ds l→ actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→ Ds l→ Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    fun (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
      (hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I)=>
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    fun (υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→ Bps l D q i→ Character)(vheight : ℝ)=>
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (R*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (R*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    let hchildslot:=fun (l : labels)(D : Ds l)(q : elementPool P)=>actual_child_full_slot_coprime s (Ideal.span {q.val})
      (hslot q) (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    let hsource' : ∀l D q i ψ Bp,sourceRadius (source l D q i ψ Bp)≤ Z^(B+1):=by
      intro l D q i ψ Bp
      have hc:=hz.2.2 s B hcard hend hvolume
        (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
        (selected_error_allocation_nonzero s reflected first projector hinj alloc R hf ⟨l,D⟩)
        q.val (elementPool_data P hprime hbad q.val q.property).1.ne_zero
        (errorIndex i+1) (hchildslot l D q) Bp.val (υ l D q i ψ Bp) vheight
      exact hc.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
    let hpaid:=pay P hP hprime hbad hchildslot υ vheight hsource'
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
      let pair:=e j
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    let hc : ∀(q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label),0≤ cost q i ψ j:=by
      intro q i ψ j
      exact error_menu_nonneg _ (fun Bp=>error_actual_label_scalar_sum_nonneg
        (source (e j).1 (e j).2 q i ψ Bp) (R₂ (e j).1 q i) (e j).2.val
        (by
          have h:=(selected_low_pair_inverse_fields first projector hinj (e j)).2
          rw [←h]
          exact hprojector (e.symm (e j))) hw₁ hw₂ reflected second (e j).1.val
        Z M a δ reserve error εcommon (volume s) q.val (errorIndex i+1) hZ0.le)
    let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
    let hF : 0≤ F:=(geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
    let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)
    let hm : ∀j,mass j≤ F*Z^(B*εmass-side):=fun j=>actual_geometry_low_uniform_mass
      reflected N lo ap hlo hap s R seed W M Z ξ B εmass side hZ hK hemass hcard hlower
      hs hw₁ hw₂ hsource hs₁ hs₂ bin (column j) (gates.2 (column j)).2.2
    let weighted:=error_weighted_prime_cost mass cost (56/(P.card:ℝ))
      (F*Z^(B*εmass-side)) (fun i=>16*(errorIndex i+2:ℝ))
      (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (fun i=>by positivity) hc hm
    let binPaid:=error_physical_bin_exponent_payment Z F K (seed.absNorm:ℝ) B εmass p exponent side M
      hZ hF hKscalar.le (Nat.cast_nonneg _) hbin
    show (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,mass j*cost q i ψ j)≤
      16*F*K*Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ) from
    weighted.trans ((mul_le_mul_of_nonneg_left hpaid
      (mul_nonneg hF (Real.rpow_nonneg hZ0.le _))).trans binPaid)
  )
  Exists.intro K (And.intro hKscalar (combined.mono pointwise))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.extracted_error_label_scalar_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_physical_bin_exponent_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_first_label_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_physical_shell_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.ErrorPhysicalShellBound

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorPhysicalScalarPacket
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_error_physical_scalar_packet_at

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalTotal; sha256 02be644d441d2153e9ab86f54704ecc6fa7f6de72ae09d6565d465348f1f779f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                
                                                         
                                                          
                                                                   
                                                           
                                                        

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open Cycle61Moment CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentRankinRadical ActualEisensteinCubic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O
local instance errorPhysicalTotalSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


/-- Complete extracted scalar cost retains its prime average and all three
branch factors before the first allocation is paid. -/
def geometryErrorPhysicalCompleteCost {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(P : Finset (Ideal O))
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ)
    (Z M a δ reserve error εcommon : ℝ) : ℝ :=
  (56/(P.card:ℝ))*∑q : elementPool P,∑i : Fin 3,
    (16*(errorIndex i+2:ℝ))*∑ψ : RayCharacter,
      geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t
        (υ q i ψ) vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon

private theorem error_complete_order {Label Q : Type}[Fintype Label][Fintype Q]
    (mass : Label→ℝ)(cost : Q→ Fin 3→ RayCharacter→ Label→ℝ)
    (outside : ℝ)(branch : Fin 3→ℝ) :
    (∑j,mass j*(outside*∑q,∑i,branch i*∑ψ,cost q i ψ j))=
      outside*(∑q,∑i,branch i*∑j,∑ψ,mass j*cost q i ψ j) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ψ _
  ring

set_option maxHeartbeats 1200000 in
/-- Actual shell payment on the original first indices, with no inverse-key
allocator or extracted-character choice left in the cost. -/
theorem actual_error_physical_complete_shell
    (N : ℕ)(lo ap εv B ε b bs Mmin εaffine K Z : ℝ)
    (paid : ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z)
    {ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
    (s : Input ι)(hcard : Fintype.card ι≤ N)(hlower : lo≤ s.lower)
    (hend : Endpoints b bs bs s)(hvolume : volume s≤ Z^B)
    (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
    (hM : Mmin≤ M)(hecommon : 0≤εcommon)(hemass : 0≤εmass)
    (hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
    (R seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hsource : sourceRadius s≤ Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
      (column j).2.1.val)))
    (alloc : (j : Label)→ actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
    (hf : ∀j,frozenCoefficient (alloc j).val
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
    (χ : Label→ Character)(t T : ℝ)(hT : 1≤ T)
    (hprojector : ∀j,Squarefree (column j).2.1.val)
    (hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T)
    (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
    (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I)
    (υ : Label→ elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ) :
    (∑j,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)) (column j).2.1.val R
        (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ) := by
  let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
  let projector:=fun j=>(column j).2.1.val
  let e:=selectedLowFirstPairEquiv first projector hinj
  have hp:=paid s hcard hlower hend hvolume reflected second M ξ error εcommon εmass a δ reserve
    hM hecommon hemass hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hK bin column hinj
    alloc hf χ t T hT hprojector hdyad P hP hprime hbad hslot
    (fun l D q i ψ _=>υ (e.symm ⟨l,D⟩) q i ψ) vheight
  let paired:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
    let pair:=e j
    geometryErrorPhysicalScalarPacket s reflected second pair.1.val pair.2.val R
      (selectedErrorAllocation s reflected first projector hinj alloc pair)
      (χ (e.symm pair)) t (υ (e.symm pair) q i ψ) vheight q.val (errorIndex i+1)
      Z M a δ reserve error εcommon
  change (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,
    geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)*paired q i ψ j)≤ _ at hp
  have heq (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label) : paired q i ψ j=
      geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R (alloc j)
        (χ j) t (υ j q i ψ) vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon :=
    selected_error_physical_scalar_packet_at s reflected second first projector hinj alloc R χ
      (fun j=>υ j q i ψ) t vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon j
  simp_rw [heq] at hp
  unfold geometryErrorPhysicalCompleteCost
  rw [error_complete_order]
  exact hp

private theorem error_total_label_nonneg {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(hs : Squarefree seed)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(reflected second : Bool)(l : FirstSourceLabel)
    (Z M a δ reserve error εcommon V : ℝ)(p : O)(k : ℕ)(hZ : 0≤ Z) :
    0≤∑v∈actualSecondLabels s R seed,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V (volume s) p k := by
  exact Finset.sum_nonneg (fun v hv=>extracted_error_label_scalar_nonneg reflected second l v
    Z M a δ reserve error εcommon V (volume s) p k hZ
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).1)

private theorem error_total_menu_nonneg {Menu : Type*}[Fintype Menu]
    (cost : Menu→ℝ)(hc : ∀m,0≤ cost m) : 0≤∑m,cost m :=
  Finset.sum_nonneg (fun m _=>hc m)

private theorem error_total_packet_nonneg {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(υ : Character)(vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ)(hZ : 0≤ Z)(hL : Squarefree L)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0) :
    0≤ geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z M a δ reserve error εcommon := by
  let C:=if reflected then l.1.2 else l.1.1
  let u:=child s C R B₁ χ t
  let Q:=Ideal.span {q}
  let source:=fun (Bp : errorLiftedActiveAllocations u Q k)=>child u (Q^k) (R*C) Bp.val υ vheight
  change 0≤∑Bp : errorLiftedActiveAllocations u Q k,∑v∈actualSecondLabels (source Bp) ((R*C)*Q^k) L,
    extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
      (volume s) (volume (source Bp)) q k
  exact error_total_menu_nonneg _ (fun Bp=>error_total_label_nonneg
    (source Bp) ((R*C)*Q^k) L hL hw₁ hw₂ reflected second l
    Z M a δ reserve error εcommon (volume s) q k hZ)

/-- Positivity comes from the actual supported second labels in each
literal extracted child, including allocations before ordinary restriction. -/
theorem geometry_error_physical_complete_cost_nonneg {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(P : Finset (Ideal O))
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ)
    (Z M a δ reserve error εcommon : ℝ)(hZ : 0≤ Z)(hL : Squarefree L)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0) :
    0≤ geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z M a δ reserve error εcommon := by
  unfold geometryErrorPhysicalCompleteCost
  apply mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  exact error_total_menu_nonneg _ (fun q=>error_total_menu_nonneg _ (fun i=>
    mul_nonneg (by positivity) (error_total_menu_nonneg _ (fun ψ=>
      error_total_packet_nonneg s reflected second l L R B₁ χ t (υ q i ψ) vheight
        q.val (errorIndex i+1) Z M a δ reserve error εcommon hZ hL hw₁ hw₂))))

/-- The first-projector shell is paid before all original selected first
indices are summed. No first arithmetic label is counted. -/
def ErrorPhysicalSelectedBound (N : ℕ)(lo ap εv B ε b bs Mmin εaffine U εshell K Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(_hcard : Fintype.card ι≤ N)(_hlower : lo≤ s.lower)
      (_hend : Endpoints b bs bs s)(_hvolume : volume s≤ Z^B)
      (_hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (_hM : Mmin≤ M)(_hecommon : 0≤εcommon)(_hemass : 0≤εmass)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)(_hsource : sourceRadius s≤ Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(_hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→ firstLiveColumns
        (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus))
      (_hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j).val,
        (column j).val.2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j).val))
      (_hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j).val) R s.ν s.W s.P≠0)
      (χ : Label→ Character)(t : ℝ)(P : Finset (Ideal O))(_hP : P.Nonempty)
      (_hprime : ∀Q∈P,Prime Q)(_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I)
      (υ : Label→ elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ),
    (∑j,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j).val*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j).val) (column j).val.2.1.val R
        (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^(B*εmass+εshell-M*(7/60000000))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1200000 in
/-- Uniform selected first-column payment from actual stored-pool caps and
literal extracted packets. Constants precede every source and height. -/
theorem eventual_actual_error_physical_selected_payment
    (N : ℕ)(lo ap εv B ε b bs Mmin εaffine U εshell : ℝ)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(hMmin : 0< Mmin)(hU : 0≤ U)(heshell : 0<εshell) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ErrorPhysicalSelectedBound N lo ap εv B ε b bs Mmin εaffine U εshell K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_error_physical_shell_payment N lo ap εv B ε b bs
    hlo hap hev hB he hb hbs Mmin εaffine hMmin
  obtain ⟨C,hC,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower N U εshell hU heshell
  refine ⟨K*C,mul_pos hK hC,?_⟩
  filter_upwards [hpaid,hcount] with Z hp hc
  refine ⟨hp.1,?_⟩
  intro ι Label _ _ _ s hn hl hend hv hpool reflected second M ξ error εcommon εmass a δ reserve
    hM hecommon hemass hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin column hinj alloc hf
    χ t P hP hprime hbad hslot υ vheight
  let cols:=fun j=>(column j).val
  let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hpow bin (cols j)
  let cost:=fun j=>geometryErrorPhysicalCompleteCost s reflected second
    (geometryFirstLabel s R seed (Z^M) Z ξ hpow bin (cols j)) (cols j).2.1.val R
    (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon
  let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let E:=16*F*K*Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ)
  have hz : 1≤ Z:=by linarith [hp.1]
  have hE : 0≤ E:=by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le)
      hK.le) (Real.rpow_nonneg (zero_le_one.trans hz) _)) (Nat.cast_nonneg _)
  have hbound (n : ℤ)(hns : n∈selectedShells (selectedFirstProjectors cols)) :
      (∑j : SelectedFirstShell cols n,mass j.val*cost j.val)≤ E := by
    have hscale:=actual_geometry_selected_first_shell_scale s N R seed (Z^M) Z ξ U hpow
      hn hz hU hpool bin cols n hns
    have hrestrict:=actual_geometry_selected_first_shell_restriction reflected s R seed (Z^M) Z ξ hpow
      bin column alloc hinj hf n
    exact actual_error_physical_complete_shell N lo ap εv B ε b bs Mmin εaffine K Z hp.2
      s hn hl hend hv reflected second M ξ error εcommon εmass a δ reserve hM hecommon hemass hloss
      R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin
      (fun j : SelectedFirstShell cols n=>cols j.val) hrestrict.1 (fun j=>alloc j.val)
      hrestrict.2.1 (fun j=>χ j.val) t (dyadicScale n) hscale.1
      (fun j=>(selected_first_shell_gates cols n j).1) hrestrict.2.2 P hP hprime hbad hslot
      (fun j=>υ j.val) vheight
  have hm:=selected_first_shell_payment cols
    (fun j=>actual_first_live_squarefree _ _ _ (column j).property)
    (fun j=>mass j*cost j) E C Z εshell hE
    (hc.2 s hn hpool R seed (Z^M) ξ hpow bin cols) hbound
  apply hm.trans_eq
  dsimp only [E,F]
  rw [show B*εmass+εshell-M*(7/60000000)=εshell+(B*εmass-M*(7/60000000)) by ring,
    Real.rpow_add (zero_lt_one.trans_le hz)]
  ring

/-- Undivided first allocation weights ingest the complete physical cost.
The displayed exponent includes first selection and shared shell losses. -/
def ErrorPhysicalAllocationBound {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z : ℝ) : Prop :=
  ∀(s : Input ι)(_hcard : Fintype.card ι≤ N)(_hmass : ∀i,s.M i≤ Cs)
      (_hlower : lo≤ s.lower)(_hend : Endpoints b bs bs s)(_hvolume : volume s≤ Z^B)
      (_hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
      (reflected second : Bool)(M error εcommon a δ reserve : ℝ)
      (_hM : Mmin≤ M)(_hecommon : 0≤εcommon)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)
      (_hsourcepos : 0< sourceRadius s)(_hsource : sourceRadius s≤ Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(_hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin)))
      (_hrows : rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus))
      (t : ℝ)(P : Finset (Ideal O))(_hP : P.Nonempty)
      (_hprime : ∀Q∈P,Prime Q)(_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I),
    let C:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.val
    ∀(υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character)
      (vheight : ℝ),
    let A:=Real.logb Z (volume s)
    let weight:=fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let cost:=fun (j : rows)(alloc : actualAllocations s.pools (C j))=>
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.val) j.val.2.1.val R alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.val) t P
        (υ j alloc) vheight Z M a δ reserve error εcommon
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK bin weight N b j.val alloc*
        cost j alloc)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^((B+1)*εalloc+εshell-M*(7/60000000))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1600000 in
/-- Genuine selected first mass and allocation selection pay every original
allocation. The prime average occurs once, inside the literal cost. -/
theorem eventual_actual_error_physical_allocation_payment {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc : ℝ)
    (hCs : 1≤ Cs)(hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(hMmin : 0< Mmin)(hU : 0≤ U)(heshell : 0<εshell)
    (hξ : 0≤ξ)(healloc : 0<εalloc) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_error_physical_selected_payment
    N lo ap εv B ε b bs Mmin εaffine U εshell hlo hap hev hB he hb hbs hMmin hU heshell
  obtain ⟨D,hD,hselection⟩:=actual_geometry_weighted_selected_cost (ι:=ι)
    N Cs b εalloc B 0 B ξ hCs healloc hB (by norm_num) hB hξ
  refine ⟨K*D,mul_pos hK hD,?_⟩
  filter_upwards [hpaid,hselection] with Z hp ha
  refine ⟨hp.1,?_⟩
  intro s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot
    C υ vheight A weight cost
  let E:=16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
    Z^(B*εalloc+εshell-M*(7/60000000))/(seed.absNorm:ℝ)
  have hKi : (Z^M)⁻¹≤ Z^(0:ℝ):=by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow ha.1 (hMmin.le.trans hM))
  have hC (j : rows) : C j≠0:=by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hpow bin j.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hpow bin j.val.1).hD.1
  have hcost (j : rows)(alloc : actualAllocations s.pools (C j)) : 0≤ cost j alloc:=
    geometry_error_physical_complete_cost_nonneg s reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hpow bin j.val) j.val.2.1.val R alloc
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hpow bin j.val) t P (υ j alloc)
      vheight Z M a δ reserve error εcommon (zero_le_one.trans ha.1)
      (actual_first_live_squarefree _ _ _ (hrows j.property)) hw₁ hw₂
  have hselected {Label : Type}[Fintype Label](column : Label → rows)
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hpow bin (column j).val,
        (column j).val.2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools (C (column j)))
      (hf : ∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) :
      (∑j,‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hpow bin weight (column j).val‖^2*
        ((C (column j)).absNorm:ℝ)^(εalloc-1)*cost (column j) (alloc j))≤ E := by
    let live : Label→ firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hpow bin) (fun _=>logAnnulus):=
      fun j=>⟨(column j).val,hrows (column j).property⟩
    have hh:=hp.2 s hn hl hend hv hpool reflected second M ξ error εcommon εalloc a δ reserve
      hM hecommon healloc.le hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin live hinj
      alloc hf (fun j=>geometryColumnCharacter reflected s R seed (Z^M) Z ξ hpow bin (column j).val)
      t P hP hprime hbad hslot (fun j=>υ (column j) (alloc j)) vheight
    simpa only [geometryFirstHighMass,live,cost,A,weight,
      CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hpay:=ha.2 s hn hm reflected R seed (Z^M) M A hpow bin weight hs hw₁ hw₂
    hsourcepos hsource hv hKi rows E cost hcost hC hselected
  apply hpay.trans_eq
  dsimp only [E]
  rw [show (B+1)*εalloc+εshell-M*(7/60000000)=
    εalloc+(B*εalloc+εshell-M*(7/60000000)) by ring,
    Real.rpow_add (zero_lt_one.trans_le ha.1)]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_physical_complete_shell
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_physical_complete_cost_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_physical_selected_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_physical_allocation_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalTotal -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorScalar; sha256 30b57cd6c0b8e0dd5bec5242feb2bc8d8d1d9381945f1c67f18b03ac79532f35 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                              
                                              
                                                          
                                                            
                                  

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open Cycle61Moment CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentRankinRadical ActualEisensteinCubic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O
local instance affineErrorScalarSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _



open Cycle61InitialSource ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedRayDictionary

/-- Increasing a fixed payment constant preserves the actual physical
allocation contract; every remaining factor is nonnegative. -/
theorem error_physical_allocation_constant_mono {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K K' Z : ℝ)
    (hZ : 0≤ Z)(hlo : 0< lo)(hap : 0< ap)(hK : K≤ K')
    (paid : ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z) :
    ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K' Z := by
  intro s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot
    C υ vheight A weight cost
  have h:=paid s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot υ vheight
  apply h.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num)
        (geometry_high_factor_pos reflected _ bin
          (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le))
      (Real.rpow_nonneg hZ _)) (Nat.cast_nonneg _)

/-- Finite ambient slot subsets share one constant and one threshold.
Each subset keeps its own literal source and original allocation types. -/
theorem uniform_error_physical_allocation_payment {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc : ℝ)
    (hCs : 1≤ Cs)(hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(hMmin : 0< Mmin)(hU : 0≤ U)(heshell : 0<εshell)
    (hξ : 0≤ξ)(healloc : 0<εalloc) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧ ∀T : Finset α,
      ErrorPhysicalAllocationBound (ι:=T) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z := by
  have data (T : Finset α):=eventual_actual_error_physical_allocation_payment (ι:=T)
    N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    hCs hlo hap hev hB he hb hbs hMmin hU heshell hξ healloc
  choose C hC hbound using data
  let K:=1+∑T : Finset α,C T
  have hn : ∀T : Finset α,0≤ C T:=fun T=>(hC T).le
  have hK : 0< K:=by
    have hsum:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hn T)
    dsimp only [K];linarith
  have hCK (T : Finset α) : C T≤ K:=by
    have hh:=Finset.single_le_sum (fun T _=>hn T) (Finset.mem_univ T)
    dsimp only [K];linarith
  refine ⟨K,hK,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound,eventually_ge_atTop (2:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T
  exact error_physical_allocation_constant_mono N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    (C T) K Z (by linarith) hlo hap (hCK T) (hz T).2

/-- Source facts supplied by the literal affine construction, rather than
premises about the extracted energies or desired numerator. -/
structure AffineErrorSourceGates {ι : Type}[Fintype ι]
    (s : Input ι)(N : ℕ)(Cs Z : ℝ)(P : Finset (Ideal O)) : Prop where
  card : Fintype.card ι≤ N
  mass : ∀i,s.M i≤ Cs
  lower : (1:ℝ)≤ s.lower
  endpoints : Endpoints (9/4) (9/4) (9/4) s
  volume : CenteredMomentAmplificationChildInput.volume s≤ Z^(3:ℝ)
  pool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^(2:ℝ)
  plainZero₁ : s.W₁ 0=0
  plainZero₂ : s.W₂ 0=0
  radius_pos : 0< sourceRadius s
  radius : sourceRadius s≤ Z^(3:ℝ)
  plainLower₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤ x
  plainLower₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤ x
  primes_nonempty : P.Nonempty
  primes : ∀Q∈P,Prime Q
  primes_good : ∀Q∈P,Q∉fixedBadPrimes
  coprime : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I

variable {α : Type}[Fintype α][DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorScalarFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤ H)

include hH in
/-- Genuine prime pools are nonempty simultaneously for every physical
width cell. The deleted fixed primes remain in the pool definition. -/
theorem eventual_affine_error_pools_nonempty (Sbad : Finset (Ideal O)) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀j : ↥(Finset.Icc 1 600),
      (CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
        (Z^(Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper j.val)))).Nonempty := by
  have hcell (j : ↥(Finset.Icc 1 600)) :=
    Cycle61.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2
  have hp (j : ↥(Finset.Icc 1 600)):=
    CenteredMomentFirstAmplificationChoice.eventually_actual_pool_card rayM H hH Sbad
      (Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper j.val)) 1
      (Cycle61.Arithmetic.amp_pos (hcell j)) (by norm_num)
  filter_upwards [Filter.eventually_all.mpr hp,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro j
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le (hz j)

set_option maxHeartbeats 1200000 in
/-- All scalar source and prime gates hold uniformly before the live subset,
characters, profiles, lengths and heights are chosen. -/
theorem eventual_actual_affine_error_source_gates
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ)(hmesh : mesh<(902420521/120632400000:ℝ)/2) :
    ∃Cs : ℝ,1≤ Cs ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta:=Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(Cycle61.Arithmetic.amp beta))
      AffineErrorSourceGates inp (Fintype.card α) Cs Z P := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW 1 2
      (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh,
    eventual_affine_error_pools_nonempty rayM H hH Sbad,
    eventually_ge_atTop (9/4:ℝ)] with Z hc hcop hp hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi inp beta P
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa only [mul_one] using hlo₁)
    (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₁)
    (by simpa only [mul_one] using hhi₂) (by simpa only [one_div] using hwhi)
  rcases hcaps with ⟨hVge,hVlog,hV,hsource,hcolumns⟩
  rcases hfixed T η₀ θ w σ freq hσ state p 1 t X₁ X₂ hX₁ hX₂ with
    ⟨hcard,hmass,hupper,hend,hb₁,hb₂,hW₁,hW₂,hη,hmatch⟩
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ)≤ x:=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0:=by
    by_contra hne
    have h:=hplain j 0 hne
    norm_num at h
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50) (by norm_num) hWs
    w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ (by norm_num) (by norm_num)
  have he' : Endpoints (9/4) (9/4) (9/4) inp:=by
    refine ⟨he.1.trans ?_,he.2⟩
    norm_num
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num) (by simpa using (show (2:ℝ)≤ Z by linarith))
    hlarge hw (by simpa using hwhi) (by simpa using hhi₁) (by simpa using hhi₂)
  have hpool' : ∀j I,I∈inp.pools j→(I.absNorm:ℝ)≤ Z^(2:ℝ):=by
    simpa only [show (1:ℝ)+1=2 by norm_num] using hpool
  have hsource' : sourceRadius inp≤ Z^(3:ℝ):=by
    simpa only [show (1:ℝ)+2=3 by norm_num] using hsource
  have hradpos : 0< sourceRadius inp:=by
    change 0<(∏i : T,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i : T,Z^(w i))
    exact mul_pos (mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun _ _=>by norm_num))
      (by norm_num)) (by norm_num)) (mul_pos hX₁ hX₂))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (zero_lt_one.trans hc.1) _))
  have hcell:=Cycle61.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  let j : ↥(Finset.Icc 1 600):=⟨Cycle61.Moment.originalCell (∑i,w i),Finset.mem_Icc.mpr ⟨hcell.1,hcell.2.1⟩⟩
  have hbeta:=Cycle61.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  refine ⟨hcard,hmass,le_rfl,he',?_,hpool',hzero 0,hzero 1,hradpos,hsource',hplain 0,hplain 1,
    hp.2 j,?_,?_,?_⟩
  · exact hV.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by norm_num))
  · intro Q hQ
    exact (primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  · intro Q hQ
    exact (primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  · exact hcop.2 beta hbeta.1 hbeta.2 inp η₀ θ w σ freq W hmatch hwm

private def affine_error_allocation_frame {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(s : Input ι)(Z ξ εalloc εshell K amp reserve error εcommon : ℝ)
    (reflected second : Bool)(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ))
    (radius : ℝ)(hk : 0< radius) : Prop :=
  ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s 1 1 radius Z ξ hk bin))),
    rows⊆firstLiveColumns (geometryFirstSource s 1 1 radius Z ξ hk bin) (fun _=>logAnnulus) →
  ∀(height : ℝ)(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) →
    (∀Q∈P,Q∉fixedBadPrimes) →
    (∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I) →
  let C:=fun j : rows=>geometryColumnIdeal reflected s 1 1 radius Z ξ hk bin j.val
  ∀(υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume s)
  let weight:=fun q=>normPhase (coordinateBlock s 1 1 Φ radius Z ξ q)
  (∑j : rows,∑alloc : actualAllocations s.pools (C j),
    geometryAllocationWeight reflected s 1 1 radius Z ξ 1 A hk bin weight N (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s 1 1 radius Z ξ hk bin j.val) j.val.2.1.val 1 alloc
        (geometryColumnCharacter reflected s 1 1 radius Z ξ hk bin j.val) height P (υ j alloc)
        vheight Z 1 amp (3*amp) reserve error εcommon)≤
    16*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*K*
      Z^(((3:ℝ)+1)*εalloc+εshell-1*(7/60000000))/( (1:Ideal O).absNorm:ℝ)

/-- Literal affine specialization of the complete physical scalar payment.
The actual prime pool, characters and undivided allocation weights are kept. -/
def AffineErrorScalarBound (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh K Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
  (∀i,0≤ w i) → (∀i,w i≤ mesh) →
  (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
  length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
  (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
  let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
  let beta:=Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))
  let amp:=Cycle61.Arithmetic.amp beta
  let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
  ∀(reflected second : Bool)(error εcommon reserve : ℝ),
  0≤εcommon → error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine →
  ∀(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ)),
  let hK:=zero_lt_one.trans hZ
  let rows:=firstLiveColumns (geometryFirstSource inp 1 1 Z Z ξ hK bin) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected inp 1 1 Z Z ξ hK bin j.val
  ∀(height : ℝ)(υ : (j : rows)→ actualAllocations inp.pools (C j)→
    elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)
  let weight:=fun q=>normPhase (coordinateBlock inp 1 1 Φ Z Z ξ q)
  (∑j : rows,∑alloc : actualAllocations inp.pools (C j),
    geometryAllocationWeight reflected inp 1 1 Z Z ξ 1 A hK bin weight (Fintype.card α) (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost inp reflected second
        (geometryFirstLabel inp 1 1 Z Z ξ hK bin j.val) j.val.2.1.val 1 alloc
        (geometryColumnCharacter reflected inp 1 1 Z Z ξ hK bin j.val) height P (υ j alloc)
        vheight Z 1 amp (3*amp) reserve error εcommon)≤
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-(7/60000000:ℝ))

set_option maxHeartbeats 1600000 in
/-- Actual affine source facts discharge every source and prime gate of the
saved physical payment. A single constant precedes all live slot subsets. -/
theorem eventual_actual_affine_error_scalar_payment
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh : ℝ)
    (hev : 0<εv)(he : 0<ε)(heshell : 0<εshell)(hξ : 0≤ξ)(healloc : 0<εalloc)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      AffineErrorScalarBound (α:=α) rayM H hH Sbad W hW hWs εv ε εaffine εshell ξ εalloc mesh K Z := by
  obtain ⟨Cs,hCs,hgates⟩:=eventual_actual_affine_error_source_gates (α:=α) rayM H hH
    Sbad hbad W hW hWs mesh hmesh
  obtain ⟨K,hK,hpaid⟩:=uniform_error_physical_allocation_payment (α:=α)
    (Fintype.card α) Cs 1 (1/4) εv 3 ε (9/4) (9/4) 1 εaffine 2 εshell ξ εalloc
    hCs (by norm_num) (by norm_num) hev (by norm_num) he (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heshell hξ healloc
  refine ⟨K,hK,?_⟩
  filter_upwards [hgates,hpaid] with Z hg hp
  refine ⟨hp.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
    inp beta amp P reflected second error εcommon reserve hecommon hloss Φ bin hpow rows C height υ vheight A weight
  have g:=hg.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  have hk : 0< Z^(1:ℝ):=by simpa only [Real.rpow_one] using hpow
  have hh:=(hp.2 T) inp g.card g.mass g.lower g.endpoints g.volume g.pool
    reflected second 1 error εcommon amp (3*amp) reserve le_rfl hecommon
    (by simpa only [show (3:ℝ)+1=4 by norm_num] using hloss)
    1 1 squarefree_one one_ne_zero g.plainZero₁ g.plainZero₂ g.radius_pos g.radius
    g.plainLower₁ g.plainLower₂ Φ hk bin
  have hframe : affine_error_allocation_frame (Fintype.card α) inp Z ξ εalloc εshell K amp reserve
      error εcommon reflected second Φ bin (Z^(1:ℝ)) hk:=hh
  have heq : (⟨Z^(1:ℝ),hk⟩ : {r : ℝ // 0< r})=⟨Z,hpow⟩:=Subtype.ext (Real.rpow_one Z)
  have htype:=congrArg (fun r : {r : ℝ // 0< r}=>
    affine_error_allocation_frame (Fintype.card α) inp Z ξ εalloc εshell K amp reserve
      error εcommon reflected second Φ bin r.val r.property) heq
  have hframeZ:=Eq.mp htype hframe
  have hfinal:=hframeZ rows (Finset.Subset.refl _) height P g.primes_nonempty g.primes g.primes_good g.coprime υ vheight
  simpa only [mul_one,one_mul,map_one,Nat.cast_one,div_one,
    show (3:ℝ)+1=4 by norm_num] using hfinal

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_physical_allocation_constant_mono
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_error_physical_allocation_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_affine_error_pools_nonempty
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_source_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_scalar_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorScalar -/
