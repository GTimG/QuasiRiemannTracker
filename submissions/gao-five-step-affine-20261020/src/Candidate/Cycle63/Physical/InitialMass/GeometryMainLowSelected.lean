import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowAggregate
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle25.Energy.Endpoint
import Candidate.Cycle63.Physical.InitialMass.SecondLowProfileColumn

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
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
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance geometryMainLowSelectedDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The literal child and all Mellin height shifts retain a fixed four-power
profile bound, chosen before the source labels and allocations. -/
theorem actual_child_low_profile_factor {ι : Type*}[Fintype ι]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤Cs)(hbp : 1≤bp)
    (s : Input ι)(hn : Fintype.card ι≤N)(hM : ∀i,s.M i≤Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)
    (C R : Ideal O)(alloc : actualAllocations s.pools C)(χ τ : Character)(t v : ℝ) :
    let src := withHeight (child s C R alloc χ t) τ v
    src.toData.profileFactor*(∏i,src.M i)^2≤2*bp^2*Cs^(4*N) := by
  intro src
  have hm : mass s≤Cs^N := by
    apply le_trans (Finset.prod_le_prod₀
      (fun i (_ : i∈Finset.univ)=>zero_le_one.trans (s.M_ge_one i)) (fun i _=>hM i))
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hCs hn
  have hc : mass (child s C R alloc χ t)≤Cs^N := (child_mass s C R alloc χ t).trans hm
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

variable [Cycle63.AffineLedger] in
/-- Fixed source-profile factors are extracted from the genuine low analytic estimate. -/
theorem actual_low_fixed_profile_columns [Cycle63.AffineLedger.DeletesIntoOldRegion]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*unit+ξ/2
    let padding := omega+εpad*unit
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0≤Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1≤Z^L) →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*(2*b^2*Cs^(4*N))*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh)*Z^pad := by
  have hcolumn := actual_live_main_low_profile_column (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  obtain ⟨degree,Sp,hcolumn⟩ := hcolumn
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hω hξ hMcap' hfit hzslot haff q cell amp g χ hP hPN st src nominal δwidth padding
    seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps hQM' hQη low zs weight hnonneg hkeep hweight
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hω hξ hMcap' hfit hzslot haff q g χ hP hPN seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps zs weight hnonneg hkeep hweight
  have hprofile : src.toData.profileFactor*(∏j,src.M j)^2≤2*b^2*Cs^(4*N) :=
    actual_child_low_profile_factor N Cs b hCs hb s hcard hmass hsb₁ hsb₂ q.C₁ q.R₁ q.B₁
      q.η₁ (g.datum.τ χ) q.t₁ v
  let R := QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
    Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh)*Z^pad
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hR : 0≤R := by dsimp only [R]; positivity
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprofile hCg.le) hR
  apply hh.trans
  convert hbnd using 1 <;> dsimp only [R] <;> ring

theorem actual_low_label_normalizer (C D : Ideal O)(U : Finset (CommonIndex C D))
    (l : FirstSourceLabel)(hc : C=l.1.1)(hd : D=l.1.2)(hu : HEq U l.2.val) :
    normalizer C D U=normalizer l.1.1 l.1.2 l.2.val := by
  subst C; subst D
  rw [eq_of_heq hu]

theorem actual_low_label_nominal (unit Z amp omega : ℝ)(C₁ D₁ C D : Ideal O)
    (U : Finset (CommonIndex C D))(l : FirstSourceLabel)
    (hc : C=l.1.1)(hd : D=l.1.2)(hu : HEq U l.2.val) :
    secondNominal unit Z amp omega C₁ D₁ C D U=
      secondNominal unit Z amp omega C₁ D₁ l.1.1 l.1.2 l.2.val := by
  subst C; subst D
  rw [eq_of_heq hu]

/-- The selected scalar is the original first-column mass. Its physical
D factor is retained on both orientations, before any second-row sum. -/
theorem actual_geometry_low_uniform_mass {ι : Type}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(N : ℕ)(lo ap : ℝ)(hlo : 0<lo)(hap : 0<ap)
    (s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D Z ξ B ε side : ℝ)
    (hZ : 1<Z)(hK : 0<Z^D)(hε : 0≤ε)(hcard : Fintype.card ι≤N)(hlower : lo≤ s.lower)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ap≤x)(hs₂ : ∀x,s.W₂ x≠0→ap≤x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
    (hside : side≤geometryHighSide reflected (Real.logb Z (volume s))
      (geometryExponents s R seed (Z^D) Z ξ j.1.val)) :
    geometryFirstHighMass reflected s R seed W D Z ξ ε hK bin j≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*ε-side) := by
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hh:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z ξ B ε
    hZ hK hε hcard hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin j
  have hfactor : 0≤geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin := by
    cases reflected <;> simp only [geometryHighFactor,ite_true]
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

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 200000 in
/-- Complete selected low frequency columns are paid by the actual finite supported label budget. -/
theorem actual_selected_low_paid_columns [Cycle63.AffineLedger.DeletesIntoOldRegion] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→FirstSourceLabel)
      (_hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (_heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤Tfirst → p≤Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤Z^L) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→Finset O)(weight : rows→O→ℝ),(∀r,∀z∈zs r,0≤weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0≤physical → (∀l,0≤ mass l) →
      (∀l,mass l≤physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) := by
  let hbase := actual_low_fixed_profile_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  let hpbase := eventual_actual_selected_low_second_paid
    N supply εv Bnorm εlabels hsupply hev hBnorm hel
  let K₀ := Classical.choose hpbase
  let hpspec := Classical.choose_spec hpbase
  have hK₀ : 0<K₀ := hpspec.1
  let hpaid := hpspec.2
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hcbase := hcolumn η₀ Q hQM hQ0 hQt hQ72
  let C := Classical.choose hcbase
  let hcspec := Classical.choose_spec hcbase
  have hC : 0<C := hcspec.1
  let hbound := hcspec.2
  refine ⟨C*K₀,mul_pos hC hK₀,?_⟩
  filter_upwards [hbound,hpaid] with Z hz hzpaid
  refine ⟨hzpaid.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hω hξ hMcap' hfit hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight mass physical loss hphysical hmass0 hmasscap c error
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let errorBase := εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
    Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
  let pay := fun r : rows=>Z^(-amp)*
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
    (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
      ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
    Z^(secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val+amp+errorBase)
  let fixed := (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(2*T)^(3*εshell)
  have hfixed : 0≤fixed := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
    dsimp only [fixed]; positivity
  have hpoint (r : rows) : c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)≤
      C*fixed*(physical*Z^(loss+amp))*pay r := by
    have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
      hMmin hω hξ hMcap' hfit hzslot haff (q r) (g r) (χ r) (hP r) (hPN r)
      (divisorSeed r) (hE₂ r) (hdivisor r) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow r) (hcaps r)
      (zs r) (weight r) (hnonneg r) (hkeep r) (hweight r)
    have hc : 0≤ c r := by
      dsimp only [c]
      exact mul_nonneg (mul_nonneg (div_nonneg (hmass0 _) (CenteredMomentAmplificationChildInput.volume_pos _).le)
        (g r).datum.K_pos.le) (normalizer_pos _ _ (g r).datum.hC _).le
    have h := mul_le_mul_of_nonneg_left hh hc
    have hcancel : Z^amp*Z^(-amp)=(1:ℝ) := by rw [←Real.rpow_add hZ0]; simp
    have hscale : mass r.val.1*Z^amp≤physical*Z^(loss+amp) := by
      simpa only [Real.rpow_add hZ0,mul_assoc] using mul_le_mul_of_nonneg_right (hmasscap r.val.1)
        (Real.rpow_nonneg hZ0.le amp)
    have hpay0 : 0≤pay r := by
      dsimp only [pay]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (div_nonneg (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _).le (CenteredMomentAmplificationChildInput.volume_pos _).le))
        (mul_nonneg (normalizer_pos _ _ ((hC₂ r) ▸ (g r).datum.hC) _).le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ0.le _)
    have heq' : c r*(C*(2*b^2*Cs^(4*N))*
      QuadraticInitialBound.diagonalControl (st r).radial.profile*(p₀.control Sp)^2*
      (1+|v|+height)^degree*((q r).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
      Z^(secondNominal unit Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
        (g r).datum.inactive+(εwidth*unit+ξ/2)+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+
        2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh)*Z^pad)=
      C*fixed*(mass r.val.1*Z^amp)*pay r := by
      have hpayeq : (mass r.val.1*Z^amp)*pay r=
          mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+errorBase) := by
        dsimp only [pay]
        calc
          _=(Z^amp*Z^(-amp))*(mass r.val.1*
              (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
              (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
                ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
              Z^(secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
                (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
                (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
                (label r).1.1 (label r).1.2 (label r).2.val+amp+errorBase)) := by ring
          _=_ := by rw [hcancel]; ring
      have hnom : secondNominal unit Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive=
          secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val := by
        have hback:=actual_low_label_nominal unit Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive (label r) (hC₂ r) (hD₂ r) (hU₂ r)
        have hfront:=congrArg₂ (fun C₁ D₁ : Ideal O=>
          secondNominal unit Z amp omega C₁ D₁ (label r).1.1 (label r).1.2 (label r).2.val)
          (hC₁ r) (hD₁ r)
        have homega:=congrArg (fun omega : ℝ=>secondNominal unit Z amp omega
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val) hωeq
        exact hback.trans (hfront.trans homega)
      have hnormal := actual_low_label_normalizer _ _ _ _ (hC₂ r) (hD₂ r) (hU₂ r)
      have hnorm := congrArg (fun I : Ideal O=>(I.absNorm:ℝ)^(εshell-1)) (hEeq r)
      have hrad : (st r).radial.profile=ballProfile := rfl
      have hexp : secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*unit+ξ/2)+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+
        2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*
        (omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad=
        secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+amp+
        (εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
        Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad) := by ring
      have hpower := (Real.rpow_add hZ0
        (secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*unit+ξ/2)+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+
          2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*
          (omega+εpad*unit)+Cycle63.AffineLedger.q*mesh) pad).symm
      have hpowerExact := hpower.trans (congrArg (fun exponent : ℝ=>Z^exponent) hexp)
      have hnomPower:=congrArg (fun nominal : ℝ=>Z^(nominal+(εwidth*unit+ξ/2)+amp-
        unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
        Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh)) hnom
      have hpowerSource: Z^(secondNominal unit Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive+(εwidth*unit+ξ/2)+amp-
          unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh)*Z^pad=
          Z^(secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+errorBase) :=
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
        (Z^(secondNominal unit Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
          (g r).datum.inactive+(εwidth*unit+ξ/2)+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+
          2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh))
        (Z^pad) _ _ _ _ hcoef hdiag hnorm hpowerSource
      calc
        _=_ := htrans
        _=C*fixed*(mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal unit Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+errorBase)) := by dsimp only [fixed]; ring
        _=_ := (congrArg (fun x : ℝ=>C*fixed*x) hpayeq).symm.trans (by ring)
    have hfull := h.trans_eq heq'
    exact hfull.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (mul_nonneg hC.le hfixed)) hpay0)
  have hpays := hzpaid.2 s hcard hsupply' reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    R seed K Tsec ξ unit Mrow amp reserve errorBase εshell hseed hw₁ hw₂ heshell.le hsource
    Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
    rows hU box hbox
  have hpays' : (∑r,pay r)≤
      (box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ)) := by
    have hex : p+exponent+errorBase+(unit-Mrow)+εv+Bnorm*εshell+εlabels=
        p+exponent+error+εv+Bnorm*εshell+εlabels := by
      dsimp only [error,errorBase]; ring
    rw [hex] at hpays
    exact hpays
  calc
    _≤∑r,C*fixed*(physical*Z^(loss+amp))*pay r := Finset.sum_le_sum (fun r _=>hpoint r)
    _=(C*fixed*(physical*Z^(loss+amp)))*(∑r,pay r) := by rw [Finset.mul_sum]
    _≤(C*fixed*(physical*Z^(loss+amp)))*
      ((box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ))) :=
      mul_le_mul_of_nonneg_left hpays' (by positivity)
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
    (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j)
    (hU : ActualSecondBlockIndex.IsInactive n)
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
    g.datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve first ∧
    g.datum.radius=frequencyRadius (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first)
      Z ξ := by
  intro q g first label
  exact ⟨rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum

end
end OAI.SevenEighths.Cycle63InitialMass
