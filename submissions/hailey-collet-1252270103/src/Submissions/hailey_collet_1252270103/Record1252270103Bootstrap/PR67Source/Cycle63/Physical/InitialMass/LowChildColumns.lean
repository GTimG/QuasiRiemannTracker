import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildCommon
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowSelected
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound for the normalized columns of a LOW child, and with the fixed source-profile factors extracted, with the
returned part of the second step. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
open CenteredMomentCommonPairedSource
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The bound for the normalized columns of the final daughters of a LOW child, after both allocation layers, with the
returned part of the second step. -/
def LowColumnStmt [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Kcls : ℝ, ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C
      g.datum.D g.datum.inactive
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
    ∀(v₁ : O)(Tz : ℝ),
      (∀(W' : ℝ)(hW' : st.width≤W'),Presented η₀ Z (widenState st W' hW') v₁ Tz) →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∃Ret : ℝ,0≤Ret ∧
      ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ st.rowWidth lossFloor
        (Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-unit*Cycle63.Optimization.fixedDeletion cell+gridSlack)
        (unit*Cycle63.Optimization.secondAmp cell+ampSlack) Kcls
        (Z^(2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh)))
        Ret ∧
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
          rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)*Z^pad

/-- The bound for the final daughters through both allocation layers gives the bound for the normalized columns. -/
theorem lowColumn_of_common [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (heshell : 0<εshell)
    (hcommon : LowCommonStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented) :
    LowColumnStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell
      Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented := by
  obtain ⟨K,hK,hpoint⟩ := actual_uniform_second_column_extraction (α:=α) εshell heshell
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,Sp,Kcls,C,hC,hbound⟩ := hcommon η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,Sp,Kcls,K*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps v₁ Tz hpres
    hQM' hQη low
  obtain ⟨Ret,hRet0,hRet,hh⟩ := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q g χ hP hPN Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps v₁ Tz hpres
  refine ⟨Ret,hRet0,hRet,?_⟩
  intro zs weight hnonneg hkeep hweight
  have hh := hh zs weight hkeep hweight
  have hT0 : 0<2*T := by linarith
  have hmajor : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      K*(2*T)^εshell*(∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun D hD => Finset.sum_le_sum fun z hz => ?_
    have hp:=mul_le_mul_of_nonneg_left
      (hpoint (liveIndices q.B₁.val) src q.E₂ hE₂ q.R₂ seed D hseed (hDs D hD).1 z) (hnonneg z hz)
    apply hp.trans
    have hd:=Real.rpow_le_rpow (Nat.cast_nonneg D.absNorm) (hDs D hD).2.2.le heshell.le
    have hc:=common_retained_cost_nonneg src q.E₂ q.R₂ D z
    have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK.le)
      (mul_nonneg (hnonneg z hz) hc)
    convert hbnd using 1; ring
  apply hmajor.trans
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤K*(2*T)^εshell)).trans_eq
  rw [show 3*εshell=εshell+2*εshell by ring,Real.rpow_add hT0 εshell (2*εshell)]
  ring

/-- The bound for the normalized columns of the final daughters of a LOW child, with the fixed source-profile factors
extracted and the returned part of the second step. -/
def LowFixedColumnsStmt [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Kcls : ℝ, ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C
      g.datum.D g.datum.inactive
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
    ∀(v₁ : O)(Tz : ℝ),
      (∀(W' : ℝ)(hW' : st.width≤W'),Presented η₀ Z (widenState st W' hW') v₁ Tz) →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∃Ret : ℝ,0≤Ret ∧
      ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ st.rowWidth lossFloor
        (Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-unit*Cycle63.Optimization.fixedDeletion cell+gridSlack)
        (unit*Cycle63.Optimization.secondAmp cell+ampSlack) Kcls
        (Z^(2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh)))
        Ret ∧
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*(2*b^2*Cs^(4*N))*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
          rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)*Z^pad

/-- The bound for the normalized columns gives the bound with the fixed source-profile factors extracted. -/
theorem lowFixedColumns_of_column [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (hCs : 1≤Cs) (hb : 1≤b)
    (hcolumn : LowColumnStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented) :
    LowFixedColumnsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell
      N Cs Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,Sp,Kcls,Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,Sp,Kcls,Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hunit hω hξ hMcap' hfit hzslot haff q cell amp g χ hP hPN st src nominal δwidth padding
    seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps v₁ Tz hpres hQM' hQη low
  obtain ⟨Ret,hRet0,hRet,hh⟩ := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hunit hω hξ hMcap' hfit hzslot haff q g χ hP hPN seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps v₁ Tz hpres
  refine ⟨Ret,hRet0,hRet,?_⟩
  intro zs weight hnonneg hkeep hweight
  have hh := hh zs weight hnonneg hkeep hweight
  have hprofile : src.toData.profileFactor*(∏j,src.M j)^2≤2*b^2*Cs^(4*N) :=
    actual_child_low_profile_factor N Cs b hCs hb s hcard hmass hsb₁ hsb₂ q.C₁ q.R₁ q.B₁
      q.η₁ (g.datum.τ χ) q.t₁ v
  let R := QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
    (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
      rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)*Z^pad
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hZE : 0≤Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+
      2*ε*d*(Fintype.card α:ℝ)+rate*padding+Cycle63.AffineLedger.q*mesh+
      Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂) := Real.rpow_nonneg (zero_le_one.trans hZ.le) _
  have hR : 0≤R := by dsimp only [R]; positivity
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprofile hCg.le) hR
  apply hh.trans
  convert hbnd using 1 <;> dsimp only [R] <;> ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
