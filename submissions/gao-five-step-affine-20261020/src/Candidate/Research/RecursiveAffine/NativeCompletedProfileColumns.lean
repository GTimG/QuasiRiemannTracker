import Candidate.Research.RecursiveAffine.NativeCompletedColumns
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Candidate.Research.RecursiveAffine.NativeCommonMap
import Candidate.Cycle63.Physical.InitialHeight
/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeAnnular CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentInductionEnergy CenteredMomentDivisorAllocation
open CenteredMomentCanonicalFirst
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle153SourceReturn Cycle153RegionalLow
open Cycle153Reachable Cycle153HighProvider Cycle63InitialMass Cycle63Moment
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource

attribute [local irreducible] nativeColumnPhysicalFactor

attribute [local irreducible] nodeOfNativeContinuation

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {Current : Type} [Fintype Current]
local instance selectedProfileCurrentDecidableEq : DecidableEq Current := Classical.decEq _
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/- The actual Column source normalized by its original finite profile family.
No energy estimate is a premise: the only provider is the exact checked native
CompletedColumnsAt source operator. The SAME selected daughter/R/out is retained. -/
def CompletedProfileColumnsAt
    (hH : RayOrthogonality.globalUnits M    ≤    H)
    (W : ℝ→ℂ)(hWs : Function.support W   ⊆   Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed    ≤    M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed    ≤    Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1    ≤    Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100    ≤    HeckeZeroSupremum.beta)
    (childStage : Fin 4) (embedding : Current↪alpha)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0    ≤    Bmask)(hMcap : 0<Mcap) (hRw : 0    ≤    Rwidth) (hdmax : 0    ≤    dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0    ≤    heightExponent)
    (hbudget : 8*e*Rwidth+kappa    ≤    epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin    ≤    d) (hdm : d    ≤    dmax)
    (hq0 : 0    ≤    q) (hq1 : q    ≤    1) (inputBound epsShell : ℝ)(hShell : 0<epsShell) (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))
    (Kterminal Cpay Kcol Zparent : ℝ)(Nbudget : ℕ)(Cs : ℝ) : Prop :=
    ∀(C : SourceContext (α:=alpha) M H)(hCW : C.W=W)(hCeta : C.etaSeed=etaSeed)(hCQ : C.Q=Qfixed),
    ∀(hZ : 1<Zparent)(parentUnit : ℝ)(hparentUnit : 0<parentUnit)
      (hbase : Zparent=C.globalBase^parentUnit)
      (s : Input Current)(t height mesh a del : ℝ)(i : ℕ),
    Matches M H hH s C.etaSeed (fun j=>C.theta (embedding j))
      (fun j=>C.originalWeight (embedding j)/parentUnit) (fun j=>C.sigma (embedding j)) (fun j=>C.frequency (embedding j))
      C.W 2 Zparent →
    Fintype.card Current ≤ Nbudget → (∀j : Current,s.M j ≤ Cs) →
    s.b₁=(9/4:ℝ) → s.b₂=(9/4:ℝ) →
    (∀j : Current,(C.originalWeight (embedding j)/parentUnit)/d    ≤    Rwidth) →
    (∀j : Current,C.originalWeight (embedding j)/parentUnit    ≤
      Cycle25.Energy.commonMesh Mcap Bmask Lbound epsOld) →
    0    ≤    mesh → (∀j : Current,C.originalWeight (embedding j)/parentUnit    ≤    mesh) →
    ∀(hheight : 0    ≤    height)(hfreq : ∀j : Current,|C.frequency (embedding j)|    ≤    height),
    51/100    ≤    a → a    ≤    (1+q)/2 → 0    ≤    del →
    |t|+height+Zparent^tau/2    ≤    (3*i+2:ℕ)*Zparent^tau →
    (3+(3*i+2:ℕ)*Zparent^tau)^2    ≤    (Zparent^d)^heightExponent →
    ∀(ch : Chain s)(chi : Character)(Q : Ideal O)(hP : ch.R₂*ch.E₂≠0)
      (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)   ≤   Zparent^Bmask)(radius : ℝ)
      (Ccommon Dcommon : Ideal O)(Ucommon : Finset (CommonIndex Ccommon Dcommon))
      (Ds : Finset (Ideal O))(zs : Finset O)(rowWeight : O→ℝ)(T pad : ℝ)
      (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂),
    let st := retainedState Zparent Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
      radius Ccommon Dcommon Ucommon
    let firstInput := withHeight ch.first chi t
    firstInput.upper   ≤   inputBound → 1   ≤   T →
    (∀D∈Ds,Squarefree D ∧ T   ≤   (D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    st.width   ≤   Mcap →
    ∀(hQM : st.fixedModulus   ≤   M)(hQeta : st.fixedModulus   ≤   C.etaSeed.modulus),
    let low := ActualLow M H hH st C.etaSeed hQM hQeta a e (3*(i+1:ℕ)*Zparent^tau)
    (∀z,st.radial.keep z ∧ low z → 0   ≤   (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
    (∀z∈zs,0   ≤   rowWeight z) → (∀z∈zs,st.radial.keep z ∧ low z) →
    (∀z∈zs,rowWeight z   ≤   (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
    (∀B : actualAllocations firstInput.pools ch.E₂,commonScalar firstInput ch.E₂ ch.R₂ B≠0 →
      (commonData firstInput ch.E₂ ch.R₂ B).toSource.allowance Zparent   ≤   pad) →
    ∀(u : ℝ)(hu : 0<u)(hu1 : u   ≤   1)(hwidth : st.width   ≤   u)
      (hwide : (397/1000:ℝ)   ≤   u)(huMcap : u   ≤   Mcap)(p : Profiles (1/4) (9/4)),
    s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
    let Daughter := PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src := fun daughter : Daughter=>commonData firstInput ch.E₂ ch.R₂ daughter.1
    let J := fun daughter : Daughter=>(CenteredMomentDivisorRaw.liveIndices daughter.2.1.1 daughter.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ daughter.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    let continues := fun (daughter : Daughter)(R : Finset Current)=>nativeMainContinuation st u (J daughter) R
      (fun j=>C.originalWeight (embedding j)/parentUnit)
      (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
      (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1)
    (∀daughter : Daughter,rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0   ≤   Zparent^Lbound) →
    (∀daughter : Daughter,rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1   ≤   Zparent^Lbound) →
    ∀(P : PrefixHighPresentation (prefixDictionary childStage.val C.etaSeed) st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ)   ≤   C.globalBase^(prefixCap childStage.val))
      (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)
      (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
      (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ)),
    (∀N : ReachableNode C childStage,Nonempty (NodeOutput hH N
      (constant childStage) (eps childStage) (Bsrc childStage) (control childStage) (degree childStage) (boxes childStage))) →
    0   ≤   constant childStage → 0   ≤   eps childStage →
    ∀(childMask : ∀(daughter : Daughter)
      (hn : commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
      (liveRow : O)(hne : Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 liveRow≠0)(R : Finset Current),R  ⊆  J daughter →
      (∑j∈R,C.originalWeight (embedding j)/parentUnit)   ≤   del+mesh →
      (R=J daughter ∨ del   ≤   ∑j∈R,C.originalWeight (embedding j)/parentUnit) →
      continues daughter R → (st.puncture.absNorm:ℝ)   ≤   (Zparent^u)^(20:ℝ)),
    ∀(childGeometry : ∀(daughter : Daughter)
      (hn : commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
      (liveRow : O)(hne : Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 liveRow≠0)(R : Finset Current),R  ⊆  J daughter →
      (∑j∈R,C.originalWeight (embedding j)/parentUnit)   ≤   del+mesh →
      (R=J daughter ∨ del   ≤   ∑j∈R,C.originalWeight (embedding j)/parentUnit) →
      continues daughter R →
      NativeChildGeometry C childStage Zparent parentUnit u (((J daughter\R).map embedding))
        (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
        (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1)),
    ∀(childHistory : ∀(daughter : Daughter)
      (hn : commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
      (liveRow : O)(hne : Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 liveRow≠0)(R : Finset Current)(hR : R  ⊆  J daughter)
      (hsum : (∑j∈R,C.originalWeight (embedding j)/parentUnit)   ≤   del+mesh)
      (hcover : R=J daughter ∨ del   ≤   ∑j∈R,C.originalWeight (embedding j)/parentUnit)
      (hcontinue : continues daughter R),
      let geom := childGeometry daughter hn liveRow hne R hR hsum hcover hcontinue
      Real.logb C.globalBase (st.puncture.absNorm:ℝ)   ≤
        modelMissing childStage geom.coordinates+modelReduction childStage geom.coordinates+
          ((childStage.val:ℝ)+1)/1000000000000000),
    let Env : ℝ := Cpay^(Fintype.card Current)*(Kterminal+constant childStage)*
      QuadraticInitialBound.diagonalControl st.radial.profile*
      (p.control (controlTerminal ∪ control childStage))^2*
      (1+|t|+height)^(max degreeTerminal (degree childStage))
    let Old : ℝ := u+epsOld+epsReflect+eps childStage+2*epsilon*d*(Fintype.card Current:ℝ)+q*(del+mesh)
    let ColumnEnergy : ℝ := ∑D∈Ds,∑z∈zs,rowWeight z*‖normalizedColumn firstInput ch.E₂ hOwn ch.R₂ seed D z‖^2
    let PhysicalFactor : ℝ := (2*(9/4:ℝ)^2*Cs^(4*Nbudget))*(ch.E₂.absNorm:ℝ)^(epsShell-1)*
      (2*T)^(3*epsShell)*Zparent^pad
    let Trace := fun (daughter : Daughter)(R : Finset Current)
      (F : SuffixFamily (hH:=hH) childStage.val (4-childStage.val) C.etaSeed Zparent C.Bnorm C.Tz P.mult)=>
      (F=emptyReturnedForest ∧ ∀z,Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 z=0) ∨
      ∃(hn : commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
        (liveRow : O)(hne : Cycle63.Physical.sourcePositiveRow (src daughter).toSource
          daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 liveRow≠0)
        (hR : R ⊆ J daughter)
        (hsum : (∑j∈R,C.originalWeight (embedding j)/parentUnit)  ≤  del+mesh)
        (hcover : R=J daughter ∨ del  ≤  ∑j∈R,C.originalWeight (embedding j)/parentUnit),
      let second := daughter.2.2.2
      let L := daughter.2.1.1
      let alloc := daughter.2.2.1.1
      let src := src daughter
      let J := J daughter
      let continues := continues daughter
      ((F=emptyReturnedForest ∧ ¬continues R) ∨
    ∃hcontinue : continues R,
    let hmask := childMask daughter hn liveRow hne R hR hsum hcover hcontinue
    let child := nodeOfNativeContinuation C childStage Zparent parentUnit u Bmask hu hbase
      st hwidth hmask (((J\R).map embedding)) p
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
      (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
      P hPnorm hfixed t height hheight
      (nativeMappedFrequencyBound embedding J R C.frequency height hfreq)
      (childGeometry daughter hn liveRow hne R hR hsum hcover hcontinue) (childHistory daughter hn liveRow hne R hR hsum hcover hcontinue)
    ∃out : NodeOutput hH child (constant childStage) (eps childStage) (Bsrc childStage)
      (control childStage) (degree childStage) (boxes childStage),
    F.value=out.family.value)
    (((∀daughter : Daughter,commonScalar firstInput ch.E₂ ch.R₂ daughter.1=0) ∧
      ColumnEnergy ≤ Kcol*PhysicalFactor*(Env*Zparent^Old)) ∨
    ∃(daughter : Daughter),commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0 ∧
    ∃(R : Finset Current)(F : SuffixFamily (hH:=hH) childStage.val (4-childStage.val)
      C.etaSeed Zparent C.Bnorm C.Tz P.mult),Trace daughter R F ∧
      ColumnEnergy ≤ Kcol*PhysicalFactor*(Env*(Zparent^Old+
        Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+q*((∑j∈R,C.originalWeight (embedding j)/parentUnit)+mesh))*F.value)))


attribute [local irreducible] CompletedProfileColumnsAt

theorem actual_completed_profile_columns
    (hH : RayOrthogonality.globalUnits M    ≤    H)
    (W : ℝ→ℂ)(hWs : Function.support W   ⊆   Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed    ≤    M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed    ≤    Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1    ≤    Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100    ≤    HeckeZeroSupremum.beta)
    (childStage : Fin 4) (embedding : Current↪alpha)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0    ≤    Bmask)(hMcap : 0<Mcap) (hRw : 0    ≤    Rwidth) (hdmax : 0    ≤    dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0    ≤    heightExponent)
    (hbudget : 8*e*Rwidth+kappa    ≤    epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin    ≤    d) (hdm : d    ≤    dmax)
    (hq0 : 0    ≤    q) (hq1 : q    ≤    1) (inputBound epsShell : ℝ)(hShell : 0<epsShell) (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))
    (Kterminal Cpay Kcol Zparent : ℝ)(Nbudget : ℕ)(Cs : ℝ)
    (hCs : 1 ≤ Cs)(hKterminal : 0<Kterminal)(hCpay : 1≤Cpay)(hKcol : 0≤Kcol)
    (hsource : CompletedColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent) :
    CompletedProfileColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent Nbudget Cs := by
  unfold CompletedProfileColumnsAt
  intro C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
    hmatch hcard hmass hsb1 hsb2 hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh ch chi Q hP hPN
    radius Ccommon Dcommon Ucommon Ds zs rowWeight T pad hOwn seed hseed st firstInput
    hInput hT hDs hMcapNow hQM hQeta low hPhi hrow0 hkeep hrow hallow
    u hu hu1 hwidth hwide huMcap p hp1 hp2 Daughter src J continues hX1bound hX2bound
    P hPnorm hfixed constant eps Bsrc control degree boxes hIH hconstant heps
    childMask childGeometry childHistory Env Old ColumnEnergy PhysicalFactor Trace
  have hz0 : 0<Zparent:=zero_lt_one.trans hZ
  have hprofile : firstInput.toData.profileFactor*(∏j,firstInput.M j)^2≤2*(9/4:ℝ)^2*Cs^(4*Nbudget) :=
    actual_child_low_profile_factor Nbudget Cs (9/4) hCs (by norm_num) s hcard hmass hsb1 hsb2
      ch.C₁ ch.R₁ ch.B₁ ch.η₁ chi ch.t₁ t
  have hEnv : 0≤Env := by
    have hd:=QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    dsimp only [Env];positivity
  have hfactor : nativeColumnPhysicalFactor firstInput ch.E₂ epsShell T Zparent pad≤PhysicalFactor := by
    unfold nativeColumnPhysicalFactor
    dsimp only [PhysicalFactor]
    have htail : 0≤(ch.E₂.absNorm:ℝ)^(epsShell-1)*(2*T)^(3*epsShell)*Zparent^pad := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprofile htail
  unfold CompletedColumnsAt at hsource
  have hraw:=hsource C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
    hmatch hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh ch chi Q hP hPN
    radius Ccommon Dcommon Ucommon Ds zs rowWeight T pad hOwn seed hseed
    hInput hT hDs hMcapNow hQM hQeta hPhi hrow0 hkeep hrow hallow
    u hu hu1 hwidth hwide huMcap p hp1 hp2 hX1bound hX2bound
    P hPnorm hfixed constant eps Bsrc control degree boxes hIH hconstant heps
    childMask childGeometry childHistory
  rcases hraw with hzero|hselected
  · refine Or.inl ⟨hzero.1,?_⟩
    exact hzero.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hKcol)
      (mul_nonneg hEnv (Real.rpow_nonneg hz0.le _)))
  · obtain ⟨daughter,hn,R,F,htrace,henergy⟩:=hselected
    refine Or.inr ⟨daughter,hn,R,F,htrace,?_⟩
    have hvalue:=F.value_nonneg hz0.le
    have htail : 0≤Env*(Zparent^Old+Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+
        q*((∑j∈R,C.originalWeight (embedding j)/parentUnit)+mesh))*F.value) := by positivity
    exact henergy.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hKcol) htail)

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_completed_profile_columns
