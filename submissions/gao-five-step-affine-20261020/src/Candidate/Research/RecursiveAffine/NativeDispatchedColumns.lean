import Candidate.Research.RecursiveAffine.NativeCompletedProfileColumns
import Candidate.Research.RecursiveAffine.NativeDirectProfileColumns
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Candidate.Research.RecursiveAffine.NativeCommonMap
import Candidate.Cycle63.Physical.InitialHeight
/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
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
open Cycle153Reachable Cycle153HighProvider Cycle63InitialMass Cycle63Moment Cycle63FinalCapacity
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource

attribute [local irreducible] nativeColumnPhysicalFactor

attribute [local irreducible] nodeOfNativeContinuation

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {Current : Type} [Fintype Current]
local instance dispatchedColumnCurrentDecidableEq : DecidableEq Current := Classical.decEq _
variable [Cycle63.AffineLedger]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/- The actual Column source normalized by its original finite profile family.
No energy estimate is a premise: the only provider is the exact checked native
CompletedColumnsAt source operator. The SAME selected daughter/R/out is retained. -/
/-- Add the other genuine branch constant and widen only the OLD exponent. -/
theorem column_branch_to_union {Z C D factor old target ret : ℝ}
    (hZ : 1<Z)(hC : 0≤C)(hD : 0≤D)(hf : 0≤factor)(hret : 0≤ret)
    (hpow : old≤target) :
    C*factor*(Z^old+ret)≤(C+D)*factor*(Z^target+ret) := by
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le hpow
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hf)
    (add_le_add hp le_rfl) (add_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hret)
    (mul_nonneg (add_nonneg hC hD) hf)

def DispatchedColumnsAt
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
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C₀ C₁ Kdirect : ℝ) : Prop :=
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
    ∀(ch : Chain s)(Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax : ℝ)
      (budget : ℕ)(g : LiveMainGeometry s ch Zparent Mrow amp omega xi bs budget)
      (ray : RayFourExpansion.RayCharacter)(Q : Ideal O)(hP : ch.R₂*ch.E₂≠0)
      (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤Zparent^Bmask)
      (Ds : Finset (Ideal O))(zs : Finset O)(rowWeight : O→ℝ)(T pad : ℝ)
      (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂),
    let chi:=g.datum.τ ray
    let st:=retainedState Zparent Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first chi t
    let nominal:=secondNominal 1 Zparent amp omega ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    1≤bs→s.upper≤bs→
    (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Zparent (s.P j) ∧
      (∑j,Real.logb Zparent (s.P j))≤Cycle63.AffineLedger.slotTop)→
    length Zparent s.X₁+length Zparent s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Zparent (s.P j))≤Cycle63.AffineLedger.B→
    Mrow+Real.logb Zparent (s.η.modulus.absNorm:ℝ)≤1+epsWidth/2→
    Real.logb Zparent CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(budget:ℝ)*Real.logb Zparent bs+Real.logb Zparent 1+
      Real.logb Zparent (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤epsWidth/2→
    0≤epsWidth→0≤xi→0≤omega→0≤epsPad→
    supportPadding (Fintype.card Current) bs s.b₁ s.b₂ Zparent≤epsPad→
    omega≤omegaMax→epsWidth+xi/2≤deltaMax→q/(6*Cycle63.Optimization.slotPrice)≤1/2→
    Cycle63.AffineLedger.lowReserve≤amp→
    (q/(6*Cycle63.Optimization.slotPrice)*
      (Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Zparent (s.P j))))+6*amp)-amp)+
      Cycle63.AffineLedger.lowReserve+q/(6*Cycle63.Optimization.slotPrice)*(deltaMax+epsPad)+
      2*(q/(6*Cycle63.Optimization.slotPrice))*omegaMax≤
        q/(6*Cycle63.Optimization.slotPrice)*(1-6*amp-2*(397/1000:ℝ))→
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
    ∀(u : ℝ)(hu1 : u   ≤   1)(hwidth : st.width   ≤   u)
      (hunit : u=nominal+(epsWidth+xi/2))(huMcap : u   ≤   Mcap)(p : Profiles (1/4) (9/4)),
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
    let OldWide : ℝ := u+epsOld+epsReflect+eps childStage+2*epsilon*d*(Fintype.card Current:ℝ)+q*(del+mesh)
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
    let child := nodeOfNativeContinuation C childStage Zparent parentUnit u Bmask
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hcontinue.1) hbase
      st hwidth hmask (((J\R).map embedding)) p
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
      (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
      P hPnorm hfixed t height hheight
      (nativeMappedFrequencyBound embedding J R C.frequency height hfreq)
      (childGeometry daughter hn liveRow hne R hR hsum hcover hcontinue) (childHistory daughter hn liveRow hne R hR hsum hcover hcontinue)
    ∃out : NodeOutput hH child (constant childStage) (eps childStage) (Bsrc childStage)
      (control childStage) (degree childStage) (boxes childStage),
    F.value=out.family.value)
    let EnvDirect : ℝ:=Cdirect^(Fintype.card Current)*((C₀+C₁)*
      QuadraticInitialBound.diagonalControl st.radial.profile*(p.control controlDirect)^2*
      (1+|t|+height)^degreeDirect)
    let OldDirect : ℝ:=nominal+(epsWidth+xi/2)+amp-Cycle63.AffineLedger.lowReserve+
      lowAllowance Zparent ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂+
      epsOld+2*epsilon*d*(Fintype.card Current:ℝ)+
      q/(6*Cycle63.Optimization.slotPrice)*(omega+epsPad)+q*mesh
    ∃(R : Finset Current)(F : SuffixFamily (hH:=hH) childStage.val (4-childStage.val)
      C.etaSeed Zparent C.Bnorm C.Tz P.mult),
      (F=emptyReturnedForest ∨ ∃daughter : Daughter,
        commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0 ∧ Trace daughter R F) ∧
      ColumnEnergy≤(Kcol*Env+Kdirect*EnvDirect)*PhysicalFactor*
        (Zparent^(max OldWide OldDirect)+
          Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+
            q*((∑j∈R,C.originalWeight (embedding j)/parentUnit)+mesh))*F.value)

attribute [local irreducible] DispatchedColumnsAt

theorem actual_dispatched_columns
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
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C₀ C₁ Kdirect : ℝ)
    (hCs : 1≤Cs)(hKterminal : 0<Kterminal)(hCpay : 1≤Cpay)(hKcol : 0≤Kcol)
    (hCdirect : 0≤Cdirect)(hC₀ : 0≤C₀)(hC₁ : 0≤C₁)(hKdirect : 0≤Kdirect)
    (hwideSource : CompletedColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal
      Kterminal Cpay Kcol Zparent)
    (hdirectSource : DirectColumnsAt (α:=Current) M H hH W Bmask Lbound Mcap epsOld hWs hW hBmask hMcap hOld hbeta
      Rwidth dmax tau epsilon e kappa heightExponent margin d q hRw hdmax htau hepsilon he he' hkappa
      hheightExponent hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
      degreeDirect controlDirect etaSeed Qfixed Cdirect C₀ C₁ Kdirect Zparent) :
    DispatchedColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal
      Kterminal Cpay Kcol Zparent Nbudget Cs degreeDirect controlDirect Cdirect C₀ C₁ Kdirect := by
  have hwideProfile:=actual_completed_profile_columns hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal
      Kterminal Cpay Kcol Zparent Nbudget Cs hCs hKterminal hCpay hKcol hwideSource
  have hdirectProfile:=actual_direct_profile_columns (α:=Current) M H hH W Bmask Lbound Mcap epsOld hWs hW hBmask hMcap hOld hbeta
      Rwidth dmax tau epsilon e kappa heightExponent margin d q hRw hdmax htau hepsilon he he' hkappa
      hheightExponent hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
      degreeDirect controlDirect etaSeed Qfixed Cdirect C₀ C₁ Kdirect Zparent Nbudget Cs hCs hCdirect hC₀ hC₁ hKdirect hdirectSource
  unfold CompletedProfileColumnsAt at hwideProfile
  unfold DirectProfileColumnsAt at hdirectProfile
  unfold DispatchedColumnsAt
  intro C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
    hmatch hcard hmass hsb1 hsb2 hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh
    ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax budget g ray Q hP hPN
    Ds zs rowWeight T pad hOwn seed hseed chi st firstInput nominal
    hb hs hslots haff hfit hconstants hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate hreserve hcert
    hInput hT hDs hMcapNow hQM hQeta low hPhi hrow0 hkeep hrow hallow
    u hu1 hwidth hunit huMcap p hp1 hp2 Daughter src J continues hX1bound hX2bound
    P hPnorm hfixed constant eps Bsrc control degree boxes hIH hconstant heps
    childMask childGeometry childHistory Env OldWide ColumnEnergy PhysicalFactor Trace EnvDirect OldDirect
  have hZ0 : 0<Zparent:=zero_lt_one.trans hZ
  have hd:=QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hEnv : 0≤Env := by dsimp only [Env];positivity
  have hEnvDirect : 0≤EnvDirect := by dsimp only [EnvDirect];positivity
  have hPhysical : 0≤PhysicalFactor := by dsimp only [PhysicalFactor];positivity
  have hcoeff : 0≤Kcol*Env:=mul_nonneg hKcol hEnv
  have hcoeffDirect : 0≤Kdirect*EnvDirect:=mul_nonneg hKdirect hEnvDirect
  by_cases hwide : (397/1000:ℝ)≤u
  · have hu : 0<u:=lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hwide
    have hactual:=hwideProfile C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
      hmatch hcard hmass hsb1 hsb2 hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh
      ch chi Q hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive Ds zs rowWeight T pad hOwn seed hseed
      hInput hT hDs hMcapNow hQM hQeta hPhi hrow0 hkeep hrow hallow
      u hu hu1 hwidth hwide huMcap p hp1 hp2 hX1bound hX2bound P hPnorm hfixed
      constant eps Bsrc control degree boxes hIH hconstant heps childMask childGeometry childHistory
    rcases hactual with hzero|hselected
    · refine ⟨∅,emptyReturnedForest,Or.inl rfl,?_⟩
      have hbnd:=hzero.2
      have hscalar:=column_branch_to_union hZ hcoeff hcoeffDirect hPhysical (by norm_num : (0:ℝ)≤0)
        (le_max_left OldWide OldDirect)
      simp only [emptyReturnedForest_value,mul_zero,add_zero]
      apply hbnd.trans
      convert hscalar using 1 <;> ring
    · obtain ⟨daughter,hn,R,F,htrace,hbound⟩:=hselected
      refine ⟨R,F,Or.inr ⟨daughter,hn,htrace⟩,?_⟩
      have hret : 0≤Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+
          q*((∑j∈R,C.originalWeight (embedding j)/parentUnit)+mesh))*F.value := by
        exact mul_nonneg (Real.rpow_nonneg hZ0.le _) (F.value_nonneg hZ0.le)
      have hscalar:=column_branch_to_union hZ hcoeff hcoeffDirect hPhysical hret
        (le_max_left OldWide OldDirect)
      apply hbound.trans
      convert hscalar using 1 <;> ring
  · have hnarrow : nominal+(epsWidth+xi/2)<(397/1000:ℝ) := by
      rw [←hunit];exact lt_of_not_ge hwide
    have hraw : ColumnEnergy≤Kdirect*(2*(9/4:ℝ)^2*Cs^(4*Nbudget))*
        (EnvDirect*Zparent^OldDirect)*(ch.E₂.absNorm:ℝ)^(epsShell-1)*
        (2*T)^(3*epsShell)*Zparent^pad := by
      subst W;subst etaSeed;subst Qfixed
      exact hdirectProfile hZ s (fun j=>C.theta (embedding j)) (fun j=>C.originalWeight (embedding j)/parentUnit)
        (fun j=>C.sigma (embedding j)) (fun j=>C.frequency (embedding j)) t height mesh a i
        hmatch hcard hmass hsb1 hsb2
        (fun j=>div_nonneg (C.originalWeight_nonneg (embedding j)) hparentUnit.le)
        hwOld hmesh hwm hwr (fun j=>(C.sigma_fixed (embedding j)).1)
        (fun j=>(C.sigma_fixed (embedding j)).2) hheight hfreq ha ha' hfreqbin hhigh
        ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax (397/1000:ℝ) budget g ray Q hP hPN
        hfixed hMcapNow p hp1 hp2 hb hs hslots haff hfit hconstants hepsWidth hxi homega hepsPad hpad
        homegaMax hdeltaMax hrate hreserve hnarrow hcert hQM hQeta Ds zs rowWeight T pad seed hOwn hseed
        hInput hT hDs hPhi hrow0 hkeep hrow hallow hX1bound hX2bound
    refine ⟨∅,emptyReturnedForest,Or.inl rfl,?_⟩
    simp only [emptyReturnedForest_value,mul_zero,add_zero]
    have hscalar:=column_branch_to_union hZ hcoeffDirect hcoeff hPhysical (by norm_num : (0:ℝ)≤0)
      (le_max_right OldWide OldDirect)
    apply hraw.trans
    convert hscalar using 1 <;> dsimp only [PhysicalFactor] <;> ring

/-- The complete genuine source schedule: BOTH branches and their constants
are chosen before the moving context, physical source, detector allocation,
source attainer, child output and height. This constructs the source predicate;
it does not postulate a column-energy estimate. -/
theorem eventual_actual_dispatched_columns
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
    (hq0 : 0    ≤    q) (hq1 : q    ≤    1) (inputBound epsShell : ℝ)(hShell : 0<epsShell)
    (Nbudget : ℕ)(Cs : ℝ)(hCs : 1≤Cs) :
    ∃(degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
      (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C₀ C₁ Kdirect : ℝ),
      0<Kterminal ∧ 1≤Cpay ∧ 0<Kcol ∧ 1≤Cdirect ∧ 0<C₀ ∧ 0<C₁ ∧ 0<Kdirect ∧
      ∀ᶠZparent : ℝ in atTop,1<Zparent ∧
      DispatchedColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent Nbudget Cs
        degreeDirect controlDirect Cdirect C₀ C₁ Kdirect := by
  obtain ⟨degreeTerminal,controlTerminal,Kterminal,hKterminal,Cpay,hCpay,Kcol,hKcol,hwide⟩:=eventual_actual_completed_columns_forest (Current:=Current) hH W hWs hW etaSeed Qfixed
      hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect hLbound hOld hReflect hbeta childStage embedding
      Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
      hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
  obtain ⟨degreeDirect,controlDirect,hdirs⟩:=eventual_actual_direct_columns (α:=Current) M H hH W Bmask Lbound Mcap epsOld hWs hW
      hBmask hMcap hOld hbeta Rwidth dmax tau epsilon e kappa heightExponent margin d q
      hRw hdmax htau hepsilon he he' hkappa hheightExponent hbudget hmargin hd hdsupply hdm hq0 hq1
      inputBound epsShell hShell
  obtain ⟨Cdirect,C₀,C₁,Kdirect,hCdirect,hC₀,hC₁,hKdirect,hdirect⟩:=
    hdirs etaSeed Qfixed hQfixedM hQ0 hQt hQ72
  refine ⟨degreeTerminal,controlTerminal,Kterminal,Cpay,Kcol,degreeDirect,controlDirect,Cdirect,C₀,C₁,Kdirect,
    hKterminal,hCpay,hKcol,hCdirect,hC₀,hC₁,hKdirect,?_⟩
  filter_upwards [hwide,hdirect] with Zparent hw hdirectNow
  refine ⟨hw.1,?_⟩
  exact actual_dispatched_columns hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent Nbudget Cs
    degreeDirect controlDirect Cdirect C₀ C₁ Kdirect hCs hKterminal hCpay hKcol.le
    (zero_le_one.trans hCdirect) hC₀.le hC₁.le hKdirect.le hw.2 hdirectNow.2

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_dispatched_columns

#print axioms OAI.SevenEighths.Cycle153ActualColumn.eventual_actual_dispatched_columns
