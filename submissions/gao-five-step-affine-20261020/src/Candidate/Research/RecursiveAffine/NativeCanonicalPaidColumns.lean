import Candidate.Research.RecursiveAffine.NativeUniformPaidColumns
import Candidate.Research.RecursiveAffine.NativeCanonicalActual
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Candidate.Research.RecursiveAffine.NativeCommonMap
import Candidate.Cycle63.Physical.InitialHeight
/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 600000
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
open Cycle153SourceSchedule Cycle153AnalyticPrimitive CenteredMomentSectorLocalization CenteredExceptionalProfile CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource

attribute [local irreducible] nativeColumnPhysicalFactor

attribute [local irreducible] nodeOfNativeContinuation
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant NativeColumnOutputTrace

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {Current : Type} [Fintype Current] [decCurrent : DecidableEq Current]
variable [Cycle63.AffineLedger]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

open Cycle153CanonicalLow ActualEisensteinCubic ConcretePrimeRowBridge LocalMoment CompletedGauss
open CenteredMomentSecondHeightFamily
/- The actual canonical LOW selector supplies the physical admission and
unit row weight; no keep/energy gate is passed to this caller. -/
def NativeCanonicalPaidColumnsAt
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
    (epsNode : ℝ) : Prop :=
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
      (Ds : Finset (Ideal O))(zs : Finset O)(T pad : ℝ)
      (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂),
    let chi:=g.datum.τ ray
    let st:=retainedState Zparent Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first chi t
    let nominal:=secondNominal 1 Zparent amp omega ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let cell:=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Zparent (s.P j)))
    amp=Cycle63.AffineLedger.amp cell→
    del=(Cycle63.AffineLedger.regionGap cell+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+detectorExtra→
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
    ∀(datum : SecondInputDatum Current)(second : Bool)
      (frame : CanonicalSourceFrame s ch g datum second)
      (chi0 chi psi : RayFourExpansion.RayCharacter)(m : O)(hm : m≠0)
      (hml : goodLambda∣m)(hm2 : (2:O)∣m)
      (hQ72source : Q≤Ideal.span {(72:O)})(hTsource : 2<Zparent^tau)
      (hBetaHigh : HeckeZeroSupremum.beta≤7/8),
    ray=(if second then psi⁻¹ else chi) →
    a=((1+Cycle63.AffineLedger.q)/2) →
    ∀(buffer : BufferIndex e),buffer.1.val=i →
    let hp : datum.R*(if second then datum.D else datum.C)≠0 := by
      simpa only [frame.puncture_eq,frame.own_eq] using hP
    let hn : ((datum.R*(if second then datum.D else datum.C)).absNorm:ℝ)≤Zparent^Bmask := by
      simpa only [frame.puncture_eq,frame.own_eq] using hPN
    let ordinaryRows:=mainLowSourceRows second (ordinarySecondDatum datum chi0 Q m) (fun _=>True)
    let selector:=mainLowCanonicalSelector M H hH datum chi0 chi psi Q hQ72source
      m hm hml hm2 Zparent Bmask hZ second hp hn C.etaSeed hQM hQeta
      e (Zparent^tau) he hTsource hbeta hBetaHigh
    (∀z∈zs,z∈mainLowPaymentRows ordinaryRows selector buffer) →
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
    eps childStage≤oldLoss epsNode→
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
    let ColumnEnergy : ℝ := ∑D∈Ds,∑z∈zs,(1:ℝ)*‖normalizedColumn firstInput ch.E₂ hOwn ch.R₂ seed D z‖^2
    let PhysicalFactor : ℝ := (2*(9/4:ℝ)^2*Cs^(4*Nbudget))*(ch.E₂.absNorm:ℝ)^(epsShell-1)*
      (2*T)^(3*epsShell)*Zparent^pad
    let childAt := fun (daughter : Daughter)
      (hn : commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
      (liveRow : O)(hne : Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 liveRow≠0)
      (R : Finset Current)(hR : R⊆J daughter)
      (hsum : (∑j∈R,C.originalWeight (embedding j)/parentUnit)≤del+mesh)
      (hcover : R=J daughter ∨ del≤∑j∈R,C.originalWeight (embedding j)/parentUnit)
      (hcontinue : continues daughter R)=>
        nodeOfNativeContinuation C childStage Zparent parentUnit u Bmask
          (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hcontinue.1) hbase
          st hwidth (childMask daughter hn liveRow hne R hR hsum hcover hcontinue)
          (((J daughter\R).map embedding)) p
          (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
          (rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1)
          (raw_daughter_scale_pos (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0)
          (raw_daughter_scale_pos (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1)
          P hPnorm hfixed t height hheight
          (by
            intro k
            obtain ⟨i,hi,hki⟩:=Finset.mem_map.mp k.property
            change |C.frequency k.val|≤height
            rw [←hki]
            exact hfreq i)
          (childGeometry daughter hn liveRow hne R hR hsum hcover hcontinue)
          (childHistory daughter hn liveRow hne R hR hsum hcover hcontinue)
    let Trace:=NativeColumnOutputTrace
      (fun daughter : Daughter=>commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0)
      (fun (daughter : Daughter)(z : O)=>Cycle63.Physical.sourcePositiveRow (src daughter).toSource
        daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 z)
      J (fun j=>C.originalWeight (embedding j)/parentUnit) del mesh continues childAt
      (constant childStage) (eps childStage) (Bsrc childStage) (control childStage)
      (degree childStage) (boxes childStage)
    let EnvDirect : ℝ:=Cdirect^(Fintype.card Current)*((C₀+C₁)*
      QuadraticInitialBound.diagonalControl st.radial.profile*(p.control controlDirect)^2*
      (1+|t|+height)^degreeDirect)
    let OldDirect : ℝ:=nominal+(epsWidth+xi/2)+amp-Cycle63.AffineLedger.lowReserve+
      lowAllowance Zparent ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂+
      epsOld+2*epsilon*d*(Fintype.card Current:ℝ)+
      q/(6*Cycle63.Optimization.slotPrice)*(omega+epsPad)+q*mesh
    let slotLoss:=2*epsilon*d*(Fintype.card Current:ℝ)
    let sourceCommon:=epsWidth+xi/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
      slotLoss+q/(6*Cycle63.Optimization.slotPrice)*(omega+epsPad)+q*mesh
    let OldPaid:=nominal+amp+sourceCommon+
      lowAllowance Zparent ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂
    let Fixed:=nativeSharedColumnFixed Nbudget (Fintype.card Current) Cs Cpay Kterminal
      (constant childStage) Kcol Cdirect C₀ C₁ Kdirect (controlTerminal ∪ control childStage)
      controlDirect (max degreeTerminal (degree childStage)) degreeDirect p t height epsShell T
    let SourceK:=nativeColumnSourceConstant Nbudget Cs Cpay Kterminal (constant childStage)
      Kcol Cdirect C₀ C₁ Kdirect
    let Control:=(p.control ((controlTerminal ∪ control childStage)∪controlDirect))^2*
      (1+|t|+height)^(max (max degreeTerminal (degree childStage)) degreeDirect)*(2*T)^(3*epsShell)
    ∃(R : Finset Current)(F : SuffixFamily (hH:=hH) childStage.val (4-childStage.val)
      C.etaSeed Zparent C.Bnorm C.Tz P.mult),
      (F=emptyReturnedForest ∨ ∃daughter : Daughter,
        commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0 ∧ Trace daughter R F) ∧
      ColumnEnergy≤SourceK*Control*(ch.E₂.absNorm:ℝ)^(epsShell-1)*
        (Zparent^OldPaid+Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+
          q*((∑j∈R,C.originalWeight (embedding j)/parentUnit)+mesh))*F.value)*Zparent^pad

attribute [local irreducible] NativeCanonicalPaidColumnsAt

theorem actual_canonical_paid_columns
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
    (epsNode : ℝ)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKterminal : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC₀ : 0≤C₀)(hC₁ : 0≤C₁)(hKdirect : 0≤Kdirect)
    (hsource : NativeUniformPaidColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal
      Kterminal Cpay Kcol Zparent Nbudget Cs degreeDirect controlDirect Cdirect C₀ C₁ Kdirect epsNode) :
    NativeCanonicalPaidColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal
      Kterminal Cpay Kcol Zparent Nbudget Cs degreeDirect controlDirect Cdirect C₀ C₁ Kdirect epsNode := by
  cases Subsingleton.elim decCurrent (Classical.decEq Current)
  unfold NativeCanonicalPaidColumnsAt
  intro C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
    hmatch hcard hmass hsb1 hsb2 hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh
    ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax budget g ray Q hP hPN
    Ds zs T pad hOwn seed hseed chi st firstInput nominal cell hamp hdelTarget
    hb hs hslots haff hfit hconstants hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate hreserve hcert
    hInput hT hDs hMcapNow hQM hQeta low datum second frame chi0 chiRay psi m hm hml hm2
    hQ72source hTsource hBetaHigh hray haLow buffer hbuffer hp hn ordinaryRows selector hzs
    hallow u hu1 hwidth hunit huMcap p hp1 hp2 Daughter src J continues hX1bound hX2bound
    P hPnorm hfixed constant eps Bsrc control degree boxes hIH hconstant heps hChild
    childMask childGeometry childHistory Env OldWide ColumnEnergy PhysicalFactor childAt Trace EnvDirect OldDirect
    slotLoss sourceCommon OldPaid Fixed SourceK Control
  have hcanonical:=actual_chain_canonical_payment_gates frame M H hH chi0 chiRay psi Q
    hQ72source m hm hml hm2 Bmask hZ hP hPN C.etaSeed hQM hQeta e (Zparent^tau)
    he hTsource hbeta hBetaHigh
  have hkeep : ∀z∈zs,st.radial.keep z ∧ low z := by
    intro z hz
    have hh:=hcanonical buffer z (hzs z hz)
    simpa only [←hray,←haLow,hbuffer] using (And.intro hh.1 hh.2.1)
  have hweight : ∀z∈zs,(1:ℝ)≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
    intro z hz
    have hh:=(hcanonical buffer z (hzs z hz)).2.2.1
    simpa only [←hray] using hh
  unfold NativeUniformPaidColumnsAt at hsource
  exact hsource C hCW hCeta hCQ hZ parentUnit hparentUnit hbase s t height mesh a del i
    hmatch hcard hmass hsb1 hsb2 hwr hwOld hmesh hwm hheight hfreq ha ha' hdel hfreqbin hhigh
    ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax budget g ray Q hP hPN
    Ds zs (fun _=>1) T pad hOwn seed hseed hamp hdelTarget
    hb hs hslots haff hfit hconstants hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate hreserve hcert
    hInput hT hDs hMcapNow hQM hQeta (fun z _=>st.radial.nonneg z)
    (fun _ _=>zero_le_one) hkeep hweight hallow
    u hu1 hwidth hunit huMcap p hp1 hp2 hX1bound hX2bound
    P hPnorm hfixed constant eps Bsrc control degree boxes hIH hconstant heps hChild
    childMask childGeometry childHistory

theorem eventual_actual_canonical_paid_columns
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
    (Nbudget : ℕ)(Cs : ℝ)(hCs : 1≤Cs)(epsNode : ℝ)(hepsNode : 0<epsNode)
    (hq : q=Cycle63.AffineLedger.q)
    (hOldLoss : epsOld≤oldLoss epsNode)(hReflectLoss : epsReflect≤oldLoss epsNode) :
    ∃(degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
      (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C₀ C₁ Kdirect : ℝ),
      0<Kterminal ∧ 1≤Cpay ∧ 0<Kcol ∧ 1≤Cdirect ∧ 0<C₀ ∧ 0<C₁ ∧ 0<Kdirect ∧
      ∀ᶠZparent : ℝ in atTop,1<Zparent ∧
      NativeCanonicalPaidColumnsAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent Nbudget Cs
        degreeDirect controlDirect Cdirect C₀ C₁ Kdirect epsNode := by
  obtain ⟨dt,St,Kt,Cpay,Kcol,dd,Sd,Cdirect,C₀,C₁,Kdirect,hKt,hCpay,hKcol,hCdirect,hC₀,hC₁,hKdirect,hsource⟩:=
    eventual_actual_uniform_native_paid_columns hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell Nbudget Cs hCs epsNode hepsNode
      hq hOldLoss hReflectLoss
  refine ⟨dt,St,Kt,Cpay,Kcol,dd,Sd,Cdirect,C₀,C₁,Kdirect,hKt,hCpay,hKcol,hCdirect,hC₀,hC₁,hKdirect,?_⟩
  filter_upwards [hsource] with Zparent hz
  refine ⟨hz.1,?_⟩
  exact actual_canonical_paid_columns hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage embedding Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell dt St Kt Cpay Kcol Zparent Nbudget Cs
    dd Sd Cdirect C₀ C₁ Kdirect epsNode hCs hCpay hCdirect hKt.le hKcol.le hC₀.le hC₁.le hKdirect.le hz.2

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_canonical_paid_columns

#print axioms OAI.SevenEighths.Cycle153ActualColumn.eventual_actual_canonical_paid_columns
