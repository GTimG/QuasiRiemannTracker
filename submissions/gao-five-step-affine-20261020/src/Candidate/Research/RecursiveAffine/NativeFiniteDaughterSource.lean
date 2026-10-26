/- Actual native wide LOW sources on every original subset before moving Z.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeDaughterForest
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeAnnular CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentInductionEnergy CenteredMomentDivisorAllocation
open CenteredMomentCanonicalFirst
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle153SourceReturn
open Cycle153Reachable Cycle153HighProvider

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

open Cycle153SourceUniform

/-- The current source embeds into the fixed ORIGINAL ray carrier. -/
def originalSubsetEmbedding (J0 : Finset alpha) : (↥J0)↪alpha :=
  Function.Embedding.subtype (fun i=>i∈J0)

/-- Literal NativeDaughterForest specification on one original subset.
Only its carrier is specialized; source coefficients, deletion witnesses,
returned family, child geometry and all norm/height gates stay unchanged. -/
def NativeWideSubsetSourceAt

    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hWs : Function.support W ⊆ Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed ≤ M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed ≤ Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1 ≤ Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (parentStage childStage : Fin 4)
    (hdepth : parentStage.val<childStage.val)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0 ≤ Bmask)(hMcap : 0<Mcap) (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0 ≤ heightExponent)
    (hbudget : 8*e*Rwidth+kappa ≤ epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (J0 : Finset alpha) (degreeTerminal : ℕ) (controlTerminal : Finset (ℕ×ℕ))
    (Kterminal Cpay Zparent : ℝ) : Prop :=
    letI : DecidableEq (↥J0):=Classical.decEq _
    1<Zparent ∧
    ∀(C : SourceContext (α:=alpha) M H)(hCW : C.W=W)(hCeta : C.etaSeed=etaSeed)(hCQ : C.Q=Qfixed),
    ∀(hZ : 1<Zparent)(parentUnit : ℝ)(hparentUnit : 0<parentUnit)
      (hbase : Zparent=C.globalBase^parentUnit)
      (s : Input (↥J0))(t height mesh a del : ℝ)(i : ℕ),
    Matches M H hH s C.etaSeed (fun j=>C.theta ((originalSubsetEmbedding J0) j))
      (fun j=>C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) (fun j=>C.sigma ((originalSubsetEmbedding J0) j)) (fun j=>C.frequency ((originalSubsetEmbedding J0) j))
      C.W 2 Zparent →
    (∀j : (↥J0),(C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit)/d ≤ Rwidth) →
    (∀j : (↥J0),C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit ≤
      Cycle25.Energy.commonMesh Mcap Bmask Lbound epsOld) →
    0 ≤ mesh → (∀j : (↥J0),C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit ≤ mesh) →
    ∀(hheight : 0 ≤ height)(hfreq : ∀j : (↥J0),|C.frequency ((originalSubsetEmbedding J0) j)| ≤ height),
    51/100 ≤ a → a ≤ (1+q)/2 → 0 ≤ del →
    |t|+height+Zparent^tau/2 ≤ (3*i+2:ℕ)*Zparent^tau →
    (3+(3*i+2:ℕ)*Zparent^tau)^2 ≤ (Zparent^d)^heightExponent →
    ∀(ch : Chain s)(chi : Character)(Q : Ideal O)(hP : ch.R₂*ch.E₂ ≠ 0)
      (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Zparent^Bmask)(radius : ℝ)
      (Ccommon Dcommon : Ideal O)(Ucommon : Finset (CommonIndex Ccommon Dcommon))
      (second : Bool)(L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset
        (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2))),
    let st := retainedState Zparent Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
      radius Ccommon Dcommon Ucommon
    let src := ch.final chi t
    let J := ch.indices L alloc
    st.width ≤ Mcap →
    ∀(hQM : st.fixedModulus ≤ M)(hQeta : st.fixedModulus ≤ C.etaSeed.modulus),
    let low := ActualLow M H hH st C.etaSeed hQM hQeta a e (3*(i+1:ℕ)*Zparent^tau)
    ∀(u : ℝ)(hu : 0<u)(hu1 : u ≤ 1)(hwidth : st.width ≤ u)(hwide : (397/1000:ℝ) ≤ u)(huMcap : u ≤ Mcap)
      (p : Profiles (1/4) (9/4)),s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
    rawDaughterScale src second L alloc 0 ≤ Zparent^Lbound →
    rawDaughterScale src second L alloc 1 ≤ Zparent^Lbound →
    let remainingEnergy := fun R : Finset (↥J0)=>
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun j : ↥(J\R)=>CenteredMomentPrimeSlot.primePool M H 2 (Zparent^(C.originalWeight ((originalSubsetEmbedding J0) j.val)/parentUnit)))
        (fun (j : ↥(J\R)) I=>idealCoeff (relativeCharacter M H hH C.etaSeed (C.theta ((originalSubsetEmbedding J0) j.val))) I*
          annularWeight C.W (Zparent^(C.originalWeight ((originalSubsetEmbedding J0) j.val)/parentUnit))
            (C.sigma ((originalSubsetEmbedding J0) j.val)) (C.frequency ((originalSubsetEmbedding J0) j.val)) I)
        (fun j : ↥(J\R)=>Zparent^(C.originalWeight ((originalSubsetEmbedding J0) j.val)/parentUnit))
        (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
        st.radial.keep st.radial.profile st.radial.scale
    let continues := fun R=>nativeMainContinuation st u J R
      (fun j=>C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit)
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
    ∀(P : PrefixHighPresentation (prefixDictionary childStage.val C.etaSeed)
        st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap childStage.val))
      (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)
      (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
      (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ)),
    StrictDepthIH hH C parentStage constant eps Bsrc control degree boxes →
    ∀(childMask : ∀(R : Finset (↥J0)),R ⊆ J →
      (∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) ≤ del+mesh →
      (R=J ∨ del ≤ ∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) →
      continues R → (st.puncture.absNorm:ℝ) ≤ (Zparent^u)^(20:ℝ)),
    ∀(childGeometry : ∀(R : Finset (↥J0)),R ⊆ J →
      (∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) ≤ del+mesh →
      (R=J ∨ del ≤ ∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) →
      continues R →
      NativeChildGeometry C childStage Zparent parentUnit u (((J\R).map (originalSubsetEmbedding J0)))
        (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)),
    ∀(childHistory : ∀(R : Finset (↥J0))(hR : R ⊆ J)
      (hsum : (∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) ≤ del+mesh)
      (hcover : R=J ∨ del ≤ ∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit)
      (hcontinue : continues R),
      let geom := childGeometry R hR hsum hcover hcontinue
      Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
        modelMissing childStage geom.coordinates+modelReduction childStage geom.coordinates+
          ((childStage.val:ℝ)+1)/1000000000000000),
    ∃(R : Finset (↥J0))(hR : R ⊆ J)
      (hsum : (∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit) ≤ del+mesh)
      (hcover : R=J ∨ del ≤ ∑j∈R,C.originalWeight ((originalSubsetEmbedding J0) j)/parentUnit),
    ∃F : SuffixFamily (hH:=hH) childStage.val (4-childStage.val)
      C.etaSeed Zparent C.Bnorm C.Tz P.mult,
    (F=emptyReturnedForest ∧ ¬continues R ∧ finalPositiveEnergy src second L alloc (fun z=>st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale ≤
      Cpay^(Fintype.card (↥J0))*Zparent^(2*epsilon*d*(Fintype.card (↥J0):ℝ)+q*(del+mesh))*
        remainingEnergy R ∧ finalPositiveEnergy src second L alloc (fun z=>st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale ≤
      Cpay^(Fintype.card (↥J0))*Zparent^(2*epsilon*d*(Fintype.card (↥J0):ℝ)+q*(del+mesh))*
        (Kterminal*QuadraticInitialBound.diagonalControl st.radial.profile*
          (p.control controlTerminal)^2*(1+|t|+height)^degreeTerminal*
          Zparent^(u+epsOld+epsReflect))) ∨
    ∃hcontinue : continues R,
    let hmask := childMask R hR hsum hcover hcontinue
    let child := nodeOfNativeContinuation C childStage Zparent parentUnit u Bmask hu hbase
      st hwidth hmask (((J\R).map (originalSubsetEmbedding J0))) p
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
      (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
      P hPnorm hfixed t height hheight
      (nativeMappedFrequencyBound (originalSubsetEmbedding J0) J R C.frequency height hfreq)
      (childGeometry R hR hsum hcover hcontinue) (childHistory R hR hsum hcover hcontinue)
    ∃out : NodeOutput hH child (constant childStage) (eps childStage) (Bsrc childStage)
      (control childStage) (degree childStage) (boxes childStage),
    F=rebaseDepthReturnedFamily hZ hu hu1 C.normCap_nonneg out.family ∧
    finalPositiveEnergy src second L alloc (fun z=>st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale ≤
      Cpay^(Fintype.card (↥J0))*Zparent^(2*epsilon*d*(Fintype.card (↥J0):ℝ)+q*(del+mesh))*
        (constant childStage*QuadraticInitialBound.diagonalControl child.state.radial.profile*
          (child.profiles.control (control childStage))^2*
          (1+|child.t|+child.height)^(degree childStage)*
          ((Zparent^u)^(1+eps childStage)+F.value))

/-- All native constants and eventual cutoffs are selected on the finite
original carrier before the surviving source can vary with Z. There is
no uniformity assumption on a moving source type. -/
theorem eventual_native_wide_original_subsets

    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hWs : Function.support W ⊆ Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed ≤ M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed ≤ Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1 ≤ Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (parentStage childStage : Fin 4)
    (hdepth : parentStage.val<childStage.val)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0 ≤ Bmask)(hMcap : 0<Mcap) (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0 ≤ heightExponent)
    (hbudget : 8*e*Rwidth+kappa ≤ epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃(degreeTerminal : Finset alpha→ℕ)(controlTerminal : Finset alpha→Finset (ℕ×ℕ))
      (Kterminal Cpay : Finset alpha→ℝ),
    (∀J0,0<Kterminal J0) ∧ (∀J0,1≤Cpay J0) ∧
    ∀ᶠ Zparent : ℝ in atTop,∀J0 : Finset alpha,
      NativeWideSubsetSourceAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72
      Lbound epsOld epsReflect hLbound hOld hReflect hbeta parentStage childStage hdepth
      Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
      hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 J0
        (degreeTerminal J0) (controlTerminal J0) (Kterminal J0) (Cpay J0) Zparent := by
  classical
  apply finite_original_subset_source_schedule
  intro J0
  simpa only [NativeWideSubsetSourceAt] using
    (eventual_actual_wide_daughter_forest (Current:=(↥J0)) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72
      Lbound epsOld epsReflect hLbound hOld hReflect hbeta parentStage childStage hdepth (originalSubsetEmbedding J0)
      Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
      hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1)

/-- The same actual source providers work at every rebased child base.
The retained original unit is bounded below before choosing any child. -/
theorem eventual_native_wide_original_subsets_rebased

    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hWs : Function.support W ⊆ Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed ≤ M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed ≤ Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1 ≤ Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (parentStage childStage : Fin 4)
    (hdepth : parentStage.val<childStage.val)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0 ≤ Bmask)(hMcap : 0<Mcap) (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0 ≤ heightExponent)
    (hbudget : 8*e*Rwidth+kappa ≤ epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃(degreeTerminal : Finset alpha→ℕ)(controlTerminal : Finset alpha→Finset (ℕ×ℕ))
      (Kterminal Cpay : Finset alpha→ℝ),
    (∀J0,0<Kterminal J0) ∧ (∀J0,1≤Cpay J0) ∧
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U→∀J0 : Finset alpha,
      NativeWideSubsetSourceAt hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72
      Lbound epsOld epsReflect hLbound hOld hReflect hbeta parentStage childStage hdepth
      Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
      hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 J0
        (degreeTerminal J0) (controlTerminal J0) (Kterminal J0) (Cpay J0) (Z^U) := by
  obtain ⟨degreeTerminal,controlTerminal,Kterminal,Cpay,hK,hC,hs⟩:=
    eventual_native_wide_original_subsets (alpha:=alpha) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72
      Lbound epsOld epsReflect hLbound hOld hReflect hbeta parentStage childStage hdepth
      Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
      hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1
  exact ⟨degreeTerminal,controlTerminal,Kterminal,Cpay,hK,hC,
    eventually_all_rebased_sources _ hs⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_native_wide_original_subsets
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_native_wide_original_subsets_rebased
