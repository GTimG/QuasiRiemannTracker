/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeMappedChildIH
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
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
variable {Current : Type} [Fintype Current]
local instance strictCurrentDecidableEq : DecidableEq Current := Classical.decEq _
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- Literal main-branch tests at a retained source. Small width,
exhaustion, the licensed old region, and the full actual reflection test
terminate instead of invoking a deeper regional state. -/
def nativeMainContinuation {iota : Type} [Fintype iota]
    {Z Bmask : ℝ}(st : NaturalState Z Bmask 2)(u : ℝ)
    (J R : Finset iota)(w : iota→ℝ)(X1 X2 : ℝ) : Prop :=
  (397/1000:ℝ) ≤ u ∧ R ≠ J ∧
  u < length Z X1+length Z X2+6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j) ∧
  ¬(length Z X1+length Z X2+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j) ≤ u+19/5000 ∧
    (max 0 (u-length Z X2+1/10000)+length Z X1+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j)+19/5000 ≤ u ∨
     max 0 (u-length Z X1+1/10000)+length Z X2+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j)+19/5000 ≤ u))

/-- The physical source overshoot certificate is used before extracting
failure of each paired reflection test. This prevents a paired test alone
from being used as a terminal reflection hypothesis. -/
theorem nativeMainContinuation_paired {iota : Type} [Fintype iota]
    {Z Bmask : ℝ}(st : NaturalState Z Bmask 2)(u : ℝ)
    (J R : Finset iota)(w : iota→ℝ)(X1 X2 : ℝ)
    (h : nativeMainContinuation st u J R w X1 X2)
    (hover : length Z X1+length Z X2+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j) ≤ u+19/5000) :
    u < max 0 (u-length Z X2+1/10000)+length Z X1+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j)+19/5000 ∧
    u < max 0 (u-length Z X1+1/10000)+length Z X2+
      6*Cycle63.Optimization.slotPrice*(∑j∈J\R,w j)+19/5000 := by
  rcases h with ⟨_,_,_,h⟩
  constructor
  · exact not_le.mp (fun hh=>h ⟨hover,Or.inl hh⟩)
  · exact not_le.mp (fun hh=>h ⟨hover,Or.inr hh⟩)

/-- The genuine LOW detector chooses the deletion, and the strict-depth
IH is then used on that SAME actual daughter. The only daughter-construction
input is arithmetic geometry for the detector's admissible deletions; it
contains no energy or returned-count estimate. Original ray coefficients,
source scale, profiles, puncture and entire returned-family provenance are
preserved. The source power includes the native LOW loss and deletion
charge once, before the same family reaches the common Cauchy operator. -/
theorem eventual_actual_strict_low_step
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hWs : Function.support W ⊆ Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(parentStage childStage : Fin 4)
    (hdepth : parentStage.val<childStage.val) (embedding : Current↪alpha)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0 ≤ heightExponent)
    (hbudget : 8*e*Rwidth+kappa ≤ epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃Cpay : ℝ,1 ≤ Cpay ∧ ∀ᶠ Zparent : ℝ in atTop,1<Zparent ∧
    ∀(C : SourceContext (α:=alpha) M H)(hCW : C.W=W)(hCeta : C.etaSeed=etaSeed),
    ∀(hZ : 1<Zparent)(parentUnit : ℝ)(hparentUnit : 0<parentUnit)
      (hbase : Zparent=C.globalBase^parentUnit)
      (s : Input Current)(t height mesh a del : ℝ)(i : ℕ),
    Matches M H hH s C.etaSeed (fun j=>C.theta (embedding j))
      (fun j=>C.originalWeight (embedding j)/parentUnit) (fun j=>C.sigma (embedding j)) (fun j=>C.frequency (embedding j))
      C.W 2 Zparent →
    (∀j : Current,(C.originalWeight (embedding j)/parentUnit)/d ≤ Rwidth) →
    0 ≤ mesh → (∀j : Current,C.originalWeight (embedding j)/parentUnit ≤ mesh) →
    ∀(hheight : 0 ≤ height)(hfreq : ∀j : Current,|C.frequency (embedding j)| ≤ height),
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
    ∀(u : ℝ)(hu : 0<u)(hu1 : u ≤ 1)(hwidth : st.width ≤ u)
      (p : Profiles (1/4) (9/4)),s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
    let remainingEnergy := fun R : Finset Current=>
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun j : ↥(J\R)=>CenteredMomentPrimeSlot.primePool M H 2 (Zparent^(C.originalWeight (embedding j.val)/parentUnit)))
        (fun (j : ↥(J\R)) I=>idealCoeff (relativeCharacter M H hH C.etaSeed (C.theta (embedding j.val))) I*
          annularWeight C.W (Zparent^(C.originalWeight (embedding j.val)/parentUnit))
            (C.sigma (embedding j.val)) (C.frequency (embedding j.val)) I)
        (fun j : ↥(J\R)=>Zparent^(C.originalWeight (embedding j.val)/parentUnit))
        (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
        st.radial.keep st.radial.profile st.radial.scale
    let continues := fun R=>nativeMainContinuation st u J R
      (fun j=>C.originalWeight (embedding j)/parentUnit)
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
    ∀(P : PrefixHighPresentation (prefixDictionary childStage.val C.etaSeed)
        st.character st.puncture)
      (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap childStage.val))
      (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)
      (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
      (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ)),
    StrictDepthIH hH C parentStage constant eps Bsrc control degree boxes →
    ∀(childMask : ∀(R : Finset Current),R ⊆ J →
      (∑j∈R,C.originalWeight (embedding j)/parentUnit) ≤ del+mesh →
      (R=J ∨ del ≤ ∑j∈R,C.originalWeight (embedding j)/parentUnit) →
      continues R → (st.puncture.absNorm:ℝ) ≤ (Zparent^u)^(20:ℝ)),
    ∀(childGeometry : ∀(R : Finset Current),R ⊆ J →
      (∑j∈R,C.originalWeight (embedding j)/parentUnit) ≤ del+mesh →
      (R=J ∨ del ≤ ∑j∈R,C.originalWeight (embedding j)/parentUnit) →
      continues R →
      NativeChildGeometry C childStage Zparent parentUnit u (((J\R).map embedding))
        (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)),
    ∀(childHistory : ∀(R : Finset Current)(hR : R ⊆ J)
      (hsum : (∑j∈R,C.originalWeight (embedding j)/parentUnit) ≤ del+mesh)
      (hcover : R=J ∨ del ≤ ∑j∈R,C.originalWeight (embedding j)/parentUnit)
      (hcontinue : continues R),
      let geom := childGeometry R hR hsum hcover hcontinue
      Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
        modelMissing childStage geom.coordinates+modelReduction childStage geom.coordinates+
          ((childStage.val:ℝ)+1)/1000000000000000),
    ∃(R : Finset Current)(hR : R ⊆ J)
      (hsum : (∑j∈R,C.originalWeight (embedding j)/parentUnit) ≤ del+mesh)
      (hcover : R=J ∨ del ≤ ∑j∈R,C.originalWeight (embedding j)/parentUnit),
    (¬continues R ∧ finalPositiveEnergy src second L alloc (fun z=>st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale ≤
      Cpay^(Fintype.card Current)*Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+q*(del+mesh))*
        remainingEnergy R) ∨
    ∃hcontinue : continues R,
    let hmask := childMask R hR hsum hcover hcontinue
    let child := nodeOfNativeContinuation C childStage Zparent parentUnit u Bmask hu hbase
      st hwidth hmask (((J\R).map embedding)) p
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
      (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
      P hPnorm hfixed t height hheight
      (nativeMappedFrequencyBound embedding J R C.frequency height hfreq)
      (childGeometry R hR hsum hcover hcontinue) (childHistory R hR hsum hcover hcontinue)
    ∃out : NodeOutput hH child (constant childStage) (eps childStage) (Bsrc childStage)
      (control childStage) (degree childStage) (boxes childStage),
    let F := rebaseDepthReturnedFamily hZ hu hu1 C.normCap_nonneg out.family
    finalPositiveEnergy src second L alloc (fun z=>st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale ≤
      Cpay^(Fintype.card Current)*Zparent^(2*epsilon*d*(Fintype.card Current:ℝ)+q*(del+mesh))*
        (constant childStage*QuadraticInitialBound.diagonalControl child.state.radial.profile*
          (child.profiles.control (control childStage))^2*
          (1+|child.t|+child.height)^(degree childStage)*
          ((Zparent^u)^(1+eps childStage)+F.value)) := by
  obtain ⟨Cpay,hCpay,hsource⟩ := actual_regional_daughter_source (α:=Current) M H hH
    W 1 2 (by norm_num) hWs hW Rwidth dmax tau epsilon e kappa heightExponent
    (33/50) (33/50) Mcap Bmask margin d hRw hdmax htau hepsilon he he' hkappa hheightExponent
    hbudget hmargin hd hdsupply hdm q hq0 hq1
  refine ⟨Cpay,hCpay,?_⟩
  filter_upwards [hsource etaSeed] with Zparent hz
  refine ⟨hz.1,?_⟩
  intro C hCW hCeta hZ parentUnit hparentUnit hbase s t height mesh a del i hmatch hwr hmesh hwm hheight hfreq
    ha ha' hdel hfreqbin hhigh ch chi Q hP hPN radius Ccommon Dcommon Ucommon second L alloc
    st src J hMcap hQM hQeta low u hu hu1 hwidth p hp1 hp2 remainingEnergy continues P hPnorm hfixed
    constant eps Bsrc control degree boxes hIH childMask childGeometry childHistory
  have hw : ∀j : Current,0 ≤ C.originalWeight (embedding j)/parentUnit :=
    fun j=>div_nonneg (C.originalWeight_nonneg (embedding j)) hparentUnit.le
  have sourceC := hz.2
  rw [←hCW,←hCeta] at sourceC
  obtain ⟨R,hR,hsum,hcover,hpaid⟩ := sourceC hZ s (fun j=>C.theta (embedding j))
    (fun j=>C.originalWeight (embedding j)/parentUnit) (fun j=>C.sigma (embedding j)) (fun j=>C.frequency (embedding j))
    t height mesh a del i hmatch hw hwr hmesh hwm (fun j=>(C.sigma_fixed (embedding j)).1)
    (fun j=>(C.sigma_fixed (embedding j)).2) hheight hfreq ha ha' hdel hfreqbin hhigh ch chi Q hP hPN
    radius Ccommon Dcommon Ucommon second L alloc hMcap hQM hQeta
  rw [hp1,hp2] at hpaid
  refine ⟨R,hR,hsum,hcover,?_⟩
  by_cases hcontinue : continues R
  · right
    refine ⟨hcontinue,?_⟩
    let hmask := childMask R hR hsum hcover hcontinue
    let geom := childGeometry R hR hsum hcover hcontinue
    obtain ⟨out,hout⟩ := actual_mapped_child_from_strict_depth hH C parentStage childStage hdepth
      constant eps Bsrc control degree boxes hIH embedding Zparent parentUnit u Bmask hZ hu hu1 hbase
      st hwidth hmask J R p
      (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
      (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
      P hPnorm hfixed t height hheight hfreq geom (childHistory R hR hsum hcover hcontinue)
    refine ⟨out,?_⟩
    dsimp only at hout ⊢
    exact hpaid.trans (mul_le_mul_of_nonneg_left hout (by positivity))
  · exact Or.inl ⟨hcontinue,hpaid⟩

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_strict_low_step
