/- Genuine pre-source ROOT quantitative metadata on every original subset.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootLowCanonicalMetadata
import Candidate.Research.RecursiveAffine.NativeLowCoarseSchedule
import Candidate.Research.RecursiveAffine.NativeLowLargeHeight
import Candidate.Research.RecursiveAffine.NativeRootAnalyticReturnConstant
import Candidate.Research.RecursiveAffine.NativeRootPhysicalThreshold
import Candidate.Research.RecursiveAffine.NativeSelectedOldThreshold
import Candidate.Research.RecursiveAffine.NativeSelectedScalarThreshold
import Candidate.Research.RecursiveAffine.NativeRootAllRowThreshold

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RootLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153Reachable Cycle153ActualColumn Cycle153RegionalLow
open Cycle153SourceSchedule Cycle153SourceUniform Cycle153ActualSourceGates
open CenteredMomentInductionEnergy CenteredMomentSecondInputCapacitySource Cycle63Moment LocalMoment
open CenteredMomentFirstAmplificationChoice CenteredMomentEnergyState
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)
variable (eta : Character)(Q : Ideal O)(hQM : Q≤M)
variable (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})
variable (g : GeometryAffineLowSchedule)(Cs epsNode Bnorm : ℝ)
variable (hCs : 1≤Cs)(hepsNode : 0<epsNode)(hB : 0≤Bnorm)
noncomputable local instance rootQuantitativeMetadataLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
attribute [local irreducible] RootCanonicalSubsetAt

/-- The literal physical multiplicity outside the ROOT selected source. -/
def rootLowPhysicalMultiplicity (n : ℕ)(e : ℝ) : ℝ:=
  (1/lowerFactor n 1 (1/4))*
    ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex e):ℝ))

theorem rootLowPhysicalMultiplicity_nonneg (n : ℕ)(e : ℝ) :
    0≤rootLowPhysicalMultiplicity n e:=by
  have hl:=(lowerFactor_pos n 1 (1/4) (by norm_num) (by norm_num)).le
  unfold rootLowPhysicalMultiplicity
  positivity

/- Every coefficient below is computed from a genuine source selected
before Z. The actual ROOT source for T uses ambient type T and reflexive
embedding; driver/fee rate and coarse height degree keep the ORIGINAL
ambient budget. No returned forest, moving context or energy bound is
used in choosing these data. -/
include hW hWs hQM hQ0 hQt hQ72 hCs in
theorem actual_root_low_quantitative_metadata
    (Kchild : Finset alpha→ℝ)(hKchild : ∀T,0≤Kchild T)
    (controlChild : Finset alpha→Finset (ℕ×ℕ))(degreeChild : Finset alpha→ℕ) :
    let r:=postDictionaryRate Bnorm (Fintype.card alpha)
    let hr:=(postDictionaryRate_budgets hB (Fintype.card alpha)).1
    let Dlarge:=nativeLowLargeHeightDegree (Fintype.card alpha) g.τ g.τ_pos
    ∃(dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
      (Kt Cp Kc Cd C0 C1 Kd Kcoarse : Finset alpha→ℝ)
      (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
      (Klow Kreturn : Finset alpha→ℝ),
      (∀T,0<Kt T ∧1≤Cp T ∧0<Kc T ∧1≤Cd T ∧0<C0 T ∧0<C1 T ∧0<Kd T ∧0<Kcoarse T) ∧
      (∀T,Sp T=insert (0,0) ((ct T∪controlChild T)∪cd T) ∧(0,0)∈Sp T ∧
        let Dsmall:=max (max (dt T) (degreeChild T)) (dd T)
        let Cg:=nativeColumnSourceConstant T.card Cs (Cp T) (Kt T) (Kchild T) (Kc T)
          (Cd T) (C0 T) (C1 T) (Kd T)
        let Cu:=actualRootPhysicalConstant (alpha:=T) hH Bnorm hB (Fintype.card alpha) T.card
        degreeLow T=max Dsmall Dlarge ∧0≤Klow T ∧0≤Kreturn T ∧
        Klow T=rootLowPhysicalMultiplicity T.card g.e*Cu*
          actualSelectedOldConstant Bnorm hB (Fintype.card alpha)*Cg*
          actualSelectedOldBoxConstant Bnorm hB (Fintype.card alpha) T.card*
          (2+4*Real.pi)^Dsmall+(2+4*Real.pi)^Dlarge*Kcoarse T ∧
        Kreturn T=actualRootAnalyticReturnCoefficient (alpha:=T) hH Bnorm hB
          (Fintype.card alpha) T.card g.e Cs (Cp T) (Kt T) (Kchild T) (Kc T)
          (Cd T) (C0 T) (C1 T) (Kd T) Dsmall) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀T : Finset alpha,
        RootCanonicalSubsetAt hH W hbeta eta Q g Cs epsNode r hepsNode hr T
          (dt T) (dd T) (ct T) (cd T) (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) Z ∧
        NativeLowCoarseSubsetAt T (Fintype.card alpha) Cs (Kcoarse T) Z ∧
        actualRootPhysicalThreshold (alpha:=T) hH Bnorm hB (Fintype.card alpha) T.card≤Z ∧
        actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card≤Z ∧
        actualSelectedScalarThreshold T.card r hr≤Z ∧actualRootAllRowThreshold T.card≤Z :=by
  intro r hr Dlarge
  obtain ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,hcanonical⟩:=
    actual_root_canonical_metadata (alpha:=alpha) hH W hW hWs hbeta eta Q hQM hQ0 hQt hQ72
      g Cs epsNode r hCs hepsNode hr
  obtain ⟨Kcoarse,hcoarsepos,hcoarse⟩:=
    eventual_actual_native_low_coarse_sources (alpha:=alpha) eta Cs hCs
  let Dsmall:=fun (T : Finset alpha)=>max (max (dt T) (degreeChild T)) (dd T)
  let Sp:=fun (T : Finset alpha)=>insert (0,0) ((ct T∪controlChild T)∪cd T)
  let degreeLow:=fun (T : Finset alpha)=>max (Dsmall T) Dlarge
  let Cg:=fun (T : Finset alpha)=>nativeColumnSourceConstant T.card Cs (Cp T) (Kt T) (Kchild T) (Kc T)
    (Cd T) (C0 T) (C1 T) (Kd T)
  let Cu:=fun (T : Finset alpha)=>actualRootPhysicalConstant (alpha:=T) hH Bnorm hB (Fintype.card alpha) T.card
  let Klow:=fun (T : Finset alpha)=>rootLowPhysicalMultiplicity T.card g.e*Cu T*
    actualSelectedOldConstant Bnorm hB (Fintype.card alpha)*Cg T*
    actualSelectedOldBoxConstant Bnorm hB (Fintype.card alpha) T.card*
    (2+4*Real.pi)^(Dsmall T)+(2+4*Real.pi)^Dlarge*Kcoarse T
  let Kreturn:=fun (T : Finset alpha)=>actualRootAnalyticReturnCoefficient (alpha:=T) hH Bnorm hB
    (Fintype.card alpha) T.card g.e Cs (Cp T) (Kt T) (Kchild T) (Kc T)
    (Cd T) (C0 T) (C1 T) (Kd T) (Dsmall T)
  have hCg : ∀T,0≤Cg T:=by
    intro T
    obtain ⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩:=hpositive T
    have hchild:=hKchild T
    have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
    dsimp only [Cg,nativeColumnSourceConstant]
    positivity
  have hCu : ∀T,0≤Cu T:=fun (T : Finset alpha)=>
    (actualRootPhysicalConstant_pos (alpha:=T) hH Bnorm hB (Fintype.card alpha) T.card).le
  have hPow (D : ℕ) : 0≤(2+4*Real.pi)^D:=pow_nonneg (by linarith only [Real.pi_pos]) D
  have hKlow : ∀T,0≤Klow T:=by
    intro T
    dsimp only [Klow]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (rootLowPhysicalMultiplicity_nonneg T.card g.e) (hCu T))
      (actualSelectedOldConstant_pos Bnorm hB (Fintype.card alpha)).le) (hCg T))
      (actualSelectedOldBoxConstant_pos Bnorm hB (Fintype.card alpha) T.card).le) (hPow _))
      (mul_nonneg (hPow Dlarge) (hcoarsepos T).le)
  have hKreturn : ∀T,0≤Kreturn T:=by
    intro T
    obtain ⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩:=hpositive T
    exact actualRootAnalyticReturnCoefficient_nonneg (alpha:=T) hH Bnorm hB
      (Fintype.card alpha) T.card g.e Cs (Cp T) (Kt T) (Kchild T) (Kc T)
      (Cd T) (C0 T) (C1 T) (Kd T) (Dsmall T)
      hCs hCp hCd hKt.le (hKchild T) hKc.le hC0.le hC1.le hKd.le
  have hthresholds : ∀T : Finset alpha,∀ᶠZ : ℝ in atTop,
      actualRootPhysicalThreshold (alpha:=T) hH Bnorm hB (Fintype.card alpha) T.card≤Z ∧
      actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card≤Z ∧
      actualSelectedScalarThreshold T.card r hr≤Z ∧actualRootAllRowThreshold T.card≤Z:=by
    intro T
    filter_upwards [eventually_ge_atTop (actualRootPhysicalThreshold (alpha:=T) hH Bnorm hB
        (Fintype.card alpha) T.card),
      eventually_ge_atTop (actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card),
      eventually_ge_atTop (actualSelectedScalarThreshold T.card r hr),
      eventually_ge_atTop (actualRootAllRowThreshold T.card)] with Z hphys hold hscalar hrow
    exact ⟨hphys,hold,hscalar,hrow⟩
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,Kcoarse,Sp,degreeLow,Klow,Kreturn,?_,?_,?_⟩
  · intro T
    exact ⟨(hpositive T).1,(hpositive T).2.1,(hpositive T).2.2.1,(hpositive T).2.2.2.1,
      (hpositive T).2.2.2.2.1,(hpositive T).2.2.2.2.2.1,(hpositive T).2.2.2.2.2.2,hcoarsepos T⟩
  · intro T
    exact ⟨rfl,Finset.mem_insert_self _ _,rfl,hKlow T,hKreturn T,rfl,rfl⟩
  · filter_upwards [hcanonical,hcoarse,Filter.eventually_all.mpr hthresholds] with Z hc hco ht
    refine ⟨hc.1,fun T=>⟨hc.2 T,?_,(ht T).1,(ht T).2.1,(ht T).2.2.1,(ht T).2.2.2⟩⟩
    simpa only [Real.rpow_one] using hco.2 1 (by norm_num) T

end
end OAI.SevenEighths.Cycle153RootLowSchedule
#print axioms OAI.SevenEighths.Cycle153RootLowSchedule.actual_root_low_quantitative_metadata
