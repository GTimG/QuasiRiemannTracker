/- Fixed quantitative metadata for the actual INNER LOW dispatcher. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerLowCanonicalMetadata
import Candidate.Research.RecursiveAffine.InnerLowPhysicalMetadata

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153InnerLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153RegionalLow Cycle153SourceUniform Cycle153SourceSchedule
open Cycle153TerminalSchedule Cycle153Reachable Cycle153ActualColumn Cycle153ActualSourceGates
open CenteredMomentFirstAmplificationChoice CenteredMomentEnergyState
open CenteredMomentInductionEnergy
attribute [local irreducible] InnerCanonicalSubsetAt
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}

/-- Genuine all-height splice degree, chosen before Z or a returned family. -/
def innerLowDegree (original : ℕ)(tau : ℝ)(htau : 0<tau)(smallDegree : ℕ) : ℕ :=
  Classical.choose (native_low_returned_height_splice (nativeLowCoarseExponent original original)
    (-1) tau htau smallDegree)

def innerLowDegreeRule (original : ℕ)(tau : ℝ)(htau : 0<tau)(smallDegree : ℕ) :=
  Classical.choose_spec (native_low_returned_height_splice (nativeLowCoarseExponent original original)
    (-1) tau htau smallDegree)

variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
variable (eps tau Bnorm : ℝ)(heps : 0<eps)(hB : 0≤Bnorm)(eta : Character)(Q : Ideal O)
variable (hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
variable (i : InnerGridIndex j)
variable (S : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
  eps tau Bnorm heps eta Q hQM hQ72 j i)

/-- All constants and profile/height metadata are chosen from genuine
native sources before the moving context, node, ledger realization or Z.
The future strictly-deeper availability is used only by the later actual
source invocation; no LOW or node-energy conclusion is assumed here. -/
theorem actual_inner_low_quantitative_metadata
    (Kchild : ℝ)(hKchild : 0≤Kchild)(controlChild : Finset (ℕ×ℕ))(degreeChild : ℕ) :
    let r:=postDictionaryRate Bnorm (Fintype.card alpha)
    let hr:=(postDictionaryRate_budgets hB (Fintype.card alpha)).1
    ∃(dt dd : Finset alpha→ℕ)(ct cd : Finset alpha→Finset (ℕ×ℕ))
      (Kt Cp Kc Cd C0 C1 Kd Kcoarse : Finset alpha→ℝ)
      (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
      (Klow : Finset alpha→ℝ)(Kreturn : ℝ),
      (∀T,0<Kt T ∧1≤Cp T ∧0<Kc T ∧1≤Cd T ∧0<C0 T ∧0<C1 T ∧0<Kd T ∧0<Kcoarse T) ∧
      (∀T,Sp T=((ct T∪controlChild)∪cd T)∪{(0,0)} ∧(0,0)∈Sp T ∧
        degreeLow T=innerLowDegree (Fintype.card alpha) S.g.τ S.g.τ_pos
          (max (max (dt T) degreeChild) (dd T)) ∧0≤Klow T ∧
        let Cg:=nativeColumnSourceConstant T.card S.Cs (Cp T) (Kt T) Kchild (Kc T)
          (Cd T) (C0 T) (C1 T) (Kd T)
        let Cu:=innerPhysicalConstant hH j r hr T
        Klow T=(2+4*Real.pi)^(degreeLow T)*
          (innerRawOldConstant T.card S.g.e Cu Cg
            (actualSelectedOldConstant Bnorm hB (Fintype.card alpha))
            (actualSelectedOldBoxConstant Bnorm hB (Fintype.card alpha) T.card)+Kcoarse T) ∧
        (2+4*Real.pi)^(degreeLow T)*innerRawReturnConstant T.card S.g.e Cu Cg≤Kreturn) ∧
      0≤Kreturn ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
        InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72
          j hj i S r hr T (dt T) (dd T) (ct T) (cd T)
          (Kt T) (Cp T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T) (Z^U) ∧
        NativeLowCoarseSubsetAt T (Fintype.card alpha) S.Cs (Kcoarse T) (Z^U) ∧
        innerPhysicalThreshold hH j r hr T≤Z^U ∧
        actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card≤Z^U :=by
  intro r hr
  obtain ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,hcanonical⟩:=
    actual_inner_canonical_metadata hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q
      hQM hQ0 hQt hQ72 j hj i S r hr
  obtain ⟨Kcoarse,hcoarsepos,hcoarse⟩:=eventual_actual_native_low_coarse_sources
    (alpha:=alpha) eta S.Cs S.Cs_one
  let Sp:=fun (T : Finset alpha)=>((ct T∪controlChild)∪cd T)∪{(0,0)}
  let degreeLow:=fun (T : Finset alpha)=>innerLowDegree (Fintype.card alpha) S.g.τ S.g.τ_pos
    (max (max (dt T) degreeChild) (dd T))
  let Cg:=fun (T : Finset alpha)=>nativeColumnSourceConstant T.card S.Cs (Cp T) (Kt T) Kchild (Kc T)
    (Cd T) (C0 T) (C1 T) (Kd T)
  let Cu:=fun (T : Finset alpha)=>innerPhysicalConstant hH j r hr T
  let Klow:=fun (T : Finset alpha)=>(2+4*Real.pi)^(degreeLow T)*
    (innerRawOldConstant T.card S.g.e (Cu T) (Cg T)
      (actualSelectedOldConstant Bnorm hB (Fintype.card alpha))
      (actualSelectedOldBoxConstant Bnorm hB (Fintype.card alpha) T.card)+Kcoarse T)
  let KreturnAt:=fun (T : Finset alpha)=>(2+4*Real.pi)^(degreeLow T)*
    innerRawReturnConstant T.card S.g.e (Cu T) (Cg T)
  let Kreturn:=∑T : Finset alpha,KreturnAt T
  have hCu : ∀T,0≤Cu T:=fun (T : Finset alpha)=>(innerPhysicalConstant_pos hH j r hr T).le
  have hCg : ∀T,0≤Cg T:=by
    intro T
    obtain ⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩:=hpositive T
    have hCs:=S.Cs_one
    have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
    dsimp only [Cg,nativeColumnSourceConstant]
    positivity
  have hPow : ∀T,0≤(2+4*Real.pi)^(degreeLow T):=by
    intro T
    exact pow_nonneg (by linarith only [Real.pi_pos]) _
  have hKlow : ∀T,0≤Klow T:=by
    intro T
    exact mul_nonneg (hPow T) (add_nonneg
      (innerRawOldConstant_nonnegative T.card S.g.e (Cu T) (Cg T) _ _ (hCu T) (hCg T)
        (actualSelectedOldConstant_pos Bnorm hB (Fintype.card alpha)).le
        (actualSelectedOldBoxConstant_pos Bnorm hB (Fintype.card alpha) T.card).le)
      (hcoarsepos T).le)
  have hKretAt : ∀T,0≤KreturnAt T:=by
    intro T
    exact mul_nonneg (hPow T)
      (innerRawReturnConstant_nonnegative T.card S.g.e (Cu T) (Cg T) (hCu T) (hCg T))
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,Kcoarse,Sp,degreeLow,Klow,Kreturn,?_,?_,?_,?_⟩
  · intro T
    exact ⟨(hpositive T).1,(hpositive T).2.1,(hpositive T).2.2.1,(hpositive T).2.2.2.1,
      (hpositive T).2.2.2.2.1,(hpositive T).2.2.2.2.2.1,(hpositive T).2.2.2.2.2.2,hcoarsepos T⟩
  · intro T
    refine ⟨rfl,Finset.mem_union_right _ (Finset.mem_singleton_self _),rfl,hKlow T,rfl,?_⟩
    exact Finset.single_le_sum (fun J _=>hKretAt J) (Finset.mem_univ T)
  · exact Finset.sum_nonneg (fun T _=>hKretAt T)
  · filter_upwards [hcanonical,hcoarse,eventual_inner_low_auxiliary_thresholds
      (alpha:=alpha) hH j Bnorm hB (Fintype.card alpha)] with Z hc hco ha
    exact ⟨hc.1,fun U hU T=>⟨hc.2 U hU T,hco.2 U hU T,(ha.2 U hU T).1,(ha.2 U hU T).2⟩⟩

end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.actual_inner_low_quantitative_metadata
