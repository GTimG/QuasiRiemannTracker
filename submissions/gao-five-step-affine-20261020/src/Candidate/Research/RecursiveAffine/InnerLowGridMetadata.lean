/- Fixed quantitative metadata for the actual INNER LOW dispatcher. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerLowQuantitativeMetadata

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

variable (hH : RayOrthogonality.globalUnits M≤H)
variable (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
variable (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
variable (eps tau Bnorm : ℝ)(heps : 0<eps)(hB : 0≤Bnorm)(eta : Character)(Q : Ideal O)
variable (hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
variable (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
variable (S : ∀i : InnerGridIndex j,InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
  eps tau Bnorm heps eta Q hQM hQ72 j i)
/- One actual metadata collection covers EVERY finite native ledger before Z. -/
theorem actual_inner_low_grid_metadata
    (Kchild : ℝ)(hKchild : 0≤Kchild)(controlChild : Finset (ℕ×ℕ))(degreeChild : ℕ) :
    let r:=postDictionaryRate Bnorm (Fintype.card alpha)
    let hr:=(postDictionaryRate_budgets hB (Fintype.card alpha)).1
    ∃(dt dd : InnerGridIndex j→Finset alpha→ℕ)(ct cd : InnerGridIndex j→Finset alpha→Finset (ℕ×ℕ))
      (Kt Cp Kc Cd C0 C1 Kd Kcoarse : InnerGridIndex j→Finset alpha→ℝ)
      (Sp : InnerGridIndex j→Finset alpha→Finset (ℕ×ℕ))(degreeLow : InnerGridIndex j→Finset alpha→ℕ)
      (Klow : InnerGridIndex j→Finset alpha→ℝ)(Kreturn : ℝ),
      (∀i T,0<Kt i T ∧1≤Cp i T ∧0<Kc i T ∧1≤Cd i T ∧0<C0 i T ∧0<C1 i T ∧0<Kd i T ∧0<Kcoarse i T) ∧
      (∀i T,Sp i T=((ct i T∪controlChild)∪cd i T)∪{(0,0)} ∧(0,0)∈Sp i T ∧
        degreeLow i T=innerLowDegree (Fintype.card alpha) (S i).g.τ (S i).g.τ_pos
          (max (max (dt i T) degreeChild) (dd i T)) ∧0≤Klow i T ∧
        let Cg:=nativeColumnSourceConstant T.card (S i).Cs (Cp i T) (Kt i T) Kchild (Kc i T)
          (Cd i T) (C0 i T) (C1 i T) (Kd i T)
        let Cu:=innerPhysicalConstant hH j r hr T
        Klow i T=(2+4*Real.pi)^(degreeLow i T)*
          (innerRawOldConstant T.card (S i).g.e Cu Cg
            (actualSelectedOldConstant Bnorm hB (Fintype.card alpha))
            (actualSelectedOldBoxConstant Bnorm hB (Fintype.card alpha) T.card)+Kcoarse i T) ∧
        (2+4*Real.pi)^(degreeLow i T)*innerRawReturnConstant T.card (S i).g.e Cu Cg≤Kreturn) ∧
      0≤Kreturn ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀i : InnerGridIndex j,∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
        InnerCanonicalSubsetAt hH W hW hWs hbeta hbetaHi eps tau Bnorm heps eta Q hQM hQ0 hQt hQ72
          j hj i (S i) r hr T (dt i T) (dd i T) (ct i T) (cd i T)
          (Kt i T) (Cp i T) (Kc i T) (Cd i T) (C0 i T) (C1 i T) (Kd i T) (Z^U) ∧
        NativeLowCoarseSubsetAt T (Fintype.card alpha) (S i).Cs (Kcoarse i T) (Z^U) ∧
        innerPhysicalThreshold hH j r hr T≤Z^U ∧
        actualSelectedOldThreshold Bnorm hB (Fintype.card alpha) T.card≤Z^U :=by
  intro r hr
  letI : Fintype (InnerGridIndex j):=Fintype.ofFinite _
  have produce:=fun i : InnerGridIndex j=>actual_inner_low_quantitative_metadata hH W hW hWs
    hbeta hbetaHi eps tau Bnorm heps hB eta Q hQM hQ0 hQt hQ72 j hj i (S i)
    Kchild hKchild controlChild degreeChild
  choose dt dd ct cd Kt Cp Kc Cd C0 C1 Kd Kcoarse Sp degreeLow Klow KretAt hp hm hKr hs using produce
  let Kreturn:=uniformConstant KretAt
  have hreturn:=uniformConstant_bounds KretAt
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,Kcoarse,Sp,degreeLow,Klow,Kreturn,hp,?_,
    zero_le_one.trans hreturn.1,?_⟩
  · intro i T
    obtain ⟨hSp,hzero,hdegree,hKlow,hKformula,hret⟩:=hm i T
    exact ⟨hSp,hzero,hdegree,hKlow,hKformula,hret.trans (hreturn.2 i)⟩
  · filter_upwards [Filter.eventually_all.mpr hs,eventually_gt_atTop (1:ℝ)] with Z hz hZ
    exact ⟨hZ,fun i U hU T=>(hz i).2 U hU T⟩

end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.actual_inner_low_grid_metadata
