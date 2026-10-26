/- The actual canonical source uniformly on original subsets and physical bases.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalPaidColumns
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle153RegionalLow Cycle153SourceUniform
attribute [local irreducible] NativeCanonicalPaidColumnsAt
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable [Cycle63.AffineLedger]
open Cycle153AnalyticPrimitive Cycle153SourceSchedule
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

theorem eventual_actual_canonical_original_subsets
    (hH : RayOrthogonality.globalUnits M     ≤     H)
    (W : ℝ→ℂ)(hWs : Function.support W    ⊆    Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed     ≤     M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed     ≤     Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1     ≤     Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100     ≤     HeckeZeroSupremum.beta)
    (childStage : Fin 4)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0     ≤     Bmask)(hMcap : 0<Mcap) (hRw : 0     ≤     Rwidth) (hdmax : 0     ≤     dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0     ≤     heightExponent)
    (hbudget : 8*e*Rwidth+kappa     ≤     epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin     ≤     d) (hdm : d     ≤     dmax)
    (hq0 : 0     ≤     q) (hq1 : q     ≤     1) (inputBound epsShell : ℝ)(hShell : 0<epsShell)
    (Nbudget : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (epsNode : ℝ)(hepsNode : 0<epsNode)(hq : q=Cycle63.AffineLedger.q)
    (hOldLoss : epsOld ≤ oldLoss epsNode)(hReflectLoss : epsReflect ≤ oldLoss epsNode) :
    ∃(degreeTerminal degreeDirect : Finset alpha→ℕ)
      (controlTerminal controlDirect : Finset alpha→Finset (ℕ×ℕ))
      (Kterminal Cpay Kcol Cdirect C₀ C₁ Kdirect : Finset alpha→ℝ),
      (∀J0,0<Kterminal J0 ∧ 1 ≤ Cpay J0 ∧ 0<Kcol J0 ∧ 1 ≤ Cdirect J0 ∧
        0<C₀ J0 ∧ 0<C₁ J0 ∧ 0<Kdirect J0) ∧
      ∀ᶠZparent : ℝ in atTop,1<Zparent ∧ ∀J0 : Finset alpha,
      NativeCanonicalPaidColumnsAt (Current:=(↥J0)) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage (originalSubsetEmbedding J0) Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
      (degreeTerminal J0) (controlTerminal J0) (Kterminal J0) (Cpay J0) (Kcol J0) Zparent Nbudget Cs
      (degreeDirect J0) (controlDirect J0) (Cdirect J0) (C₀ J0) (C₁ J0) (Kdirect J0) epsNode := by
  have produce : ∀J0 : Finset alpha,
      ∃(degreeTerminal degreeDirect : ℕ)(controlTerminal controlDirect : Finset (ℕ×ℕ))
        (Kterminal Cpay Kcol Cdirect C₀ C₁ Kdirect : ℝ),
        (0<Kterminal ∧ 1 ≤ Cpay ∧ 0<Kcol ∧ 1 ≤ Cdirect ∧ 0<C₀ ∧ 0<C₁ ∧ 0<Kdirect) ∧
        ∀ᶠZparent : ℝ in atTop,1<Zparent ∧ NativeCanonicalPaidColumnsAt (Current:=(↥J0)) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage (originalSubsetEmbedding J0) Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol Zparent Nbudget Cs
      degreeDirect controlDirect Cdirect C₀ C₁ Kdirect epsNode := by
    intro J0
    obtain ⟨dt,ct,Kt,Cp,Kc,dd,cd,Cd,C0,C1,Kd,hKt,hCp,hKc,hCd,hC0,hC1,hKd,hs⟩:=
      eventual_actual_canonical_paid_columns (Current:=(↥J0)) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72
        Lbound epsOld epsReflect hLbound hOld hReflect hbeta childStage (originalSubsetEmbedding J0)
        Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
        hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
        hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell Nbudget Cs hCs epsNode hepsNode hq hOldLoss hReflectLoss
    exact ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd⟩,hs⟩
  choose degreeTerminal degreeDirect controlTerminal controlDirect Kterminal Cpay Kcol Cdirect C₀ C₁ Kdirect
    hpositive hsource using produce
  refine ⟨degreeTerminal,degreeDirect,controlTerminal,controlDirect,Kterminal,Cpay,Kcol,Cdirect,C₀,C₁,Kdirect,hpositive,?_⟩
  filter_upwards [Filter.eventually_all.2 hsource] with Z hz
  exact ⟨(hz ∅).1,fun J0=>(hz J0).2⟩

theorem eventual_actual_canonical_original_subsets_rebased
    (hH : RayOrthogonality.globalUnits M     ≤     H)
    (W : ℝ→ℂ)(hWs : Function.support W    ⊆    Icc 1 2)(hW : ContDiff ℝ ∞ W)
    (etaSeed : Character)(Qfixed : Ideal O)
    (hQfixedM : Qfixed     ≤     M)(hQ0 : internalQ Qfixed etaSeed ≠ 0)
    (hQt : internalQ Qfixed etaSeed ≠ ⊤)(hQ72 : internalQ Qfixed etaSeed     ≤     Ideal.span {(72:O)})
    (Lbound epsOld epsReflect : ℝ)
    (hLbound : 1     ≤     Lbound)(hOld : 0<epsOld)(hReflect : 0<epsReflect)
    (hbeta : 51/100     ≤     HeckeZeroSupremum.beta)
    (childStage : Fin 4)
    (Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q : ℝ)
    (hBmask : 0     ≤     Bmask)(hMcap : 0<Mcap) (hRw : 0     ≤     Rwidth) (hdmax : 0     ≤     dmax) (htau : 0<tau) (hepsilon : 0<epsilon)
    (he : 0<e) (he' : e<1/1000) (hkappa : 0<kappa) (hheightExponent : 0     ≤     heightExponent)
    (hbudget : 8*e*Rwidth+kappa     ≤     epsilon) (hmargin : 0 < margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin     ≤     d) (hdm : d     ≤     dmax)
    (hq0 : 0     ≤     q) (hq1 : q     ≤     1) (inputBound epsShell : ℝ)(hShell : 0<epsShell)
    (Nbudget : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (epsNode : ℝ)(hepsNode : 0<epsNode)(hq : q=Cycle63.AffineLedger.q)
    (hOldLoss : epsOld ≤ oldLoss epsNode)(hReflectLoss : epsReflect ≤ oldLoss epsNode) :
    ∃(degreeTerminal degreeDirect : Finset alpha→ℕ)
      (controlTerminal controlDirect : Finset alpha→Finset (ℕ×ℕ))
      (Kterminal Cpay Kcol Cdirect C₀ C₁ Kdirect : Finset alpha→ℝ),
      (∀J0,0<Kterminal J0 ∧ 1 ≤ Cpay J0 ∧ 0<Kcol J0 ∧ 1 ≤ Cdirect J0 ∧
        0<C₀ J0 ∧ 0<C₁ J0 ∧ 0<Kdirect J0) ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ) ≤ U→∀J0 : Finset alpha,
      NativeCanonicalPaidColumnsAt (Current:=(↥J0)) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
      hLbound hOld hReflect hbeta childStage (originalSubsetEmbedding J0) Rwidth dmax tau epsilon e kappa heightExponent
      Mcap Bmask margin d q hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent
      hbudget hmargin hd hdsupply hdm hq0 hq1 inputBound epsShell hShell
      (degreeTerminal J0) (controlTerminal J0) (Kterminal J0) (Cpay J0) (Kcol J0) (Z^U) Nbudget Cs
      (degreeDirect J0) (controlDirect J0) (Cdirect J0) (C₀ J0) (C₁ J0) (Kdirect J0) epsNode := by
  obtain ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,hs⟩:=
    eventual_actual_canonical_original_subsets (alpha:=alpha) hH W hWs hW etaSeed Qfixed hQfixedM hQ0 hQt hQ72 Lbound epsOld epsReflect
    hLbound hOld hReflect hbeta childStage Rwidth dmax tau epsilon e kappa heightExponent Mcap Bmask margin d q
    hBmask hMcap hRw hdmax htau hepsilon he he' hkappa hheightExponent hbudget hmargin hd hdsupply hdm hq0 hq1
    inputBound epsShell hShell Nbudget Cs hCs epsNode hepsNode hq hOldLoss hReflectLoss
  refine ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,hpositive,?_⟩
  have hh:=eventually_all_rebased_sources _ hs
  filter_upwards [hh] with Z hz
  exact ⟨hz.1,fun U hU J0=>(hz.2 U hU).2 J0⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.eventual_actual_canonical_original_subsets_rebased
