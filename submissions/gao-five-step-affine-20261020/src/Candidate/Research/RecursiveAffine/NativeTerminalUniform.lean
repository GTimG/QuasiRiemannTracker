/- Actual terminal LOW sources on the fixed finite grid and original subsets.
Copyright (c)2026 Zhongpai Gao. Native estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeTerminalNode
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153Reachable Cycle153SourceSchedule Cycle153SourceUniform Cycle153Geometry
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)

abbrev TerminalGridIndex :=
  Cycle153.RegionalIndex Cycle153.FixedStages.stage4 Cycle153.RegionalSchedule.gridSize

/-- Literal native terminal source at one fixed grid position and original
subset. Neither the retained coefficients nor the LOW predicate is changed. -/
def TerminalLowSourceAt
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Cs : ℝ)(eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})
    (i : TerminalGridIndex)(J : Finset alpha)(Sp : Finset (ℕ×ℕ))(degree : ℕ)(K Z : ℝ) : Prop :=
  letI : DecidableEq (↥J):=Classical.decEq _
  letI : Cycle63.AffineLedger:=Cycle153.regionalFamily Cycle153.FixedStages.stage4
    Cycle153.RegionalSchedule.gridSize i
  GeometryAffineLowSelectedSpec (α:=(↥J)) M H hH W hbeta g 2
    (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
    (fun _ _ _ _ _=>True) Sp degree K eta Q hQM hQ72 Z

/-- All terminal native constants are chosen on the finite ORIGINAL
carrier and fixed coordinate grid before the moving base or source.
This invokes the actual native old-region theorem at every grid ledger. -/
theorem eventual_terminal_low_finite
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Cs : ℝ)(hCs : 1≤Cs)(eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)}) :
    ∃(Sp : TerminalGridIndex→Finset alpha→Finset (ℕ×ℕ))
      (degree : TerminalGridIndex→Finset alpha→ℕ)(K : TerminalGridIndex→Finset alpha→ℝ),
      (∀i J,0≤K i J) ∧ ∀ᶠZ : ℝ in atTop,∀i J,
        TerminalLowSourceAt hH W hbeta g Cs eta Q hQM hQ72 i J (Sp i J) (degree i J) (K i J) Z := by
  have h : ∀(i : TerminalGridIndex)(J : Finset alpha),
      ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,∃K : ℝ,0≤K ∧ ∀ᶠZ : ℝ in atTop,
        TerminalLowSourceAt hH W hbeta g Cs eta Q hQM hQ72 i J Sp degree K Z := by
    intro i J
    letI : DecidableEq (↥J):=Classical.decEq _
    letI : Cycle63.AffineLedger:=Cycle153.regionalFamily Cycle153.FixedStages.stage4
      Cycle153.RegionalSchedule.gridSize i
    letI : Cycle63.AffineLedger.DeletesIntoOldRegion:=
      Cycle153Terminal.terminal_regional_deletes_old _ i.property
    exact Cycle153Terminal.terminal_actual_low_spec (α:=(↥J)) M H hH
      W hW hWs hbeta g Cs hCs eta Q hQM hQ0 hQt hQ72
  choose Sp degree K hK hEv using h
  refine ⟨Sp,degree,K,hK,?_⟩
  exact Filter.eventually_all.2 (fun i=>Filter.eventually_all.2 (hEv i))

/-- One terminal source schedule also covers every actual child base
Z^U with the retained global unit U≥1/50. The cutoff cannot depend on U. -/
theorem eventual_terminal_low_finite_rebased
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Cs : ℝ)(hCs : 1≤Cs)(eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)}) :
    ∃(Sp : TerminalGridIndex→Finset alpha→Finset (ℕ×ℕ))
      (degree : TerminalGridIndex→Finset alpha→ℕ)(K : TerminalGridIndex→Finset alpha→ℝ),
      (∀i J,0≤K i J) ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U→∀i J,
        TerminalLowSourceAt hH W hbeta g Cs eta Q hQM hQ72 i J (Sp i J) (degree i J) (K i J) (Z^U) := by
  obtain ⟨Sp,degree,K,hK,hEv⟩:=eventual_terminal_low_finite (alpha:=alpha) hH
    W hW hWs hbeta g Cs hCs eta Q hQM hQ0 hQt hQ72
  exact ⟨Sp,degree,K,hK,eventually_all_rebased_sources _ hEv⟩

variable {C : SourceContext (α:=alpha) M H}

/-- The last plane is the actual source plane, not a fixed upper
intercept. Its identity is retained when selecting its grid ledger. -/
theorem terminal_node_plane (N : ReachableNode C (3:Fin 4)) :
    N.plane=length N.localBase N.X1+length N.localBase N.X2+
      (innerStage 3).lam*(∑i : N.slots,C.originalWeight i/N.unit) := by
  have hz : Coordinates.z4 N.coordinates/N.unit=(∑i : N.slots,C.originalWeight i/N.unit) := by
    rw [←Finset.sum_div,N.slots_eq];rfl
  have hA : Coordinates.A4 N.coordinates/N.unit=
      length N.localBase N.X1+length N.localBase N.X2+(∑i : N.slots,C.originalWeight i/N.unit) := by
    apply (div_eq_iff (ne_of_gt N.unit_pos)).2
    have hlen:=N.length_eq
    change N.unit*(length N.localBase N.X1+length N.localBase N.X2+
      (∑i : N.slots,C.originalWeight i/N.unit))=Coordinates.A4 N.coordinates at hlen
    simpa only [mul_comm] using hlen.symm
  rw [N.plane_eq]
  change (Coordinates.A4 N.coordinates+((innerStage 3).lam-1)*Coordinates.z4 N.coordinates)/N.unit=_
  calc
    _=Coordinates.A4 N.coordinates/N.unit+
      ((innerStage 3).lam-1)*(Coordinates.z4 N.coordinates/N.unit) := by ring
    _=_ := by rw [hA,hz];ring

/-- Every genuine terminal node selects one of the prechosen finite
ledgers. The index may depend on the source; its list and native constants
are fixed before Z by eventual_terminal_low_finite. -/
theorem terminal_node_ledger_mem_family (N : ReachableNode C (3:Fin 4))
    (hgrid : C.gridDenominator=Cycle153.RegionalSchedule.gridSize) :
    ∃i : TerminalGridIndex,Cycle153.regionalFamily Cycle153.FixedStages.stage4
      Cycle153.RegionalSchedule.gridSize i=N.ledger := by
  have hz : 0≤∑i : N.slots,C.originalWeight i/N.unit :=
    Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
  have hn1 : 0<length N.localBase N.X1 :=
    N.positionFacts.windowBottom_pos.trans_le N.window.left_ge
  have hn2 : 0<length N.localBase N.X2 :=
    N.positionFacts.windowBottom_pos.trans_le N.window.right_ge
  have hp0 : 0≤N.plane := by
    rw [terminal_node_plane N]
    have hl : 0≤(innerStage 3).lam := by linarith only [(innerStage 3).one_le_lam]
    positivity
  have hp : length N.localBase N.X1+length N.localBase N.X2+
      (innerStage 3).lam*(∑i : N.slots,C.originalWeight i/N.unit)≤N.plane :=
    (terminal_node_plane N).symm.le
  have hFacts : (Cycle153.roundedPosition (1/(Cycle153.RegionalSchedule.gridSize:ℝ))
      N.plane (length N.localBase N.X1) (length N.localBase N.X2)
      (∑i : N.slots,C.originalWeight i/N.unit)).Facts Cycle153.FixedStages.stage4 := by
    rw [←hgrid,←N.rounded];exact N.positionFacts
  obtain ⟨i,hi⟩:=Cycle153.roundedLedger_mem_family Cycle153.RegionalSchedule.gridSize_pos hz hp0 hp hFacts
  refine ⟨i,hi.trans ?_⟩
  apply Cycle153.regionalLedger_congr
  rw [←hgrid,←N.rounded]

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_terminal_low_finite
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_terminal_low_finite_rebased
#print axioms OAI.SevenEighths.Cycle153RegionalLow.terminal_node_plane
#print axioms OAI.SevenEighths.Cycle153RegionalLow.terminal_node_ledger_mem_family
