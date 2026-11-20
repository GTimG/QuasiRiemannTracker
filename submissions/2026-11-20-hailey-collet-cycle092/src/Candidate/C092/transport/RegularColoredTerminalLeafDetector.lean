/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual measured rows choose their genuine zero tickets and then the
recorded response windows, with no source-energy assumption. -/
import Candidate.C092.transport.RegularColoredTerminalLeafWindows
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalScale
import Candidate.C092.transport.TerminalActualRowMedium
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentWholeSlotDeletion ConcreteTraceCRT ConcretePrimeRowBridge ProbeHighRowFamily
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open QRH.Cycle092.TerminalActualRow QRH.Cycle092.StrongPair QRH.Cycle092.SourceInverseP6
open QRH.Cycle092.MediumReplace.Source QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafDetector_ed81e98d043c4cbd_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Enlarging only the finite ticket index retains the SAME zero, band,
frequency height, measured response and future cutoff witnesses. -/
def terminal_lift_row_ticket {Label : Type} [Fintype Label]
    {χ : Label→Character} {hn : ∀j,(χ j).residue≠1}
    {U d dmax τ ε ez price e : ℝ} {I J : ℕ} (hIJ : I ≤ J)
    (ticket : RowTicket χ hn U d dmax τ ε ez price e I) :
    RowTicket χ hn U d dmax τ ε ez price e J where
  band := ⟨ticket.band.val,by have h:=ticket.band.isLt;omega⟩
  band_pos := ticket.band_pos
  level := ticket.level
  lower := ticket.lower
  upper := ticket.upper
  next := ticket.next
  current := ticket.current
  ceiling := ticket.ceiling
  shared := ticket.shared

/-- This factory invokes the genuine measured detector itself. Its I and
payment constant precede U, arrays, finite rows and profiles. Window choice
occurs after each SAME zero, and never changes that zero or its label. -/
theorem terminal_actual_medium_tickets {Slot : Type} [Fintype Slot]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (buffer price Rwidth bΦ Mcap Bmask margin d dmin dmax τ η ε κ heightCost y step : ℝ)
    (cell : Cell) (table : TerminalResponseTable y step cell)
    (hbuffer : 0 < buffer) (hprice : 0 < price) (hgap : (1/50:ℝ)+price < (cell.threshold:ℝ))
    (hRw : 0 ≤ Rwidth) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hd : dmin ≤ d) (hd' : d ≤ dmax)
    (hdsupply : Mcap+Bmask+margin ≤ d)
    (hτ : 0 < τ) (hτ0 : τ < dmin/2) (hτH : 4*τ < dmin*heightCost)
    (hη : 0 ≤ η) (hheight : 2*τ < d*η)
    (hε : 0 < ε) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hcost : 0 ≤ heightCost) :
    ∃ezmax : ℝ,0 < ezmax ∧ ezmax < 1/1000 ∧
    ∀ez : ℝ,0 < ez → ez ≤ ezmax → 12*ez*(22+2)+8*κ+2*heightCost ≤ ε/2 →
    ∀(M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
    ∀W : ℝ→ℂ,Function.support W⊆Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∃I : ℕ,0 < I ∧ ∃C : ℝ,0 < C ∧ ∀base : Character,∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀Cslot : ℝ,C ≤ Cslot →
    ∀s : NaturalState U Bmask bΦ,s.width ≤ Mcap → s.mask=fixedBadMask*idealGenerator 1 →
    ∀(hQM : s.fixedModulus ≤ M) (hQbase : s.fixedModulus ≤ base.modulus)
      (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t height : ℝ),
      (∀j,0 ≤ w j) → (∀j,w j/d ≤ Rwidth) →
      (∀j,|v j| ≤ height) → |t|+height ≤ U^τ →
    ∀(rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val),
      (∀u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale)≠0) →
      (∀u∈rows,(cell.threshold:ℝ) ≤ measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u ∧
        measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u ≤ (responseUpper:ℝ)) →
    let χ := fun u : rows=>family M H hH s base (naturalRow s.character u.val.val u.val.property.1);
    let hn := fun u : rows=>family_nonprincipal M H hH s base hQM hQbase (hrows u.val u.property)
      (naturalRow s.character u.val.val u.val.property.1);
    ∃ticket : ∀u : rows,RowTicket (χ u) (hn u) U d dmax τ ε ez price
      (measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val) I,
    ∃window : rows→Fin table.Je×Fin table.Jν,
    ∃ws : ∀u : rows,SupportedWitness (χ u) (U^d) ((51/100:ℝ)+ez*(ticket u).level.val) ε
      (totalCutoff (table.cutoff (window u))) (U^τ) ((U^d)^(τ/(2*dmax))) (ticket u).band.val,
      (∀u : rows,table.egrid (window u).1 ≤ measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val ∧
        measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val < table.egrid (window u).1+step ∧
        max (table.egrid (window u).1) (table.νgrid (window u).2) ≤ 2*((51/100:ℝ)+ez*(ticket u).level.val)-1+price ∧
        2*((51/100:ℝ)+ez*(ticket u).level.val)-1 < max (table.egrid (window u).1) (table.νgrid (window u).2)+step) ∧
      (∀u : rows,(ws u).label=(ticket u).shared.label ∧ (ws u).zero=(ticket u).shared.zero) := by
  classical
  obtain ⟨ezmax,hezmax,hezsmall,hprovider⟩ := actual_medium_row_provider (Slot:=Slot) hβ
    (cell.threshold:ℝ) buffer price Rwidth bΦ Mcap Bmask margin d dmin dmax τ η ε κ heightCost
    hbuffer hprice hgap hRw hbΦ hmargin hdmin hdmax hd hd' hdsupply hτ hτ0 hτH hη hheight hε hκ hκ1 hcost
  refine ⟨ezmax,hezmax,hezsmall,?_⟩
  intro ez hez hezm hbudget M _ H hH W hWs hW
  obtain ⟨I,hI,C,hC,hprovider⟩ := hprovider ez hez hezm hbudget M H hH W hWs hW
  refine ⟨I,hI,C,hC,?_⟩
  intro base
  filter_upwards [hprovider base] with U hU
  refine ⟨hU.1,?_⟩
  intro Cslot hCslot s hs hmask hQM hQbase θ w v t height hw hwr hv ht rows hrows hΦ hmedium
  dsimp only
  let χ := fun u : rows=>family M H hH s base (naturalRow s.character u.val.val u.val.property.1)
  let hn := fun u : rows=>family_nonprincipal M H hH s base hQM hQbase (hrows u.val u.property)
    (naturalRow s.character u.val.val u.val.property.1)
  have htickets (u : rows) : Nonempty (RowTicket (χ u) (hn u) U d dmax τ ε ez price
      (measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val) I) := by
    apply rowTicket_of_provider
    exact hU.2 Cslot hCslot s hs hmask hQM hQbase θ w v t height hw hwr hv ht
      u.val (hrows u.val u.property) (hΦ u.val u.property) (hmedium u.val u.property).1
  let ticket := fun u : rows=>Classical.choice (htickets u)
  obtain ⟨window,ws,hwindow,hsame⟩ := terminal_windows_from_row_tickets χ hn U d dmax τ ε ez price y step cell table
    (fun u : rows=>measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val) hprice.le
    (fun u=>(hmedium u.val u.property)) ticket
  exact ⟨ticket,window,ws,hwindow,hsame⟩

#print axioms terminal_lift_row_ticket
#print axioms terminal_actual_medium_tickets
end
end QRH.Cycle092.RegularColoredForward
