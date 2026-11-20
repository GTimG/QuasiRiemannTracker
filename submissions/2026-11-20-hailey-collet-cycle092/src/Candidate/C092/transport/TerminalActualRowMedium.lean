/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual measured medium rows select a genuine band and SAME-zero witnesses.
Only native prime comparison and native zero selection are invoked here. -/
import Candidate.C092.transport.TerminalActualRowDetector
import Candidate.C092.transport.TerminalResponseCeilingFamily
import Candidate.C092.transport.TerminalResponseCeilingHeight
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentWholeSlotDeletion ConcreteTraceCRT ConcretePrimeRowBridge ProbeHighRowFamily
open QRH.Cycle092.SourceInverseP6
open QRH.Cycle092.MediumReplace.Source QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
open QRH.Cycle092.TerminalResponseCeiling
local notation "O" => HeckeFamily.O

theorem medium_nonfloor {response a threshold price : ℝ}
    (hmedium : threshold≤ response) (hgap : (1/50:ℝ)+price< threshold)
    (hceiling : response≤(2*a-1)+price) : (51/100:ℝ)< a := by
  linarith only [hmedium,hgap,hceiling]

/-- Zero collar chosen early, then the exact source constant and finite I,
then U; actual states, arrays, rows and cutoff choices come afterwards.
The measured response is the genuine descriptor response at unchanged pay. -/
theorem actual_medium_row_provider {Slot : Type} [Fintype Slot]
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (threshold buffer price Rwidth bPhi Mcap Bmask margin d dmin dmax tau eta epsilon kappa cost : ℝ)
    (hbuffer : 0< buffer) (hprice : 0< price) (hgap : (1/50:ℝ)+price< threshold)
    (hRw : 0≤ Rwidth) (hbPhi : 0≤ bPhi) (hmargin : 0< margin)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hd : dmin≤ d) (hd' : d≤ dmax)
    (hdsupply : Mcap+Bmask+margin≤ d)
    (htau : 0< tau) (htau0 : tau< dmin/2) (htauH : 4*tau< dmin*cost)
    (heta : 0≤ eta) (hheight : 2*tau< d*eta)
    (hepsilon : 0< epsilon) (hkappa : 0< kappa) (hkappa1 : kappa≤1) (hcost : 0≤ cost) :
    ∃ ezmax : ℝ,0< ezmax ∧ ezmax<1/1000 ∧
    ∀ ez : ℝ,0< ez → ez≤ ezmax → 12*ez*(22+2)+8*kappa+2*cost≤ epsilon/2 →
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H),
    ∀W : ℝ→ℂ,Function.support W⊆Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∃ I : ℕ,0< I ∧ ∃ C : ℝ,0< C ∧ ∀eta0 : Character,∀ᶠ U : ℝ in atTop,1< U ∧
    ∀Cslot : ℝ,C≤ Cslot →
    ∀s : NaturalState U Bmask bPhi,s.width≤ Mcap → s.mask=fixedBadMask*idealGenerator 1 →
    ∀(hQM : s.fixedModulus≤ M) (hQeta : s.fixedModulus≤ eta0.modulus),
    ∀(theta : Slot→RayQuotient.Characters M H) (width pitch : Slot→ℝ) (t height : ℝ),
      (∀j,0≤ width j) → (∀j,width j/d≤ Rwidth) →
      (∀j,|pitch j|≤ height) → |t|+height≤ U^tau →
    ∀(u : FreeRow) (hu : s.radial.keep u.val),
      s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale)≠0 →
      threshold≤ measured M H hH s.character eta0 W U (Cslot*U^buffer) theta width pitch t u →
    ∃i k : ℕ,1≤ i ∧ i≤ I ∧ k≤⌊(73/200:ℝ)/ez⌋₊ ∧
      let a : ℝ:=51/100+ez*k
      let chi:=family M H hH s eta0 (naturalRow s.character u.val (s.row_ne_zero u.val hu))
      let hn:=family_nonprincipal M H hH s eta0 hQM hQeta hu _
      51/100< a ∧ a≤7/8 ∧
      zeroMaximum chi hn (3*(i+1:ℕ)*U^tau)< a+2*ez ∧
      a≤ zeroMaximum chi hn ((3*i:ℕ)*U^tau) ∧
      measured M H hH s.character eta0 W U (Cslot*U^buffer) theta width pitch t u≤(2*a-1)+price ∧
      Nonempty (SameZero chi hn U d dmax tau a epsilon i) := by
  obtain ⟨ezmax,hezmax,hezsmall,hceil⟩:=terminal_family_measured_ceiling (Slot:=Slot)
    threshold buffer price Rwidth dmax tau eta bPhi Mcap Bmask margin d
    hbuffer hprice hgap hRw ((hdmin.trans_le hdmax).le) htau heta hbPhi hmargin
    (hdmin.trans_le hd) hdsupply hd'
  refine ⟨ezmax,hezmax,hezsmall,?_⟩
  intro ez hez hezm hbudget M _ H hH W hWs hW
  have hez1 : ez<1/1000 := hezm.trans_lt hezsmall
  obtain ⟨I,hI,htickets⟩:=regular_detector_tickets hbeta M H hH bPhi Mcap Bmask margin dmin dmax tau epsilon ez kappa cost
    hbPhi hmargin hdmin hdmax htau htau0 htauH hepsilon hez hez1 hkappa hkappa1 hcost hbudget
  obtain ⟨C,hC,hceil⟩:=hceil ez hez hezm M H hH W hWs hW
  refine ⟨I,hI,C,hC,?_⟩
  intro eta0
  filter_upwards [htickets eta0,hceil eta0,eventual_native_height_gate I htau.le hheight] with U hticket hceiling hbig
  refine ⟨hticket.1,?_⟩
  intro Cslot hCslot s hs hmask hQM hQeta theta width pitch t height hw hwr hpitch ht u hu hPhi hmedium
  obtain ⟨i,k,hi,hiI,hk,ha,ha',hnext,hcurrent,hsame⟩:=hticket.2 d hd hd' hdsupply s hs hQM hQeta u hu hPhi
  have hresponse:=hceiling.2 Cslot hCslot s hs hmask hQM hQeta (51/100+ez*k) i
    (by linarith only [ha]) ha' theta width pitch t hw hwr
    (fun j=> native_frequency_gate i (zero_lt_one.trans hticket.1).le (hpitch j) ht)
    (hbig.2 i hiI) u hu hPhi hnext hmedium
  have hapos:=medium_nonfloor hmedium hgap hresponse
  exact ⟨i,k,hi,hiI,hk,hapos,ha',hnext,hcurrent,hresponse,hsame hapos⟩

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.actual_medium_row_provider
