/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The true full detector union chooses i,a, then one attaining zero BEFORE all
cutoffs, retaining supported dyads on the same literal regular row. -/
import Candidate.C092.transport.TerminalActualRowState
import Candidate.C092.transport.SharedCutoffZero
import Candidate.C092.transport.MediumReplaceSourceWitness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CanonicalRowCompletion ConcreteTraceCRT ConcretePrimeRowBridge ProbeHighRowFamily
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

structure SameZero {Label : Type*} [Fintype Label] (chi : Label→Character) (hn : ∀j,(chi j).residue≠1)
    (U d dmax tau a epsilon : ℝ) (i : ℕ) where
  label : Label
  zero : ℂ
  is_zero : LFunction (chi label) zero=0
  maximum : zero.re=zeroMaximum chi hn ((3*i:ℕ)*U^tau)
  height : |zero.im|≤(3*i:ℕ)*U^tau
  witness : ∀cutoff : ℝ,1≤ cutoff → cutoff≤3/2 →
    SupportedWitness chi (U^d) a epsilon cutoff (U^tau) ((U^d)^(tau/(2*dmax))) i
  same_label : ∀cutoff h0 h1,(witness cutoff h0 h1).label=label
  same_zero : ∀cutoff h0 h1,(witness cutoff h0 h1).zero=zero

/-- The finite I is chosen before states, rows, relative characters, zero
labels or dyads. The SAME zero is then used for every later admitted cutoff. -/
theorem regular_detector_tickets
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (bPhi Mcap Bmask margin dmin dmax tau epsilon ez kappa cost : ℝ)
    (hbPhi : 0≤ bPhi) (hmargin : 0< margin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax)
    (htau : 0< tau) (htau0 : tau< dmin/2) (htauH : 4*tau< dmin*cost)
    (hepsilon : 0< epsilon) (hez : 0< ez) (hez1 : ez<1/1000)
    (hkappa : 0< kappa) (hkappa1 : kappa≤1) (hcost : 0≤ cost)
    (hbudget : 12*ez*(22+2)+8*kappa+2*cost≤ epsilon/2) :
    ∃ I : ℕ,0< I ∧ ∀eta0 : Character,∀ᶠ U : ℝ in atTop,1< U ∧
    ∀d : ℝ,dmin≤ d → d≤ dmax → Mcap+Bmask+margin≤ d →
    ∀s : NaturalState U Bmask bPhi,s.width≤ Mcap →
    ∀(hQM : s.fixedModulus≤ M) (hQeta : s.fixedModulus≤ eta0.modulus),
    ∀(u : FreeRow) (hu : s.radial.keep u.val),
    s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale)≠0 →
    ∃i k : ℕ,1≤ i ∧ i≤ I ∧ k≤⌊(73/200:ℝ)/ez⌋₊ ∧
    let a : ℝ:=51/100+ez*k
    let chi:=family M H hH s eta0 (naturalRow s.character u.val (s.row_ne_zero u.val hu))
    let hn:=family_nonprincipal M H hH s eta0 hQM hQeta hu _
    51/100≤ a ∧ a≤7/8 ∧
    zeroMaximum chi hn (3*(i+1:ℕ)*U^tau)< a+2*ez ∧
    a≤ zeroMaximum chi hn ((3*i:ℕ)*U^tau) ∧
    (51/100< a → Nonempty (SameZero chi hn U d dmax tau a epsilon i)) := by
  obtain ⟨I,hI,hcore⟩:=regular_core_witnesses M H hH bPhi Mcap Bmask margin dmin dmax tau epsilon ez kappa cost
    hbPhi hmargin hdmin hdmax htau htau0 htauH hepsilon hez hez1 hkappa hkappa1 hcost hbudget
  obtain ⟨U0,hshared⟩:=QRH.Cycle092.SharedCutoffZero.simultaneous_cutoffs dmin dmax tau epsilon ez kappa cost I
    hdmin hdmax htau htau0 htauH hepsilon hez hez1 hkappa hkappa1 hcost hbudget
  refine ⟨I,hI,?_⟩
  intro eta0
  filter_upwards [hcore eta0,family_conductor_eventually M H hH eta0 bPhi Mcap Bmask margin hbPhi hmargin,
    eventually_ge_atTop U0] with U hcore hcond hU0
  refine ⟨hcore.1,?_⟩
  intro d hd hd' hds s hs hQM hQeta u hu hPhi
  obtain ⟨i,k,hi,hiI,hk,ha,ha1,hnext,hcurrent,_⟩:=hcore.2 d hd hd' hds s hs hQM hQeta u.val hu hPhi
  have hau:=family_band_upper hbeta M H hH s eta0 hQM hQeta u hu _ _ hcurrent
  refine ⟨i,k,hi,hiI,?_,ha,hau,hnext,hcurrent,?_⟩
  · apply Nat.le_floor
    apply (le_div_iff₀ hez).mpr
    linarith only [hau]
  · intro hapos
    obtain ⟨j,rho,hzero,hmax,him,hw⟩:=hshared U hU0 d hd hd'
      (family M H hH s eta0 (naturalRow s.character u.val (s.row_ne_zero u.val hu)))
      (family_nonprincipal M H hH s eta0 hQM hQeta hu _) (51/100+ez*k) i hiI hapos
      (hau.trans (by norm_num)) hnext hcurrent
      (fun j=>(hcond.2 s hs u.val _ hPhi j).trans (Real.rpow_le_rpow_of_exponent_le hcond.1.le hds))
    choose witness hlabel hzero' using hw
    exact ⟨⟨j,rho,hzero,hmax,him,witness,hlabel,hzero'⟩⟩

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.regular_detector_tickets
