/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual terminal descriptor response with its unchanged early payment. -/
import Candidate.C092.transport.TerminalResponseCeilingMedium
import Candidate.C092.transport.MediumReplaceSourceFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalResponseCeiling
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.SourceInverseP6
open HeckeDetectorZeros CenteredMomentNaturalRowSource QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

/-- The terminal's actual full-family zeroMaximum band implies the response
ceiling on the same original medium rows. Only the literal zero-band gate
is an input; the prime comparison is proved by the native source. -/
theorem terminal_family_measured_ceiling {Slot : Type} [Fintype Slot]
    (threshold buffer price Rwidth dmax τ η bΦ Mcap Bmask margin d : ℝ)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
    (hgap : (1/50:ℝ)+price < threshold)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ emax : ℝ, 0 < emax ∧ emax < 1/1000 ∧
    ∀ e : ℝ, 0 < e → e ≤ emax →
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M ≤ H),
    ∀ W : ℝ→ℂ, Function.support W ⊆ Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ Cslot : ℝ, C ≤ Cslot →
      ∀ s : NaturalState U Bmask bΦ, s.width ≤ Mcap → s.mask=fixedBadMask*idealGenerator 1 →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 1/2 ≤ a → a ≤ 7/8 →
      ∀ (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ),
        (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
        (∀ j, |t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ (u : FreeRow) (hu : s.radial.keep u.val),
      s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0 →
      zeroMaximum (family M H hH s η₀ (naturalRow s.character u.val (s.row_ne_zero u.val hu)))
        (family_nonprincipal M H hH s η₀ hQM hQη hu _) (3*(i+1 : ℕ)*U^τ) < a+2*e →
      threshold ≤ measured M H hH s.character η₀ W U (Cslot*U^buffer) θ w v t u →
      measured M H hH s.character η₀ W U (Cslot*U^buffer) θ w v t u ≤ (2*a-1)+price := by
  obtain ⟨emax,hm,hms,hsource⟩ := terminal_medium_measured_ceiling (Slot:=Slot)
    threshold buffer price Rwidth dmax τ η bΦ Mcap Bmask margin d
    hbuffer hprice hgap hRw hdmax hτ hη hbΦ hmargin hd hdsupply hdm
  refine ⟨emax,hm,hms,?_⟩
  intro e he hem M _ H hH W hWs hW
  obtain ⟨C,hC,hsource⟩ := hsource e he hem M H hH W hWs hW
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hsource η₀] with U hU
  refine ⟨hU.1,?_⟩
  intro Cslot hCslot s hs hmask hQM hQη a i ha ha' θ w v t hw hwr hfreq hheight u hu hΦ hband hmedium
  have hlow := actualLow_of_family_band M H hH s η₀ hQM hQη u.val hu a e
    (3*(i+1 : ℕ)*U^τ) hΦ hband
  exact hU.2 Cslot hCslot s hs hmask hQM hQη a i ha ha' θ w v t hw hwr hfreq hheight u hu hlow hmedium

#print axioms terminal_family_measured_ceiling
end
end QRH.Cycle092.TerminalResponseCeiling
