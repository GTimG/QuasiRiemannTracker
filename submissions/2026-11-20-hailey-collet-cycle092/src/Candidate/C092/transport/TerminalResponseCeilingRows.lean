/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual terminal descriptor response with its unchanged early payment. -/
import Candidate.C092.transport.TerminalResponseCeiling
import Candidate.C092.transport.SourceInverseP6CloseNormTransport

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
local notation "O" => HeckeFamily.O

/-- The exact descriptor response, on the same marks and actual unit mask. -/
theorem measured_eq_originalResponse {Slot : Type} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η η₀ : Character) (W : ℝ→ℂ) (U pay : ℝ)
    (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ) (u : FreeRow) :
    measured M H hH η η₀ W U pay θ w v t u =
    originalResponse η (fixedBadMask*idealGenerator 1) 1 t U pay w
      (originalPools M H 2 U w) (originalCoefficients M H hH η₀ θ W U w (fun _=>33/50) v)
      (fun j=>U^(w j)) u.val := by
  unfold measured originalResponse
  apply congrArg (response U pay w)
  funext j
  rw [descriptor_short_anchor M H hH η η₀ W U θ w (fun _=>33/50) v t u j rfl]

/-- Arbitrary prescribed positive payment buffer and price. The zero collar
is early; Cslot may be raised once, preserving that exact payment throughout
all response, attainer, P4 and P6 constructions. No minimum slot width occurs. -/
theorem terminal_measured_ceiling {Slot : Type} [Fintype Slot]
    (buffer price Rwidth dmax τ η bΦ Mcap Bmask margin d : ℝ)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
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
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 7/8 →
      ∀ (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ),
        (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
        (∀ j, |t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ u : FreeRow, s.radial.keep u.val → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) u.val →
      measured M H hH s.character η₀ W U (Cslot*U^buffer) θ w v t u ≤ (2*a-1)+price := by
  obtain ⟨emax,hm,hms,hsource⟩ := terminal_prime_response_ceiling (Slot:=Slot)
    buffer price Rwidth dmax τ η (33/50) (33/50) bΦ Mcap Bmask margin d
    hbuffer hprice hRw hdmax hτ hη hbΦ hmargin hd hdsupply hdm
  refine ⟨emax,hm,hms,?_⟩
  intro e he hem M _ H hH W hWs hW
  obtain ⟨C,hC,hsource⟩ := hsource e he hem M H hH W 1 2 (by norm_num) hWs hW
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hsource η₀] with U hU
  refine ⟨hU.1,?_⟩
  intro Cslot hCslot s hs hmask hQM hQη a i ha ha' θ w v t hw hwr hfreq hheight u hu hlow
  rw [measured_eq_originalResponse]
  rw [←hmask]
  exact hU.2 Cslot hCslot s hs hQM hQη a i ha ha' θ w (fun _=>33/50) v t
    hw hwr (fun _=>le_rfl) (fun _=>le_rfl) hfreq hheight u.val hu hlow

/-- Clamping the native .51 floor loses nothing on a genuine medium row.
The small-band branch is empty by the proved response upper, rather than
by changing the original band. -/
theorem medium_ceiling_unclamp {e ν price threshold : ℝ}
    (he : threshold ≤ e) (hgap : (1/50:ℝ)+price < threshold)
    (hceil : e ≤ max (1/50:ℝ) ν+price) : e ≤ ν+price := by
  by_cases hν : (1/50:ℝ) ≤ ν
  · simpa only [max_eq_right hν] using hceil
  · rw [max_eq_left (le_of_not_ge hν)] at hceil
    linarith

#print axioms measured_eq_originalResponse
#print axioms terminal_measured_ceiling
#print axioms medium_ceiling_unclamp
end
end QRH.Cycle092.TerminalResponseCeiling
