/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual terminal descriptor response with its unchanged early payment. -/
import Candidate.C092.transport.TerminalResponseCeilingRows

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

/-- Monotonicity of the actual zero-band gate, on its original full relative family. -/
theorem actualLow_mono_band
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {U Bmask bΦ : ℝ} (s : NaturalState U Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    {a a' e T : ℝ} {z : O} (ha : a ≤ a')
    (hlow : ActualLow M H hH s η₀ hQM hQη a e T z) :
    ActualLow M H hH s η₀ hQM hQη a' e T z := by
  refine ⟨hlow.1,?_⟩
  intro hz θ
  exact (hlow.2 hz θ).trans_le (by linarith only [ha])

/-- On genuine medium rows, the native .51 floor is eliminated by the
proved small-response bound. The literal original zero band is unchanged. -/
theorem terminal_medium_measured_ceiling {Slot : Type} [Fintype Slot]
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
      ∀ u : FreeRow, s.radial.keep u.val → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) u.val →
      threshold ≤ measured M H hH s.character η₀ W U (Cslot*U^buffer) θ w v t u →
      measured M H hH s.character η₀ W U (Cslot*U^buffer) θ w v t u ≤ (2*a-1)+price := by
  obtain ⟨emax,hm,hms,hsource⟩ := terminal_measured_ceiling (Slot:=Slot)
    buffer price Rwidth dmax τ η bΦ Mcap Bmask margin d
    hbuffer hprice hRw hdmax hτ hη hbΦ hmargin hd hdsupply hdm
  refine ⟨emax,hm,hms,?_⟩
  intro e he hem M _ H hH W hWs hW
  obtain ⟨C,hC,hsource⟩ := hsource e he hem M H hH W hWs hW
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hsource η₀] with U hU
  refine ⟨hU.1,?_⟩
  intro Cslot hCslot s hs hmask hQM hQη a i ha ha' θ w v t hw hwr hfreq hheight u hu hlow hmedium
  have ha0 : (51/100:ℝ) ≤ max (51/100:ℝ) a := le_max_left _ _
  have ha1 : max (51/100:ℝ) a ≤ 7/8 := max_le (by norm_num) ha'
  have hlow' := actualLow_mono_band M H hH s η₀ hQM hQη
    (le_max_right (51/100:ℝ) a) hlow
  have hb := hU.2 Cslot hCslot s hs hmask hQM hQη (max (51/100:ℝ) a) i ha0 ha1
    θ w v t hw hwr hfreq hheight u hu hlow'
  have hid : 2*max (51/100:ℝ) a-1 = max (1/50:ℝ) (2*a-1) := by
    by_cases h : (51/100:ℝ) ≤ a
    · rw [max_eq_right h,max_eq_right (by linarith : (1/50:ℝ) ≤ 2*a-1)]
    · have h' : a ≤ (51/100:ℝ) := le_of_not_ge h
      rw [max_eq_left h',max_eq_left (by linarith : 2*a-1 ≤ (1/50:ℝ))]
      norm_num
  rw [hid] at hb
  exact medium_ceiling_unclamp hmedium hgap hb

#print axioms actualLow_mono_band
#print axioms terminal_medium_measured_ceiling
end
end QRH.Cycle092.TerminalResponseCeiling
