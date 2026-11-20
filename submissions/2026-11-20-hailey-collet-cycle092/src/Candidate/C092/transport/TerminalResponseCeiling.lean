/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Arbitrarily small paid response/zero ceiling, with early zero collar. -/
import Candidate.C092.transport.TerminalResponseCeilingSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalResponseCeiling
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

/-- The buffer and tiny comparison price are prescribed. A positive zero
collar bound precedes the ray dictionary, profile, characters, data and rows.
Every smaller positive collar works with the exact same prescribed payment.
No lower prime width, attaining slot or assumed comparison is required. -/
theorem terminal_prime_response_ceiling {Slot : Type*} [Fintype Slot]
    (buffer price Rwidth dmax τ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ emax : ℝ, 0 < emax ∧ emax < 1/1000 ∧
    ∀ e : ℝ, 0 < e → e ≤ emax →
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M ≤ H),
    ∀ (W : ℝ→ℂ) (A B : ℝ), 0 < A → Function.support W ⊆ Icc A B → ContDiff ℝ ∞ W →
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ Cslot : ℝ, C ≤ Cslot →
      ∀ s : NaturalState U Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 7/8 →
      ∀ (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (t : ℝ),
        (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
        (∀ j, σmin ≤ σ j) → (∀ j, σ j ≤ σmax) →
        (∀ j, |t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) z →
      originalResponse s.character s.mask 1 t U (Cslot*U^buffer) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j=>U^(w j)) z ≤ (2*a-1)+price := by
  let ε := buffer/(2*d)
  have hε : 0 < ε := div_pos hbuffer (by positivity)
  let emax := min (1/2000:ℝ) (ε/(32*(1+Rwidth)))
  have hden : 0 < 32*(1+Rwidth) := by positivity
  have hmax : 0 < emax := lt_min (by norm_num) (div_pos hε hden)
  have hmaxsmall : emax < 1/1000 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨emax,hmax,hmaxsmall,?_⟩
  intro e he hem M _ H hH W A B hA hWs hW
  have he' : e < 1/1000 := hem.trans_lt hmaxsmall
  have heb := (le_div_iff₀ hden).mp (hem.trans (min_le_right _ _))
  have hbudget : 8*e*Rwidth+ε/2 ≤ ε := by nlinarith [mul_nonneg he.le hRw]
  have hpay : 2*ε*d = buffer := by dsimp [ε]; field_simp
  obtain ⟨C,hC,hsource⟩ := actual_zero_band_ceiling (Slot:=Slot) M H hH price hprice
    W A B hA hWs hW Rwidth dmax τ ε e (ε/2) η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' (by positivity) hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  simpa only [hpay] using hsource

#print axioms terminal_prime_response_ceiling
end
end QRH.Cycle092.TerminalResponseCeiling
