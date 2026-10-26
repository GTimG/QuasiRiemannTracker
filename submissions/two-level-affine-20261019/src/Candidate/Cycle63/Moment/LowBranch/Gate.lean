import Candidate.Cycle63.Moment.LowBranch.Conductor
import Candidate.Cycle63.Moment.LowBranch.Slot

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The low branch is the supported part of the actual whole relative family,
for every fixed ray label. Its maximum includes every further ray twist. -/
def ActualLow {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (a e T : ℝ) (z : O) : Prop :=
  s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 ∧
  ∀ hz : s.radial.keep z, ∀ θ : RayQuotient.Characters M H,
    zeroMaximum (twistedFamily M H hH
      ((excluded (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse))
      (whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ θ).inverse hQM
        (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz
        (naturalRow s.character z (s.row_ne_zero z hz))) T < a+2*e

/-- Literal low slots satisfy the exact `restricted_low_main` payment. The
constant is chosen before all states, labels, widths and independent heights.
Only scalar buffer-height and frequency eligibility remain as live gates. -/
theorem actual_low_slots
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ (1+q)/2 →
      ∀ w σ t v : ℝ, 0 ≤ w → w/d ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z → ∀ θ : RayQuotient.Characters M H,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        (C*Z^(2*ε*d))*Z^(q*w) := by
  obtain ⟨C,hC,hslot⟩ := all_scale_buffered_slot M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε he he' hκ hη hbudget q hq₀ hq₁
  have hbase : ∀ᶠ Z : ℝ in atTop, 2 ≤ Z^d :=
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop _)
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop _)
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,
    hbase,hT] with Z hcond hZbase hZT
  refine ⟨hcond.1,?_⟩
  intro s hs hQM hQη a i ha ha' w σ t v hw hwr hσ hσ' hfreq hheight z hz hlow θ
  have hwdiv : 0 ≤ w/d := div_nonneg hw hd.le
  have hmod (θ' : RayQuotient.Characters M H) :=
    (hcond.2 s hs z (naturalRow s.character z (s.row_ne_zero z hz)) hlow.1 θ θ').trans
      (Real.rpow_le_rpow_of_exponent_le hcond.1.le hdsupply)
  have hb := hslot Z d hcond.1.le hd.le hdm hZbase hZT s
    (relativeCharacter M H hH η₀ θ).inverse hQM
    (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz
    (naturalRow s.character z (s.row_ne_zero z hz)) a i ha ha'
    (hlow.2 hz θ) (w/d) σ t v hwdiv hwr hσ hσ' hmod hfreq hheight
  have hwd : d*(w/d) = w := mul_div_cancel₀ w hd.ne'
  have hpower : (Z^d)^(w/d) = Z^w := by
    rw [← Real.rpow_mul (zero_lt_one.trans hcond.1).le, hwd]
  rw [hpower,hwd] at hb
  have hcoeff (I : Ideal O) :
      idealCoeff (relativeCharacter M H hH η₀ θ).inverse.inverse I =
        idealCoeff (relativeCharacter M H hH η₀ θ) I := by
    simp only [idealCoeff_inverse_conj, starRingEnd_self_apply]
  simp_rw [hcoeff] at hb
  apply hb.trans_eq
  rw [Real.rpow_add (zero_lt_one.trans hcond.1)]
  ring

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
