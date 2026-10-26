/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual LOW slots at the original mask, with exact enlarged-puncture transport. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.LowGate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonPositive
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.LowErasure
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open Cycle61Moment.LowBranch
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge Record1252270103Second
local notation "O" => HeckeFamily.O

lemma normalized_slot_puncture (χ : Character) (R extra : Ideal O)
    (A z : O) (t P : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (havoid : ∀I∈S,IsCoprime I extra) :
    normalizedSlot χ (fixedBadMask*idealGenerator (R*extra)) A z S β t P=
      normalizedSlot χ (fixedBadMask*idealGenerator R) A z S β t P := by
  unfold normalizedSlot
  rw [rowSlot_newton_puncture χ R extra A z t S β havoid]

variable (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hq0 hq1

theorem actual_low_slots_parent_mask
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ (1+q)/2 →
      ∀ w σ t v : ℝ, 0 ≤ w → w/d ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z → ∀ θ : RayQuotient.Characters M H,
      ∀ R extra : Ideal O, s.puncture=R*extra →
      (∀ I∈primePool M H B (Z^w), IsCoprime I extra) →
      ‖normalizedSlot s.character (fixedBadMask*idealGenerator R) 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        (C*Z^(2*ε*d))*Z^(q*w) := by
  obtain ⟨C,hC,hslots⟩ := Record12518109SourceLow.actual_low_slots q hq0 hq1 M H hH
    W A B hA hWs hW Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' w σ t v hw hwr hσ hσ' hfreq hheight z hz hlow θ
    R extra hpuncture havoid
  have hh := hZ.2 s hs hQM hQη a i ha ha' w σ t v hw hwr hσ hσ' hfreq hheight z hz hlow θ
  have hm : s.mask=fixedBadMask*idealGenerator (R*extra) := by
    change fixedBadMask*idealGenerator s.puncture=_
    rw [hpuncture]
  rw [hm, normalized_slot_puncture _ R extra _ _ _ _ _ _ havoid] at hh
  exact hh
end
end QRH.Record1252270103Source.LowErasure
#print axioms QRH.Record1252270103Source.LowErasure.normalized_slot_puncture
#print axioms QRH.Record1252270103Source.LowErasure.actual_low_slots_parent_mask
