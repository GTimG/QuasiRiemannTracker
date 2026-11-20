/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual all-scale LowActual supplier at exactly the shared normalization
used by the genuine original medium witness supplier. -/
import Candidate.C092.transport.MediumWitnessNormalization
import Candidate.C092.transport.LowActualSource

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.WholeSlot
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_MediumWitnessLowCompatibility_1e3dad0a60325d4c_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The existing genuine low supplier, with all original state/mask/pool data
retained, still proves its full slot inequalities and measured response at the
common payment. The common constant precedes all states, widths and labels. -/
theorem actual_low_common_response (D : BaselineData)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ,0 < C ∧ ∀ η₀ : Character,∀ᶠ U : ℝ in atTop,1 < U ∧
      commonPayment D U (C*U^(2*ε*d)) ≤ max 1 C*U^(2*ε*d+D.t) ∧
      ∀ s : NaturalState U Bmask bΦ,s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ),51/100 ≤ a → a ≤ (1+q)/2 →
      ∀ (θ : Slot → RayQuotient.Characters M H) (w σ v : Slot → ℝ) (t : ℝ),
        (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ Rwidth) →
        (∀ j,σmin ≤ σ j) → (∀ j,σ j ≤ σmax) →
        (∀ j,|t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ z : O,s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) z →
      LowRows Finset.univ s.character s.mask 1 t U q (commonPayment D U (C*U^(2*ε*d))) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ∧
      0 ≤ LowActual.originalResponse s.character s.mask 1 t U (commonPayment D U (C*U^(2*ε*d))) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ∧
      LowActual.originalResponse s.character s.mask 1 t U (commonPayment D U (C*U^(2*ε*d))) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ≤ q := by
  obtain ⟨C,hC,hsource⟩ := LowActual.actual_low_response (Slot := Slot) M H hH q hq0 hq1 W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hsource η₀] with U hU
  refine ⟨hU.1,commonPayment_le D U C (2*ε*d) hU.1.le (by positivity),?_⟩
  intro s hs hQM hQη a i ha ha' θ w σ v t hw hwr hσ hσ' hfreq hheight z hz hlow
  have hlowSlots := (hU.2 s hs hQM hQη a i ha ha' θ w σ v t hw hwr hσ hσ' hfreq hheight z hz hlow).1
  have hactual : ∀ j,‖normalizedSlot s.character s.mask 1 z
      (originalPools M H B U w j) (originalCoefficients M H hH η₀ θ W U w σ v j)
      t (U^(w j))‖^2 ≤ commonPayment D U (C*U^(2*ε*d))*U^(q*w j) := by
    intro j
    exact (hlowSlots j (Finset.mem_univ j)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
  exact ⟨by simpa [LowRows] using hactual,
    LowActual.originalResponse_bounded s.character s.mask 1 t U (commonPayment D U (C*U^(2*ε*d))) q w
      (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
      (fun j => U^(w j)) z hU.1 (commonPayment_pos D (zero_lt_one.trans hU.1)) hw hq0 hactual⟩

end QRH.Cycle092.MediumWitness
