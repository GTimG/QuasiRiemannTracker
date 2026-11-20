/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Applies the actual all-scale regular-row supplier to original marked slots.
   The supplier retains its Gao/OpenAI/DaysSky/predecessor source attribution. -/
import Candidate.C092.transport.LowActualResponse
import Submissions.hailey_collet_1252270103.Record1252270103Source.LowErasure.Slots

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

/-- The regular original radial state at U^V, kept at base U for the original
slot widths. Its puncture is exactly one; it adds no mask-opening premise. -/
def regularState (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ U V δ : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ) (hp : ∀ x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm : ℝ) ≤ U^δ) : NaturalState U 0 bΦ where
  character := η
  fixedModulus := Q
  puncture := 1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U^V
    scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _
    nonneg := fun _ => hp _ }
  rowWidth := V
  characterWidth := δ
  base_ge_one := hU
  row_nonneg := hV
  character_nonneg := hδ
  scale_eq := rfl
  modulus_bound := hη
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp
  radial_support := hs
  row_ne_zero := fun _ hz => hz.1
  nonexceptional := fun _ hz => hz.2

@[simp] theorem regularState_width (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ U V δ : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ) (hp : ∀ x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm : ℝ) ≤ U^δ) :
    (regularState η Q Φ bΦ U V δ hU hV hδ hs hp hη).width = V+δ := rfl

variable {Slot : Type*} [Fintype Slot]
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_LowActualSource_b98b864b71d1caca_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual all-scale source calibrates all original slot responses at
once. C precedes labels, scales, states and all finite slot data. This uses
literal ActualLow; it does not equate a zero band with measured response. -/
theorem actual_low_response
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ s : NaturalState U Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ (1+q)/2 →
      ∀ (θ : Slot → RayQuotient.Characters M H) (w σ v : Slot → ℝ) (t : ℝ),
        (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
        (∀ j, σmin ≤ σ j) → (∀ j, σ j ≤ σmax) →
        (∀ j, |t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) z →
      LowRows Finset.univ s.character s.mask 1 t U q (C*U^(2*ε*d)) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ∧
      0 ≤ originalResponse s.character s.mask 1 t U (C*U^(2*ε*d)) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ∧
      originalResponse s.character s.mask 1 t U (C*U^(2*ε*d)) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j => U^(w j)) z ≤ q := by
  obtain ⟨C,hC,hslots⟩ := Record12518109SourceLow.actual_low_slots q hq0 hq1 M H hH
    W A B hA hWs hW Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with U hU
  refine ⟨hU.1,?_⟩
  intro s hs hQM hQη a i ha ha' θ w σ v t hw hwr hσ hσ' hfreq hheight z hz hlow
  have hslt (j : Slot) := hU.2 s hs hQM hQη a i ha ha' (w j) (σ j) t (v j)
    (hw j) (hwr j) (hσ j) (hσ' j) (hfreq j) hheight z hz hlow (θ j)
  have hactual : ∀ j, ‖normalizedSlot s.character s.mask 1 z
      (originalPools M H B U w j) (originalCoefficients M H hH η₀ θ W U w σ v j)
      t (U^(w j))‖^2 ≤ (C*U^(2*ε*d))*U^(q*w j) := hslt
  exact ⟨by simpa [LowRows] using hactual,
    originalResponse_bounded s.character s.mask 1 t U (C*U^(2*ε*d)) q w
      (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
      (fun j => U^(w j)) z hU.1 (mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _)) hw hq0 hactual⟩

end
end QRH.Cycle092.LowActual
