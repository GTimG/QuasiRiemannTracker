/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine buffered original-ordinary upper on arbitrary regular source states. -/
import Candidate.C092.transport.MediumReplaceSourceWitness
import Candidate.C092.transport.MediumReplaceNative
import Candidate.C092.transport.OrdinaryColumn
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeDyadic HeckeDetectorDyadicGeometry HeckeDetectorSupportedWitness
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_MediumReplaceSourceUpper_06c2ce884df6c7f8_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The original ordinary factor is none in the same whole detector union.
The actual profile and independent ordinary height are controlled by their
own Mellin envelopes; no polynomial norm or source energy is assumed. -/
theorem regular_core_short_upper
    (bΦ Mcap Bmask margin R dmin dmax τ ε e κ heightCost : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k,0 ≤ profileBound k) :
    ∃ order : ℕ,∃ C : ℝ,0 < C ∧ ∀ (η₀ : Character) (I : ℕ),
      ∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
      ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus),
      ∀ (z : O) (hz : s.radial.keep z),
        s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      let F := naturalRow s.character z (s.row_ne_zero z hz)
      ∀ (a : ℝ) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I →
        zeroMaximum (family M H hH s η₀ F) (family_nonprincipal M H hH s η₀ hQM hQη hz F)
          (3*(i+1 : ℕ)*Z^τ) < a+2*e →
      ∀ (W : ℝ → ℂ) (A B r σ freq : ℝ),0 < A →
        Function.support W ⊆ Icc A B → ContDiff ℝ ∞ W → 0 ≤ r → r ≤ R →
        |freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (∀ x ∈ Icc (1-a-6*e-σ) (2-σ),∀ t : ℝ,
          (1+|t|)^2*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
        (∀ x ∈ Icc (1-a-6*e-σ) (2-σ),∀ t : ℝ,
          (1+|t|)^(order+2)*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
        ‖polynomial (excluded F.character s.puncture) false W ((Z^d)^r) σ freq‖^2 ≤
          C*(Z^d)^((2*a-1)*r+ε) := by
  obtain ⟨order,C,hC,hupper⟩ := source_dyadic_bounds R dmax τ ε e κ heightCost
    hR ((hdmin.trans_le hdmax).le) hτ hε he he' hκ hκ' hcost hbudget profileBound hprofile
  refine ⟨order,C,hC,?_⟩
  intro η₀ I
  filter_upwards [family_conductor_eventually M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,
    uniform_height_budget dmin τ heightCost I hτ.le hcost hheight,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))] with Z hcond hh hT
  refine ⟨hcond.1,?_⟩
  intro d hd hd' hds s hs hQM hQη z hz hΦ
  dsimp only
  intro a i ha ha' hi hnext W A B r σ freq hA hW hsm hr hr' hfreq hm₂ hmn
  let F := naturalRow s.character z (s.row_ne_zero z hz)
  have hχ := family_nonprincipal M H hH s η₀ hQM hQη hz F
  have hmod := (hcond.2 s hs z F hΦ none).trans
    (Real.rpow_le_rpow_of_exponent_le hcond.1.le hds)
  exact (hupper Z d hcond.1.le (hdmin.le.trans hd) hd' hT (family M H hH s η₀ F) hχ
    a i ha ha' hnext none false W A B hA hW hsm r σ freq hmod hr hr' hfreq
    (hh d hd i hi) hm₂ hmn).1

/-- This source-side shorter factor is the exact original normalized ordinary
row at s.mask and its actual character. The height is inside its normalized
profile, as in the original source dictionary. -/
theorem natural_plain_eq_original {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    {z : O} (F : NaturalRow s.character z) (W : ℝ → ℂ) (X σ freq : ℝ) (hX : 0 < X) :
    polynomial (excluded F.character s.puncture) false W X σ freq =
      QRH.Cycle092.OrdinaryColumn.original s.character s.mask 1 z (HeckeInverseAmplification.twistProfile W σ freq) 0 X := by
  exact CenteredMomentDetectorDictionary.plain_polynomial_eq_row s.character
    (excluded F.character s.puncture) s.mask 1 z
    (by simpa only [one_mul,NaturalState.mask] using F.masked_element s.puncture s.puncture_ne_zero)
    W X σ freq hX

end QRH.Cycle092.MediumReplace.Source
#print axioms QRH.Cycle092.MediumReplace.Source.regular_core_short_upper
#print axioms QRH.Cycle092.MediumReplace.Source.natural_plain_eq_original
