/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine buffered original-ordinary upper on arbitrary regular source states. -/
import Candidate.C092.transport.TerminalActualInverseApplySmall
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
namespace QRH.Cycle092.TerminalActualInverseApply
open HeckeInverseAmplification
open QRH.Cycle092.MediumReplace.Source QRH.Cycle092.OrdinaryColumn
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyShort_5b02addc6f7dec10_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_length_short_upper
    (bΦ Mcap Bmask margin R dmin dmax τ ε e κ heightCost : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε)
    (Bshort : ℝ) (hBshort : 0 ≤ Bshort)
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
      ∀ (W : ℝ → ℂ) (A B y Y σ freq : ℝ),0 < A →
        Function.support W ⊆ Icc A B → ContDiff ℝ ∞ W → 0 ≤ y → y/d ≤ R →
        0 < Y → Y ≤ Z^y →
        Function.support (twistProfile W σ freq) ⊆ Iic (9/4:ℝ) →
        (∀ x, ‖twistProfile W σ freq x‖ ≤ Bshort) →
        |freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (∀ x ∈ Icc (1-a-6*e-σ) (2-σ),∀ t : ℝ,
          (1+|t|)^2*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
        (∀ x ∈ Icc (1-a-6*e-σ) (2-σ),∀ t : ℝ,
          (1+|t|)^(order+2)*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
        ‖original s.character s.mask 1 z (twistProfile W σ freq) 0 Y‖^2 ≤
          C*Z^((2*a-1)*y+d*ε) := by
  obtain ⟨order,C,hC,hupper⟩ := regular_core_short_upper M H hH bΦ Mcap Bmask margin R dmin dmax
    τ ε e κ heightCost hbΦ hmargin hR hdmin hdmax hτ hheight hε he he' hκ hκ' hcost hbudget profileBound hprofile
  let C' := C+(288*Bshort)^2+1
  refine ⟨order,C',by dsimp [C']; positivity,?_⟩
  intro η₀ I
  filter_upwards [hupper η₀ I] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd hd' hds s hs hQM hQη z hz hΦ
  dsimp only
  intro a i ha ha' hi hnext W A B y Y σ freq hA hW hsm hy hyr hY hYcap hsupp hsup hfreq hm₂ hmn
  have hdp : 0 < d := hdmin.trans_le hd
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hU : 1 < Z^d := Real.one_lt_rpow hZ.1 hdp
  have hν : 0 ≤ 2*a-1 := by linarith
  have hexp : 0 ≤ (2*a-1)*y+d*ε := by positivity
  have hpow : 1 ≤ Z^((2*a-1)*y+d*ε) := Real.one_le_rpow hZ.1.le hexp
  by_cases hY1 : 1 ≤ Y
  · let r := Real.logb (Z^d) Y
    have hr0 : 0 ≤ r := Real.logb_nonneg hU hY1
    have hrcap : r ≤ y/d := (Real.logb_le_iff_le_rpow hU hY).mpr (by
      simpa only [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hdp.ne'] using hYcap)
    have hh := hZ.2 d hd hd' hds s hs hQM hQη z hz hΦ a i ha ha' hi hnext
      W A B r σ freq hA hW hsm hr0 (hrcap.trans hyr) hfreq hm₂ hmn
    have hlen : (Z^d)^r=Y := Real.rpow_logb (by positivity) hU.ne' hY
    rw [hlen,natural_plain_eq_original s _ W Y σ freq hY,←Real.rpow_mul hZp.le] at hh
    calc
      _ ≤ C*Z^(d*((2*a-1)*r+ε)) := hh
      _ ≤ C*Z^((2*a-1)*y+d*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by
          have h := mul_le_mul_of_nonneg_left hrcap (mul_nonneg hdp.le hν)
          field_simp at h
          nlinarith)) hC.le
      _ ≤ C'*Z^((2*a-1)*y+d*ε) := mul_le_mul_of_nonneg_right
        (by dsimp [C']; nlinarith [sq_nonneg (288*Bshort)]) (by positivity)
  · have hsml := short_original_subunit s.character s.mask 1 z (twistProfile W σ freq)
      0 Y Bshort hY (le_of_not_ge hY1) hBshort hsupp hsup
    have hsquare : ‖original s.character s.mask 1 z (twistProfile W σ freq) 0 Y‖^2 ≤ (288*Bshort)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsml 2
    calc
      _ ≤ (288*Bshort)^2 := hsquare
      _ ≤ C' := by dsimp [C']; linarith
      _ ≤ C'*Z^((2*a-1)*y+d*ε) := le_mul_of_one_le_right (by dsimp [C']; positivity) hpow

end QRH.Cycle092.TerminalActualInverseApply
#print axioms QRH.Cycle092.TerminalActualInverseApply.actual_length_short_upper
