import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Gate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.BufferedSlot
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open LowBranch
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- One constant controls large buffered slots and every tiny slot. The latter
uses the literal finite prime pool, uniformly in both frequency parameters.
The buffer loss is explicit and can be divided by the finite slot count. -/
theorem actual_all_scale_high_slot
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax →
      2 ≤ Z^d → 2 < Z^τ →
      ∀ {Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
        (ν : Character) (hQM : s.fixedModulus ≤ M) (hQν : s.fixedModulus ≤ ν.modulus)
        (z : O) (hz : s.radial.keep z) (F : NaturalRow s.character z) (a : ℝ) (i : ℕ),
      51/100 ≤ a → a ≤ 1 →
      zeroMaximum (twistedFamily M H hH ((excluded F.character s.puncture).product ν.inverse))
        (whole_nonprincipal M H hH s ν hQM hQν z hz F)
        (3*(i+1 : ℕ)*Z^τ) < a+2*e →
      ∀ r σ t v : ℝ, 0 ≤ r → r ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
      (∀ θ : RayQuotient.Characters M H,
        ((twistedFamily M H hH ((excluded F.character s.puncture).product ν.inverse)
          θ).modulus.absNorm : ℝ) ≤ Z^d) →
      |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B ((Z^d)^r))
        (fun I => idealCoeff ν.inverse I*annularWeight W ((Z^d)^r) σ v I)
        t ((Z^d)^r)‖^2 ≤ C*Z^((2*a-1)*(d*r)+2*ε*d) := by
  obtain ⟨Cb,hCb,hbuffer⟩ := LocalMoment.natural_relative_slot_buffered_bound M H hH
    W A B hA hWs hW Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε
    he he' hκ hη hbudget
  let K := 2*(|Real.log A|+|Real.log B|)+1
  obtain ⟨Cs,hCs,hsmall⟩ := CenteredMomentPrimeHeight.ray_prime_bounded_scale M H W A B
    σmin σmax (Real.exp K) hA hWs hW.continuous (Real.one_le_exp (by dsimp [K]; positivity))
  refine ⟨Cb^2+Cs^2,by positivity,?_⟩
  intro Z d hZ hd hdm hbase hT Bmask bΦ s ν hQM hQν z hz F a i ha ha' hmax
    r σ t v hr hr' hσ hσ' hmod hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hP : 1 ≤ (Z^d)^r := Real.one_le_rpow (by linarith) hr
  have hPp : 0 < (Z^d)^r := zero_lt_one.trans_le hP
  have hpower : (Z^d)^((2*a-1)*r+2*ε) = Z^((2*a-1)*(d*r)+2*ε*d) := by
    rw [← Real.rpow_mul hZp.le]
    congr 1
    ring
  have hδ : 0 ≤ 2*a-1 := by linarith
  have htarget : 1 ≤ Z^((2*a-1)*(d*r)+2*ε*d) :=
    Real.one_le_rpow hZ (by positivity)
  by_cases hlarge : K ≤ Real.log ((Z^d)^r)
  · have hb := hbuffer Z d hZ hd hdm hbase hT s.character z F ν s.puncture
      s.puncture_ne_zero (whole_nonprincipal M H hH s ν hQM hQν z hz F)
      a i ha ha' hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
    change ‖normalizedSlot s.character s.mask 1 z _ _ _ _‖^2 ≤ _ at hb
    rw [hpower] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (show Cb^2 ≤ Cb^2+Cs^2 by nlinarith [sq_nonneg Cs])
      (Real.rpow_nonneg hZp.le _))
  · have hPD : (Z^d)^r ≤ Real.exp K := by
      have hb := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
      simpa only [Real.exp_log hPp] using hb
    have hb := hsmall ((excluded F.character s.puncture).product ν.inverse)
      ((Z^d)^r) σ (t+v) hP hPD hσ hσ'
    rw [relative_normalizedSlot_eq_ray M H s.character (excluded F.character s.puncture)
      ν.inverse s.mask 1 z
      (by simpa only [one_mul, NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)
      W B ((Z^d)^r) σ t v hPp, norm_mul,
      CenteredMomentTwist.norm_real_imaginary_power _ t hPp, one_mul]
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans
    exact (show Cs^2 ≤ Cb^2+Cs^2 by nlinarith [sq_nonneg Cb]).trans
      (le_mul_of_one_le_right (by positivity) htarget)

theorem actual_high_slots
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
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
      ∀ w σ t v : ℝ, 0 ≤ w → w/d ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z → ∀ θ : RayQuotient.Characters M H,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        (C*Z^(2*ε*d))*Z^((2*a-1)*w) := by
  obtain ⟨C,hC,hslot⟩ := actual_all_scale_high_slot M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε he he' hκ hη hbudget
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
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
