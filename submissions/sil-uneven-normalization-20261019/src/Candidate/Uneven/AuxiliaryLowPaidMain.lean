import Candidate.Uneven.AuxiliarySchedule
import Candidate.Cycle63.Moment.LowBranch.Families
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeHeight
import Candidate.Cycle63.Moment.LowBranch.Gate
import Candidate.Target836.SourceProvider.RestrictedLow
import Candidate.Uneven.AuxiliaryIncumbent
import Candidate.Cycle63.Physical.TerminalLedger
import Candidate.Cycle63.Moment.LowBranch.Payment

/- Original module: Candidate.Uneven.AuxiliaryLowSlot. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch
open Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- One constant controls large buffered slots and every tiny slot. The latter
uses the literal finite prime pool, uniformly in both frequency parameters.
The buffer loss is explicit and can be divided by the finite slot count. -/
theorem all_scale_buffered_slot
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
      51/100 ≤ a → a ≤ (1+Sil.Uneven.AuxiliarySource.q)/2 →
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
        t ((Z^d)^r)‖^2 ≤ C*Z^(Sil.Uneven.AuxiliarySource.q*(d*r)+2*ε*d) := by
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
  have hexp : (2*a-1)*(d*r)+2*ε*d ≤ Sil.Uneven.AuxiliarySource.q*(d*r)+2*ε*d := by
    have hh := mul_le_mul_of_nonneg_right ((show 2*a-1≤Sil.Uneven.AuxiliarySource.q by linarith [ha'])) (mul_nonneg hd hr)
    linarith
  have htarget : 1 ≤ Z^(Sil.Uneven.AuxiliarySource.q*(d*r)+2*ε*d) :=
    Real.one_le_rpow hZ (by
      have hq : 0 ≤ Sil.Uneven.AuxiliarySource.q := by norm_num [Sil.Uneven.AuxiliarySource.q]
      positivity)
  by_cases hlarge : K ≤ Real.log ((Z^d)^r)
  · have hb := hbuffer Z d hZ hd hdm hbase hT s.character z F ν s.puncture
      s.puncture_ne_zero (whole_nonprincipal M H hH s ν hQM hQν z hz F)
      a i ha (by norm_num [Sil.Uneven.AuxiliarySource.q] at ha'; linarith) hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
    change ‖normalizedSlot s.character s.mask 1 z _ _ _ _‖^2 ≤ _ at hb
    rw [hpower] at hb
    apply hb.trans
    apply mul_le_mul
    · nlinarith [sq_nonneg Cs]
    · exact Real.rpow_le_rpow_of_exponent_le hZ hexp
    · exact Real.rpow_nonneg hZp.le _
    · positivity
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

end
end OAI.SevenEighths.AuxiliaryLow
end

/- Original module: Candidate.Uneven.AuxiliaryLowGate. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

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
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ (1+Sil.Uneven.AuxiliarySource.q)/2 →
      ∀ w σ t v : ℝ, 0 ≤ w → w/d ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        |t+v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
        (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z → ∀ θ : RayQuotient.Characters M H,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        (C*Z^(2*ε*d))*Z^(Sil.Uneven.AuxiliarySource.q*w) := by
  obtain ⟨C,hC,hslot⟩ := all_scale_buffered_slot M H hH W A B hA hWs hW
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
end OAI.SevenEighths.AuxiliaryLow
end

/- Original module: Candidate.Uneven.AuxiliaryLowMain. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open OAI OAI.SevenEighths
open Target874836.SourceProvider (restricted_low_main)
open OAI.SevenEighths.Cycle63Moment.LowBranch
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine original incumbent moments plus the proved actual low slots.
All fixed constants precede the live state, selected slots and both heights.
The retained low predicate and the exhaustion alternative remain explicit. -/
theorem actual_low_main
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ incumbentKappa)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      ∀ hQM : Q ≤ M, internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+Sil.Uneven.AuxiliarySource.q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      let F := max (length Z X₁+length Z X₂+(6*incumbentKappa)*(∑ j ∈ J, w j)-s.width) 0
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(6*incumbentKappa)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        (C*Z^(2*ε*d))^J.card *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(s.width+εold+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*F+Sil.Uneven.AuxiliarySource.q*mesh) := by
  obtain ⟨degree,S,hinc⟩ := accepted_incumbent (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta hκbeta
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hslots⟩ := actual_low_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η lo hi bΦ Mcap Bmask margin d hRw hdmax hτ hε he he' hκ hη
    hbudget hbΦ.le hmargin hd hdsupply hdm
  refine ⟨max 1 C,C₀,C₁,le_max_left _ _,hC₀,hC₁,?_⟩
  filter_upwards [hold,hslots η₀] with Z hZ hslot
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv
    ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  let hQM' : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
  let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
  let low := ActualLow M H hH s η₀ hQM' hQη a e (3*(i+1 : ℕ)*Z^τ)
  let pay : ℝ := max 1 C*Z^(2*ε*d)
  have hpay : 1 ≤ pay := by
    have hpow : 1 ≤ Z^(2*ε*d) := Real.one_le_rpow hZ.1.le (by positivity)
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow
  have hBpay : ∀ j ∈ J, 0 ≤ pay := fun _ _ => zero_le_one.trans hpay
  have hpayslot : ∀ z, s.radial.keep z → low z → ∀ j ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w j)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (v j) I) t (Z^(w j))‖^2 ≤
          pay*Z^(Sil.Uneven.AuxiliarySource.q*w j) := by
    intro z hz hl j hj
    have hf : |t+v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
      have hh := abs_add_le t (v j)
      linarith [hv j]
    exact (hslot.2 s hs hQM' hQη a i ha ha' (w j) (σ j) t (v j) (hw j)
      (hwr j hj) (hσlo j) (hσhi j) hf hhigh z hz hl (θ j)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 C)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
  obtain ⟨R,hR,hcap,hbound⟩ := restricted_low_main M H hH W B ap bp bΦ Bmask L
    (Cycle25.Energy.commonMesh Mcap Bmask L εold) lo hi Mcap εold Z mesh Sil.Uneven.AuxiliarySource.q incumbentKappa (by norm_num [incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]) (by norm_num [Sil.Uneven.AuxiliarySource.q]) η₀ Q
    degree S C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2 J θ w σ v t height (fun _ => pay)
    hw hwL hmesh hwm hσlo hσhi hheight hv hBpay s hQ hs low p X₁ X₂
    hX₁ hX₂ hc₁ hc₂ hpayslot
  refine ⟨R,hR,hcap,hbound.trans ?_⟩
  have hprod : (∏ j ∈ R, pay) ≤ pay^J.card := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hpay (Finset.card_le_card hR)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hmoment : 0 ≤ (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hmoment)
    (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)

end
end OAI.SevenEighths.AuxiliaryLow
end

/- Original module: Candidate.Uneven.AuxiliaryLowPayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch

/-- Joint width and capacity deletion retain the exact new source reserve. -/
theorem low_paid_excess_bound {b M nominal width delta total padding : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤Sil.Uneven.AuxiliarySource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤delta) (hdelta : 0≤delta) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.AuxiliarySource.gap b+6*(M*Sil.Uneven.AuxiliarySource.amp b)+padding) :
    width+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0≤
      nominal+delta+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding := by
  have hprice : 0≤Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa) := by norm_num [Sil.Uneven.AuxiliarySource.q,incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]
  have hpriceHi : Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa)≤1 := by norm_num [Sil.Uneven.AuxiliarySource.q,incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]
  have heq := Sil.Uneven.AuxiliarySource.low_identity b
  change Sil.Uneven.AuxiliarySource.amp b-Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa)*(Sil.Uneven.AuxiliarySource.gap b+6*Sil.Uneven.AuxiliarySource.amp b)=Sil.Uneven.AuxiliarySource.lowReserve at heq
  have hmul := congrArg (fun x : ℝ=>M*x) heq
  have hguard := Sil.Uneven.AuxiliarySource.source_guards hb
  have ha0 : 0≤Sil.Uneven.AuxiliarySource.amp b := by
    have hamin := hguard.2.1
    have hamp := hguard.2.2.1
    linarith
  have ha : Sil.Uneven.AuxiliarySource.lowReserve≤Sil.Uneven.AuxiliarySource.amp b := by
    have hp := mul_nonneg hprice (show 0≤Sil.Uneven.AuxiliarySource.gap b+6*Sil.Uneven.AuxiliarySource.amp b by linarith [hguard.1])
    linarith
  by_cases hm : total≤width
  · rw [max_eq_right (by linarith : total-width≤0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0≤total-width)]
    nlinarith [mul_le_mul_of_nonneg_left htotal hprice,
      mul_nonneg (sub_nonneg.mpr hpriceHi) (sub_nonneg.mpr hwidth)]

theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤Sil.Uneven.AuxiliarySource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤δ) (hdelta : 0≤δ) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.AuxiliarySource.gap b+6*(M*Sil.Uneven.AuxiliarySource.amp b)+padding) :
    width+εold+buffer+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+Sil.Uneven.AuxiliarySource.q*mesh≤
      nominal+δ+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+εold+buffer+
        (Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding+Sil.Uneven.AuxiliarySource.q*mesh := by
  linarith [low_paid_excess_bound hb hM hwidth hdelta hpad htotal]

end
end OAI.SevenEighths.AuxiliaryLow
end

/- Original module: Candidate.Uneven.AuxiliaryLowPaidMain. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Algebraic payment of the actual greedy-deletion energy bound. The
constant uses the fixed ambient label count, before the live selected set. -/
theorem paid_energy_bound {E A C Z ε d b M nominal width δ total padding εold mesh : ℝ}
    {n N : ℕ} (hZ : 1 < Z) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hε : 0 < ε) (hd : 0 < d) (hn : n ≤ N)
    (hb : Sil.Uneven.AuxiliarySource.widthLo ≤ b ∧ b ≤ Sil.Uneven.AuxiliarySource.widthHi) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Sil.Uneven.AuxiliarySource.gap b+6*(M*Sil.Uneven.AuxiliarySource.amp b)+padding)
    (hE : E ≤ (C*Z^(2*ε*d))^n*A*
      Z^(width+εold+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+
        Sil.Uneven.AuxiliarySource.q*mesh)) :
    E ≤ C^N*A*Z^(nominal+δ+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+εold+
      2*ε*d*(N:ℝ)+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding+Sil.Uneven.AuxiliarySource.q*mesh) := by
  have hp := paid_low_exponent_shifted (buffer := 2*ε*d*(N:ℝ)) (εold := εold) (mesh := mesh) hb hM hwidth hδ hpad htotal
  have hn' : (n:ℝ) ≤ N := by exact_mod_cast hn
  have hbuf := mul_le_mul_of_nonneg_left hn' (show 0 ≤ 2*ε*d by positivity)
  have hexp : width+εold+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+
      Sil.Uneven.AuxiliarySource.q*mesh+2*ε*d*(n:ℝ) ≤
    nominal+δ+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+εold+
      2*ε*d*(N:ℝ)+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding+Sil.Uneven.AuxiliarySource.q*mesh := by
    linarith
  rw [buffer_power_identity C Z ε d n (zero_lt_one.trans hZ)] at hE
  have heq : C^n*Z^(2*ε*d*(n:ℝ))*A*
      Z^(width+εold+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+Sil.Uneven.AuxiliarySource.q*mesh) =
    C^n*A*Z^(width+εold+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+
      Sil.Uneven.AuxiliarySource.q*mesh+2*ε*d*(n:ℝ)) := by
    conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ)]
    ring
  rw [heq] at hE
  exact hE.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hn) hA)
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity))

/-- Actual local low energy with the genuine incumbent and slot estimates,
paid at the second-transform nominal width. No low-slot moment premise. -/
theorem actual_paid_low_main
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ incumbentKappa)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      ∀ hQM : Q ≤ M, internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+Sil.Uneven.AuxiliarySource.q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ (b Mrow nominal δ padding : ℝ),
      (Sil.Uneven.AuxiliarySource.widthLo ≤ b ∧ b ≤ Sil.Uneven.AuxiliarySource.widthHi) → 0 ≤ Mrow →
      s.width-nominal ≤ δ → 0 ≤ δ → 0 ≤ padding →
      length Z X₁+length Z X₂+(6*incumbentKappa)*(∑ j ∈ J, w j)-nominal ≤
        Mrow*Sil.Uneven.AuxiliarySource.gap b+6*(Mrow*Sil.Uneven.AuxiliarySource.amp b)+padding →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(6*incumbentKappa)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        C^(Fintype.card α) *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+δ+Mrow*Sil.Uneven.AuxiliarySource.amp b-Mrow*Sil.Uneven.AuxiliarySource.lowReserve+εold+
            2*ε*d*(Fintype.card α:ℝ)+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding+
            Sil.Uneven.AuxiliarySource.q*mesh) := by
  obtain ⟨degree,S,hmain⟩ := actual_low_main (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta hκbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin
    hd hdsupply hdm
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,hC,hC₀,hC₁,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv
    ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ b Mrow nominal δ padding
    hb hMrow hwidth hδ hpad htotal
  dsimp only
  obtain ⟨R,hR,hcap,henergy⟩ := hZ.2 J θ w σ v t height mesh a i hw hwL hwr hmesh
    hwm hσlo hσhi hheight hv ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  refine ⟨R,hR,hcap,?_⟩
  exact paid_energy_bound hZ.1 hC (by
    have hdiag := diagonalControl_nonneg s.radial.profile
    positivity) hε hd (by simpa using Finset.card_le_univ J)
    hb hMrow hwidth hδ hpad htotal henergy

end
end OAI.SevenEighths.AuxiliaryLow
end
