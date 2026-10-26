import Candidate.Cycle63.Moment.LowBranch.Gate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeHeight
import Candidate.Cycle63.Moment.BufferedRetainedRows
import Candidate.Cycle63.Moment.LowBranch.FinalDictionary

/- Original module: Candidate.Cycle63.Moment.HighSlots. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

#print axioms actual_all_scale_high_slot
#print axioms actual_high_slots
end
end OAI.SevenEighths.Cycle63Moment
end

/- Original module: Candidate.Cycle63.Moment.HighSlotProduct. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The finite live slots all use the same buffered whole-family bin. The
buffer loss is proportional to the live slot count; the zero rate is charged
only to their total actual width. -/
theorem actual_high_slot_product
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
      ∀ {ι : Type*} [Fintype ι] (w σ v : ι → ℝ) (t : ℝ)
        (θ : ι → RayQuotient.Characters M H),
      (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
      (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
      (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z →
      (∏ k, ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w k)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
          annularWeight W (Z^(w k)) (σ k) (v k) I) t (Z^(w k))‖^2) ≤
        C^(Fintype.card ι)*Z^((2*a-1)*(∑ k, w k)+2*ε*d*(Fintype.card ι)) := by
  obtain ⟨C,hC,hslots⟩ := actual_high_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' ι _ w σ v t θ hw hwr hσ hσ' hfreq hheight z hz hbin
  calc
    _ ≤ ∏ k, (C*Z^(2*ε*d))*Z^((2*a-1)*w k) :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun k _ =>
        hZ.2 s hs hQM hQη a i ha ha' (w k) (σ k) t (v k)
          (hw k) (hwr k) (hσ k) (hσ' k) (hfreq k) hheight z hz hbin (θ k))
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow,
        ←Real.rpow_sum_of_pos (zero_lt_one.trans hZ.1),←Finset.mul_sum,
        ←Real.rpow_mul_natCast (zero_lt_one.trans hZ.1).le,
        mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ.1)]
      congr 2
      ring

#print axioms actual_high_slot_product
end
end OAI.SevenEighths.Cycle63Moment
end

/- Original module: Candidate.Cycle63.Moment.HighRetainedRows. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual retained row is estimated at one whole-family bin. Plain
coefficients are supplied by the natural row itself, including its puncture. -/
theorem actual_high_retained_row
    (Wslot : ℝ → ℂ) (A₀ B₀ : ℝ) (hA₀ : 0 < A₀)
    (hWs : Function.support Wslot ⊆ Icc A₀ B₀) (hW : ContDiff ℝ ∞ Wslot)
    (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax
      bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hRp : 0 ≤ Rplain) (hdmax : 0 ≤ dmax)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hεp : 0 < εplain)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hvp : 0 ≤ vplain) (hvs : 0 ≤ vslot)
    (hslotBudget : 8*e*Rwidth+κ ≤ εslot)
    (hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hd : 0 < d)
    (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
    ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : NaturalState Z Bmask bΦ), s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
    ∀ z : O, ∀ hz : s.radial.keep z, ∀ F : NaturalRow s.character z,
    ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ) z →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (j : Dict),
    χ j = excluded F.character s.puncture →
    zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    (χ j).modulus.absNorm ≤ Z^d →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (t : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
    (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
    (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
    (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^vslot →
    |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
    (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^vplain →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ),
    (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
    (∀ k, 0 < A k) →
    (∀ k, Function.support (dilated (W k) (clipDilation (X k))) ⊆ Icc (A k) (B k)) →
    (∀ k, ContDiff ℝ ∞ (dilated (W k) (clipDilation (X k)))) →
    (∀ k, 0 ≤ r k) → (∀ k, r k ≤ Rplain) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^2*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
    ‖retainedPositiveRow s.character s.mask 1 z (W 0) (W 1)
      (fun k => primePool M H B₀ (Z^(w k)))
      (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
        annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
      (fun k => Z^(w k)) t (X 0) (X 1)‖^2 ≤
      Cp^2*Cs^(Fintype.card ι)*
        Z^((2*a-1)*(d*(r 0+r 1)+(∑ k, w k))+
          2*εplain*d+2*εslot*d*(Fintype.card ι)) := by
  obtain ⟨n,Cp,hCp,hplain⟩ := actual_buffered_retained_plain_factors
    Rplain dmax τ εplain e κ vplain hRp hdmax hτ hεp he he' hκ hκ' hvp
    hplainBudget profileBound hprofile
  obtain ⟨Cs,hCs,hslots⟩ := actual_high_slot_product M H hH Wslot A₀ B₀ hA₀ hWs hW
    Rwidth dmax τ εslot e κ vslot σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hεs he he' hκ hvs hslotBudget hbΦ hmargin hd hdsupply hdm
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop _)
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hslots η₀,hT] with Z hZ hZT
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' z hz F hbin Dict _ χ hχ j hj hzero hmod
    ι _ _ w σ v θ t hw hwr hσ hσ' hfreq hheight hfreqP hheightP W X r A B
    hX hscale hA hsupport hsmooth hr hrR hm₂ hmn
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hcoeff (I : Ideal O) :
      idealCoeff s.character I*CanonicalRowCompletion.idealRowHom (s.mask^6*(1*z)) I =
        if false then star (idealCoeff (χ j) I) else idealCoeff (χ j) I := by
    simp only [Bool.false_eq_true, ite_false, hj, one_mul]
    simpa only [NaturalState.mask] using (F.masked_ideal s.puncture s.puncture_ne_zero I).symm
  have hp := hplain Z d hZ.1.le hd.le hdm hZT χ hχ a i ha ha' hzero
    j s.character s.mask z false hcoeff
    (fun k => primePool M H B₀ (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
    (fun k => Z^(w k)) (fun _ => Real.rpow_pos_of_pos hZp _)
    W X r A B t hX hscale hA (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hsupport)
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hsmooth) hmod hr hrR hfreqP hheightP
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hm₂) (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hmn)
  have hslt := hZ.2 s hs hQM hQη a i ha ha' w σ v t θ
    hw hwr hσ hσ' hfreq hheight z hz hbin
  apply hp.trans
  apply (mul_le_mul_of_nonneg_left hslt
    (mul_nonneg (sq_nonneg Cp) (Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _))).trans_eq
  rw [←Real.rpow_mul hZp.le]
  calc
    _ = Cp^2*Cs^(Fintype.card ι)*
        (Z^(d*((2*a-1)*(r 0+r 1)+2*εplain))*
         Z^((2*a-1)*(∑ k, w k)+2*εslot*d*(Fintype.card ι))) := by ring
    _ = _ := by
      rw [←Real.rpow_add hZp]
      congr 2
      ring

#print axioms actual_high_retained_row
end
end OAI.SevenEighths.Cycle63Moment
end

/- Original module: Candidate.Cycle63.Moment.FinalRowDictionary. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEnergyState CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual residual allocation changes its two raw plain scales and
restricts the live slot index. It does not change the row mask or frequency. -/
theorem final_source_row_eq
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (src : Data ι) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t : ℝ) (z : O)
    (hchar : src.η = st.character) (hmask : src.m = st.mask)
    (hA : src.A = 1) (ht : src.t = t)
    (hpool : ∀ j, src.slots j = pool j)
    (hcoeff : ∀ j I, src.coefficient j I = coeff j I)
    (hP : ∀ j, src.P j = P j) :
    Cycle63.Physical.sourcePositiveRow src.toSource second L a z =
      retainedPositiveRow st.character st.mask 1 z src.W₁ src.W₂
        (fun j : liveIndices L a => pool j)
        (fun j : liveIndices L a => coeff j)
        (fun j : liveIndices L a => P j) t
        (Cycle63.Physical.postPlainScale L a
          (Cycle63.Physical.sourcePlainScales src.toSource second) 0)
        (Cycle63.Physical.postPlainScale L a
          (Cycle63.Physical.sourcePlainScales src.toSource second) 1) := by
  change retainedPositiveRow src.η src.m src.A z src.W₁ src.W₂
    (fun j : liveIndices L a => src.slots j)
    (fun j : liveIndices L a => src.coefficient j)
    (fun j : liveIndices L a => src.P j) src.t _ _ = _
  rw [hchar,hmask,hA,ht]
  simp_rw [hpool, funext (hcoeff _), hP]
  rfl

#print axioms final_source_row_eq
end
end OAI.SevenEighths.Cycle63Moment
end
