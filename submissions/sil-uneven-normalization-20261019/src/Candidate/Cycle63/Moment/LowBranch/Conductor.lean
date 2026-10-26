import Candidate.Cycle63.Moment.LowBranch.Families
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval

/- Original module: Candidate.Cycle63.Moment.LowBranch.Slot. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators ContDiff
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
      51/100 ≤ a → a ≤ 21/25 →
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
        t ((Z^d)^r)‖^2 ≤ C*Z^(Cycle63.Arithmetic.q0*(d*r)+2*ε*d) := by
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
  have hexp : (2*a-1)*(d*r)+2*ε*d ≤ Cycle63.Arithmetic.q0*(d*r)+2*ε*d := by
    have hh := mul_le_mul_of_nonneg_right (low_rate ha') (mul_nonneg hd hr)
    linarith
  have htarget : 1 ≤ Z^(Cycle63.Arithmetic.q0*(d*r)+2*ε*d) :=
    Real.one_le_rpow hZ (by
      have hq : 0 ≤ Cycle63.Arithmetic.q0 := by norm_num [Cycle63.Arithmetic.q0]
      positivity)
  by_cases hlarge : K ≤ Real.log ((Z^d)^r)
  · have hb := hbuffer Z d hZ hd hdm hbase hT s.character z F ν s.puncture
      s.puncture_ne_zero (whole_nonprincipal M H hH s ν hQM hQν z hz F)
      a i ha (by linarith) hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
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

#print axioms all_scale_buffered_slot
end
end OAI.SevenEighths.Cycle63Moment.LowBranch
end

/- Original module: Candidate.Cycle63.Moment.LowBranch.Conductor. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators
open ConcreteTraceCRT CenteredMomentAllocatedNaturalSource
open Filter HeckeFamily HeckePrimeRay ConcretePrimeRowBridge CompletedGauss
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual common puncture contributes its radical, with no conductor
renaming or removal of Euler factors. -/
theorem excluded_conductor (χ : Character) (R : Ideal O) (hR : R ≠ 0) :
    (excluded χ R).modulus.absNorm = χ.modulus.absNorm*R.radical.absNorm := by
  change (χ.modulus*(∏ P ∈ primeSupport R, P)).absNorm = _
  rw [primeSupport_product_radical R hR, map_mul]

/-- A common threshold precedes every natural state, live width and ray label.
Only the actual radial support controls the moving row conductor. -/
theorem eventual_relative_conductor (η₀ : Character) (bΦ Mcap Bmask margin : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ s : NaturalState Z Bmask bΦ,
      s.width ≤ Mcap → ∀ z : O, ∀ F : NaturalRow s.character z,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ θ₀ θ : RayQuotient.Characters M H,
      ((twistedFamily M H hH ((excluded F.character s.puncture).product
        (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ).modulus.absNorm : ℝ)
        ≤ Z^(Mcap+Bmask+margin) := by
  let C : ℝ := (fixedConductorFactor : ℝ)*bΦ*
    ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ))*(M.absNorm : ℝ)
  have hfixed : ∀ᶠ Z : ℝ in atTop, C ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop C)
  filter_upwards [hfixed, eventually_gt_atTop (1:ℝ)] with Z hC hZ
  refine ⟨hZ,?_⟩
  intro s hs z F hΦ θ₀ θ
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*Z^s.rowWidth := by
    rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have hF := F.modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZp hbΦ
    s.modulus_bound hn
  have hwidth : Z^(s.characterWidth+s.rowWidth) ≤ Z^Mcap :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by simpa [NaturalState.width,add_comm] using hs)
  have hFn : (F.character.modulus.absNorm : ℝ) ≤
      (fixedConductorFactor : ℝ)*bΦ*Z^Mcap :=
    hF.trans (mul_le_mul_of_nonneg_left hwidth (by positivity))
  have hν : (((relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ)
      ≤ (M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ) := by
    exact_mod_cast relativeCharacter_modulus M H hH η₀ θ₀
  have hp := HeckePrimeScale.product_modulus_bound (excluded F.character s.puncture)
    (relativeCharacter M H hH η₀ θ₀).inverse.inverse
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH
    ((excluded F.character s.puncture).product (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ
  have he : ((excluded F.character s.puncture).modulus.absNorm : ℝ) ≤
      ((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask := by
    rw [excluded_conductor _ _ s.puncture_ne_zero, Nat.cast_mul]
    exact mul_le_mul hFn s.radical_bound (Nat.cast_nonneg _) (by positivity)
  have hp' : (((excluded F.character s.puncture).product
      (relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ) ≤
      (((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask)*
        ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ)) := by
    exact (show _ ≤ _ by exact_mod_cast hp).trans
      (mul_le_mul he hν (Nat.cast_nonneg _) (by positivity))
  have ht' : ((twistedFamily M H hH ((excluded F.character s.puncture).product
      (relativeCharacter M H hH η₀ θ₀).inverse.inverse) θ).modulus.absNorm : ℝ) ≤
      (((excluded F.character s.puncture).product (relativeCharacter M H hH η₀ θ₀).inverse.inverse).modulus.absNorm : ℝ)*(M.absNorm : ℝ) := by exact_mod_cast ht
  apply ht'.trans
  calc
    _ ≤ ((((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask)*
        ((M.absNorm : ℝ)*(η₀.modulus.absNorm : ℝ)))*(M.absNorm : ℝ) :=
      mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg _)
    _ = C*Z^(Mcap+Bmask) := by dsimp [C]; rw [Real.rpow_add hZp]; ring
    _ ≤ Z^margin*Z^(Mcap+Bmask) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(Mcap+Bmask+margin) := by
      rw [← Real.rpow_add hZp]
      congr 1
      ring

#print axioms eventual_relative_conductor
end
end OAI.SevenEighths.Cycle63Moment.LowBranch
end
