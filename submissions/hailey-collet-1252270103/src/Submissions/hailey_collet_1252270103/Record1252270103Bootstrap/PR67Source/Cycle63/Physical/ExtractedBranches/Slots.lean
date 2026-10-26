import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Conductor
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Prior
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Families
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.FirstLevel
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Physical.ExtractedBranches
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open Cycle63Moment.LowBranch
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Global bootstrap pricing for the literal punctured natural relative slot,
including tiny scales and independent external and slot frequencies. -/
theorem actual_global_slots
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (bΦ Mcap Bmask Lslot margin loss lo hi : ℝ)
    (hbΦ : 0 ≤ bΦ) (hMcap : 0 ≤ Mcap) (hBmask : 0 ≤ Bmask)
    (hLslot : 0 ≤ Lslot) (hmargin : 0 < margin) (hloss : 0 < loss)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (_hQM : s.fixedModulus ≤ M) (_hQη : s.fixedModulus ≤ η₀.modulus),
      ∀ w σ t v : ℝ, 0 ≤ w → w ≤ Lslot → lo ≤ σ → σ ≤ hi →
      ∀ z : O, s.radial.keep z →
        s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ θ : RayQuotient.Characters M H,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        C*(1+|t|+|v|)^degree*Z^loss*Z^(Cycle63.Optimization.slotPrice*w) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩ := CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W A B hA hWs hW (Mcap+Bmask+margin) Lslot loss lo hi Cycle63.Optimization.slotPrice
    (by positivity) hLslot hloss hbeta Cycle63.Assembly.slotPrice_admissible
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,
    eventually_ge_atTop Z₀] with Z hcond hZ₀'
  refine ⟨hcond.1,?_⟩
  intro s hs hQM hQη w σ t v hw hwL hσ hσ' z hz hΦ θ
  let F := naturalRow s.character z (s.row_ne_zero z hz)
  let χ := (excluded F.character s.puncture).product
    (relativeCharacter M H hH η₀ θ).inverse.inverse
  let : Finite (O ⧸ (twistedFamily M H hH χ 1).modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient (twistedFamily M H hH χ 1).modulus_ne_bot
  have hc : (χ.modulus.absNorm : ℝ) ≤ Z^(Mcap+Bmask+margin) := by
    have hn : χ.modulus.absNorm ≤ (twistedFamily M H hH χ 1).modulus.absNorm :=
      FiniteConductor.absNorm_le_of_le inf_le_left
    exact (show (χ.modulus.absNorm : ℝ) ≤ _ by exact_mod_cast hn).trans
      (hcond.2 s hs z F hΦ θ 1)
  have hnp := whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ θ).inverse
    hQM (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz F
  have hZp : 0 < Z := zero_lt_one.trans hcond.1
  have hP : 1 ≤ Z^w := Real.one_le_rpow hcond.1.le hw
  have hb := hbound Z (Z^w) hZ₀' hP
    (Real.rpow_le_rpow_of_exponent_le hcond.1.le hwL) χ hc hnp σ (t+v) hσ hσ'
  have hcoeff (I : Ideal O) :
      idealCoeff (relativeCharacter M H hH η₀ θ).inverse.inverse I =
        idealCoeff (relativeCharacter M H hH η₀ θ) I := by
    simp only [idealCoeff_inverse_conj,starRingEnd_self_apply]
  have htransport := relative_normalizedSlot_eq_ray M H s.character
    (excluded F.character s.puncture)
    (relativeCharacter M H hH η₀ θ).inverse.inverse s.mask 1 z
    (by simpa only [one_mul,NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)
    W B (Z^w) σ t v (zero_lt_one.trans_le hP)
  simp_rw [hcoeff] at htransport
  rw [htransport, norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power _ t (zero_lt_one.trans_le hP), one_mul]
  have hp : (Z^w)^Cycle63.Optimization.slotPrice = Z^(Cycle63.Optimization.slotPrice*w) := by
    rw [← Real.rpow_mul hZp.le]
    congr 1
    ring
  rw [hp] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

end
end OAI.SevenEighths.Cycle63Physical.ExtractedBranches

end Record1252270103Bootstrap.PR67
