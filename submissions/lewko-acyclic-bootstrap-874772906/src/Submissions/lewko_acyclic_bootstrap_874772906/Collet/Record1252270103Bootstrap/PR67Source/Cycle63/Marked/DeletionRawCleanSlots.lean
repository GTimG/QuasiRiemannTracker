import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionRawSlots
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.WholeFamilyZeros
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentSecondHeightFamily HeckePrimeAnnular Cycle63MarkedPlain
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- The arbitrary fixed positive deletion tolerance used to compare the
raw masked row and the independently masked common detector core. -/
theorem eventually_annular_deletion_tolerance (W : ℝ→ℂ) (a b lo hi Bmask wmin err : ℝ)
    (ha : 0< a) (hWs : Function.support W⊆Icc a b) (hW : Continuous W)
    (hBmask : 0≤ Bmask) (hwmin : 0< wmin) (herr : 0< err) :
    ∀ᶠU : ℝ in atTop,1< U ∧
      ∀(χ ν : Character)(R : Ideal O),R≠0 → (R.absNorm : ℝ)≤ U^Bmask →
      ∀pool : Finset (Ideal O),(∀I∈pool,Prime I) →
      ∀w σ v t : ℝ,wmin≤ w → lo≤σ → σ≤ hi →
      let β:=heightCoefficient (fun I=>idealCoeff ν I*annularWeight W (U^w) σ v I) t
      ‖naturalSlot (excluded χ R) pool β (U^w)-naturalSlot χ pool β (U^w)‖≤ err := by
  obtain ⟨C,hC,hdel⟩ := annular_slot_deletion W a b lo hi Bmask (wmin/4)
    ha hWs hW hBmask (by positivity)
  have hlarge := (tendsto_rpow_atTop (show 0< wmin/4 by positivity)).eventually
    (eventually_ge_atTop (C/err))
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro χ ν R hR hRN pool hp w σ v t hw hσlo hσhi β
  apply (hdel U hU.le χ ν R hR hRN pool hp w σ v t hσlo hσhi).trans
  have hUp : 0< U := zero_lt_one.trans hU
  calc
    C*U^(-w/2+wmin/4)≤ C*U^(-(wmin/4)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)) hC.le
    _ ≤ err := by
      rw [Real.rpow_neg hUp.le,←div_eq_mul_inv]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mpr
      exact (div_le_iff₀ herr).mp hlarge |>.trans_eq (mul_comm _ _)

/-- The actual raw slot and the clean common core slot differ by at most
one half. Both the moving geometric holes and the fixed anchor mask are
removed explicitly; no coprimality condition between those masks is used. -/
theorem eventually_raw_clean_slot_comparison (A : Ideal O) (hA : A≠0)
    (W : ℝ→ℂ) (a b lo hi Bmask Broot wmin : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : Continuous W)
    (hBmask : 0≤ Bmask) (hBroot : 0≤ Broot) (hwmin : 0< wmin) :
    ∀ᶠU : ℝ in atTop,1< U ∧
      ∀(η ν χ : Character)(u : FreeRow)(B : NZIdeal)(R : Ideal O),R≠0 →
      (R.absNorm : ℝ)≤ U^Bmask → (B.val.absNorm : ℝ)≤ U^Broot →
      (∀I,idealCoeff χ I=idealCoeff
        (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
          (sixthFrequencyEquiv (u,B)).property).character R) I) →
      ∀pool : Finset (Ideal O),(∀I∈pool,Prime I) →
      ∀w σ v t : ℝ,wmin≤ w → lo≤σ → σ≤ hi →
      let β:=heightCoefficient (fun I=>idealCoeff ν I*annularWeight W (U^w) σ v I) t
      ‖naturalSlot χ pool β (U^w)-
        naturalSlot (naturalRow (excluded η A) u.val u.property.1).character pool β (U^w)‖≤1/2 := by
  filter_upwards [eventually_annular_deletion_tolerance W a b lo hi (Broot+Bmask) wmin (1/4)
      ha hWs hW (add_nonneg hBroot hBmask) hwmin (by norm_num),
    eventually_annular_deletion_tolerance W a b lo hi 1 wmin (1/4)
      ha hWs hW (by norm_num) hwmin (by norm_num),
    eventually_ge_atTop (A.absNorm:ℝ)] with U hraw hanchor hAN
  refine ⟨hraw.1,?_⟩
  intro η ν χ u B R hR hRN hBN hcoeff pool hp w σ v t hw hσlo hσhi β
  let F := naturalRow η u.val u.property.1
  let Fr := naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property
  have hg : ConcretePrimeRowBridge.idealGenerator B.val≠0 :=
    ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hrawcoeff (I : Ideal O) : idealCoeff χ I=idealCoeff (excluded F.character (B.val*R)) I := by
    rw [hcoeff I]
    have hh:=naturalRow_sixth_masked_ideal F (ConcretePrimeRowBridge.idealGenerator B.val) hg Fr R hR I
    rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh
  have hclean := naturalSlot_congr_ideal
    (naturalRow (excluded η A) u.val u.property.1).character (excluded F.character A)
    (natural_excluded_base_coefficients η A hA u.val u.property.1) pool β (U^w)
  rw [naturalSlot_congr_ideal χ _ hrawcoeff,hclean]
  have h1:=hraw.2 F.character ν (B.val*R) (mul_ne_zero B.property hR)
    (holes_with_root_norm B.val R U Broot Bmask (zero_lt_one.trans hraw.1) hBN hRN)
    pool hp w σ v t hw hσlo hσhi
  have h2:=hanchor.2 F.character ν A hA (by simpa using hAN)
    pool hp w σ v t hw hσlo hσhi
  have ht:=dist_triangle (naturalSlot (excluded F.character (B.val*R)) pool β (U^w))
    (naturalSlot F.character pool β (U^w)) (naturalSlot (excluded F.character A) pool β (U^w))
  simp only [dist_eq_norm] at ht
  rw [norm_sub_rev (naturalSlot F.character pool β (U^w))] at ht
  linarith

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
