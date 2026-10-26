import Candidate.Cycle63.Density.FixedDensity

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ConcretePrimeRowBridge
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- A uniform sixth-power lift for predicates of the free core. This pays
all multiples of finitely many exceptional cores, including principal rows. -/
theorem raw_core_density_uniform :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : FreeRow → Prop) (C ρ : ℝ), 0 ≤ C → 2/7 ≤ ρ →
      (∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ P u) → (F.card : ℝ) ≤ C*Y^ρ) →
      ∀ H : ℝ, 0 < H → ∀ R : Finset NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ P (sixthFrequencyEquiv.symm h).1) →
        (R.card : ℝ) ≤ C*D*H^ρ := by
  let w : NZIdeal → ℝ := fun B => (B.val.absNorm : ℝ)^(-6*(2/7 : ℝ))
  have hw := ideal_sixth_power_summable (2/7) (by norm_num)
  have hw0 : ∀ B, 0 ≤ w B := fun B => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D : ℝ := (∑' B : NZIdeal, w B)+1
  have hsum : 0 ≤ ∑' B : NZIdeal, w B := tsum_nonneg hw0
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro P C ρ hC hρ hfree H hH R hR
  have hBpos (B : NZIdeal) : 0 < (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hBone (B : NZIdeal) : 1 ≤ (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hfiber (B : NZIdeal) : ((sixthFreeFiber R B).card : ℝ) ≤
      C*(H/(B.val.absNorm : ℝ)^6)^ρ := by
    let Y : ℝ := H/(B.val.absNorm : ℝ)^6
    have hmem (u : FreeRow) (hu : u ∈ sixthFreeFiber R B) : rowNorm u ≤ Y ∧ P u := by
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
      obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
      have he : p = (u,B) := Prod.ext hpu hpB
      subst p
      have hr := hR _ ((mem_sixthPairs R (u,B)).mp hp)
      rw [raw_sixth_norm] at hr
      exact ⟨(le_div_iff₀ (pow_pos (hBpos B) 6)).mpr hr.1,
        by simpa only [Equiv.symm_apply_apply] using hr.2⟩
    by_cases hY : 1 ≤ Y
    · exact hfree Y hY (sixthFreeFiber R B) hmem
    · have he : sixthFreeFiber R B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hY ((rowNorm_ge_one u).trans (hmem u hu).1)
      rw [he, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hc : (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
      C*(H/(B.val.absNorm : ℝ)^6)^ρ := by
    rw [raw_sixth_cardinality R, Nat.cast_sum]
    exact Finset.sum_le_sum (fun B _ => hfiber B)
  simp_rw [sixth_window_power H _ ρ hH (hBpos _)] at hc
  calc
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
        C*(H^ρ*(B.val.absNorm : ℝ)^(-6*ρ)) := hc
    _ ≤ ∑ B ∈ (sixthPairs R).image Prod.snd, C*(H^ρ*w B) := by
      refine Finset.sum_le_sum fun B _ => ?_
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH.le _)
      exact Real.rpow_le_rpow_of_exponent_le (hBone B) (by linarith)
    _ = (C*H^ρ)*∑ B ∈ (sixthPairs R).image Prod.snd, w B := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun B _ => ?_
      ring
    _ ≤ (C*H^ρ)*∑' B : NZIdeal, w B := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum _ (fun B _ => hw0 B)) (by positivity)
    _ ≤ C*D*H^ρ := by
      have ht : (∑' B : NZIdeal, w B) ≤ D := by dsimp [D]; linarith
      calc
        _ ≤ (C*H^ρ)*D := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by ring

end SevenEighths.LocalMoment
end
end OAI
