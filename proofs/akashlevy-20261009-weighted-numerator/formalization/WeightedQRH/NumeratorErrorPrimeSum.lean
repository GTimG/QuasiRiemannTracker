import WeightedQRH.NumeratorActualError
import OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed

/-! Summing actual positive error coefficient majorants over a physical prime slot. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem errorSize_nonneg (u : FreeRow) (P : ProbePhysical.PrimeIdeal) :
    0 ≤ errorSize u P := by
  unfold errorSize
  split_ifs <;> positivity

theorem error_coefficient_slot_sum (epsilon c d B : ℝ) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
      (Y : ℝ), 1 ≤ Y → ∀ (W : ℝ → ℂ), Function.support W ⊆ Set.Icc c d →
      (∀ y, ‖W y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∑ P : T, ‖W ((P.val.val.absNorm : ℝ) / Y) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
        errorSize u P.val) ≤ C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          Y^(-(4 / 25 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    epsilon c d (-(4 / 25 : ℝ)) 1 B 1 hepsilon hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro u T Y hY W hWS hWB z hz
  let f : T → Ideal O := fun P => P.val.val
  have hf : Function.Injective f := fun P Q h => Subtype.ext (Subtype.ext h)
  let E : T → ℂ := fun P => (errorSize u P.val : ℂ)
  let G : T → ℂ := fun P => ((f P).absNorm : ℂ)^(1 / 2 : ℂ) * E P
  have hnorm (P : T) : ‖G P‖ ≤ 1 *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 : ℝ) else 1) := by
    have hQ0 : (0 : ℝ) < (f P).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
    have hQ1 : (1 : ℝ) ≤ (f P).absNorm := by
      exact_mod_cast Nat.succ_le_of_lt (show 0 < (f P).absNorm from by exact_mod_cast hQ0)
    have hn : ‖((f P).absNorm : ℂ)^(1 / 2 : ℂ)‖ = ((f P).absNorm : ℝ)^(1 / 2 : ℝ) := by
      rw [show ((f P).absNorm : ℂ) = (((f P).absNorm : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
      norm_num
    dsimp only [G,E]
    rw [norm_mul,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (errorSize_nonneg u P.val)]
    change ((f P).absNorm : ℝ)^(1 / 2 : ℝ) *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 / 2 : ℝ)
       else ((f P).absNorm : ℝ)^(-(51 / 100 : ℝ))) ≤ _
    by_cases hdiv : f P ∣ Ideal.span {u.val}
    · rw [ite_eq_left hdiv,ite_eq_left hdiv,one_mul,←Real.rpow_add hQ0]
      norm_num
    · rw [ite_eq_right hdiv,ite_eq_right hdiv,one_mul,←Real.rpow_add hQ0]
      exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num :
        (1 / 2 : ℝ) + -(51 / 100 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero _)
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _ => P.val.property.ne_zero) W hWS hWB G (fun P _ => hnorm P)
    (z - 1 / 2) (by simp only [Complex.sub_re]; rw [hz]; norm_num)
  have heq (P : T) :
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^((z - 1 / 2) - 1) * G P =
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^(z - 1) * E P := by
    have hn : ((f P).absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _),←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simp only [heq,norm_mul,E,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (errorSize_nonneg u _)] at hb
  simpa only [f,norm_mul] using hb

end WeightedQRH.Numerator
