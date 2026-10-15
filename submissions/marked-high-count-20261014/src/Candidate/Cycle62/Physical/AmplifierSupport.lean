import Candidate.Cycle62.Arithmetic.LocalReserves
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

namespace Cycle62.Physical
noncomputable section
open Filter Cycle62.Arithmetic
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open CenteredMomentPrimePool

/-- One threshold controls every amplifier width in the compact cell family. -/
theorem uniform_amplifier_norm_lower (amin : ℝ) (hmin : 0 < amin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ a : ℝ, amin ≤ a →
      ∀ n : ℝ, Z^a/2 ≤ n → Z^(3*a/4) ≤ n := by
  filter_upwards [(tendsto_rpow_atTop (show 0 < amin/4 by linarith)).eventually
    (eventually_ge_atTop (2:ℝ)), eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  refine ⟨hZ,?_⟩
  intro a ha n hn
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hsmall : 2 ≤ Z^(a/4) := hpow.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hid : Z^(3*a/4)*Z^(a/4) = Z^a := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left hsmall
    (Real.rpow_nonneg hZ0.le (3*a/4))
  rw [hid] at hm
  linarith

/-- The literal annular prime pool supplies the stronger 3a/4 lower width
needed by all three extracted errors. No separately assumed prime range. -/
theorem actual_amplifier_prime_width
    (rayModulus : Ideal O) [NeZero rayModulus]
    (H : Subgroup (O ⧸ rayModulus)ˣ) (Sbad : Finset (Ideal O))
    (Mmin : ℝ) (hMmin : 0 < Mmin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ M b : ℝ, Mmin ≤ M →
      3401/100000 ≤ b → b ≤ 1/25 →
      ∀ P ∈ primePool rayModulus H Sbad (1/2) 1 (Z^(M*amp b)),
        3*(M*amp b)/4 ≤ Real.logb Z (P.absNorm:ℝ) ∧
          Real.logb Z (P.absNorm:ℝ) ≤ M*amp b := by
  have hmin : 0 < Mmin*(902420521/120632400000) := by positivity
  filter_upwards [uniform_amplifier_norm_lower _ hmin] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro M b hM hb₁ hb₂ P hP
  have ha := amp_bounds ⟨hb₁,hb₂⟩
  have hamp : Mmin*(902420521/120632400000) ≤ M*amp b := by
    have hm : 0 ≤ M := hMmin.le.trans hM
    nlinarith
  have hs := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) (M*amp b))
    (Finset.mem_sdiff.mp hP).1
  have hlo : Z^(M*amp b)/2 ≤ (P.absNorm:ℝ) := by linarith [hs.1]
  have hup : (P.absNorm:ℝ) ≤ Z^(M*amp b) := by simpa only [mul_one] using hs.2
  have hnorm : 0 < (P.absNorm:ℝ) :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) (by norm_num)) hlo
  exact ⟨(Real.le_logb_iff_rpow_le hZ.1 hnorm).mpr (hZ.2 _ hamp _ hlo),
    (Real.logb_le_iff_le_rpow hZ.1 hnorm).mpr hup⟩

end
end Cycle62.Physical

#print axioms Cycle62.Physical.actual_amplifier_prime_width
