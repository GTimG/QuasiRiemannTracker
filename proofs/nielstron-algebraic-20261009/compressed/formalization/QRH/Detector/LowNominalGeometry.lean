import OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import QRH.Detector.LowReflectedLength

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual physical objects unchanged. Optimized scales and explicit reflected penalty. -/
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowLength_bounds_optimized {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤QRH.ell) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤QRH.ell ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤QRH.ell-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩


lemma lowPhysicalScale_source_optimized (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(QRH.lx:ℝ)/L) (Z^(QRH.ly:ℝ)/L)=
      elementNorm C.generator*Z^(QRH.M:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(QRH.lx:ℝ)*Z^(QRH.ly:ℝ)=Z^(QRH.M:ℝ) := by rw [←Real.rpow_add hZ]; congr 1; dsimp [QRH.lx, QRH.ly]; ring
  rw [←he]
  ring


lemma lowPhysicalScale_nominal_bound_optimized (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(QRH.lx:ℝ)/L) (Z^(QRH.ly:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^(QRH.M-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source_optimized C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(QRH.M:ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring


end SevenEighths.ProbePhysical
end

end OAI
