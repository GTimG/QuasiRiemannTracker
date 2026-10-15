import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowLength_bounds_generic {K : ℕ} (Etotal : ℝ) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Etotal) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤Etotal ∧
    0≤lowSelectedLength ell J ∧
      lowSelectedLength ell J≤Etotal-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowPhysicalScale_source_generic (C : CalibrationData)
    (Etotal lx ly Z L : ℝ) (hZ : 0<Z) (hxy : lx+ly=1-Etotal) :
    lowPhysicalScale C (Z^lx/L) (Z^ly/L)=
      elementNorm C.generator*Z^(1-Etotal)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^lx*Z^ly=Z^(1-Etotal) := by
    rw [←Real.rpow_add hZ,hxy]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound_generic (C : CalibrationData)
    (Etotal lx ly Z L c d : ℝ) (hZ : 0<Z) (hxy : lx+ly=1-Etotal)
    (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^lx/L) (Z^ly/L)≤
      (elementNorm C.generator/c^2)*Z^(1-Etotal-2*d) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source_generic C Etotal lx ly Z L hZ hxy]
  calc
    _≤elementNorm C.generator*Z^(1-Etotal)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ (1-Etotal) (2*d)]
      ring

lemma lowSelectedScale_product_generic {K : ℕ} (ell : Fin K→ℝ)
    (J : Finset (Fin K)) (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) :=
  lowSelectedScale_product ell J Z hZ

end SevenEighths.ProbePhysical
end
end OAI
