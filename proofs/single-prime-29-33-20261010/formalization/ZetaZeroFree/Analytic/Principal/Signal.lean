import OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual
import OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds

namespace ZetaZeroFree.Analytic.Principal

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual

lemma scale_exponent : (5/6:ℝ)-(13/33)/3-(5/33)/6=67/99 := by norm_num

lemma source_power_identity {Z : ℝ} (hZ : 0<Z) (s : ℂ) :
    ((Z^(13/33:ℝ):ℝ):ℂ)^(1/3:ℂ)*(Z:ℂ)^(s-5/6)=
      (Z:ℂ)^(((-(5/33:ℝ)/6:ℝ):ℂ))*(Z:ℂ)^(s-67/99) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [←Complex.cpow_mul_ofReal_nonneg hZ.le (13/33) (1/3),
    ←Complex.cpow_add _ _ hz,←Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring

lemma signal_scale (χ : Character) (H : ℂ→ℂ) {Z : ℝ} (hZ : 0<Z) :
    HeckeSignal.signal χ H (-67/99) Z=
      (Z:ℂ)^((11/16:ℂ)-67/99)*HeckeSignal.signal χ H (-11/16) Z := by
  unfold HeckeSignal.signal
  rw [←mul_assoc,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hZ.ne')]
  congr 2
  norm_num

lemma sourceResidueConstant_positive (M : Ideal HeckeFamily.O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    ∃c : ℝ,0<c ∧ sourceResidueConstant W0 W1 M=(c:ℂ) :=
  ProbePrincipalNormalizer.sourceResidueConstant_positive M W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1

/-- The signed one-prime normalizer uses the actual ray-prime mass. -/
theorem one_prime_normalizer_eventually (M : Ideal HeckeFamily.O) [NeZero M]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (E : Finset (Ideal HeckeFamily.O)) (W : ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c≤d)
    (hsupp : Function.support W⊆Set.Ioo c d) (hW : ContDiff ℝ ∞ W)
    (hcompact : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hne : W≠0) (cs : ℂ) (hcs : cs≠0)
    (nu : ℝ) (hnu : 0<nu) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun (_ : Fin 1)=>ProbeRaySlots.pool (RayQuotient.identityClass M H) E c d (Z^(5/33:ℝ))
      let weights := residueWeights (fun (_ : Fin 1)=>W) (fun _=>Z^(5/33:ℝ))
      let N := cs*(Probe.principalScalar Finset.univ Z (5/33) (slotMass T weights):ℂ)
      N≠0 ∧ ‖N⁻¹‖≤‖cs⁻¹‖*Z^nu := by
  filter_upwards [ProbeRaySlots.power_ray_mass_and_normalizer M H hH E
    (fun (_ : Fin 1)=>W) c d hc hd (fun _=>hsupp) (fun _=>hW)
    (fun _=>hcompact) (fun _=>hp) (fun _=>hW0) (fun _=>hne)
    (fun (_ : Fin 1)=>(5/33:ℝ)) (fun _=>by norm_num) nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only at hmass ⊢
  constructor
  · exact mul_ne_zero hcs (source_normalizer_ne_zero Finset.univ _ _ hZ (fun j _=>hmass.1 j))
  · rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    have hi : |(Probe.principalScalar Finset.univ Z (5/33)
        (slotMass (fun (_ : Fin 1)=>ProbeRaySlots.pool (RayQuotient.identityClass M H) E c d (Z^(5/33:ℝ)))
          (residueWeights (fun (_ : Fin 1)=>W) (fun _=>Z^(5/33:ℝ)))))⁻¹|≤Z^nu := by
      simpa using hmass.2
    simpa only [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_right hi (norm_nonneg cs⁻¹)

end
end ZetaZeroFree.Analytic.Principal
