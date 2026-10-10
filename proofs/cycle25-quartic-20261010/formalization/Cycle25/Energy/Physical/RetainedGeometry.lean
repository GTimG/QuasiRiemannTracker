import Cycle25.Numerator.ReflectionRetained
import Cycle25.Numerator.Imported.RowConductor
import OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentRetainedWeightedSource CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentNaturalPrimitive CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionTailMass
open CenteredMomentReflectionRetainedLength CenteredMomentSectorLocalization

/-- All natural primitive/deletion scales obey the combined conductor bound;
no individual deletion factor is charged a second time. -/
lemma actual_dual_scale_bound (τ ψ : Character) (X B : ℝ) (hX : 0 < X)
    (hcap : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ B*X)
    (D : (sourcePrimes τ ψ).powerset) (I : SmoothIdeal (sourcePrimes τ ψ)) :
    dualScale τ ψ X D I ≤ B := by
  have hQ : 0 < (ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact (dual_scale_bounds (sourcePrimes τ ψ) D.val (redundantSet_prime _ _)
    (Finset.mem_powerset.mp D.property) I _ X B hQ hX hcap).2

/-- A uniform logarithmic scale interval for every retained annulus and every
rowwise coefficient dilation, under only its combined-scale bound. -/
theorem eventually_retained_log_interval (C xi : ℝ) (hC : 0 < C) (hxi : 0 < xi) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀(τ ψ:Character) (X m:ℝ), 0 < X →
      (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ C*U^m*X →
      ∀a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes τ ψ),
      ∀hY:0 < dualScale τ ψ X a.1.1 a.1.2,
      a.2 ∈ retainedAnnuli (U^(xi/4)) (dualScale τ ψ X a.1.1 a.1.2) hY →
      Real.log (dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2) ∈
        Set.Icc 0 ((m+xi)*Real.log U) := by
  have hc : ∀ᶠU:ℝ in atTop, 4*C ≤ U^(3*xi/4) :=
    (tendsto_rpow_atTop (by linarith:0 < 3*xi/4)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with U hc hU
  refine ⟨hU,?_⟩
  intro τ ψ X m hX hcap a hY ha
  have hz := zero_lt_one.trans hU
  have hlow := retained_scale_lower _ _ hY _ ha
  have hdual := actual_dual_scale_bound τ ψ X (C*U^m) hX hcap a.1.1 a.1.2
  have hscale : dyadicScale a.2 ≤ 4*U^(xi/4) :=
    retained_scale_le _ _ ((retainedAnnuli_mem _ _ hY _).mp ha).1
  have hupper : dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2 ≤ U^(m+xi) := by
    calc
      _ ≤ (4*U^(xi/4))*(C*U^m) :=
        mul_le_mul hscale hdual hY.le (by positivity)
      _ = (4*C)*U^(xi/4)*U^m := by ring
      _ ≤ U^(3*xi/4)*U^(xi/4)*U^m := by gcongr
      _ = U^(m+xi) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  refine ⟨Real.log_nonneg hlow,?_⟩
  calc
    _ ≤ Real.log (U^(m+xi)) := Real.log_le_log (zero_lt_one.trans_le hlow) hupper
    _ = _ := by rw [Real.log_rpow hz]

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
