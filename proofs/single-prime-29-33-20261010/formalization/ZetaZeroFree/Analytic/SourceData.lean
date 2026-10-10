import OAI.NumberTheory.DirichletL.ParametersFixedSource
import ZetaZeroFree.Analytic.Principal.Residues

/-! Common source data for the new one-prime probe. The exclusion set,
window and ray modulus are chosen before the target character. -/

namespace ZetaZeroFree.Analytic
noncomputable section
open scoped Classical ContDiff BigOperators
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

structure SourceData (e : ℝ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀ P ∈ S, P.IsMaximal
  first : FirstTail (4 * e) S
  w : ℝ → ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w ⊆ Set.Ioo 1 2
  positive_support : tsupport w ⊆ Set.Ioi 0
  bounded : ∀ x, 0 ≤ w x ∧ w x ≤ 1
  nonzero : w ≠ 0
  complex_eq : ∀ x, W x = (w x : ℂ)
  complex_nonzero : W ≠ 0
  complex_support : Function.support W ⊆ Set.Icc 1 2
  real : ∀ x, (W x).im = 0
  nonnegative : ∀ x, 0 ≤ (W x).re

theorem exists_source_data (e : ℝ) (he : 0 < e) : Nonempty (SourceData e) := by
  obtain ⟨S, _, hS, hfirst, hmax⟩ := Parameters.exists_fixed_source e he ∅ (by simp)
  obtain ⟨w, W, hw, hc, hs, hp, hb, hn, heq, hWn, hWs, hr, hWpos⟩ :=
    Parameters.exists_fixed_probe_window
  exact ⟨⟨S, hS, hmax, hfirst, w, W, hw, hc, hs, hp, hb, hn, heq, hWn, hWs, hr, hWpos⟩⟩

namespace SourceData
variable {e : ℝ} (F : SourceData e)

def modulus : Ideal O := ∏ P ∈ F.S, P

instance : NeZero F.modulus := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

def lengths (_F : SourceData e) (Z : ℝ) : Fin 1 → ℝ := fun _ => Z ^ (5 / 33 : ℝ)

def pools (Z : ℝ) : Fin 1 → Finset PrimeIdeal :=
  fun _ => pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z ^ (5 / 33 : ℝ))

def normalizer (Z : ℝ) : ℂ :=
  sourceResidueConstant F.W F.W F.modulus *
    (Probe.principalScalar Finset.univ Z (5 / 33)
      (slotMass (F.pools Z) (residueWeights (fun (_ : Fin 1) => F.w) (F.lengths Z))) : ℂ)

def physicalProbe (η : Character) (Z : ℝ) : ℂ :=
  compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
    (fun j => canonicalSlotSupport (F.pools Z j)) (fun (_ : Fin 1) y => (F.w y : ℂ))
    (F.lengths Z) (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z

def probe (η : Character) (Z : ℝ) : ℂ := F.physicalProbe η Z / F.normalizer Z

theorem correction_analytic (η : Character) :
    AnalyticOnNhd ℂ (sourceCorrection η F.S) {s : ℂ | 7 / 8 < s.re} :=
  (sourceCorrection_differentiable η F.S F.exclusions).analyticOnNhd
    (Complex.isOpen_re_gt _)

theorem correction_bound (η : Character) (s : ℂ) (hs : 7 / 8 < s.re) :
    ‖sourceCorrection η F.S s - 1‖ ≤ 1 / 2 :=
  sourceCorrection_bound η F.S F.exclusions s hs

end SourceData
end
end ZetaZeroFree.Analytic
