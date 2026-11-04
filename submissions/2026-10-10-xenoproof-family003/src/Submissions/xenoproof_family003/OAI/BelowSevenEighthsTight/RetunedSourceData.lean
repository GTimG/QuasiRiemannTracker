import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedHighData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedGlobalCorrection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

/- Adapts the original generic finite-source and smooth-window constructors
   to the retuned parameter record. It does not define or estimate a probe. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily
local notation "O" => HeckeFamily.O

structure RetunedSourceData {Δ L margin mesh : ℝ}
    (D : RetunedHighData Δ L margin mesh) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀ P ∈ S, P.IsMaximal
  first : FirstTail (4*D.e) S
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

theorem exists_retuned_source_data {Δ L margin mesh : ℝ}
    (D : RetunedHighData Δ L margin mesh) : Nonempty (RetunedSourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ :=
    OAI.SevenEighths.Parameters.exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ :=
    OAI.SevenEighths.Parameters.exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def RetunedSourceData.modulus {Δ L margin mesh : ℝ}
    {D : RetunedHighData Δ L margin mesh} (F : RetunedSourceData D) : Ideal O :=
  ∏ P ∈ F.S, P

instance {Δ L margin mesh : ℝ} {D : RetunedHighData Δ L margin mesh}
    (F : RetunedSourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {Δ L margin mesh : ℝ} {D : RetunedHighData Δ L margin mesh}
    (F : RetunedSourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem retuned_source_analytic {Δ L margin mesh : ℝ}
    {D : RetunedHighData Δ L margin mesh} (F : RetunedSourceData D)
    (s₀ : ℝ) (hs₀ : (13/15:ℝ) ≤ s₀) (η : Character) :
    (∀ I, idealCoeff (η.excludePrimes F.S F.exclusions.prime) I =
      if IsCoprime I (η.excludePrimes F.S F.exclusions.prime).modulus
        then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (fun s=>globalClosedCorrection η F.S s 1 (1/6))
      {s : ℂ | s₀ < s.re} ∧
    (∀ s : ℂ, s₀ < s.re → ‖globalClosedCorrection η F.S s 1 (1/6)-1‖ ≤ 1/2) := by
  refine ⟨excludePrimes_mask η F.S F.exclusions.prime,?_,?_⟩
  · apply (CorrectionExtension.globalClosedCorrection_analytic_x
      η F.S F.exclusions.tail 1 (1/6) (by norm_num) (by norm_num)).mono
    intro s hs
    exact hs₀.trans_lt hs
  · intro s hs
    exact CorrectionExtension.globalClosedCorrection_bound η F.S F.exclusions.tail
      s 1 (1/6) (hs₀.trans hs.le) (by norm_num) (by norm_num)

#print axioms exists_retuned_source_data
#print axioms retuned_source_analytic
end
end BelowSevenEighthsTight.Parameters
