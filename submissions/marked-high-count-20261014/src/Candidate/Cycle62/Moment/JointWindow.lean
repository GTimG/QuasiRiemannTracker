import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalIndexedWindow

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle62Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_window_column_integral (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    windowColumn s C hC R seed L η t θ X V z =
      ∫ u : ℝ, columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
        normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z := by
  have hh := plain_column_integral Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, windowColumn, coefficient_polynomial] using hh

theorem actual_window_column_integrable (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun u : ℝ => columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
      normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z) := by
  have hh := plain_column_integrable Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, coefficient_polynomial] using hh

/-- The common Mellin densities are integrated after summing the matched actual
source coordinates. Characters, masks, heights and scales may vary by coordinate. -/
theorem actual_joint_window_pair {κ : Type*}
    (rows : Finset κ) (s v : κ → Input ι)
    (C D R seed L : κ → Ideal O) (hC : ∀ k, Supported (C k))
    (hD : ∀ k, Supported (D k)) (η τ : κ → Character)
    (t₁ t₂ θ₁ θ₂ X Y : κ → ℝ) (hX : ∀ k, 0 < X k) (hY : ∀ k, 0 < Y k)
    (row₁ row₂ : κ → O) (scalar₁ scalar₂ : κ → ℂ)
    (V₁ V₂ : ℝ → ℂ) (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : ContDiff ℝ ∞ V₁) (hs₂ : ContDiff ℝ ∞ V₂)
    (J₁ J₂ : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ u w : ℝ,
      (∑ k ∈ rows,
        ‖scalar₁ k*normalizedColumn
          (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
          (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
        ‖scalar₂ k*normalizedColumn
          (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
          (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖) ≤
      E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :
    (∑ k ∈ rows,
      ‖scalar₁ k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k)‖*
      ‖scalar₂ k*windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k)‖) ≤
      E*(∫ u : ℝ, (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫ w : ℝ, (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖) := by
  let f := fun k : κ => fun u : ℝ => scalar₁ k*
    (columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁ k-u) (Real.log (X k))*
      normalizedColumn (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
        (C k) (hC k) (R k) (seed k) (L k) (row₁ k))
  let g := fun k : κ => fun w : ℝ => scalar₂ k*
    (columnDensity V₂ hc₂ hs₂ w*logPhase (θ₂ k-w) (Real.log (Y k))*
      normalizedColumn (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
        (D k) (hD k) (R k) (seed k) (L k) (row₂ k))
  have hf (k : κ) : Integrable (f k) :=
    (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)).const_mul _
  have hg (k : κ) : Integrable (g k) :=
    (actual_window_column_integrable (v k) (D k) (hD k) (R k) (seed k) (L k)
      (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)).const_mul _
  have hh := paired_integrals rows f g (fun k _ => hf k) (fun k _ => hg k)
    (fun u => (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun w => (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun _ => by positivity) (fun _ => by positivity) E hE ?_
  · have hfEq (k : κ) : (∫ u : ℝ, f k u) = scalar₁ k*
        windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
          (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k) := by
      dsimp only [f]
      rw [integral_const_mul, ←actual_window_column_integral
        (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)]
    have hgEq (k : κ) : (∫ w : ℝ, g k w) = scalar₂ k*
        windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
          (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k) := by
      dsimp only [g]
      rw [integral_const_mul, ←actual_window_column_integral
        (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)]
    simpa only [hfEq, hgEq] using hh
  · intro u w
    simp only [f, g, norm_mul, logPhase_norm, mul_one]
    calc
      _ = (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          ∑ k ∈ rows,
            ‖scalar₁ k*normalizedColumn
              (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
              (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
            ‖scalar₂ k*normalizedColumn
              (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
              (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, norm_mul]
        ring
      _ ≤ (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          (E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :=
        mul_le_mul_of_nonneg_left (hpair u w) (by positivity)
      _ = _ := by ring

#print axioms actual_window_column_integral
#print axioms actual_window_column_integrable
#print axioms actual_joint_window_pair
end
end OAI.SevenEighths.Cycle62Moment
