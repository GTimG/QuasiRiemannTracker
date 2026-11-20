/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Genuine short fourth source and quantitative .875--.89424 bridge. -/
import Candidate.C092.transport.TinyCoreCauchy

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.NativeStrip QRH.Cycle092.LowActual QRH.Cycle090 QRH.SourceCertificate

def bridgeMin : ℝ := 7/8
def bridgeMax : ℝ := 5589/6250
def bridgeCap : ℝ := sourceY/bridgeMin
def bridgeWidth : ℝ := 1/2-bridgeCap-1/1000

theorem bridge_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformBox bridgeCap bridgeCap bridgeWidth := by
  apply native_mean_box hβ <;> norm_num [bridgeCap,bridgeWidth,bridgeMin,sourceY]

theorem bridge_width_positive : 0 < bridgeWidth := by norm_num [bridgeWidth,bridgeCap,bridgeMin,sourceY]

def repeatedProfile {a b : ℝ} (p : Profiles a b) (j : Fin 2) : Profiles a b :=
  ⟨fun _ => p.profile j,fun _ => p.support j⟩

theorem repeated_control {a b : ℝ} (p : Profiles a b) (j : Fin 2) (S : Finset (ℕ×ℕ)) :
    (repeatedProfile p j).control S = (sourceControl S (p.profile j))^2 := by
  simp [repeatedProfile,Profiles.control,pow_two]

theorem control_mono (S T : Finset (ℕ×ℕ)) (h : S ⊆ T) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S W ≤ sourceControl T W :=
  CenteredMomentEnergyReferenceProfileBudget.control_mono h W

theorem duplicated_sum {Slot : Type*} (F : Finset Slot) (w : Slot → ℝ) :
    (∑ j ∈ duplicated F, w j.2) = 2*(∑ i ∈ F, w i) := by
  simp [duplicated,Finset.sum_product]

/-- Two same-prefactor fourth moments recover the original product control,
including the cases where either profile seminorm is zero. -/
theorem common_cauchy_factor {E₁ E₂ G A B : ℝ}
    (hG : 0 ≤ G) (h₁ : E₁ ≤ G*A^4) (h₂ : E₂ ≤ G*B^4) :
    Real.sqrt E₁*Real.sqrt E₂ ≤ G*(A*B)^2 := by
  have hs (x : ℝ) : Real.sqrt (x^4) = x^2 := by
    rw [show x^4=(x^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  calc
    _ ≤ Real.sqrt (G*A^4)*Real.sqrt (G*B^4) :=
      mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hG,Real.sqrt_mul hG,hs,hs]
      calc
        _ = (Real.sqrt G)^2*(A*B)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hG]

/-- The actual retained original marks have half the duplicated native
quota. Its deletion price pays the full bridge, including fixed source and
slot errors and one actual original-slot rounding. -/
theorem bridge_paid {V e S mesh buffer : ℝ} {k : ℕ}
    (hV0 : bridgeMin ≤ V) (hV1 : V ≤ bridgeMax)
    (he0 : 0 ≤ e) (he1 : e ≤ 3/4) (hS : S ≤ 134/1000)
    (hm0 : 0 ≤ mesh) (hm : mesh ≤ 1/100000)
    (hb : buffer*(k : ℝ) ≤ 1/10000) :
    V+1/1000+buffer*(k : ℝ)+e*max 0 (S-V*bridgeWidth/2+mesh) ≤
      V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V) := by
  have hcap : max 0 (S-V*bridgeWidth/2+mesh) ≤
      (134/1000 : ℝ)-bridgeMin*bridgeWidth/2+1/100000 := by
    apply max_le
    · norm_num [bridgeMin,bridgeWidth,bridgeCap,sourceY]
    · have hVW := mul_le_mul_of_nonneg_right hV0 bridge_width_positive.le
      linarith
  have hew := mul_le_mul_of_nonneg_left hcap he0
  have hew' := mul_le_mul_of_nonneg_right he1
    (show 0 ≤ (134/1000 : ℝ)-bridgeMin*bridgeWidth/2+1/100000 by norm_num [bridgeMin,bridgeWidth,bridgeCap,sourceY])
  have hVH : 0 ≤ (H : ℝ)-V := by norm_num [H,u,bridgeMax] at *; linarith only [hV1]
  rw [max_eq_right hVH]
  norm_num [H,u,rho,bridgeMin,bridgeWidth,bridgeCap,bridgeMax,sourceY] at *
  linarith

end
end QRH.Cycle092.TinyCore
