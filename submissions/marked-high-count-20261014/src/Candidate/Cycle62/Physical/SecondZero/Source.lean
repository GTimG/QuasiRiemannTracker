/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle62SecondZero
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow
open EisensteinSchwartzPoisson CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- These are the actual source profile and support factors; independent
plain and slot heights remain in the literal input profiles. -/
def zeroControl {a b : ℝ} (s : Input ι) (p : Profiles a b) (ε : ℝ) : ℝ :=
  (2*p.control {(0,0)}*(∏ i, s.M i))^2 *
    (1+(∏ i, max 0 (s.hi i))*b*b)^(1+ε)

omit [DecidableEq ι] in
lemma zeroControl_nonneg {a b : ℝ} (s : Input ι) (p : Profiles a b) (ε : ℝ) :
    0 ≤ zeroControl s p ε := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by
      have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
      nlinarith [sq_nonneg b]) _)

lemma singleton_control {a b : ℝ} (p : Profiles a b) :
    p.control {(0,0)} = SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1) := by
  simp [Profiles.control,sourceControl,schwartzSeminormFamily]

/-- Genuine second diagonal, uniformly at every positive physical radius.
The original centered finite-column coefficient and divisor seed are retained. -/
theorem actual_second_zero_radius (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (a b : ℝ), 0 < a → 0 ≤ b →
    ∀ (s : Input ι) (p : Profiles a b), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ), 0 < K →
    ‖((K : ℂ)*paperRadialFourier W 0)*
      sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData ≤
      C*zeroControl s p ε*‖paperRadialFourier W 0‖*K*
        (volume s.toData)^ε/(seed.absNorm : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := CenteredMomentSecondSourceDiagonal.actual_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p h₁ h₂ R seed hseed W K hK
  have hh := hbound hcard a b ha hb s p h₁ h₂ R seed hseed
    ((K : ℂ)*paperRadialFourier W 0)
  conv at hh => rhs; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK]
  rw [zeroControl,singleton_control]
  convert hh using 1; ring

/-- The base, profiles, heights, masks, radius, and seed are all live after
one source constant. Seed and raw-volume caps are structural source gates. -/
theorem actual_second_zero_power (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (a b : ℝ), 0 < a → 0 ≤ b →
    ∀ (s : Input ι) (p : Profiles a b), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ)) (Z r B s₀ : ℝ),
    1 ≤ Z → volume s.toData ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    ‖((Z^r : ℝ) : ℂ)*paperRadialFourier W 0*
      sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData ≤
      C*zeroControl s p ε*‖paperRadialFourier W 0‖*Z^(r+ε*B-s₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_second_zero_radius N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p h₁ h₂ R seed hseed W Z r B s₀ hZ hvol hseedN
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hzn : 0 < Z^s₀ := Real.rpow_pos_of_pos hz _
  have hp := Real.rpow_le_rpow (volume_pos s.toData).le hvol hε.le
  rw [←Real.rpow_mul hz.le] at hp
  have hc := zeroControl_nonneg s p ε
  have hh := hbound hcard a b ha hb s p h₁ h₂ R seed hseed W (Z^r)
    (Real.rpow_pos_of_pos hz _)
  apply hh.trans
  calc
    _ ≤ C*zeroControl s p ε*‖paperRadialFourier W 0‖*Z^r*Z^(B*ε)/Z^s₀ := by
      apply div_le_div₀ (by positivity) _ hzn hseedN
      gcongr
    _ = _ := by
      calc
        _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*(Z^r*Z^(B*ε)/Z^s₀) := by ring
        _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*Z^(r+B*ε-s₀) := by
          rw [←Real.rpow_add hz,←Real.rpow_sub hz]
        _ = _ := by congr 1; congr 1; ring

end
end OAI.SevenEighths.Cycle62SecondZero
#print axioms OAI.SevenEighths.Cycle62SecondZero.actual_second_zero_radius
#print axioms OAI.SevenEighths.Cycle62SecondZero.actual_second_zero_power
#print axioms OAI.SevenEighths.Cycle62SecondZero.zeroControl_nonneg
#print axioms OAI.SevenEighths.Cycle62SecondZero.singleton_control
