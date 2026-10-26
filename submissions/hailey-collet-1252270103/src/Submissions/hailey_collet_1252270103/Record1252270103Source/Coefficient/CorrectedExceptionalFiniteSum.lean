/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete residual divisor pool is paid after the fixed-divisor norm bound.
No row-dependent divisor maximum or truncated support is substituted. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.Divisor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondHarmonicBudget

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter UniqueFactorizationMonoid HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup CenteredMomentDivisorBoundary
open ExceptionalWindow
local notation "O" => ActualEisensteinCubic.O

/-- The exact seed factor is summed in the full original divisor pool,
with an arbitrary nonnegative scalar independent of that seed. All moving
parameters follow the one harmonic constant and threshold. -/
theorem actual_full_divisor_budget (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃H : ℝ,0<H ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι],∀s : Input ι,
    ∀(T : Finset (ℕ×ℕ))(W₁ W₂ Φ : 𝓢(ℝ,ℂ))(Q C D : Ideal O)
      (U : Finset (CommonIndex C D))(ε εL α Lraw Cr Mrow C₀ K₀ A : ℝ),
    0≤εL→0≤Cr→0≤K₀→0≤A→
    ∀{κ : Type*}(V : Finset κ)(v : κ→Ideal O),
      (∀j∈V,v j≠0)→(∀j∈V,((v j).absNorm:ℝ)≤Z^B)→
      (∑L∈divisorPool V v,‖(moebius L:ℂ)‖*
        (A*correctedExceptionalBudget s T W₁ W₂ Φ Q C D L U
          Z ε εL α Lraw Cr Mrow C₀ K₀))≤
      H*Z^(δ+B*εL)*A*correctedExceptionalBudget s T W₁ W₂ Φ Q C D 1 U
        Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  obtain ⟨H,hH,hm⟩:=full_seed_mass_subpower B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hm] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst s T W₁ W₂ Φ Q C D U ε εL α Lraw Cr Mrow C₀ K₀ A
    hεL hCr hK₀ hA κ V v hv hcap
  have hmass:=hz.2 εL hεL (divisorPool V v)
    (fun L hL=>(divisorPool_nonzero_norm V v hv (Z^B) hcap L hL).2)
  have hbudget:=correctedExceptionalBudget_nonneg s T W₁ W₂ Φ Q C D 1 U
    Z ε εL α Lraw Cr Mrow C₀ K₀ (zero_lt_one.trans hz.1).le hCr hK₀
  have hpaid:=mul_le_mul_of_nonneg_right hmass (mul_nonneg hA hbudget)
  calc
    _=(∑L∈divisorPool V v,‖(moebius L:ℂ)‖*((L.absNorm:ℝ)^εL/(L.absNorm:ℝ)))*
        (A*correctedExceptionalBudget s T W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro L hL
      rw [corrected_seed_exact s T W₁ W₂ Φ Q C D L]
      ring
    _≤_ := by convert hpaid using 1 <;> ring

end
end OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_full_divisor_budget
