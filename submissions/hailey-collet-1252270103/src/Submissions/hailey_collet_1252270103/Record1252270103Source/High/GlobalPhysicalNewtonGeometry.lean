/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite source geometry supplies the joint Newton support gates on exactly
the nonzero marked and ordinary character terms. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.PuncturedNewtonSupport
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredNewtonPositive
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion
open OAI.SevenEighths.Record1252270103Source Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
local notation "O"=>ActualEisensteinCubic.O

/-- No coprimality condition is imposed on character-zero rows. -/
theorem corrected_geometry_newton_support {ι:Type*}[Fintype ι]
    (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ))(b Z BA Bpool:ℝ)(depth:ℕ)
    (A₁ A₂ D K R:Ideal O)(P:Finset (Ideal O))
    (g:CorrectedSourceGeometry s W₁ W₂ b Z BA Bpool depth A₁ A₂ D K R P)
    (τ:Character)(t:ℝ)(z:O)
    (v:∀i,s.slots i)
    (hv:markedNewtonCoefficient s K R τ t z v≠0)
    (n:Ideal O×Ideal O)(hn:n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (hsf:Squarefree ((A₁*n.1)*(A₂*n.2)))
    (hf:frozenProfile s.W₁ s.W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0)
    (hrow:rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (n.1*n.2)≠0):
    IsCoprime D ((∏i,(v i:Ideal O))*n.1*n.2) ∧
      (idealDividingPool P (n.1*n.2)).card≤depth ∧
      (idealDividingPool P (D*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card := by
  have hm:rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O))≠0 :=
    right_ne_zero_of_mul hv
  have hf':frozenProfile W₁ W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0 := by
    rw [g.profile_left,g.profile_right] at hf
    exact hf
  exact punctured_newton_support τ R D _ n.1 n.2 g.correction_dvd 1 z t hm hrow
    P depth g.pool_prime (input_pool_avoids_marked s P g.pool_prime g.pool_avoids v)
    (g.residual_count n hn hsf hf') g.pool_budget

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_geometry_newton_support
