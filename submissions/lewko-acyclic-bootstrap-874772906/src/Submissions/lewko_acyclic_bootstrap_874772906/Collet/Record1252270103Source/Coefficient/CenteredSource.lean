/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Unconditional fixed-inducing centered source estimate for the literal
squarefree ordinary pair and fixed ordinary-only small-prime hole. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CenteredBound

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open HeckeFamily CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rectangle_squarefree_source_control_fractional (a b ε B α : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B →Q≤ψ.modulus →CenteredExceptionalProfile.InducedBy χ ψ →
      ∀m A z : O,ConcretePrimeRowBridge.goodLambda∣m →(2:O)∣m →
      (∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      ‖centeredSquarefreeRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨J,S,hS,hsource⟩:=rectangle_source_control_fractional a b ε B α ha hb hε hB hα0 (by linarith)
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩:=hsource Q hQ
  let mass : ℝ:=(mobiusPool.card:ℝ)*eulerBound 5 (1-α)
  have hm : 0≤mass:=mul_nonneg (Nat.cast_nonneg _) (eulerBound_pos _ _).le
  refine ⟨C*(1+mass),mul_pos hC (by linarith),?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let base : ℝ:=C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J
  have hb0 : 0≤base := by
    dsimp only [base]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)) (by positivity)
  have bound:=centeredSquarefreeRow_bound η χ m A z hrow W₁ W₂ b t X₁ X₂ Y₁ Y₂ T L α base hb
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY hα hb0
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2)
    (fun x₁ x₂ y₁ y₂ t' l hl hx₁ hx₂ hy₁ hy₂ hpx hpy=>
      hsource W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
        t x₁ x₂ y₁ y₂ t' l hl hx₁ hx₂ hy₁ hy₂ hpx hpy)
  have hscale : 0≤Real.sqrt T*L^(-α):=mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
  calc
    _≤(base*mass)*(Real.sqrt T*L^(-α)) := by
      convert bound using 1 <;> dsimp only [mass] <;> ring
    _≤(base*(1+mass))*(Real.sqrt T*L^(-α)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hb0) hscale
    _=_ := by dsimp only [base];ring

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.rectangle_squarefree_source_control_fractional
