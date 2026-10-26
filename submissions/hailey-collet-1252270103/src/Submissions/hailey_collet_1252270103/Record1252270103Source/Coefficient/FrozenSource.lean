/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal frozen centered child has uniform control from the unchanged
inducing character, with only a fixed enlarged modulus exponent. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FrozenCentered

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O

theorem frozen_squarefree_source_control_fractional
    (a b ε Bχ BF α : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε)
    (hBχ : 0≤Bχ) (hBF : 0≤BF) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η χ ψ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^Bχ →Q≤ψ.modulus →InducedBy χ ψ →
      ∀m A z : O,goodLambda∣m →(2:O)∣m →
      (∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) →
      ∀A₁ A₂ : Ideal O,A₁≠0 →A₂≠0 →((A₁*A₂).absNorm:ℝ)≤Z^BF →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      ‖frozenCenteredRow (rowWeight η m A z t) W₁ W₂ A₁ A₂ b X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨J,S,hS,hsource⟩ := excluded_rectangle_squarefree_source_control_fractional
    a b ε Bχ BF α ha hb hε hBχ hBF hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow A₁ A₂ hA₁ hA₂ hnormF
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have he := frozenCenteredRow_excluded η χ m A z hml hm2 hrow A₁ A₂ hA₁ hA₂
    W₁ W₂ b t X₁ X₂ Y₁ Y₂ T hb (hL.trans_le hX₁) (hL.trans_le hX₂)
    (hL.trans_le hY₁) (hL.trans_le hY₂) (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2)
  have hc : ‖(squarefreeIndicator (A₁*A₂):ℂ)*ordinaryHoleIndicator A₁ A₂‖≤1 := by
    by_cases hs : Squarefree (A₁*A₂) <;> by_cases hh : ordinarySmallHole A₁ A₂ <;>
      simp [squarefreeIndicator,ordinaryHoleIndicator,hs,hh]
  rw [he,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans
    (hsource W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
      (A₁*A₂) (mul_ne_zero hA₁ hA₂) hnormF t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.frozen_squarefree_source_control_fractional
