/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.ExcludedCharacterBound
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CenteredSource

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredExceptionalProfile
open CenteredMomentFiniteProfileExceptional Record1252270103Source
open QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O

/-- Uniform centered source control after an actual moving exclusion ideal.
The derivative degree and seminorm set precede Q; the positive constant
precedes all profiles, characters, exclusion ideals, rows and heights. The
fixed enlarged modulus exponent is Bχ+BR. -/
theorem excluded_rectangle_squarefree_source_control_fractional
    (a b ε Bχ BR α : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε)
    (hBχ : 0≤Bχ) (hBR : 0≤BR) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η χ ψ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^Bχ →Q≤ψ.modulus →InducedBy χ ψ →
      ∀m A z : O,goodLambda∣m →(2:O)∣m →
      (∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) →
      ∀R : Ideal O,R≠0 →(R.absNorm:ℝ)≤Z^BR →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      ‖centeredSquarefreeRow η (m*idealGenerator R) A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨J,S,hS,hsource⟩ := rectangle_squarefree_source_control_fractional
    a b ε (Bχ+BR) α ha hb hε (add_nonneg hBχ hBR) hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow R hR hmask
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  exact hsource W₁ W₂ hs₁ hs₂ Z hZ η (excluded χ R) ψ
    (excluded_character_power_bound Z Bχ BR (zero_lt_one.trans_le hZ) χ R hR hnorm hmask)
    hQψ (excluded_character_induced χ ψ R hind) (m*idealGenerator R) A z
    (hml.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _))
    (excluded_character_row η χ m A z hml hm2 hrow R hR)
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.excluded_rectangle_squarefree_source_control_fractional
