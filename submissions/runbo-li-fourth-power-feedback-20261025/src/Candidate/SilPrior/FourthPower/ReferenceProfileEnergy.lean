/- Copyright (c) 2026 Sil. Apache-2.0.
The common smooth-profile energy is proved from the actual sextic reference.
In particular it is not an extra analytic assumption in the reflection step.
-/
import Candidate.SilPrior.FourthPower.ReferenceHeckeProducts
import Candidate.SilPrior.FourthPower.ReferenceFactors
import Candidate.SilPrior.FourthPower.ReferenceNaturalProfiles

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReferenceProfileEnergy
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic CanonicalRowCompletion
open CanonicalQuadraticSieve
open ReferenceFactors ReferenceHeckeProducts
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

def pairFactors (F G : Factor) (H : α → Factor) : Option (Option α) → Factor
  | none => F
  | some none => G
  | some (some i) => H i

theorem pair_product {β : Type*} [CommMonoid β] (f : Factor → β)
    (F G : Factor) (H : α → Factor) :
    (∏ i, f (pairFactors F G H i)) = f F*f G*∏ i, f (H i) := by
  simp only [Fintype.prod_option,pairFactors,mul_assoc]

theorem bounded_scaleTests (W : ℝ → ℂ) (a b : ℝ)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ B : ℝ, 0 < B ∧ ∀ (j : Fin 2) (x : ℝ), ‖scaleTest W j x‖ ≤ B := by
  have hc (j : Fin 2) : ∃ B : ℝ, ∀ x : ℝ, ‖scaleTest W j x‖ ≤ B := by
    obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      (scaleTest_continuous W hW j).continuousOn
    refine ⟨|C|,?_⟩
    intro x
    by_cases hx : scaleTest W j x = 0
    · simp only [hx,norm_zero]
      exact abs_nonneg _
    · exact (hC x (scaleTest_support W a b hs j hx)).trans (le_abs_self C)
  choose B hB using hc
  refine ⟨1+∑ j, |B j|,by positivity,?_⟩
  intro j x
  have hj := Finset.single_le_sum (s:=Finset.univ) (f:=fun j : Fin 2 => |B j|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  exact (hB j x).trans ((le_abs_self _).trans (by linarith))

/-- Two actual smooth Hecke factors and any fixed number of finite marked
factors. Frequencies are arbitrary but common across the variable rows. -/
theorem two_smooth_product (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (η : Character) (m D : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      ∀ (W V : ℝ → ℂ) (b d B Q X Y f g : ℝ) (H : α → Factor),
      0 ≤ b → 0 ≤ d → 0 ≤ B → 0 ≤ Q → 0 < X → 0 < Y →
      (∀ x, ‖W x‖ ≤ B) → (∀ x, ‖V x‖ ≤ Q) →
      Function.support W ⊆ Iic b → Function.support V ⊆ Iic d →
      (b*X)*(d*Y)*(∏ i, (H i).length) ≤ N →
      (∑ x : rows, ‖polynomial (χ x) false W X 0 (2*Real.pi*f)*
        polynomial (χ x) false V Y 0 (2*Real.pi*g)*∏ i, (H i).value (χ x)‖^2) ≤
        C*Z^(R+ε)*(3+T^(1/3 : ℝ))*(Real.sqrt b*B*(Real.sqrt d*Q)*∏ i, (H i).amplitude)^2 := by
  obtain ⟨C,hC,hb⟩ := identified_product_reference (α:=Option (Option α)) ε L hε hL
  refine ⟨C,hC,?_⟩
  intro Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr
  intro W V b d B Q X Y f g H hb0 hd hB hQ hX hY hW hV hWs hVs hlen
  let F := Factor.smooth W b B X f hb0 hB hX hW
  let G := Factor.smooth V d Q Y g hd hQ hY hV
  let K := pairFactors F G H
  have hK : (∏ i, (K i).length) ≤ N := by
    simpa only [K,pair_product,F,G,Factor.smooth] using hlen
  have he := hb Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr
    (fun i => (K i).pool) (fun i => (K i).coefficient)
    (fun i => (K i).length) (fun i => (K i).amplitude)
    (fun i => (K i).amplitude_nonneg) hK
    (fun i => (K i).support_bound) (fun i => (K i).coefficient_bound)
  change (∑ x : rows, ‖∏ i, (K i).value (χ x)‖^2) ≤
    C*Z^(R+ε)*(3+T^(1/3 : ℝ))*(∏ i, (K i).amplitude)^2 at he
  have heq (x : rows) : (∏ i, (K i).value (χ x)) =
      polynomial (χ x) false W X 0 (2*Real.pi*f)*
      polynomial (χ x) false V Y 0 (2*Real.pi*g)*∏ i, (H i).value (χ x) := by
    rw [show K = pairFactors F G H from rfl,pair_product (fun F => F.value (χ x))]
    rw [Factor.smooth_value W b B X f hb0 hB hX hW hWs,
      Factor.smooth_value V d Q Y g hd hQ hY hV hVs]
  simp_rw [heq] at he
  simpa only [K,pair_product,F,G,Factor.smooth] using he

end
end Candidate.SilPrior.FourthPower.ReferenceProfileEnergy
