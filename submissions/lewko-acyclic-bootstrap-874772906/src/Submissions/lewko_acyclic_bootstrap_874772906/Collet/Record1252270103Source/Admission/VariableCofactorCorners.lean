/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Heterogeneous centered Newton families with independent corner budgets. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FamilyNewton
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.VariableRestoration
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => ActualEisensteinCubic.O
variable {ι Row : Type*} [Fintype ι]

theorem newton_positive_variable_two_corner_family
    (rows : Finset Row) (τ : Row→Character) (t weight : Row→ℝ) (z : Row→O)
    (hw : ∀u∈rows,0≤weight u) (R A₁ A₂ : Row→Ideal O)
    (hA₁ : ∀u∈rows,A₁ u≠0) (hA₂ : ∀u∈rows,A₂ u≠0)
    (hAR : ∀u∈rows,A₁ u*A₂ u∣R u) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b : ℝ) (hb : 0≤b)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (X₁ X₂ Y₁ Y₂ : Row→ℝ)
    (hX : ∀u∈rows,0<X₁ u ∧ 0<X₂ u) (hY : ∀u∈rows,0<Y₁ u ∧ 0<Y₂ u)
    (hXY : ∀u∈rows,Y₁ u*Y₂ u=X₁ u*X₂ u)
    (Eₓ Eᵧ δ B U : ℝ) (hEₓ : 0≤Eₓ) (hEᵧ : 0≤Eᵧ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : ∀u∈rows,b^2*X₁ u*X₂ u≤U^B)
    (hordinaryX : ∀Z₁ Z₂ : Row→ℝ,
      (∀u∈rows,0<Z₁ u ∧ 0<Z₂ u ∧ Z₁ u≤X₁ u ∧ Z₂ u≤X₂ u) →
      (∑u∈rows,‖positiveSlotRow (τ u) (fixedBadMask*idealGenerator (R u*(d.1*d.2)))
        1 (z u) W₁ W₂ S β P (t u) (Z₁ u) (Z₂ u)‖^2*weight u)≤Eₓ)
    (hordinaryY : ∀Z₁ Z₂ : Row→ℝ,
      (∀u∈rows,0<Z₁ u ∧ 0<Z₂ u ∧ Z₁ u≤Y₁ u ∧ Z₂ u≤Y₂ u) →
      (∑u∈rows,‖positiveSlotRow (τ u) (fixedBadMask*idealGenerator (R u*(d.1*d.2)))
        1 (z u) W₁ W₂ S β P (t u) (Z₁ u) (Z₂ u)‖^2*weight u)≤Eᵧ) :
    (∑u∈rows,‖newtonPositiveChild (τ u) (R u) (A₁ u) (A₂ u) d W₁ W₂ b S β P
      (t u) (X₁ u) (X₂ u) (Y₁ u) (Y₂ u) (z u)‖^2*weight u)≤
      2*(holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
        eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*(Eₓ+Eᵧ) := by
  let m := fun u=>fixedBadMask*idealGenerator (R u*(d.1*d.2))
  let f := fun u=>squarefreePositiveSlotRow (τ u) (m u) 1 (z u) W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)
  let g := fun u=>squarefreePositiveSlotRow (τ u) (m u) 1 (z u) W₁ W₂ b S β P (t u) (Y₁ u) (Y₂ u)
  have hc (u : Row) : ‖((squarefreeIndicator ((A₁ u*d.1)*(A₂ u*d.2)):ℂ)*
      ordinaryHoleIndicator (A₁ u*d.1) (A₂ u*d.2))‖^2≤1 := by
    unfold squarefreeIndicator ordinaryHoleIndicator
    split_ifs <;> norm_num
  have hn (u : Row) (hu : u∈rows) :
      ‖newtonPositiveChild (τ u) (R u) (A₁ u) (A₂ u) d W₁ W₂ b S β P
        (t u) (X₁ u) (X₂ u) (Y₁ u) (Y₂ u) (z u)‖^2≤2*(‖f u‖^2+‖g u‖^2) := by
    rw [newton_positive_child_row (τ u) (R u) (A₁ u) (A₂ u) (hA₁ u hu) (hA₂ u hu)
      (hAR u hu) d hd W₁ W₂ b hb hs₁ hs₂ S β P hP havoid (t u)
      (X₁ u) (X₂ u) (Y₁ u) (Y₂ u) (hX u hu).1 (hX u hu).2
      (hY u hu).1 (hY u hu).2 (hXY u hu) (z u),norm_mul,mul_pow]
    apply (mul_le_of_le_one_left (sq_nonneg _) (hc u)).trans
    change ‖f u-g u‖^2≤_
    have hh:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f u) (g u)) 2
    nlinarith [sq_nonneg (‖f u‖-‖g u‖)]
  have hx:=forward_finite_family_variable_rankin rows τ m (fun _=>1) z t weight hw
    W₁ W₂ b hs₁ hs₂ S β P hP X₁ X₂ hX Eₓ hEₓ δ B U hδ hB hU hcut
    hordinaryX
  have hy:=forward_finite_family_variable_rankin rows τ m (fun _=>1) z t weight hw
    W₁ W₂ b hs₁ hs₂ S β P hP Y₁ Y₂ hY Eᵧ hEᵧ δ B U hδ hB hU
    (by intro u hu;simpa only [mul_assoc,hXY u hu] using hcut u hu)
    hordinaryY
  have hh : (∑u∈rows,‖newtonPositiveChild (τ u) (R u) (A₁ u) (A₂ u) d W₁ W₂ b S β P
      (t u) (X₁ u) (X₂ u) (Y₁ u) (Y₂ u) (z u)‖^2*weight u)≤
      2*((∑u∈rows,‖f u‖^2*weight u)+(∑u∈rows,‖g u‖^2*weight u)) := by
    rw [←Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_le_sum (fun u hu=>(mul_le_mul_of_nonneg_right (hn u hu) (hw u hu)).trans_eq (by ring))
  exact hh.trans (by dsimp only [f,g] at *;linarith)

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.newton_positive_variable_two_corner_family
