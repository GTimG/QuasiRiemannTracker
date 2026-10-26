/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The frozen row on the common maximal pool is the literal centered difference
of its original two finite rows. Compact support supplies only zero padding. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

theorem frozenCenteredRow_eq_difference (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)
    (A₁ A₂:Ideal O)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hb:0≤b)
    (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
    (hs₁:Function.support W₁⊆Set.Iic b)(hs₂:Function.support W₂⊆Set.Iic b) :
    frozenCenteredRow ψ W₁ W₂ A₁ A₂ b X₁ X₂ Y₁ Y₂ T=
      (Real.sqrt T:ℂ)⁻¹*
        ((∑n∈holePairPool b X₁ X₂,(squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*
            ψ (n.1*n.2)*ordinaryHoleIndicator (A₁*n.1) (A₂*n.2)*pairProfile W₁ W₂ X₁ X₂ n)-
         (∑n∈holePairPool b Y₁ Y₂,(squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*
            ψ (n.1*n.2)*ordinaryHoleIndicator (A₁*n.1) (A₂*n.2)*pairProfile W₁ W₂ Y₁ Y₂ n)) := by
  let κ:=fun n:IdealPair=>(squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*
    ψ (n.1*n.2)*ordinaryHoleIndicator (A₁*n.1) (A₂*n.2)
  have hx:=hole_pair_sum_pad W₁ W₂ b X₁ X₂ (max X₁ Y₁) (max X₂ Y₂) hb hX₁ hX₂
    (le_max_left _ _) (le_max_left _ _) hs₁ hs₂ κ
  have hy:=hole_pair_sum_pad W₁ W₂ b Y₁ Y₂ (max X₁ Y₁) (max X₂ Y₂) hb hY₁ hY₂
    (le_max_right _ _) (le_max_right _ _) hs₁ hs₂ κ
  unfold frozenCenteredRow
  apply congrArg (fun w:ℂ=>(Real.sqrt T:ℂ)⁻¹*w)
  change _=(∑n∈holePairPool b X₁ X₂,κ n*pairProfile W₁ W₂ X₁ X₂ n)-
    ∑n∈holePairPool b Y₁ Y₂,κ n*pairProfile W₁ W₂ Y₁ Y₂ n
  rw [hx,hy,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [κ,frozenProfile,centeredProfile]
  ring

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.frozenCenteredRow_eq_difference
