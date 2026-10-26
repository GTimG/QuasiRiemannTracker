/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact normalized h and fixed-hole expansions preserve the centered difference
and the same presented character, including every character zero. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CenteredFinite

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeExpansion
open CenteredMomentAbsoluteEnergy
local notation "O" => HeckeFamily.O

def centeredHoleRow (η : Character) (m A z : O) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt T:ℂ)⁻¹*(ordinaryHolePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂-
    ordinaryHolePlainSum (rowWeight η m A z t) W₁ W₂ b Y₁ Y₂)

def centeredSquarefreeRow (η : Character) (m A z : O) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt T:ℂ)⁻¹*(squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂-
    squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b Y₁ Y₂)

theorem ordinary_pair_sum_twisted (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    (∑n∈plainPairPool b X₁ X₂,rowWeight η m A z t (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n)=
      twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂ := by
  rw [←ordinary_product_eq_pair_sum η m A z t W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂,
    rowTwistedSum_eq η χ m A z hrow,rowTwistedSum_eq η χ m A z hrow]

theorem centeredHoleRow_mobius (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hT : 0<T)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    centeredHoleRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T=
      ∑d∈mobiusPool,
        (mobiusSign d*rowWeight η m A z t ((mobiusPair d).1*(mobiusPair d).2)/
          (Real.sqrt (pairNorm (mobiusPair d)):ℂ))*
        centeredRectangle χ W₁ W₂ t
          (X₁/Ideal.absNorm (mobiusPair d).1) (X₂/Ideal.absNorm (mobiusPair d).2)
          (Y₁/Ideal.absNorm (mobiusPair d).1) (Y₂/Ideal.absNorm (mobiusPair d).2)
          (T/pairNorm (mobiusPair d)) := by
  unfold centeredHoleRow
  rw [hole_plain_mobius,hole_plain_mobius,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd₁ : (mobiusPair d).1≠0:=subsetProduct_nonzero _
  have hd₂ : (mobiusPair d).2≠0:=subsetProduct_nonzero _
  have hn₁ : 0<(Ideal.absNorm (mobiusPair d).1:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd₁)
  have hn₂ : 0<(Ideal.absNorm (mobiusPair d).2:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hd₂)
  rw [ordinary_pair_sum_twisted η χ m A z hrow W₁ W₂ b t _ _
      (div_pos hX₁ hn₁) (div_pos hX₂ hn₂) hs₁ hs₂,
    ordinary_pair_sum_twisted η χ m A z hrow W₁ W₂ b t _ _
      (div_pos hY₁ hn₁) (div_pos hY₂ hn₂) hs₁ hs₂]
  unfold centeredRectangle
  rw [normalized_divisor_identity T (pairNorm (mobiusPair d)) hT (pairNorm_pos hd₁ hd₂)]
  ring

theorem centeredSquarefreeRow_forward (η : Character) (m A z : O)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T : ℝ) (hb : 0≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hT : 0<T)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    centeredSquarefreeRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T=
      ∑d∈divisorPool (holePairPool b (max X₁ Y₁) (max X₂ Y₂)),
        ((forwardKernel d.1 d.2:ℂ)*rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ))*
          centeredHoleRow η m A z W₁ W₂ b t (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)
            (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2) (T/pairNorm d) := by
  unfold centeredSquarefreeRow
  rw [forward_centered_common_pool _ W₁ W₂ b X₁ X₂ Y₁ Y₂ hb hX₁ hX₂ hY₁ hY₂ hs₁ hs₂,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hg:=divisorPool_hole_good hd
  unfold centeredHoleRow
  rw [normalized_divisor_identity T (pairNorm d) hT (pairNorm_pos hg.1 hg.2.1)]
  ring

theorem mobius_row_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (d : Finset PrimeIdeal×Finset PrimeIdeal) :
    ‖mobiusSign d*rowWeight η m A z t ((mobiusPair d).1*(mobiusPair d).2)‖≤1 := by
  rw [norm_mul]
  have hs : ‖mobiusSign d‖=1 := by simp [mobiusSign,norm_pow]
  rw [hs,one_mul]
  exact rowWeight_norm_le_one_all η m A z t _

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.centeredHoleRow_mobius
#print axioms OAI.SevenEighths.Record1252270103Source.centeredSquarefreeRow_forward
