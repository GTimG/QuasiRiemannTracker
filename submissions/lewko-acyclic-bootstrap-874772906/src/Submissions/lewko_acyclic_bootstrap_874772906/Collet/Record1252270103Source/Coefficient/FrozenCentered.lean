/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Frozen ordinary factors become a literal exclusion mask in the same centered
row. The squarefree and fixed small-prime projectors are retained exactly. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.ExcludedCharacterSource

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O

theorem ordinaryHoleIndicator_frozen (A₁ A₂ I J : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hI : I≠0) (hJ : J≠0)
    (hh : ordinarySmallHole I J) :
    ordinaryHoleIndicator (A₁*I) (A₂*J)=ordinaryHoleIndicator A₁ A₂ := by
  have he : ordinarySmallHole (A₁*I) (A₂*J) ↔ ordinarySmallHole A₁ A₂ := by
    unfold ordinarySmallHole
    simp only [valuation_mul hA₁ hI,valuation_mul hA₂ hJ]
    constructor <;> intro h P hP
    · simpa only [(hh P hP).1,(hh P hP).2,add_zero] using h P hP
    · simpa only [(hh P hP).1,(hh P hP).2,add_zero] using h P hP
  simp only [ordinaryHoleIndicator,he]

theorem rowWeight_excluded_mask (η χ : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (R : Ideal O) (hR : R≠0) (t : ℝ) (I : Ideal O) :
    rowWeight η (m*idealGenerator R) A z t I=
      rowWeight η m A z t I*(if IsCoprime I R then 1 else 0) := by
  have he := idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at he
  have he' := excluded_character_row_ideal η χ m A z hml hm2 hrow R hR I
  change (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*
      (I.absNorm:ℂ)^(Complex.I*t)=_
  rw [←he',excluded_character_ideal χ R hR I,he]
  change (_*(if IsCoprime I R then 1 else 0))*_=_
  split_ifs <;> simp only [mul_one,mul_zero,zero_mul] <;> rfl

theorem squarefree_frozen_mask (A₁ A₂ I J : Ideal O) :
    (squarefreeIndicator ((A₁*I)*(A₂*J)):ℂ)=
      (squarefreeIndicator (A₁*A₂):ℂ)*(squarefreeIndicator (I*J):ℂ)*
        (if IsCoprime (I*J) (A₁*A₂) then 1 else 0) := by
  simp only [squarefreeIndicator_cast]
  rw [show (A₁*I)*(A₂*J)=(A₁*A₂)*(I*J) by ring,
    QRH.Record1252270103TwoIdeal.squarefreeIndicator_mul]
  congr 1
  unfold QRH.Record1252270103TwoIdeal.coprimalityIndicator
  congr 1
  apply propext
  constructor
  · intro h
    apply IsCoprime.symm
    apply Ideal.isCoprime_iff_gcd.mpr
    simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp
      (h (GCDMonoid.gcd_dvd_left _ _) (GCDMonoid.gcd_dvd_right _ _))
  · exact fun h=>h.symm.isRelPrime

theorem centeredSquarefreeRow_common_pool (η : Character) (m A z : O)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T : ℝ) (hb : 0≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    centeredSquarefreeRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T=
      (Real.sqrt T:ℂ)⁻¹*∑n∈commonPool b X₁ X₂ Y₁ Y₂,
        (squarefreeIndicator (n.1*n.2):ℂ)*rowWeight η m A z t (n.1*n.2)*
          centeredProfile W₁ W₂ X₁ X₂ Y₁ Y₂ n := by
  unfold centeredSquarefreeRow commonPool centeredProfile
  rw [squarefreePlainSum_eq_hole_sum,squarefreePlainSum_eq_hole_sum,
    hole_pair_sum_pad W₁ W₂ b X₁ X₂ (max X₁ Y₁) (max X₂ Y₂) hb hX₁ hX₂
      (le_max_left _ _) (le_max_left _ _) hs₁ hs₂,
    hole_pair_sum_pad W₁ W₂ b Y₁ Y₂ (max X₁ Y₁) (max X₂ Y₂) hb hY₁ hY₂
      (le_max_right _ _) (le_max_right _ _) hs₁ hs₂,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem frozenCenteredRow_excluded (η χ : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T : ℝ) (hb : 0≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    frozenCenteredRow (rowWeight η m A z t) W₁ W₂ A₁ A₂ b X₁ X₂ Y₁ Y₂ T=
      ((squarefreeIndicator (A₁*A₂):ℂ)*ordinaryHoleIndicator A₁ A₂)*
        centeredSquarefreeRow η (m*idealGenerator (A₁*A₂)) A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T := by
  rw [centeredSquarefreeRow_common_pool η (m*idealGenerator (A₁*A₂)) A z W₁ W₂
    b t X₁ X₂ Y₁ Y₂ T hb hX₁ hX₂ hY₁ hY₂ hs₁ hs₂]
  unfold frozenCenteredRow
  rw [mul_left_comm _ ((Real.sqrt T:ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hg := holePairPool_good hn
  have hh := (ordinarySmallHole_iff_good hg.1 hg.2.1).mpr hg
  unfold frozenProfile
  rw [ordinaryHoleIndicator_frozen A₁ A₂ n.1 n.2 hA₁ hA₂ hg.1 hg.2.1 hh,
    squarefree_frozen_mask,
    rowWeight_excluded_mask η χ m A z hml hm2 hrow (A₁*A₂) (mul_ne_zero hA₁ hA₂)]
  ring

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.frozenCenteredRow_excluded
