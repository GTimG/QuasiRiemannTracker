/- Copyright (c) 2026 Sil. Apache-2.0.
One homogeneous ordinary-profile/height factor for all four genuine
small Gauss providers. Fixed marked-profile bounds precede moving data.

-/
import Candidate.SilPrior.FourthPower.RepairedSmallCostControl
import Candidate.SilPrior.FourthPower.MixedInnerExceptionalLedger
import Candidate.SilPrior.FourthPower.MixedPrincipalBudget

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedSmallCommonProfile
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondWindowBudget
open MixedPrincipalPair MixedPrincipalBudget MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedOriginalTail MixedFirstProfileEnvelope
open RepairedSmallRawBudget RepairedSmallCostControl
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def commonProfile (s : Source ι a b) (J : ℕ) (U : Finset (ℕ×ℕ)) (t₀ V v : ℝ) : ℝ :=
  (sourceControl U s.W₁*sourceControl U s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J*heightEnvelope v^(2*J)

theorem common_profile_nonneg (s : Source ι a b) (J : ℕ) (U : Finset (ℕ×ℕ))
    (t₀ V v : ℝ) (hV : 0≤V) : 0≤commonProfile s J U t₀ V v := by
  have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
  have hv := (heightEnvelope_pos v).le
  unfold commonProfile
  positivity

theorem profile_powers_le (s : Source ι a b) (j k J : ℕ)
    (T U : Finset (ℕ×ℕ)) (t₀ V v : ℝ) (hT : T⊆U) (hj : j≤J) (hk : k≤2*J) (hV : 0≤V) :
    (sourceControl T s.W₁*sourceControl T s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^j*heightEnvelope v^k≤commonProfile s J U t₀ V v := by
  have hp := pow_le_pow_left₀
    (mul_nonneg (sourceControl_nonneg T s.W₁) (sourceControl_nonneg T s.W₂))
    (mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hT) s.W₁)
      (Seminorm.le_def.mp (Finset.sup_mono hT) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)) 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hh := pow_le_pow_right₀ hheight hj
  have hv := pow_le_pow_right₀ (height_envelope_one v) hk
  have hheight0 := zero_le_one.trans hheight
  exact mul_le_mul
    (mul_le_mul hp hh (pow_nonneg (zero_le_one.trans hheight) _) (sq_nonneg _)) hv
    (pow_nonneg (heightEnvelope_pos v).le _) (by positivity)

theorem marked_product_le (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot) :
    (∏i,s.M i)≤Kslot^N := by
  calc
    _≤∏_i : ι,Kslot := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.hM i))
      (fun i _=>hM i)
    _=Kslot^Fintype.card ι := by simp only [Finset.prod_const,Finset.card_univ]
    _≤Kslot^N := pow_le_pow_right₀ hK hN

theorem slot_cost_le (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot) :
    slotCost s≤(Kslot^N)^2*(2:ℝ)^N := by
  have hp := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i)))
    (marked_product_le s N Kslot hN hK hM) 2
  exact mul_le_mul hp (pow_le_pow_right₀ (by norm_num) hN) (by positivity) (sq_nonneg _)

theorem marked_cost_le (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot) :
    fullMarkedCost s≤(1024:ℝ)^N*(Kslot^N)^3 := by
  rw [fullMarkedCost_eq]
  have hm0 : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hN)
    (pow_le_pow_left₀ hm0 (marked_product_le s N Kslot hN hK hM) 3)
    (pow_nonneg hm0 3) (by positivity)

theorem profile_cap_le (s : Source ι a b) (N J : ℕ) (Kslot : ℝ)
    (U : Finset (ℕ×ℕ)) (h00 : (0,0)∈U) (t₀ V v : ℝ)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot) (hV : 0≤V) :
    (profileCap s)^2≤(4*(Kslot^N)^2)*commonProfile s J U t₀ V v := by
  have hp : (sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂)^2≤
      commonProfile s J U t₀ V v := by
    simpa only [pow_zero,mul_one] using profile_powers_le s 0 0 J {(0,0)} U t₀ V v
      (Finset.singleton_subset_iff.mpr h00) (Nat.zero_le _) (Nat.zero_le _) hV
  have hm := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i)))
    (marked_product_le s N Kslot hN hK hM) 2
  have he := mul_le_mul hp hm (sq_nonneg _) (common_profile_nonneg s J U t₀ V v hV)
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤4)
  convert hh using 1 <;> (try unfold profileCap) <;> (try unfold supControl) <;> ring

theorem exceptional_profile_le (s : Source ι a b) (N j J : ℕ) (Kslot : ℝ)
    (T U : Finset (ℕ×ℕ)) (t₀ V v Z ε : ℝ)
    (hN : Fintype.card ι≤N) (hK : 1≤Kslot) (hM : ∀i,s.M i≤Kslot)
    (hT : T⊆U) (hj : 2*j≤J) (hV : 0≤V) (hZ : 0<Z) :
    (sourceProfile s j T Z ε)^2*heightBase v^(2*j)≤
      ((1024:ℝ)^N*(Kslot^N)^3)^2*commonProfile s J U t₀ V v*Z^(2*ε) := by
  have hheight : 1+‖s.t₁‖+‖s.t₂‖≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀]
  have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+‖s.t₁‖+‖s.t₂‖) hheight (2*j)
  have hp := profile_powers_le s (2*j) (2*j) J T U t₀ V v hT hj (by omega) hV
  have hprof : (sourceControl T s.W₁*sourceControl T s.W₂)^2*
      (1+‖s.t₁‖+‖s.t₂‖)^(2*j)*heightEnvelope v^(2*j)≤commonProfile s J U t₀ V v := by
    apply le_trans _ hp
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) (pow_nonneg (heightEnvelope_pos v).le _)
  have hm := pow_le_pow_left₀ (fullMarkedCost_nonneg s)
    (marked_cost_le s N Kslot hN hK hM) 2
  have henv := (heightEnvelope_pos v).le
  have hmain := mul_le_mul hm hprof (by positivity)
    (sq_nonneg ((1024:ℝ)^N*(Kslot^N)^3))
  have hz : (Z^ε)^2=Z^(2*ε) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hZ.le (2*ε))
  have hjpow : ((1+‖s.t₁‖+‖s.t₂‖)^j)^2=(1+‖s.t₁‖+‖s.t₂‖)^(2*j) := by
    rw [←pow_mul]
    congr 1
    omega
  calc
    _=(fullMarkedCost s)^2*((sourceControl T s.W₁*sourceControl T s.W₂)^2*
        (1+‖s.t₁‖+‖s.t₂‖)^(2*j)*heightEnvelope v^(2*j))*Z^(2*ε) := by
      unfold sourceProfile
      simp only [mul_pow,hjpow,hz,show heightBase v=heightEnvelope v by rfl]
      ring
    _≤_ := he

end
end Candidate.SilPrior.FourthPower.RepairedSmallCommonProfile
