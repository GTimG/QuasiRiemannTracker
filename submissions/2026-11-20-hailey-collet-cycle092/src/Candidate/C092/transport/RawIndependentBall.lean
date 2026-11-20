/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual packed finite frequency ball, before any free-core restriction.
The per-core suppliers see precisely the classes and shortened slots left
by the cofactor identity. -/
import Candidate.C092.transport.RawIndependentFiber
import Candidate.C092.transport.MeasuredBall
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion IdealMobiusDivisorSum
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
namespace QRH.Cycle092.RawIndependentFiber
local notation "O" => HeckeFamily.O
local notation "mask₀" => fixedBadMask*idealGenerator 1
local instance c092LocalInst_Candidate_C092_transport_RawIndependentBall_75a3a17b6a7dd2e1_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem packed_raw_from_free_classes {ι : Type} [Fintype ι] [DecidableEq ι]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U M H loss : ℝ, 1<U → 0≤M → M≤2 →
    ∀ (η₁ η₂ ηmark base : Character) (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (t₁ t₂ tMark X₁ X₂ b₁ b₂ K : ℝ) (R : Finset NonzeroFrequency),
      (∀ i,0≤w i) → (∀ i,0≤σ i) → Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0≤K → (∀ z∈R,rawFrequencyNorm z ≤ U^M) →
      let mark := fun i z => normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
      (∀ B : HeckeInverseAmplification.NonzeroIdeal, (sixthFreeFiber R B).Nonempty →
        ∀ D∈idealDivisors B.val,∀ F∈idealDivisors B.val,∀ T : Finset ι,
        StrongPair.finiteEnergyOn T (sixthFreeFiber R B) η₁ η₂ W₁ W₂ t₁ t₂
          (X₁/(D.absNorm:ℝ)) (X₂/(F.absNorm:ℝ)) (fun i r => mark i r.val)
            ≤ K*U^(coreWidth U M B+loss+(5/6)*max 0 (H-coreWidth U M B))) →
      (∑ z∈R,(∏ i, ‖mark i z.val‖^2) *
        ‖original η₁ mask₀ 1 z.val W₁ t₁ X₁ * original η₂ mask₀ 1 z.val W₂ t₂ X₂‖^2)
          ≤ C*K*U^(M+loss+(5/6)*max 0 (H-M)+ε) := by
  let δ := ε/3
  have hd : 0<δ := div_pos hε (by norm_num)
  obtain ⟨A,hA,harm⟩ := grouped_ball δ hd
  obtain ⟨D,hD,hf⟩ := actual_independent_fiber (ι:=ι) rayM Hr hHr W hW hsW 2 δ (by norm_num) hd
  refine ⟨A*D,mul_pos hA hD,?_⟩
  intro U M H loss hU hM hM' η₁ η₂ ηmark base θ w σ v W₁ W₂ t₁ t₂ tMark X₁ X₂ b₁ b₂ K R hw hσ h₁ h₂ hX hY hK hR
  let mark := fun i z => normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
    (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
  let f := fun z : NonzeroFrequency => (∏ i, ‖mark i z.val‖^2) *
    ‖original η₁ mask₀ 1 z.val W₁ t₁ X₁ * original η₂ mask₀ 1 z.val W₂ t₂ X₂‖^2
  dsimp only
  intro hfree
  have hUp := zero_lt_one.trans hU
  have hraw := harm R f U M H (loss+δ) (D*K) hU hM (mul_nonneg hD.le hK) hR (by
    intro B hB
    obtain ⟨u,hu⟩ := hB
    have hN : 1 ≤ (B.val.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have ht := hR _ (MeasuredBall.fiber_mem hu)
    rw [raw_sixth_norm] at ht
    have h₆ : (B.val.absNorm:ℝ)^6 ≤ U^M := by
      have hpositive : 0≤(B.val.absNorm:ℝ)^6 := by positivity
      nlinarith only [ht,mul_nonneg (sub_nonneg.mpr (rowNorm_ge_one u)) hpositive]
    have hBnorm : (B.val.absNorm:ℝ) ≤ U^(2:ℝ) := calc
      _ = (B.val.absNorm:ℝ)^1 := (pow_one _).symm
      _ ≤ (B.val.absNorm:ℝ)^6 := pow_le_pow_right₀ hN (by norm_num)
      _ ≤ _ := h₆.trans (Real.rpow_le_rpow_of_exponent_le hU.le hM')
    let V := coreWidth U M B
    let m := (5/6:ℝ)*max 0 (H-V)
    have hr := hf U hU.le B hBnorm η₁ η₂ ηmark base θ w σ v W₁ W₂ t₁ t₂ tMark X₁ X₂ b₁ b₂
      (K*U^(V+loss+m)) (sixthFreeFiber R B) hw hσ h₁ h₂ hX hY (mul_nonneg hK (Real.rpow_nonneg hUp.le _))
      (hfree B ⟨u,hu⟩)
    refine hr.trans_eq ?_
    change D*U^δ*(K*U^(V+loss+m))=D*K*U^(V+(loss+δ)+m)
    rw [show V+(loss+δ)+m=δ+(V+loss+m) by ring,Real.rpow_add hUp δ (V+loss+m)];ring)
  apply hraw.trans
  rw [show D*K*A=A*D*K by ring]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le ?_) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hM' hd.le
  dsimp only [δ] at hscaled ⊢; linarith

#print axioms packed_raw_from_free_classes
end QRH.Cycle092.RawIndependentFiber
end
