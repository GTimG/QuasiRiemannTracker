/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Weighted original-sublattice common-profile frame bound from the actual
StrongPair sixth-free leaves. The original label set, original divisor
fibre weight, two independent heights and original profile controls remain.
Adapted from Sil weighted class separation and the checked raw ball opening.
-/
import Candidate.C092.transport.RegularColoredFrameRaw
import Candidate.C092.transport.GroupedPairClassControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open LocalMoment ProbePhysical Record12518109GainRoot
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstAmplificationChoice QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet
open ProfileSeparation (commonPair scale pairWeight scale_pos)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local notation "mask₀" => fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameClass_82420c23d22b36d0_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem frame_raw_class_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (rayM : Id) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (ε : ℝ) (hε : 0<ε) (J : ℕ) :
    ∃ S : Finset (ℕ×ℕ), ∃ Kprofile C : ℝ, 0<Kprofile ∧ 0<C ∧ ∀ (U M H loss : ℝ),1<U → 0≤M → M≤2 →
    ∀ (η₁ η₂ ηmark base : Character) (θ : ι→RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ)
      (t₁ t₂ tMark Y₁ Y₂ K : ℝ) (keep : O→Prop),
      (∀z,keep z→z≠0) → (∀i,0≤w i) → (∀i,0≤σ i) →
      0<Y₁ → 0<Y₂ → 0≤K →
      ∀ {Λ : Type*} (labels : Finset Λ) (weight : Λ→ℝ)
        (hweight : ∀x,0≤weight x) (V : Λ→O) (Krow X₁ X₂ : Λ→ℝ)
        (p₀ p₁ : 𝓢(ℝ,ℂ)),
        Function.support (p₀:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) →
        Function.support (p₁:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) →
        (∀x∈labels,0<((Ideal.span {V x}).absNorm:ℝ)*Krow x) →
        (∀x∈labels,2*(((Ideal.span {V x}).absNorm:ℝ)*Krow x)≤U^M) →
        (∀x∈labels,0<X₁ x ∧ Y₁/2≤X₁ x ∧ X₁ x≤Y₁ ∧
          0<X₂ x ∧ Y₂/2≤X₂ x ∧ X₂ x≤Y₂) →
        ∀ D : ℝ,0≤D →
        (∀y:O,y≠0 → ‖eisEmbedding y‖^2≤U^M →
          ∑x∈labels.filter (fun x=>V x∣y),weight x≤D) →
      let mark := fun i z=>normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
      (∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (R:Finset NonzeroFrequency),
        (∀z∈R,keep z.val ∧ rawFrequencyNorm z≤U^M) →
        ∀ B : HeckeInverseAmplification.NonzeroIdeal,(sixthFreeFiber R B).Nonempty →
        ∀ D∈IdealMobiusDivisorSum.idealDivisors B.val,
        ∀ F∈IdealMobiusDivisorSum.idealDivisors B.val,∀ T : Finset ι,
          StrongPair.finiteEnergyOn T (sixthFreeFiber R B) η₁ η₂
            ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) t₁ t₂
            ((scale e.1*Y₁)/(D.absNorm:ℝ)) ((scale e.2*Y₂)/(F.absNorm:ℝ))
            (fun i r=>mark i r.val) ≤ K*pairWeight J τ*
              U^(coreWidth U M B+loss+(5/6)*max 0 (H-coreWidth U M B))) →
      (∑x∈labels,weight x * GroupedPair.pairEnergy η₁ η₂ mask₀ 1 1 (fun z=>∏i,mark i z)
        t₁ t₂ p₀ p₁ (X₁ x) (X₂ x) (fun y=>V x∣y ∧ keep y) ballProfile
        (((Ideal.span {V x}).absNorm:ℝ)*Krow x)) ≤
        (4*D)*C*K*Kprofile*(sourceControl S p₀*sourceControl S p₁)^2*
          U^(M+loss+(5/6)*max 0 (H-M)+ε) := by
  obtain ⟨C,hC,hraw⟩ := frame_raw_common_source (ι:=ι) rayM Hr hHr W hW hsW ε hε
  obtain ⟨S,Kprofile,hKprofile,hcontrol⟩ := GroupedPair.majorant_masses_control J
  refine ⟨S,Kprofile,C,hKprofile,hC,?_⟩
  intro U M H loss hU hM hM₂ η₁ η₂ ηmark base θ w σ v t₁ t₂ tMark Y₁ Y₂ K keep
    hkeep hw hσ hY₁ hY₂ hK Λ labels weight hweight V Krow X₁ X₂ p₀ p₁ hs₀ hs₁
    hKrow hscale hX D hD0 hD
  let mark := fun i z=>normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
    (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
  dsimp only
  intro hstrong
  have hrawsource := hraw U M H loss hU hM hM₂ η₁ η₂ ηmark base θ w σ v
    t₁ t₂ tMark Y₁ Y₂ K J keep hkeep hw hσ hY₁ hY₂ hK hstrong
  have hpower : 0≤U^(M+loss+(5/6)*max 0 (H-M)+ε) := Real.rpow_nonneg (zero_lt_one.trans hU).le _
  have hb := GroupedPair.class_bound η₁ η₂ mask₀ 1 1 (fun z=>∏i,mark i z)
    t₁ t₂ keep hkeep p₀ p₁ hs₀ hs₁ Y₁ Y₂ (U^M) hY₁ hY₂
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) labels weight hweight V Krow hKrow hscale
    X₁ X₂ hX D hD0 hD (C*K) (U^(M+loss+(5/6)*max 0 (H-M)+ε)) J
    (mul_nonneg hC.le hK) hpower hrawsource
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (hcontrol p₀ p₁ hs₀ hs₁)
    (show 0≤(4*D)*(C*K)*U^(M+loss+(5/6)*max 0 (H-M)+ε) by positivity)
  convert hh using 1 <;> ring

#print axioms frame_raw_class_bound
end
end QRH.Cycle092.RegularColoredForward
