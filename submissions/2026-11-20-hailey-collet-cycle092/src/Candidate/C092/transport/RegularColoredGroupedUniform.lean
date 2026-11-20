/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
One original control set and class constant for every surviving slot subset.
The bound keeps the actual native labels and independent StrongPair fiber leaves.
-/
import Candidate.C092.transport.RegularColoredFrameEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredGroupedUniform_cdfd1ade28e66a77_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}

theorem frame_native_class_uniform (θ : GData L)
    (εraw : ℝ) (hεraw : 0<εraw) (J : ℕ) :
    ∃ controls : Finset (ℕ×ℕ),∃ Cclass : ℝ,0<Cclass ∧
    ∀ A : Finset (Fin θ.N),
    ∀ (mesh Z : ℝ) (η ω₁ ω₂ : Character) (r : GSrc θ mesh Z) (v : ℝ) (j : DictIdx)
      (M H loss K Cred εred δ D : ℝ),
      0≤M → M≤2 → 0≤K → 0≤Cred → 0≤δ → 0≤D →
    ∀ (labels : Finset (GLabel θ mesh Z)),
      (∀x∈labels,Fits η r x) →
      (∀x∈labels,2*(((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*dyadicScale (x.n 1))≤Z^M) →
    ∀ (X₁ X₂ : GLabel θ mesh Z→ℝ) (Y₁ Y₂ : ℝ),0<Y₁ → 0<Y₂ →
      (∀x∈labels,0<X₁ x ∧ Y₁/2≤X₁ x ∧ X₁ x≤Y₁ ∧
        0<X₂ x ∧ Y₂/2≤X₂ x ∧ X₂ x≤Y₂) →
      (∀y:O,y≠0 → ‖eisEmbedding y‖^2≤Z^M →
        ∑x∈labels.filter (fun x=>x.twist∣y),gWeight x≤D) →
      let mark := fun (i:A) y=>normalizedSlot (anchors η j) pmask 1 y
        (originalPools θ.rayM θ.Hray 2 Z (fun i:A=>r.w i.val) i)
        (originalCoefficients θ.rayM θ.Hray θ.hH θ.η₀ (fun i:A=>r.χ i.val) θ.W Z
          (fun i:A=>r.w i.val) (fun i:A=>r.σ i.val) (fun i:A=>r.freq i.val) i) (r.t+v) (Z^(r.w i.val))
      (∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (R:Finset NonzeroFrequency),
        (∀z∈R,initialKeep (anchors η j) (internalQ θ.Q θ.η₀) z.val ∧ rawFrequencyNorm z≤Z^M) →
        ∀ B : HeckeInverseAmplification.NonzeroIdeal,(sixthFreeFiber R B).Nonempty →
        ∀ D₁∈IdealMobiusDivisorSum.idealDivisors B.val,
        ∀ D₂∈IdealMobiusDivisorSum.idealDivisors B.val,∀ T : Finset A,
          StrongPair.finiteEnergyOn T (sixthFreeFiber R B) ((anchors η j).product ω₁) ((anchors η j).product ω₂)
            ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
            (2*Real.pi*(r.t₁+v/(2*Real.pi))) (2*Real.pi*(r.t₂+v/(2*Real.pi)))
            ((scale e.1*Y₁)/(D₁.absNorm:ℝ)) ((scale e.2*Y₂)/(D₂.absNorm:ℝ))
            (fun i u=>mark i u.val) ≤ K*pairWeight J τ*
              Z^(coreWidth Z M B+loss+(5/6)*max 0 (H-coreWidth Z M B))) →
      (∑x∈labels,frameExtractionWeight Cred εred δ r x*
        frameChildE ω₁ ω₂ η r v j A (X₁ x) (X₂ x) (r.V₀*x.twist) (dyadicScale (x.n 1))) ≤
      (4*(Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D))*Cclass*K*
        (sourceControl controls r.W₁*sourceControl controls r.W₂)^2*
          Z^(M+loss+(5/6)*max 0 (H-M)+εraw) := by
  classical
  have hex : ∀ A : Finset (Fin θ.N), ∃ controls : Finset (ℕ×ℕ),∃ Kprofile Craw : ℝ,
      0<Kprofile ∧ 0<Craw ∧ _ := fun A=>frame_native_class_bound θ A εraw hεraw J
  choose S kp cr hkp hcr hc using hex
  let controls : Finset (ℕ×ℕ) := Finset.univ.biUnion S
  let Cclass : ℝ := ∑ A : Finset (Fin θ.N),cr A*kp A
  have hcoeff (A : Finset (Fin θ.N)) : cr A*kp A≤Cclass :=
    Finset.single_le_sum (fun B _=>mul_nonneg (hcr B).le (hkp B).le) (Finset.mem_univ A)
  have hCclass : 0<Cclass := lt_of_lt_of_le (mul_pos (hcr ∅) (hkp ∅)) (hcoeff ∅)
  refine ⟨controls,Cclass,hCclass,?_⟩
  intro A mesh Z η ω₁ ω₂ r v j M H loss K Cred εred δ D hM hM₂ hK hCred hδ hD
    labels hfit hscale X₁ X₂ Y₁ Y₂ hY₁ hY₂ hX hfibre
  dsimp only
  intro hstrong
  have hb := hc A mesh Z η ω₁ ω₂ r v j M H loss K Cred εred δ D hM hM₂ hK hCred hδ hD
    labels hfit hscale X₁ X₂ Y₁ Y₂ hY₁ hY₂ hX hfibre hstrong
  have hsub : S A⊆controls := fun a ha=>Finset.mem_biUnion.mpr ⟨A,Finset.mem_univ A,ha⟩
  have hsc (W : 𝓢(ℝ,ℂ)) : sourceControl (S A) W≤ sourceControl controls W :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) W
  have hpr : (sourceControl (S A) r.W₁*sourceControl (S A) r.W₂)^2≤
      (sourceControl controls r.W₁*sourceControl controls r.W₂)^2 :=
    pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
      (mul_le_mul (hsc r.W₁) (hsc r.W₂) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)) 2
  have hp : 0≤4*(Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D)*K := by
    have := Real.rpow_nonneg (zero_lt_one.trans r.hZ).le (εred+3*δ*θ.Bmask)
    have := (r.vol_pos (zero_lt_one.trans r.hZ)).le
    positivity
  have hz : 0≤Z^(M+loss+(5/6)*max 0 (H-M)+εraw) :=
    Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _
  apply hb.trans
  calc _ = (4*(Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D)*K)*(cr A*kp A)*
      (sourceControl (S A) r.W₁*sourceControl (S A) r.W₂)^2*
        Z^(M+loss+(5/6)*max 0 (H-M)+εraw) := by ring
    _ ≤ (4*(Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D)*K)*Cclass*
      (sourceControl controls r.W₁*sourceControl controls r.W₂)^2*
        Z^(M+loss+(5/6)*max 0 (H-M)+εraw) := by
      apply mul_le_mul_of_nonneg_right _ hz
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hcoeff A) hp) hpr
        (sq_nonneg _) (mul_nonneg hp hCclass.le)
    _ = _ := by ring

#print axioms frame_native_class_uniform
end
end QRH.Cycle092.RegularColoredForward
