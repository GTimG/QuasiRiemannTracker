/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The independently colored regular class on the actual native label set.
Native extraction weights and the original weighted divisor fibre remain;
its only analytic leaves are actual StrongPair finite energies on the
original sixth-free cofactor fibers and independent shortened lengths.
-/
import Candidate.C092.transport.RegularColoredFrameMass

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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameNativeClass_baf14a9ef5f2c414_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}

theorem frame_native_class_bound (θ : GData L) (A : Finset (Fin θ.N))
    (εraw : ℝ) (hεraw : 0<εraw) (J : ℕ) :
    ∃ controls : Finset (ℕ×ℕ),∃ Kprofile Craw : ℝ,0<Kprofile ∧ 0<Craw ∧
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
      (4*(Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D))*Craw*K*Kprofile*
        (sourceControl controls r.W₁*sourceControl controls r.W₂)^2*
          Z^(M+loss+(5/6)*max 0 (H-M)+εraw) := by
  obtain ⟨S,Kprofile,Craw,hKprofile,hCraw,hclass⟩ := frame_raw_class_bound (ι:=A)
    θ.rayM θ.Hray θ.hH θ.W θ.hW.continuous θ.hWs εraw hεraw J
  refine ⟨S,Kprofile,Craw,hKprofile,hCraw,?_⟩
  intro mesh Z η ω₁ ω₂ r v j M H loss K Cred εred δ D hM hM₂ hK hCred hδ hD
    labels hfit hscale X₁ X₂ Y₁ Y₂ hY₁ hY₂ hX hfibre
  dsimp only
  intro hstrong
  have hsourcekeep : ∀y:O,initialKeep (anchors η j) (internalQ θ.Q θ.η₀) y → y≠0 := fun y hy=>hy.1
  have hKrow (x : GLabel θ mesh Z) (hx : x∈labels) :
      0<((Ideal.span {r.V₀*x.twist}).absNorm:ℝ)*dyadicScale (x.n 1) := by
    have hn : 0<((Ideal.span {r.V₀*x.twist}).absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero r.hV₀ (hfit x hx).twist_ne)))
    exact mul_pos hn (dyadicScale_pos _)
  have hs₁ : Function.support (r.W₁:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) :=
    r.hs₁.trans (Set.Icc_subset_Icc θ.ha θ.hb)
  have hs₂ : Function.support (r.W₂:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) :=
    r.hs₂.trans (Set.Icc_subset_Icc θ.ha θ.hb)
  have hDf : 0≤Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D := by
    have hp := (r.vol_pos (zero_lt_one.trans r.hZ)).le
    have hz := Real.rpow_nonneg (zero_lt_one.trans r.hZ).le (εred+3*δ*θ.Bmask)
    positivity
  have hb := hclass Z M H loss r.hZ hM hM₂ ((anchors η j).product ω₁) ((anchors η j).product ω₂)
    (anchors η j) θ.η₀ (fun i:A=>r.χ i.val) (fun i:A=>r.w i.val) (fun i:A=>r.σ i.val)
    (fun i:A=>r.freq i.val) (2*Real.pi*(r.t₁+v/(2*Real.pi)))
    (2*Real.pi*(r.t₂+v/(2*Real.pi))) (r.t+v) Y₁ Y₂ K
    (initialKeep (anchors η j) (internalQ θ.Q θ.η₀)) hsourcekeep (fun i=>r.hw i.val)
    (fun i=>by have hh:=(r.hσ i.val).ge; linarith) hY₁ hY₂ hK
    labels (frameExtractionWeight Cred εred δ r) (frameExtractionWeight_nonneg Cred εred δ hCred r)
    (fun x=>r.V₀*x.twist) (fun x=>dyadicScale (x.n 1)) X₁ X₂ r.W₁ r.W₂ hs₁ hs₂ hKrow hscale hX
    (Cred*Z^(εred+3*δ*θ.Bmask)*r.vol*D) hDf
    (fun y hy hY=>frameExtractionWeight_fibre Cred εred δ D hCred hδ η r labels hfit y (hfibre y hy hY))
    hstrong
  have hprod (y : O) :
      (∏i∈A,normalizedSlot (anchors η j) pmask 1 y
        (CenteredMomentPrimeSlot.primePool θ.rayM θ.Hray 2 (Z^(r.w i)))
        (slotBeta θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq i) (r.t+v) (Z^(r.w i))) =
      ∏i:A,normalizedSlot (anchors η j) pmask 1 y
        (CenteredMomentPrimeSlot.primePool θ.rayM θ.Hray 2 (Z^(r.w i.val)))
        (slotBeta θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq i.val) (r.t+v) (Z^(r.w i.val)) :=
    (Finset.prod_coe_sort A _).symm
  unfold frameChildE
  simp_rw [hprod]
  exact hb

#print axioms frame_native_class_bound
end
end QRH.Cycle092.RegularColoredForward
