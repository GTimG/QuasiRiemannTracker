/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Actual colored regular class sums to the exact original Lambda shape. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetAssembly
import Candidate.C092.transport.PairedRetainedBudgetLambda
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondHeightFamily CenteredMomentSecondWindowBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentChildRows
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows Packet Packet.Grouped
open Second.ConcreteFrame Second.ConcreteGroup Second.ConcreteLabelAssembly Second.Concrete
open QRH.Cycle092.ColoredGaussFrameProvider QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.PairedRetainedBudget
namespace QRH.Cycle092.RegularPhysicalClassBudget
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Honest class assembly from the native grouped frame bound. Finite
multiplicity/box costs are derived for actual colored columns, and paid once. -/
theorem part_of_native_bound (ω₁ ω₂ : Character) (J : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ Cg : ℝ,0≤Cg ∧ ∀ᶠ Z : ℝ in atTop,2≤Z ∧
    ∀ {L mesh : ℝ} {θ : GData L} {η : Character} (P : SidePack η) (ξ χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z),
    rs.W₁=s.W₁ → rs.W₂=s.W₂ → rs.t₁=s.t₁/(2*Real.pi) → rs.t₂=s.t₂/(2*Real.pi) →
    rs.X₁=s.X₁ → rs.X₂=s.X₂ → rs.Y₁=s.Y₁ → rs.Y₂=s.Y₂ →
    Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d → rs.V₀=P.V → P.Cs∣s.R →
    s.H=∅ → 24≤θ.Bmask → (s.R.absNorm:ℝ)≤Z^(8:ℝ) →
    (∀I∈RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) →
    ∀ (Q : Id) (m : O),m≠0 → goodLambda∣m → (2:O)∣m → Q≤Ideal.span {(72:O)} → internalQ θ.Q θ.η₀=Q →
    ∀ (t Kc Tsec ξr H Cb Psel : ℝ),0<Kc → Z^rs.kLog=Kc →
    32*frequencyRadius Tsec Z ξr≤Z^cutoffLog rs → 8≤Kc → Kc≤Z^(2:ℝ) →
    0≤Tsec → Tsec≤Z^(2:ℝ) → ξr≤1 → H≤Z^(8:ℝ) → 0≤Cb → 0≤Psel →
    (∀n,∀g : Lab (RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂))→Id,
      IsColumn _ g → ∀χ v,
      (∑x∈actualFrameLabels η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc
        (frequencyRadius Tsec Z ξr) H rs P.j₀ ξ g n χ,gWeight x*framegEnergy ω₁ ω₂ η rs x v)≤
        (Cb*rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Psel)*(1+‖v‖)^(2*J)) →
    RootColoredSeed.groupedPartTerms false s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H≤
      (classLambda 1 Cg 1 Cb θ.a J*Z^δ*rs.vol^2*Psel*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J) := by
  obtain ⟨Cg,hCg,hsplit⟩ := actual_split_bound ω₁ ω₂ J
  obtain ⟨Cf,hCf,hfin⟩ := ActualLabelFiniteCosts.actual_window_finite_costs δ hδ
  refine ⟨Cf*Cg,mul_nonneg hCf.le hCg,?_⟩
  filter_upwards [hfin] with Z hf
  refine ⟨hf.1,?_⟩
  intro L mesh θ η P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR
    hH hB hR hX Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H Cb Psel hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hCb hPsel hframe
  obtain ⟨Mm,M,hMm,hM,hsize,hcard,hcm,hmult,hbox⟩ := hf.2 s θ.ha0 ω₁ ω₂ hX Kc Tsec ξr H hk8 hk2 hT0 hT hξ hH8
  let B0 := Cb*rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Psel
  have hv := rs.vol_pos (zero_lt_one.trans rs.hZ)
  have hB0 : 0≤B0 := by dsimp [B0];positivity
  have hsH : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap) := by simp [hH]
  have hr : ∀i,∀P∈s.H,P.val∈rs.R₀ i := by simp [hH]
  have hbud : (s.R.absNorm:ℝ)*(Z^(8:ℝ))^2*((∏I∈holes s.H,I).absNorm:ℝ)≤Z^θ.Bmask := by
    rw [hH]
    simp only [holes,Finset.image_empty,Finset.prod_empty,map_one,Nat.cast_one,mul_one]
    calc
      _≤Z^(8:ℝ)*(Z^(8:ℝ))^2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
      _=Z^(24:ℝ) := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans rs.hZ).le,←Real.rpow_add (zero_lt_one.trans rs.hZ)]
        norm_num
      _≤_ := Real.rpow_le_rpow_of_exponent_le rs.hZ.le hB
  have hp := hsplit P ξ Q m hm hl h2 hQ72 hQ χ₀ s θ.ha0 rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    hV₀ hCR hcan t Kc (frequencyRadius Tsec Z ξr) H M hK hklog hcut hbox hsH hr (Z^(8:ℝ)) hX hbud
    Mm hmult B0 hB0 (fun n hn g hg χ v=>hframe n g hg χ v)
  have hLam := lambda_of_class_bound _ _ Cg rs.vol Mm B0 Cb _ Psel θ.a t J
    (by positivity) hCg hv.le (by positivity) hCb (by positivity) hPsel le_rfl hp
  apply hLam.trans
  have hw := windowHeightConstant_nonneg J
  have hh := mul_le_mul_of_nonneg_right hcm
    (show 0≤Cg*Cb*windowHeightConstant J/θ.a^2*rs.vol^2*Psel*
      ((Ideal.span {rs.V₀}).absNorm:ℝ)*(1+‖t‖)^(2*J) by positivity)
  unfold classLambda
  convert hh using 1 <;> ring

/-- The two genuine frame scale logarithms recover the original source
volume and packed first-twist norm exactly. -/
lemma frame_price_normalization {L mesh Z : ℝ} {θ : GData L} (rs : GSrc θ mesh Z)
    (p ε : ℝ) :
    Z^(rs.colLog+rs.twistLog+p+ε)=rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Z^(p+ε) := by
  have hz := zero_lt_one.trans rs.hZ
  rw [show rs.colLog+rs.twistLog+p+ε=(rs.colLog+rs.twistLog)+(p+ε) by ring,
    Real.rpow_add hz,Real.rpow_add hz]
  rw [GSrc.colLog,GSrc.twistLog,Real.rpow_logb hz rs.hZ.ne' (rs.vol_pos hz),
    Real.rpow_logb hz rs.hZ.ne' (absNorm_span_pos _ rs.hV₀)]

#print axioms part_of_native_bound
#print axioms frame_price_normalization
end QRH.Cycle092.RegularPhysicalClassBudget
