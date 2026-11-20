/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Genuine native regular grouped prices reach the original physical part. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetLambda
import Candidate.C092.transport.ColoredFrameAdmissibleActual
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
variable {L : ℝ}

abbrev FrameAt (θ : GData L) (mesh : ℝ) (η ω₁ ω₂ : Character) (Mmin Mmax ε : ℝ)
    (J : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ)
    (price : ∀Z : ℝ,GSrc θ mesh Z→ℝ→ℝ) (caps : ∀Z : ℝ,GSrc θ mesh Z→Prop) (Z : ℝ) : Prop :=
  ∀ (rs : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z)) (w₀ v : ℝ),
    Second.AdmissibleGroup (frameSideFrame L θ mesh ω₁ ω₂ η Z) Mmin Mmax mesh ε Z rs labels (commonH rs) →
    caps Z rs → (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η rs x v)≤
      C*gAmp L θ mesh η Z rs J controls*(1+‖v‖)^(2*J)*Z^(rs.colLog+rs.twistLog+price Z rs w₀+ε)

/-- Fully expanded actual class return. The only later scalar price gate is
numerical; there is no source-energy, class-energy or admissibility premise. -/
abbrev PartAt (θ : GData L) (mesh : ℝ) (η ω₁ ω₂ : Character) (Mmin Mmax ε δ : ℝ)
    (J : ℕ) (controls : Finset (ℕ×ℕ)) (C Cg : ℝ)
    (price : ∀Z : ℝ,GSrc θ mesh Z→ℝ→ℝ) (caps : ∀Z : ℝ,GSrc θ mesh Z→Prop) (Z : ℝ) : Prop :=
  2≤Z ∧ ∀ (P : SidePack η) (ξ χ₀ : RayCharacter) (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z),
    rs.W₁=s.W₁ → rs.W₂=s.W₂ → rs.t₁=s.t₁/(2*Real.pi) → rs.t₂=s.t₂/(2*Real.pi) →
    rs.X₁=s.X₁ → rs.X₂=s.X₂ → rs.Y₁=s.Y₁ → rs.Y₂=s.Y₂ →
    Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d → rs.V₀=P.V → P.Cs∣s.R →
    s.H=∅ → 24≤θ.Bmask → (s.R.absNorm:ℝ)≤Z^(8:ℝ) →
    (∀I∈RootColoredSeed.active s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) →
    Mmin≤commonH rs → commonH rs≤Mmax → caps Z rs →
    ∀ (Q : Id) (m : O),m≠0 → goodLambda∣m → (2:O)∣m → Q≤Ideal.span {(72:O)} → internalQ θ.Q θ.η₀=Q →
    ∀ (t Kc Tsec ξr H w₀ u' : ℝ),0<Kc → Z^rs.kLog=Kc →
    32*frequencyRadius Tsec Z ξr≤Z^cutoffLog rs → 8≤Kc → Kc≤Z^(2:ℝ) →
    0≤Tsec → Tsec≤Z^(2:ℝ) → ξr≤1 → H≤Z^(8:ℝ) → price Z rs w₀+ε≤u' →
    RootColoredSeed.groupedPartTerms false s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H≤
      (classLambda 1 Cg 1 (C*gAmp L θ mesh η Z rs J controls) θ.a J*
        Z^δ*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J)

/-- All true H5/admissibility and original finite costs are internal. The
input is exactly the native grouped producer's already-proved conclusion. -/
theorem part_from_grouped (θ : GData L) (mesh : ℝ) (η ω₁ ω₂ : Character)
    (Mmin Mmax ε δ : ℝ) (hMmax : 0≤Mmax+2) (hε : 0<ε) (hδ : 0<δ) (hmesh : 0< mesh)
    (J : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0<C)
    (price : ∀Z : ℝ,GSrc θ mesh Z→ℝ→ℝ) (caps : ∀Z : ℝ,GSrc θ mesh Z→Prop)
    (hgroup : ∀ᶠ Z : ℝ in atTop,FrameAt θ mesh η ω₁ ω₂ Mmin Mmax ε J controls C price caps Z) :
    ∃ Cg : ℝ,0≤Cg ∧ ∀ᶠ Z : ℝ in atTop,PartAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ J controls C Cg price caps Z := by
  obtain ⟨Cg,hCg,hnative⟩ := part_of_native_bound ω₁ ω₂ J δ hδ
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hgroup,hnative,
    ColoredFrameAdmissible.eventually_actual_class_admissible Mmin Mmax ε mesh hMmax hε hmesh L θ]
    with Z hg hn hadm
  refine ⟨hn.1,?_⟩
  intro P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX hlo hhi hcaps
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hpaid
  have hheight : 0≤rs.height := zero_le_one.trans rs.one_le_height
  have hAmp : 0≤gAmp L θ mesh η Z rs J controls := by unfold gAmp;positivity
  apply hn.2 P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H (C*gAmp L θ mesh η Z rs J controls) (Z^u')
    hK hklog hcut hk8 hk2 hT0 hT hξ hH8 (mul_nonneg hC.le hAmp)
    (Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le _)
  intro n g hcol χ v
  have ha := (hadm η s θ.ha0 ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc
    (frequencyRadius Tsec Z ξr) H rs P.j₀ ξ g hcol n χ hH hB hR hX hlo hhi).2
  have he := hg rs _ w₀ v ha hcaps
  rw [frame_price_normalization] at he
  have hpow := Real.rpow_le_rpow_of_exponent_le rs.hZ.le hpaid
  have hv := (rs.vol_pos (zero_lt_one.trans rs.hZ)).le
  calc
    _≤C*gAmp L θ mesh η Z rs J controls*(1+‖v‖)^(2*J)*
      (rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Z^(price Z rs w₀+ε)) := he
    _≤C*gAmp L θ mesh η Z rs J controls*(1+‖v‖)^(2*J)*
      (rs.vol*((Ideal.span {rs.V₀}).absNorm:ℝ)*Z^u') := by gcongr
    _=_ := by ring

#print axioms part_from_grouped
end QRH.Cycle092.RegularPhysicalClassBudget
