/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Genuine native regular grouped prices reach the original physical part. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetPrice
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

abbrev PartWithFeeAt (θ : GData L) (mesh : ℝ) (η ω₁ ω₂ : Character) (Mmin Mmax ε δ fee : ℝ)
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
    0≤Tsec → Tsec≤Z^(2:ℝ) → ξr≤1 → H≤Z^(8:ℝ) → price Z rs w₀+ε≤u'+fee →
    RootColoredSeed.groupedPartTerms false s θ.ha0 (idealCoeff ω₁) (idealCoeff ω₂) (childCharacter P.base ξ)
      χ₀ Q m t Kc Tsec Z ξr H≤
      (classLambda 1 Cg 1 (C*gAmp L θ mesh η Z rs J controls) θ.a J*
        Z^(δ+fee)*rs.vol^2*Z^u'*((Ideal.span {rs.V₀}).absNorm:ℝ))*(1+‖t‖)^(2*J)


/-- Preserve the literal selected power Z^u' and exhibit every extra debit
as an external power. This also applies when the selected width is zero. -/
theorem part_fee_of_part (θ : GData L) (mesh : ℝ) (η ω₁ ω₂ : Character)
    (Mmin Mmax ε δ fee : ℝ) (J : ℕ) (controls : Finset (ℕ×ℕ)) (C Cg : ℝ)
    (price : ∀Z : ℝ,GSrc θ mesh Z→ℝ→ℝ) (caps : ∀Z : ℝ,GSrc θ mesh Z→Prop) (Z : ℝ)
    (h : PartAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ J controls C Cg price caps Z) :
    PartWithFeeAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ fee J controls C Cg price caps Z := by
  refine ⟨h.1,?_⟩
  intro P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX hlo hhi hcaps
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hpaid
  have he := h.2 P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX hlo hhi hcaps
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H w₀ (u'+fee) hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hpaid
  apply he.trans_eq
  simp only [Real.rpow_add (zero_lt_one.trans rs.hZ)]
  ring

#print axioms part_fee_of_part
end QRH.Cycle092.RegularPhysicalClassBudget
