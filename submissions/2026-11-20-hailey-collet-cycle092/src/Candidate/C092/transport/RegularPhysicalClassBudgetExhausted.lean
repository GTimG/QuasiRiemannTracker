/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Genuine exhausted ordinary regular part, retaining every positive loss. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetFee
import Candidate.C092.transport.RegularFramePhysicalReturnExhaustedGrouped
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092 QRH.Cycle092.RegularColoredForward QRH.Cycle092.ReferenceArmRadial QRH.Cycle092.WholeSlot
open QRH.SilDensitySplit.CubeFree Packet Packet.Grouped Second.ConcreteGroup
namespace QRH.Cycle092.RegularPhysicalClassBudget
variable {L : ℝ}

abbrev exhaustedPrice (θ : GData L) (mesh δnative : ℝ) (hδnative : 0≤δnative)
    (Z : ℝ) (rs : GSrc θ mesh Z) (w₀ : ℝ) : ℝ :=
  (PackedPrice.withLoss PackedPrice.exhausted δnative hδnative).f
    w₀ (gP rs) (∑i,rs.w i) (commonH rs)

abbrev exhaustedCaps (θ : GData L) (mesh Z : ℝ) (rs : GSrc θ mesh Z) : Prop :=
  rs.X₁≤Z^(3/4:ℝ) ∧ rs.X₂≤Z^(3/4:ℝ) ∧ rs.Y₁≤Z^(3/4:ℝ) ∧ rs.Y₂≤Z^(3/4:ℝ)

/-- The fee gate reduces exactly to the original exhausted price gate.
Thus selected width zero remains literal; its positive source/group losses
appear outside Π as Z^(δnative+ε), rather than being removed. -/
lemma exhausted_fee_gate (θ : GData L) (mesh δnative ε Z : ℝ) (hδnative : 0≤δnative)
    (rs : GSrc θ mesh Z) (w₀ u' : ℝ) :
    exhaustedPrice θ mesh δnative hδnative Z rs w₀+ε≤u'+(δnative+ε) ↔
      PackedPrice.exhausted.f w₀ (gP rs) (∑i,rs.w i) (commonH rs)≤u' := by
  change _+δnative+ε≤u'+(δnative+ε) ↔ _≤u'
  constructor <;> intro h <;> linarith

/-- No P2 premise is used at genuine slot exhaustion. The returned external
power is δfinite+δnative+εgroup, with original Π=Z^u' unchanged. -/
theorem exhausted_part (Mmin Mmax : ℝ) (hMmin : 0≤Mmin) (hMmax : Mmax<2)
    (hMmaxlo : 0≤Mmax+2) (hL : 0≤L) (ε δnative δfinite : ℝ)
    (hε : 0<ε) (hδnative : 0<δnative) (hδfinite : 0<δfinite) :
    ∃ meshMax : ℝ,0< meshMax ∧ ∀mesh : ℝ,0< mesh → mesh≤ meshMax →
    ∀ (θ : GData L),θ.N=0 →
    ∀ (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
      (hΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic θ.bΦ)
      (η ω₁ ω₂ : Character),θ.Q≤ω₁.modulus → θ.Q≤ω₂.modulus →
    ∃ J : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C Cg : ℝ,0<C ∧ 0≤Cg ∧
      ∀ᶠ Z : ℝ in atTop,PartWithFeeAt θ mesh η ω₁ ω₂ Mmin Mmax ε δfinite (δnative+ε)
        J controls C Cg (exhaustedPrice θ mesh δnative hδnative.le) (exhaustedCaps θ mesh) Z := by
  obtain ⟨meshMax,hmmax,hproduce⟩ := RegularFramePhysicalReturn.exhausted_grouped
    Mmin Mmax hMmin hMmax hL ε δnative hε hδnative
  refine ⟨meshMax,hmmax,?_⟩
  intro mesh hmesh hmm θ hN hβ hΦ η ω₁ ω₂ hQ₁ hQ₂
  obtain ⟨J,controls,C,hC,hframes⟩ := hproduce mesh hmesh hmm θ hN hβ hΦ η ω₁ ω₂ hQ₁ hQ₂
  have hf : ∀ᶠ Z : ℝ in atTop,FrameAt θ mesh η ω₁ ω₂ Mmin Mmax ε J controls C
      (exhaustedPrice θ mesh δnative hδnative.le) (exhaustedCaps θ mesh) Z := by
    filter_upwards [hframes] with Z hframe
    intro rs labels w₀ v hadm hc
    exact hframe rs labels w₀ (commonH rs) v hadm hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  obtain ⟨Cg,hCg,hpart⟩ := part_from_grouped θ mesh η ω₁ ω₂ Mmin Mmax ε δfinite hMmaxlo hε hδfinite hmesh
    J controls C hC (exhaustedPrice θ mesh δnative hδnative.le) (exhaustedCaps θ mesh) hf
  refine ⟨J,controls,C,Cg,hC,hCg,hpart.mono ?_⟩
  intro Z hz
  exact part_fee_of_part θ mesh η ω₁ ω₂ Mmin Mmax ε δfinite (δnative+ε) J controls C Cg
    (exhaustedPrice θ mesh δnative hδnative.le) (exhaustedCaps θ mesh) Z hz

#print axioms exhausted_fee_gate
#print axioms exhausted_part
end QRH.Cycle092.RegularPhysicalClassBudget
