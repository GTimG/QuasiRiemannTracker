/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Filled regular physical part, with genuine all-V P2 as its sole analytic input. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetPrice
import Candidate.C092.transport.RegularFramePhysicalReturnGrouped
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization
open CenteredMomentDetectorPlainFiberSource QRH.Cycle092.WholeSlot QRH.Cycle092.ReferenceArmRadial
open QRH.Cycle090 QRH.Cycle092 QRH.Cycle092.Source QRH.SourceCertificate
open QRH.Cycle092.RegularFramePhysicalReturn
open QRH.Cycle092.RegularColoredForward
open QRH.SilDensitySplit.CubeFree Packet Packet.Grouped Second.ConcreteGroup
namespace QRH.Cycle092.RegularPhysicalClassBudget
variable {L : ℝ}

abbrev filledPrice (θ : GData L) (mesh : ℝ) (Z : ℝ) (rs : GSrc θ mesh Z) (w₀ : ℝ) : ℝ :=
  (PackedPrice.regular PackedPrice.terminalReserve PackedPrice.terminalReserve_le).f
    w₀ (gP rs) (∑i,rs.w i) (commonH rs)

abbrev filledCaps (θ : GData L) (mesh n y Z : ℝ) (rs : GSrc θ mesh Z) : Prop :=
  rs.X₁≤ Z^n ∧ rs.X₂≤ Z^y ∧ rs.Y₁≤ Z^(23/200:ℝ) ∧ rs.Y₂≤ Z^(18023/25000:ℝ) ∧
    (∑i,rs.w i)≤ sourceWidth n y-(u:ℝ)

/-- The original η and the structural θ,n,y are fixed before the returned
constant/eventual threshold. All actual SidePack bases, colors inside columns,
classifiers, ordinary windows and labels follow that threshold. -/
theorem filled_part_of_p2 (Mmin Mmax : ℝ) (hMmin : 0≤ Mmin) (hMmax : Mmax<2)
    (hMmaxlo : 0≤ Mmax+2) (hL : 0≤ L) (ε δ : ℝ) (hε : 0< ε) (hδ : 0< δ) :
    ∃ meshMax : ℝ,0< meshMax ∧ ∀mesh : ℝ,0< mesh → mesh≤ meshMax →
    ∀ (θ : GData L) (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
      (hΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic θ.bΦ)
      (n y : ℝ) (hy₀ : sourceY0≤ y) (hy₁ : y≤ sourceY) (hn : y≤ n)
      (η ω₁ ω₂ : Character) (hQ₁ : θ.Q≤ ω₁.modulus) (hQ₂ : θ.Q≤ ω₂.modulus)
      (Dp : ℕ) (Sp : Finset (ℕ×ℕ)) (Cp : ℝ),0< Cp →
      (∀j : DictIdx,∀ᶠ Z : ℝ in atTop,
        OrderedP2At (Fin θ.N) θ.rayM θ.Hray θ.hH θ.W n y mesh Z
          (anchors η j) θ.η₀ ω₁ ω₂ θ.Q Dp Sp Cp) →
    ∃ J : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C Cg : ℝ,0< C ∧ 0≤ Cg ∧
      ∀ᶠ Z : ℝ in atTop,PartAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ J controls C Cg
        (filledPrice θ mesh) (filledCaps θ mesh n y) Z := by
  obtain ⟨meshMax,hmmax,hproduce⟩ := RegularFramePhysicalReturn.regular_grouped_of_p2
    Mmin Mmax hMmin hMmax hL ε hε
  refine ⟨meshMax,hmmax,?_⟩
  intro mesh hmesh hmm θ hβ hΦ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2
  obtain ⟨J,controls,C,hC,hframes⟩ := hproduce mesh hmesh hmm θ hβ hΦ n y hy₀ hy₁ hn
    η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2
  have hf : ∀ᶠ Z : ℝ in atTop,FrameAt θ mesh η ω₁ ω₂ Mmin Mmax ε J controls C
      (filledPrice θ mesh) (filledCaps θ mesh n y) Z := by
    filter_upwards [hframes] with Z hframe
    intro rs labels w₀ v hadm hc
    exact hframe rs labels w₀ (commonH rs) v hadm hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  obtain ⟨Cg,hCg,hpart⟩ := part_from_grouped θ mesh η ω₁ ω₂ Mmin Mmax ε δ hMmaxlo hε hδ hmesh
    J controls C hC (filledPrice θ mesh) (filledCaps θ mesh n y) hf
  exact ⟨J,controls,C,Cg,hC,hCg,hpart⟩

#print axioms filled_part_of_p2
end QRH.Cycle092.RegularPhysicalClassBudget
