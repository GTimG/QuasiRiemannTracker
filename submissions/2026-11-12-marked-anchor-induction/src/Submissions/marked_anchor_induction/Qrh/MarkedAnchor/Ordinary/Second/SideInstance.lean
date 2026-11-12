/- Copyright (c) 2026 Sil. Apache-2.0.
Instantiation of the second-step skeleton with the Seam B of `Packet.Grouped`.

* `groupedSideBoundA_iff`: `Packet.Grouped.GroupedSideBoundA` IS `Second.GroupedSideBound`
  (definitional).
* `gAmp_mono`: the source amplitude `gAmp L r J S = (‖W₁‖_S ‖W₂‖_S)² (1+|t|+V+|t₁|+|t₂|)^J` is
  nonnegative and monotone in the degree `J` and the seminorm set `S`.
* `summed_sides_of_leaves`: two Seam A leaves (step price and native price, envelopes up to
  `Hmax + 1`, ordinary lengths up to `L + 1`) give the skeleton conclusion `SideSupply` for
  the concrete frame `gFrame L`.
* `summed_sides_parent` / `summed_sides_density`: the large leaf from
  `parent_priced_source` / `density_priced_source`, the small one from `native_priced_source`,
  for step data whose price is the parent / density price.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.Side
import Submissions.sil_density_split_20261026.CubeFree.Packet.Grouped
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Parent
import Submissions.sil_density_split_20261026.Density.Leaf

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Second
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section
open Filter OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree.Packet.Grouped

theorem groupedSideBoundA_iff {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) (price : Price) (Mmin Mmax : ℝ) :
    GroupedSideBoundA Frame amp price Mmin Mmax ↔ GroupedSideBound Frame amp price Mmin Mmax :=
  Iff.rfl

theorem gAmp_mono (L : ℝ) : AmpMono (gAmp L) := by
  intro θ mesh η Z r
  have h1 := GSrc.one_le_height r
  refine ⟨fun J S => ?_, fun J J' S S' hJ hS => ?_⟩
  · unfold gAmp
    have := OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.sourceControl_nonneg S r.W₁
    positivity
  · unfold gAmp
    have hc : ∀ W : SchwartzMap ℝ ℂ,
        OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.sourceControl S W ≤
          OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.sourceControl S' W := by
      intro W
      unfold OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.sourceControl
      exact Seminorm.le_def.mp (Finset.sup_mono hS) W
    have h0 := OAI.SevenEighths.CenteredMomentFiniteProfileExceptional.sourceControl_nonneg
    apply mul_le_mul _ (pow_le_pow_right₀ h1 hJ) (by positivity) (by positivity)
    exact pow_le_pow_left₀ (mul_nonneg (h0 S _) (h0 S _))
      (mul_le_mul (hc _) (hc _) (h0 S _) (h0 S' _)) 2

/-- Seam B in the form used by the skeleton. -/
theorem grouped_of_leaf (L : ℝ) (hL : 0 ≤ L) (price : Price) (Mmin Mmax : ℝ)
    (hleaf : PricedPackedSource price Mmin (Mmax + 1) (L + 1)) :
    GroupedSideBound (gFrame L) (gAmp L) price Mmin Mmax :=
  grouped_side_bound_of_leaf L hL price Mmin Mmax hleaf

/-- The skeleton conclusion for the frame `gFrame L` from the two Seam A leaves. -/
theorem summed_sides_of_leaves (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hlarge : PricedPackedSource D.price D.Hmin (D.Hmax + 1) (L + 1))
    (hsmall : PricedPackedSource (nativePrice (3/4) (by norm_num)) D.Hmin (D.Hmax + 1) (L + 1)) :
    SideSupply D G (gFrame L) (gAmp L) :=
  summed_sides D G (gFrame L) (gAmp L) (gAmp_mono L)
    (grouped_of_leaf L hL _ _ _ hlarge) (grouped_of_leaf L hL _ _ _ hsmall)

theorem envelope_range {D : StepData} (G : StepGates D) : 0 < D.Hmin ∧ D.Hmin ≤ D.Hmax + 1 := by
  obtain ⟨h0, h1, h3⟩ := G.envelope
  exact ⟨h0, by linarith⟩

/-- Parent price (native steps): `parent_priced_source` and `native_priced_source`. -/
theorem summed_sides_parent (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (B₀ L₀ c₀ : ℝ)
    (hface : 0 < L₀ ∧ 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀)
    (hprice : D.price = parentPrice (3/4) B₀ L₀ c₀ (by norm_num) hface.1) :
    SideSupply D G (gFrame L) (gAmp L) := by
  obtain ⟨h0, h1⟩ := envelope_range G
  refine summed_sides_of_leaves D G L hL ?_
    (native_priced_source hβ D.Hmin (D.Hmax + 1) (L + 1) h0 h1)
  rw [hprice]
  exact parent_priced_source B₀ L₀ c₀ D.Hmin (D.Hmax + 1) (L + 1) hβ hface h0 h1 hparent

/-- Density price (density-split steps): `density_priced_source` and `native_priced_source`. -/
theorem summed_sides_density (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (B₀ L₀ c₀ Ld A Dd s₀ : ℝ) (hL₀ : 0 < L₀)
    (hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀)
    (hprice : D.price = QRH.SilDensitySplit.Density.densityPrice B₀ L₀ c₀ Ld A Dd s₀ hL₀) :
    SideSupply D G (gFrame L) (gAmp L) := by
  obtain ⟨h0, h1⟩ := envelope_range G
  refine summed_sides_of_leaves D G L hL ?_
    (native_priced_source hβ D.Hmin (D.Hmax + 1) (L + 1) h0 h1)
  rw [hprice]
  exact QRH.SilDensitySplit.Density.density_priced_source B₀ L₀ c₀ Ld A Dd s₀ D.Hmin (D.Hmax + 1)
    (L + 1) hL₀ hβ hface h0 h1 hparent

end
end Qrh.MarkedAnchor.Ordinary.Second
