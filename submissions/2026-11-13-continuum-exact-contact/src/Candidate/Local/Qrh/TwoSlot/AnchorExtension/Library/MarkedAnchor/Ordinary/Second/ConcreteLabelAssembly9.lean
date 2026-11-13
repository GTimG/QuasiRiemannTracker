/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 9: **the label part of one residual split** (`split_label_bound`).

From the two Seam A leaves (step price and native price, as in `SideInstance.summed_sides_of_leaves`):
for every `ε > 0` there is a mesh bound such that for every mesh, structural data `θ` and base
character `η` there are a degree `J`, a seminorm set and a constant `C > 0` with, for all large
`Z`, every first fixed pair `F`, D⁴-transfer ray `ξ`, residual split (FP source `s` on `Fin N`,
frame source `rs`, Gauss scale `Kc`, frequency radius `R`, norm cap `H`) carrying
`RootLabelData`, and branch data `(A, c, q_C)` of `rs` at the common envelope:

  `splitLabel (S0 s) (β_s) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
     C · #box(M) · (vol/c) · Mm · gAmp(rs) · Z^{A - c + q_C + ε} · (1+|t|)^{2J}`

(height-uniformly in `t`). This is the label part of `labelAvg` at one `(B, ξ)` after
reindexing the residual (`reindexSource`); `vol = X₁X₂∏Z^{wᵢ}` is the column volume of the split
(the raw normalization; `#box = (2M+1)⁴`, `Mm ≤ 4^{ω}` are subpower).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly8
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.SideInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource RayFourExpansion
open CenteredMomentSecondWindowBudget CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- **The label part of one residual split.** -/
theorem split_label_bound (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hlarge : PricedPackedSource D.price D.Hmin (D.Hmax + 1) (L + 1))
    (hsmall : PricedPackedSource (nativePrice (3/4) (by norm_num)) D.Hmin (D.Hmax + 1) (L + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
    ∀ (θ : GData L) (η : Character),
    ∃ J : ℕ, ∃ control : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (P : SidePack η) (ξ : RayCharacter) (Q : Id) (m : O) (χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z) (Kc R H : ℝ) (M : ℤ)
      (Mm : ℕ) (clow : ℝ) (hR : RootLabelData P Q m s ha rs Kc R H M Mm clow) (A c qC : ℝ)
      (hb : BranchData D G (gFrame L θ mesh η Z) ε mesh rs A c qC (commonH rs))
      (hHr : D.Hmin ≤ commonH rs ∧ commonH rs ≤ D.Hmax) (t : ℝ),
      splitLabel (S0 s ha) (sourceCoefficient s ha 1) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
        (C * ((box M).card : ℝ) * (rs.vol / clow) * Mm * gAmp L θ mesh η Z rs J control *
          Z^(A - c + qC + ε)) * (1 + ‖t‖)^(2*J) := by
  intro ε hε
  have hε2 : 0 < ε/2 := by linarith
  obtain ⟨mL, hmL, hLs⟩ := grouped_of_leaf L hL D.price D.Hmin D.Hmax hlarge (ε/2) hε2
  obtain ⟨mS, hmS, hSs⟩ := grouped_of_leaf L hL _ D.Hmin D.Hmax hsmall (ε/2) hε2
  obtain ⟨-, -, hmeshL, -, -⟩ := G.ledger_spec hε
  refine ⟨min (min mL mS) (G.meshL ε), lt_min (lt_min hmL hmS) hmeshL, ?_⟩
  intro mesh hmesh hmm θ η
  have hm1 : mesh ≤ mL := hmm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm2 : mesh ≤ mS := hmm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm3 : mesh ≤ G.meshL ε := hmm.trans (min_le_right _ _)
  obtain ⟨dL, SL, CL, hCL, hZL⟩ := hLs mesh hmesh hm1 θ η
  obtain ⟨dS, SS, CS, hCS, hZS⟩ := hSs mesh hmesh hm2 θ η
  set J := max dL dS with hJ
  obtain ⟨Cg, hCg, hsplit⟩ := split_label_at J
  set K₀ : ℝ := profileMoment J^2 * (1 + 2*Real.pi)^(4*J) with hK₀
  have hK₀0 : 0 ≤ K₀ := by have := profileMoment_nonneg J; positivity
  refine ⟨J, SL ∪ SS, Cg * max CL CS * K₀ + 1, by
    have : 0 ≤ Cg * max CL CS * K₀ := mul_nonneg (mul_nonneg hCg (le_max_of_le_left hCL.le)) hK₀0
    linarith, ?_⟩
  have hHmax : (0:ℝ) ≤ D.Hmax + 2 := by have := G.envelope; linarith [this.2.2]
  filter_upwards [hZL, hZS, eventually_ge_atTop (1:ℝ), eventually_logb_two_le mesh hmesh,
    eventually_fibreAt 2 (D.Hmax + 2) θ.Bmask (ε/2) hHmax θ.hBmask hε2]
    with Z hZL hZS hZ1 hlog hfib
  intro P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR A c qC hb hHr t
  have hZ0 : 0 < Z := by linarith
  obtain ⟨hnn, hmono⟩ := gAmp_mono L θ mesh η Z rs
  set amp := gAmp L θ mesh η Z rs J (SL ∪ SS) with hamp
  have hamp0 : 0 ≤ amp := hnn _ _
  set B₀ := max CL CS * amp * Z^(A - c + qC + ε) with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have := Real.rpow_nonneg hZ0.le (A - c + qC + ε)
    have : 0 ≤ max CL CS := le_max_of_le_left hCL.le
    positivity
  have hseam : ∀ labels : Finset (GLabel θ mesh Z),
      AdmissibleGroup (gFrame L θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z rs labels (commonH rs) →
      ∀ v : ℝ, ∑ x ∈ labels, gWeight x * gEnergy η rs x v ≤ B₀ * (1 + ‖v‖)^(2*J) := by
    intro labels hadm v
    have h := seam_column (F := gFrame L θ mesh η Z) D G hε hmesh.le hm3 Z hZ1 (gAmp L θ mesh η Z rs dL SL)
      (gAmp L θ mesh η Z rs dS SS) CL CS dL dS hCL.le hCS.le (hnn _ _) (hnn _ _) rs labels
      A c qC (commonH rs) (fun w₀ v' => hZL rs labels w₀ (commonH rs) hadm v')
      (fun v' => hZS rs labels 0 (commonH rs) hadm v') hb v
    refine h.trans ?_
    have hA : max (gAmp L θ mesh η Z rs dL SL) (gAmp L θ mesh η Z rs dS SS) ≤ amp :=
      max_le (hmono _ _ _ _ (le_max_left _ _) Finset.subset_union_left)
        (hmono _ _ _ _ (le_max_right _ _) Finset.subset_union_right)
    have hZE := Real.rpow_nonneg hZ0.le (A - c + qC + ε)
    have hCm : 0 ≤ max CL CS := le_max_of_le_left hCL.le
    have hv : 0 ≤ (1 + ‖v‖)^(2*J) := by positivity
    calc max CL CS * max (gAmp L θ mesh η Z rs dL SL) (gAmp L θ mesh η Z rs dS SS) *
          Z^(A - c + qC + ε) * (1 + ‖v‖)^(2*max dL dS)
        ≤ max CL CS * amp * Z^(A - c + qC + ε) * (1 + ‖v‖)^(2*max dL dS) := by
          apply mul_le_mul_of_nonneg_right _ hv
          apply mul_le_mul_of_nonneg_right _ hZE
          exact mul_le_mul_of_nonneg_left hA hCm
      _ = B₀ * (1 + ‖v‖)^(2*J) := rfl
  have h := hsplit P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR D.Hmin D.Hmax (ε/2) B₀ hB₀0 hHr hlog hfib
    hseam t
  refine h.trans ?_
  have hcl := hR.hclow_pos
  have hvol := rs.vol_pos hZ0
  have hZE := Real.rpow_nonneg hZ0.le (A - c + qC + ε)
  have hrest : 0 ≤ ((box M).card : ℝ) * (rs.vol / clow) * Mm * amp * Z^(A - c + qC + ε) *
      (1 + ‖t‖)^(2*J) := by positivity
  have e1 : (((box M).card : ℝ) * Cg * ((rs.vol / clow) * Mm * B₀) * K₀) * (1 + ‖t‖)^(2*J) =
      (Cg * max CL CS * K₀) * (((box M).card : ℝ) * (rs.vol / clow) * Mm * amp *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by rw [hB₀]; ring
  have e2 : ((Cg * max CL CS * K₀ + 1) * ((box M).card : ℝ) * (rs.vol / clow) * Mm * amp *
      Z^(A - c + qC + ε)) * (1 + ‖t‖)^(2*J) =
      (Cg * max CL CS * K₀ + 1) * (((box M).card : ℝ) * (rs.vol / clow) * Mm * amp *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hrest

/-- The label part of a split is invariant under reindexing the residual slots
(`Rest J ≃ Fin N`). -/
theorem splitLabel_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℝ} (r : Source ι a b)
    (e : ι ≃ κ) (ha : 0 < a) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc R H : ℝ) :
    splitLabel (S0 (reindexSource r e) ha) (sourceCoefficient (reindexSource r e) ha 1) ψ χ₀ Q m
        t Kc R H =
      splitLabel (S0 r ha) (sourceCoefficient r ha 1) ψ χ₀ Q m t Kc R H := by
  unfold S0
  rw [sourceColumns_reindex, sourceCoefficient_reindex]

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
