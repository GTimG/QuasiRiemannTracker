/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 3: the grouped label-block bound of one dyadic class of one
residual split, fed by Seam B through the frame labels.

* `column_hyp`: the hypothesis `hleft` (column `C₂`) or `hright` (column `D₂`) of
  `Concrete.grouped_label_blocks` from the frame data of the column: per (label, `t₂`, ray)
  a concrete frame label (`LabelData`, twin character, dyad above the class row scale), the
  weight ratio `wt ≤ Λ ρ(G)‖pref‖N(G)(Z^k/X²)`, injectivity, and a height-uniform Seam B bound
  `B` of the frame group (`seam_column` + `ConcreteGroup.raised_group_large/small`).
* `class_label_bound`: `(1+r)^decay ∑_l wt_l ‖labelBlock_l‖ ≤
     Cg · windowBudget J t (Λ B_C) · windowBudget J t (Λ B_D)`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondExceptionalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentFirstSectors CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- **One column of the grouped hypotheses from Seam B.** -/
theorem column_hyp {η : Character} (P : SidePack η)
    (ξ : RayCharacter) (Q : Id) (m : O) (hm : m ≠ 0)
    (hml : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hQ : internalQ θ.Q θ.η₀ = Q) (χ₀ : RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (hW₁ : rs.W₁ = s.W₁) (hW₂ : rs.W₂ = s.W₂) (ht₁ : rs.t₁ = s.t₁ / (2 * Real.pi))
    (ht₂ : rs.t₂ = s.t₂ / (2 * Real.pi)) (hX₁ : rs.X₁ = s.X₁) (hX₂ : rs.X₂ = s.X₂)
    (hY₁ : rs.Y₁ = s.Y₁) (hY₂ : rs.Y₂ = s.Y₂) (hV₀ : rs.V₀ = P.V)
    (hCR : P.Cs ∣ s.R) (S : Finset Id) (hSs : S ⊆ sourceColumns s)
    (hSz : ∀ I ∈ sourceColumns s, I ∉ S → sourceCoefficient s ha 1 I = 0)
    {Λ : Type*} (Ls : Finset Λ) (ℓ : Λ → BlockLabel (childCharacter P.base ξ) χ₀ Q m S)
    (hfam : ∀ l, Family (childCharacter P.base ξ) (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).U
      (ℓ l).τ)
    (wt : Λ → ℝ) (hwt : ∀ l, 0 ≤ wt l)
    (col : Λ → Id) (hcolS : ∀ l, Supported (col l))
    (hGc : ∀ l I, IsCoprime (col l) I → IsCoprime (ℓ l).C I ∨ IsCoprime (ℓ l).D I)
    (Hs : ℝ) (hH : 0 < Hs) (Λc B : ℝ) (hΛ : 0 ≤ Λc) (J : ℕ)
    (x : RayCharacter → (Σ _ : Λ, Id) → LabelData)
    (hj : ∀ χ k, (x χ k).j = P.j₀ * ξ * χ)
    (hA : ∀ χ k, (x χ k).A₂ = secondTwist (ℓ k.1).C (ℓ k.1).D (ℓ k.1).U)
    (hG : ∀ χ k, (x χ k).G = col k.1) (hD : ∀ χ k, (x χ k).D = k.2)
    (hseed : ∀ χ k, (x χ k).seed = 1)
    (hgood : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), (x χ k).Good rs)
    (hcan : ∀ χ k, Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ (x χ k).holesH (x χ k).R
      (x χ k).d)
    (hdyad : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), 2 * Hs ≤ dyadicScale ((x χ k).n 1))
    (hratio : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 ≤ Λc * (rho (x χ k).G *
      ‖(x χ k).prefactor‖ * ((x χ k).G.absNorm : ℝ) *
      (((x χ k).d.1.absNorm : ℝ) * ((x χ k).d.2.absNorm : ℝ)) * rs.norm))
    (Mm : ℕ) (hB : 0 ≤ B)
    (hmult : ∀ χ, ∀ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (x χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
      ((Ls.sigma (fun l => (ℓ l).pool)).filter
        (fun k => (x χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η = y)).card ≤ Mm)
    (hseam : ∀ χ v, ∑ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (x χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
        gWeight y * gEnergy η rs y v ≤ B * (1 + ‖v‖)^(2*J)) :
    ∀ (χ : RayCharacter) (v : ℝ),
      (∑ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 *
        sourceRestrictedEnergy (nonexceptional (childCharacter P.base ξ) χ Q m (ℓ k.1).A)
          (residualPool (col k.1) (hcolS k.1).1 S)
          (fun I => if IsCoprime (col k.1) I ∧ k.2 ∣ I then
            sourceCoefficient s ha 1 (col k.1 * I) else 0)
          (heightCoeff ((ℓ k.1).τ χ) v) ballProfile Hs) ≤ (Λc * Mm * B) * (1 + ‖v‖)^(2*J) := by
  intro χ
  refine weighted_column_bound_mult η rs (Ls.sigma (fun l => (ℓ l).pool)) (fun k => wt k.1)
    (fun k v => sourceRestrictedEnergy (nonexceptional (childCharacter P.base ξ) χ Q m (ℓ k.1).A)
          (residualPool (col k.1) (hcolS k.1).1 S)
          (fun I => if IsCoprime (col k.1) I ∧ k.2 ∣ I then
            sourceCoefficient s ha 1 (col k.1 * I) else 0)
          (heightCoeff ((ℓ k.1).τ χ) v) ballProfile Hs)
    (fun k => (x χ k).toLabel η) Mm (hmult χ) Λc B hΛ hB J ?_ (hseam χ)
  intro k hk v
  have hfits := toLabel_fits (θ := θ) (mesh := mesh) (Z := Z) η rs (x χ k) (hgood χ k hk)
  have hsrc := source_le_frame P ξ (hfam k.1) χ (col k.1) (hcolS k.1) (hGc k.1) Q m hm hml hm2 hQ
    s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hV₀ hCR (x χ k) (hj χ k) (hA χ k) (hG χ k)
    (hseed χ k) (hgood χ k hk) (hcan χ k) S hSs hSz Hs hH (hdyad χ k hk) v
  rw [hD χ k] at hsrc
  have hsrc0 := CenteredMomentRestrictedSourceNormalization.sourceRestrictedEnergy_nonneg
    (nonexceptional (childCharacter P.base ξ) χ Q m (ℓ k.1).A)
    (residualPool (col k.1) (hcolS k.1).1 S)
    (fun I => if IsCoprime (col k.1) I ∧ k.2 ∣ I then sourceCoefficient s ha 1 (col k.1 * I) else 0)
    (heightCoeff ((ℓ k.1).τ χ) v) ballProfile Hs hH (fun _ => ballProfile_nonneg _)
  have hr := hratio χ k hk
  have hGx : ((x χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η).G = (x χ k).G := rfl
  exact pointwise_ratio η rs _ hfits (wt k.1) _ Λc v (hwt k.1) hr hsrc0 hsrc

/-- **The grouped label-block bound of one dyadic class of one residual split.** -/
theorem class_label_bound (W : 𝓢(ℝ,ℂ)) (decay J : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
    ∀ {L : ℝ} {θ : GData L} {mesh Z : ℝ} {η : Character} (P : SidePack η)
    (ξ : RayCharacter) (Q : Id) (m : O) (hm : m ≠ 0)
    (hml : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (hQ : internalQ θ.Q θ.η₀ = Q) (χ₀ : RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (hW₁ : rs.W₁ = s.W₁) (hW₂ : rs.W₂ = s.W₂) (ht₁ : rs.t₁ = s.t₁ / (2 * Real.pi))
    (ht₂ : rs.t₂ = s.t₂ / (2 * Real.pi)) (hX₁ : rs.X₁ = s.X₁) (hX₂ : rs.X₂ = s.X₂)
    (hY₁ : rs.Y₁ = s.Y₁) (hY₂ : rs.Y₂ = s.Y₂) (hV₀ : rs.V₀ = P.V)
    (hCR : P.Cs ∣ s.R) (S : Finset Id) (hSs : S ⊆ sourceColumns s)
    (hSz : ∀ I ∈ sourceColumns s, I ∉ S → sourceCoefficient s ha 1 I = 0)
    {Λ : Type*} (Ls : Finset Λ) (ℓ : Λ → BlockLabel (childCharacter P.base ξ) χ₀ Q m S)
    (hfam : ∀ l, Family (childCharacter P.base ξ) (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).U
      (ℓ l).τ)
    (wt : Λ → ℝ) (hwt : ∀ l, 0 ≤ wt l) (r : ℝ) (hr : 0 < r) (t X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (Hs : ℝ) (hH : 0 < Hs)
    (hmajor : ∀ l ∈ Ls, ∀ z ∈ (ℓ l).rows, 1 ≤ (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/Hs)).re)
    (Λc BC BD : ℝ) (hΛ : 0 ≤ Λc) (hBC : 0 ≤ BC) (hBD : 0 ≤ BD) (Mm : ℕ)
    (xC xD : RayCharacter → (Σ _ : Λ, Id) → LabelData)
    (hjC : ∀ χ k, (xC χ k).j = P.j₀ * ξ * χ)
    (hjD : ∀ χ k, (xD χ k).j = P.j₀ * ξ * χ)
    (hAC : ∀ χ k, (xC χ k).A₂ = secondTwist (ℓ k.1).C (ℓ k.1).D (ℓ k.1).U)
    (hAD : ∀ χ k, (xD χ k).A₂ = secondTwist (ℓ k.1).C (ℓ k.1).D (ℓ k.1).U)
    (hGC : ∀ χ k, (xC χ k).G = (ℓ k.1).C) (hGD : ∀ χ k, (xD χ k).G = (ℓ k.1).D)
    (hDC : ∀ χ k, (xC χ k).D = k.2) (hDD : ∀ χ k, (xD χ k).D = k.2)
    (hsC : ∀ χ k, (xC χ k).seed = 1) (hsD : ∀ χ k, (xD χ k).seed = 1)
    (hgC : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), (xC χ k).Good rs) (hgD : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), (xD χ k).Good rs)
    (hcC : ∀ χ k, Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ (xC χ k).holesH (xC χ k).R
      (xC χ k).d)
    (hcD : ∀ χ k, Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ (xD χ k).holesH (xD χ k).R
      (xD χ k).d)
    (hdC : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), 2 * Hs ≤ dyadicScale ((xC χ k).n 1))
    (hdD : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), 2 * Hs ≤ dyadicScale ((xD χ k).n 1))
    (hrC : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 ≤ Λc * (rho (xC χ k).G *
      ‖(xC χ k).prefactor‖ * ((xC χ k).G.absNorm : ℝ) *
      (((xC χ k).d.1.absNorm : ℝ) * ((xC χ k).d.2.absNorm : ℝ)) * rs.norm))
    (hrD : ∀ χ, ∀ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 ≤ Λc * (rho (xD χ k).G *
      ‖(xD χ k).prefactor‖ * ((xD χ k).G.absNorm : ℝ) *
      (((xD χ k).d.1.absNorm : ℝ) * ((xD χ k).d.2.absNorm : ℝ)) * rs.norm))
    (hiC : ∀ χ, ∀ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (xC χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
      ((Ls.sigma (fun l => (ℓ l).pool)).filter
        (fun k => (xC χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η = y)).card ≤ Mm)
    (hiD : ∀ χ, ∀ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (xD χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
      ((Ls.sigma (fun l => (ℓ l).pool)).filter
        (fun k => (xD χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η = y)).card ≤ Mm)
    (hSC : ∀ χ v, ∑ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (xC χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
        gWeight y * gEnergy η rs y v ≤ BC * (1 + ‖v‖)^(2*J))
    (hSD : ∀ χ v, ∑ y ∈ (Ls.sigma (fun l => (ℓ l).pool)).image
        (fun k => (xD χ k).toLabel (θ := θ) (mesh := mesh) (Z := Z) η),
        gWeight y * gEnergy η rs y v ≤ BD * (1 + ‖v‖)^(2*J)),
    (1 + r)^decay * ∑ l ∈ Ls, wt l *
      ‖labelBlock (childCharacter P.base ξ) t S (sourceCoefficient s ha 1) (ℓ l).C (ℓ l).D
        (ℓ l).hC (ℓ l).hD (ℓ l).U (ℓ l).R (ℓ l).rows W r (ℓ l).ρ (ℓ l).x X Y‖ ≤
      Cg * (windowBudget J t (Λc * Mm * BC) * windowBudget J t (Λc * Mm * BD)) := by
  obtain ⟨Cg, hCg, hgr⟩ := grouped_label_blocks W decay J J
  refine ⟨Cg, hCg, ?_⟩
  intro L θ mesh Z η P ξ Q m hm hml hm2 hQ72 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    hV₀ hCR S hSs hSz Λ Ls ℓ hfam wt hwt r hr t X Y hX hY Hs hH hmajor Λc BC BD hΛ hBC hBD Mm
    xC xD hjC hjD hAC hAD hGC hGD hDC hDD hsC hsD hgC hgD hcC hcD hdC hdD hrC hrD hiC hiD hSC hSD
  refine hgr r hr (childCharacter P.base ξ) t S (sourceCoefficient s ha 1) χ₀ Q m hQ72 hml hm2
    X Y hX hY ballProfile Hs hH (fun _ => ballProfile_nonneg _) Ls ℓ wt hwt hmajor (Λc * Mm * BC)
    (Λc * Mm * BD) (by positivity) (by positivity) ?_ ?_
  · exact column_hyp P ξ Q m hm hml hm2 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hV₀ hCR S
      hSs hSz Ls ℓ hfam wt hwt (fun l => (ℓ l).C) (fun l => (ℓ l).hC) (fun l I h => Or.inl h)
      Hs hH Λc BC hΛ J xC hjC hAC hGC hDC hsC hgC hcC hdC hrC Mm hBC hiC hSC
  · exact column_hyp P ξ Q m hm hml hm2 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hV₀ hCR S
      hSs hSz Ls ℓ hfam wt hwt (fun l => (ℓ l).D) (fun l => (ℓ l).hD) (fun l I h => Or.inr h)
      Hs hH Λc BD hΛ J xD hjD hAD hGD hDD hsD hgD hcD hdD hrD Mm hBD hiD hSD

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
