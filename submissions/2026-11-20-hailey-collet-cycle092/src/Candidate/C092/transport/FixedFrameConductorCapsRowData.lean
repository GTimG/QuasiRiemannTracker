/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Hidden actual class preimages and authentic pointwise H15 row witnesses. -/
import Candidate.C092.transport.FixedFrameRowWitnessActual
import Candidate.C092.transport.FixedFrameConductorCapsRows
import Candidate.C092.transport.FixedFrameSeam
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedFrameConductorCaps
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization CenteredMomentRowNorm CenteredMomentSecondSectorColumns
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentSourceRow CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
open Filter QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

theorem eventually_actual_row_data (η : Character) (Bcap : ℝ) (hBcap : 27≤Bcap) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀ (C₀ E₀ : Id) (hC₀ : Supported C₀)
    (U₀ : Finset (CenteredMomentCanonicalFirst.CommonIndex C₀ E₀))
    (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C₀ E₀ hC₀ U₀ ξ₁ ξ₂)
    (P : SidePack η), (P.base=F.left ∨ P.base=F.right) → (C₀.absNorm:ℝ)≤Z^(8:ℝ) →
    ∀ {L mesh : ℝ} {θ : GData L} (ξ : RayFourExpansion.RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z)
    (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d)
    (hH : commonH rs≤19/10) (hR : (s.R.absNorm:ℝ)≤Z^(8:ℝ))
    (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R) (χ₀ : RayFourExpansion.RayCharacter)
    (Q : Id) (hQ : Q≠0) (m : O) (t Kc R H : ℝ)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayFourExpansion.RayCharacter)
    (x : GLabel θ mesh Z)
    (hx : x∈FixedPhysicalClassLedger.actualFrameLabels η s ha ω₁ ω₂ (childCharacter P.base ξ)
      χ₀ Q m t Kc R H rs P.j₀ ξ g n χ) (v : ℝ) (z : O)
    (hne : FixedPhysicalClassLedger.rowEnergy s ha ω₁ ω₂ η rs Q x v z≠0),
    ∀ good : Supported x.G,FixedFrameSeam.RowData s ha ω₁ ω₂ η rs Q v Bcap x good z := by
  filter_upwards [eventually_actual_conductor η] with Z hc
  refine ⟨hc.1,?_⟩
  intro C₀ E₀ hC₀ U₀ ξ₁ ξ₂ F P hbase hcap L mesh θ ξ s ha ω₁ ω₂ rs hX₁ hX₂ hcan
    hH hR hV₀ hCR χ₀ Q hQ m t Kc R H g hg n χ x hx v z hne good
  obtain ⟨l,E,hl,hE,hxfr,hxG,hxD,hxd,hxs,hprefix,hvol,hG,D,hηD,hDQ,hM,hA,hzD,hheight,hrow⟩ :=
    FixedFrameRowWitness.actual_row_witness P ξ s ha ω₁ ω₂ rs hX₁ hX₂ hcan hV₀ hCR
      χ₀ Q hQ m t Kc R H g hg n χ x hx v z hne
  have hf : Fits η rs x := by
    by_contra hn
    exact hne (by simp only [FixedPhysicalClassLedger.rowEnergy,dif_neg hn])
  have hball : (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (x.n 1))).re≠0 := by
    intro hn
    exact hne (hrow.trans (by rw [hn,mul_zero]))
  have htw : x.twist=lA (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) l := by
    rw [hxfr]
    rfl
  have hcond : (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ)≤Z^(27:ℝ) := by
    rw [hηD,hM,hA,hzD,←htw]
    exact hc.2 C₀ E₀ hC₀ U₀ ξ₁ ξ₂ F P.base hbase hcap s rs x hf hH hR ξ χ z
      (fixed_ball_support z (x.n 1) hball)
  refine ⟨D,childCharacter P.base ξ,χ,hDQ,hηD,hM,
    hcond.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le hBcap),?_⟩
  exact hrow

#print axioms eventually_actual_row_data
end
end QRH.Cycle092.FixedFrameConductorCaps
