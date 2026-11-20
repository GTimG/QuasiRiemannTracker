/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Exact colored canonical coefficient bridge, before any frame pricing. -/
import Candidate.C092.transport.RegularColoredFrameEnergy
import Candidate.C092.transport.ColoredGaussSelectionSecond
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabelAssembly12
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSectorLocalization CenteredMomentLattice
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalSource MixedRestrictedDictionary
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.Cycle092.TwistedRawSource QRH.Cycle092.RegularColoredForward
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance (priority := 2000) sumDecEq {κ κ₂ : Type*} : DecidableEq (κ⊕κ₂) := Classical.decEq _
variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The frame's original independently colored coefficient is precisely the
    selected source's coefficient, with its genuine norm-power profiles. -/
theorem sourceColumn_original {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→*₀ℂ) (seed : Id) :
    sourceColumn s ha ω₁ ω₂ seed =
      frameOriginalColumn ω₁ ω₂ s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        b s.X₁ s.X₂ s.Y₁ s.Y₂ := by
  unfold sourceColumn frameOriginalColumn
  congr 1
  funext v
  unfold MixedOriginalSecondZero.originalTuple
  ring

/-- Exact canonical source/label energy identification with two independent
    ordinary profiles. It preserves the original residual pool and keep. -/
theorem labelEnergy_source (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z)
    (hW₁ : rs.W₁=s.W₁) (hW₂ : rs.W₂=s.W₂)
    (ht₁ : rs.t₁=s.t₁/(2*Real.pi)) (ht₂ : rs.t₂=s.t₂/(2*Real.pi))
    (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂) (hY₁ : rs.Y₁=s.Y₁) (hY₂ : rs.Y₂=s.Y₂)
    (τ ω₁ ω₂ : Character) (Q : Id) (n : Fin 4→ℤ) (R G : Id) (hG : G≠0)
    (seed D : Id) (H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (v : ℝ)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ H R d) (ha : 0<θ.a) :
    frameLabelEnergy θ.rayM θ.Hray θ.hH θ.W θ.η₀ rs.χ Z rs.w rs.σ rs.freq rs.t rs.R₀
      τ ω₁ ω₂ Q n θ.Cap θ.Lcap R G hG seed D H rs.W₁ rs.W₂ rs.t₁ rs.t₂ θ.b
      rs.X₁ rs.X₂ rs.Y₁ rs.Y₂ d hd v =
    sourceRestrictedEnergy (canonicalRadial τ Q n).keep (residualPool G hG (sourceColumns s))
      (fun I=>if IsCoprime G I ∧ D∣I then
        sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) seed (G*I) else 0)
      (heightCoeff τ v) ballProfile (dyadicScale (n 1)) := by
  obtain ⟨hS,hH,hpool,hν,hWs,hP,hR,hdd⟩ := hcan
  have hpool' := funext hpool
  have hν' := funext hν
  have hWs' := funext hWs
  have hP' := funext hP
  rw [hW₁,hW₂,ht₁,ht₂,hX₁,hX₂,hY₁,hY₂,sourceColumn_original]
  unfold frameLabelEnergy sourceColumns MixedPrincipalAllocations.tuplePools
  rw [normPowerProfile_eq_phase,normPowerProfile_eq_phase]
  cases s
  simp only at hS hH hpool' hν' hWs' hP' hR hdd ⊢
  subst hS hH hpool' hν' hWs' hP' hR hdd
  rfl

#print axioms sourceColumn_original
#print axioms labelEnergy_source
end
end QRH.Cycle092.ColoredGaussFrameProvider
