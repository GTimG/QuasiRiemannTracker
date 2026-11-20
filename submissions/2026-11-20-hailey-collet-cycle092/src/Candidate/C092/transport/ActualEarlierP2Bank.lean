/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One mesh and finite uniform source metadata on all actual native
dictionary anchors from strictly earlier ordered source bands. -/
import Candidate.C092.transport.RegularP2AnchorBank
import Candidate.C092.transport.RegularColoredTerminalLeafAllSource
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalFixedRaySource QRH.SilDensitySplit.CubeFree.Packet
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle090 QRH.SourceCertificate
namespace QRH.Cycle092.RegularFramePhysicalReturn
local notation "O"=>HeckeFamily.O

theorem actual_earlier_p2_bank {n y:ℝ} (hbeta:(51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (cover:EarlierCover PairOpenWidth y) (hy0:sourceY0  ≤  y) (hy1:y  ≤  sourceY)
    (hyn:y  ≤  n) (hn:n  ≤  sourceRatio*y) :
    ∃ m:ℝ,0 < m ∧ ∀ mesh:ℝ,mesh  ≤  m → ∀ (N:ℕ) (M:Ideal O) [NeZero M]
    (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M  ≤  Hr) (W:ℝ→ℂ),
    ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ:ℝ,2  ≤  bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η base ω₁ ω₂:Character) (Q:Ideal O),Q  ≤  M →
    internalQ Q (base.product ω₁)≠0 → internalQ Q (base.product ω₁)≠⊤ → internalQ Q (base.product ω₁) ≤ Ideal.span {(72:O)} →
    internalQ Q (base.product ω₂)≠0 → internalQ Q (base.product ω₂)≠⊤ → internalQ Q (base.product ω₂) ≤ Ideal.span {(72:O)} →
    ∃ d:Fin (N+1)→ℕ,∃ S:Fin (N+1)→Finset (ℕ×ℕ),∃ C:Fin (N+1)→ℝ, (∀k,0<C k) ∧
      ∀k,∀j:DictIdx,∀ᶠ U:ℝ in atTop,
        OrderedP2At (Fin k.val) M Hr hHr W n y mesh U (anchors η j) base ω₁ ω₂ Q (d k) (S k) (C k) := by
  obtain ⟨m,hm,hsource⟩:=terminal_genuine_ordered_source hbeta cover hy0 hy1 hyn hn
  refine ⟨m,hm,?_⟩
  intro mesh hmesh N M hM Hr hHr W hW hWs bΦ hbΦ hΦ η base ω₁ ω₂ Q hQM hn₁ ht₁ h72₁ hn₂ ht₂ h72₂
  apply all_anchor_p2 N M Hr hHr W n y m mesh hmesh η base ω₁ ω₂ Q
  intro k j
  exact hsource (Fin k.val) M Hr hHr W hW hWs bΦ hbΦ hΦ (anchors η j) base ω₁ ω₂ Q hQM hn₁ ht₁ h72₁ hn₂ ht₂ h72₂

#print axioms actual_earlier_p2_bank
end QRH.Cycle092.RegularFramePhysicalReturn
