/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The exact native renorm/reindex producer preserves the whole fixed physical
partition; its shortened minimum and source volume keep the actual prefixes. -/
import Candidate.C092.transport.FixedFourierH15NativeRows
import Candidate.C092.transport.FixedFirstGeometry
import Candidate.C092.transport.ColoredGaussFrameProviderRenormFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.ColoredGaussFrameProvider
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {frameL mesh U : ℝ} {Θ : GData frameL}
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_FixedFourierH15NativeSelected_8746e5258a5182e8_001 {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _

lemma sourceVolume_eq_native {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) :
    sourceVolume s=MixedInnerExceptionalBlock.sourceVolume s := by
  unfold sourceVolume MixedInnerExceptionalBlock.sourceVolume
  rw [s.hpX]

/-- This is the genuine complete fixed physical partition, not a regular
one-sided replacement. The equality retains the original classifier, Fourier
kernel, allocation normalizer, four dyadic profiles and physical scalar. -/
theorem normalized_selected_fixed_terms (s : Source (Fin Θ.N) Θ.a Θ.b) (ha : 0<Θ.a)
    (hb : 0 ≤ Θ.b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (ω₁ ω₂ ψ : Character) (χ₀ : RayFourExpansion.RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) :
    RootColoredSeed.groupedPartTerms true (normalizedSelectedSource s hb cover G B J) ha
      (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t K Tsec Z ξ H =
    RootColoredSeed.groupedPartTerms true (restOf s hb cover G B J) ha
      (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t K Tsec Z ξ H := by
  unfold normalizedSelectedSource
  rw [groupedPartTerms_reindex,groupedPartTerms_renorm]

/-- The native selected source has genuinely absorbed its inherited pair
prefix. A second copy of that prefix is not silently charged or discarded. -/
theorem normalized_selected_prefix (s : Source (Fin Θ.N) Θ.a Θ.b) (hb : 0 ≤ Θ.b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) (C D : Id) :
    sourcePrefix (normalizedSelectedSource s hb cover G B J) C D=
      (C.absNorm:ℝ)*(D.absNorm:ℝ) := by
  simp [sourcePrefix,normalizedSelectedSource,reindexSource,renorm]

/-- The H15 volume is exactly the native frame volume on the original
surviving slot vectors. It is not the unshortened parent volume. -/
theorem normalized_selected_frame_volume (s : Source (Fin Θ.N) Θ.a Θ.b) (hb : 0 ≤ Θ.b)
    (cover : OriginalEnclosure s) (r : GSrc Θ mesh U)
    (hX₁ : r.X₁=s.X₁) (hX₂ : r.X₂=s.X₂) (hY₁ : r.Y₁=s.Y₁) (hY₂ : r.Y₂=s.Y₂)
    (hcan : Canonical s U r.χ r.w r.σ r.freq r.t r.R₀ s.H s.R s.d)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) (kLog : ℝ) :
    sourceVolume (normalizedSelectedSource s hb cover G B J)=
      (normalizedFrame s hb cover r hX₁ hX₂ hY₁ hY₂ G B J kLog).vol := by
  rw [sourceVolume_eq_native]
  exact (normalizedFrame_volume s hb cover r hX₁ hX₂ hY₁ hY₂ hcan G B J kLog).symm

/-- The actual first allocation supplies the required shortened minimum;
there is no original-scale lower-bound requirement on the selected child. -/
theorem normalized_selected_first_minimum_log (s : Source (Fin Θ.N) Θ.a Θ.b) (hb : 0 ≤ Θ.b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G ≠ 0)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (hd : s.d=(1,1)) (hU : 1<U) (hshort : U^(115/1000:ℝ) ≤ s.L) :
    max 0 (115/1000-Real.logb U (G.absNorm:ℝ)) ≤
      Real.logb U (max 1 (normalizedSelectedSource s hb cover G B J).L) :=
  QRH.Cycle092.FixedFramePacking.first_minimum_log s hb cover G hG B J hd U hU hshort

/-- Deleted original slots and the actual first divisor retain their full
volume payments. This uses the true selected source, including renorm. -/
theorem normalized_selected_first_volume (s : Source (Fin Θ.N) Θ.a Θ.b) (hb : 0 ≤ Θ.b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) :
    sourceVolume (normalizedSelectedSource s hb cover G B J)*
      (∏j:J,s.P j.val.val)*(G.absNorm:ℝ) ≤ (2:ℝ)^Θ.N*sourceVolume s := by
  rw [sourceVolume_eq_native,sourceVolume_eq_native]
  unfold normalizedSelectedSource
  rw [QRH.Cycle092.ColoredGaussFrameProvider.sourceVolume_reindex]
  simpa only [Fintype.card_fin] using
    QRH.Cycle092.FixedFramePacking.first_volume s hb cover G B J

#print axioms normalized_selected_fixed_terms
#print axioms normalized_selected_frame_volume
#print axioms normalized_selected_first_minimum_log
#print axioms normalized_selected_first_volume
end QRH.Cycle092.FixedFourierH15
