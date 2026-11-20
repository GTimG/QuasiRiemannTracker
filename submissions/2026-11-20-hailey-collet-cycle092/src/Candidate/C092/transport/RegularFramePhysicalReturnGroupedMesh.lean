/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Early-mesh and eventual-scale geometry for the full independently colored
regular summed price on the authentic native SideFrame.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafGrouped
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight scale_pos)
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularFramePhysicalReturnGroupedMesh_86176274220ba1cf_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}



/-- Native eventual-scale geometry for the independently colored regular
sum. The mesh is fixed before structural data and every live row. -/
theorem terminal_frame_grouped_common_mesh (price : Price) (Mmin Mmax : ℝ)
    (hMmin : 0≤ Mmin) (hMmax : Mmax<2) (hL : 0≤ L)
    (ε : ℝ) (hε : 0<ε) :
    ∃ meshMax : ℝ,0< meshMax ∧ ∀mesh:ℝ,0< mesh → mesh≤ meshMax →
    ∀ θ : GData L,∀ J deg : ℕ,∃ controls : Finset (ℕ×ℕ),∃ Ctot : ℝ,0< Ctot ∧
    ∀ᶠ Z:ℝ in Filter.atTop,∀ (η ω₁ ω₂ : Character) (r : GSrc θ mesh Z)
      (labels : Finset (GLabel θ mesh Z)) (w₀ H Hsource Cterm v : ℝ),0≤ Cterm →
      Second.AdmissibleGroup (frameSideFrame L θ mesh ω₁ ω₂ η Z) Mmin Mmax mesh ε Z r labels H →
      let M := Real.logb Z (2*Z^(H+mesh))
      let Pbd := gP r+2*Real.logb Z 3
      frameRectangularLeaves θ η ω₁ ω₂ r v M Hsource
        (price.f w₀ Pbd (∑i,r.w i) M-(5/6)*max 0 (Hsource-M))
        (Cterm*r.height^deg*(1+‖v‖)^(2*deg)) Pbd J →
      (∑x∈labels,gWeight x*framegEnergy ω₁ ω₂ η r x v) ≤
        Ctot*Cterm*gAmp L θ mesh η Z r deg controls*(1+‖v‖)^(2*deg)*
          Z^(r.colLog+r.twistLog+price.f w₀ (gP r) (∑i,r.w i) H+ε) := by
  have hlip := price.lip_nonneg
  let meshMax := min (1/2:ℝ) (min ((2-Mmax)/2) (ε/(8*(3+price.lip))))
  have hm0 : 0< meshMax := lt_min (by norm_num)
    (lt_min (by linarith) (by positivity))
  refine ⟨meshMax,hm0,?_⟩
  intro mesh hmesh hmm θ J deg
  have hm2 : mesh≤1/2 := hmm.trans (min_le_left _ _)
  have hmrad : mesh≤(2-Mmax)/2 := hmm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hme : mesh≤ε/(8*(3+price.lip)) :=
    hmm.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmε : (3+price.lip)*mesh≤ε/8 := by
    rw [le_div_iff₀ (by positivity)] at hme
    linarith
  obtain ⟨controls,Ctot,hCtot,hbound⟩ := terminal_frame_grouped_at price Mmin Mmax hMmin θ hL ε hε J deg
  refine ⟨controls,Ctot,hCtot,?_⟩
  filter_upwards [eventually_dyadic_count ((Fintype.card DictIdx:ℝ)*2^θ.N) L θ.b (ε/16) (by positivity),
    eventually_logb_le 3 (ε/(16*(1+3*price.lip))) (by positivity),
    eventually_logb_le 3 (1/2) (by norm_num),
    eventually_logb_le 2 ((2-Mmax)/2) (by linarith),
    Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/2)).eventually_ge_atTop (2:ℝ)]
    with Z hcount hl3 hl3' hl2 hZ1 hZ32
  have hl3e : (1+3*price.lip)*Real.logb Z 3≤ε/16 := by
    rw [le_div_iff₀ (by positivity)] at hl3
    linarith
  exact hbound mesh Z hmesh hm2 hmε hZ1 (by linarith) hcount hl3e hl3' hZ32

#print axioms terminal_frame_grouped_common_mesh
end
end QRH.Cycle092.RegularColoredForward
