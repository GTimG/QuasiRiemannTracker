/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual nonfloor cell inherits all required geometric and buffered events. -/
import Candidate.C092.transport.SelectedNonfloorGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorPhysicalSelection
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open Cycle25.Numerator Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The actual upper row bound has the phase-bin collar already built into its dyad. -/
theorem actual_cell_conductor (D : BaselineData) (F : BaselineSourceData D) (padding : ℝ) :
    ∀ᶠ Z : ℝ in atTop, ∀ (idx grid : FreeRow → ℕ),
      ∀ k ∈ smallDyadicIndices (Z^(Geometry.h+padding)), ∀ i j : ℕ,
      (cellRows D F padding Z idx grid k i j).Nonempty →
      let d := sourceDyadConductor Z D.t k
      (1/100 : ℝ) ≤ d ∧ d ≤ Geometry.h+padding+2*D.t ∧
      ∀ u ∈ cellRows D F padding Z idx grid k i j, Z^(d-2*D.t) ≤ rowNorm u ∧ rowNorm u ≤ Z^(d-D.t) := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) (Geometry.h+padding+2*D.t) D.t
    (Geometry.h+padding) (by norm_num) (by norm_num) D.t_pos (le_refl _),
    eventually_gt_atTop (1:ℝ)] with Z hg hZ
  intro idx grid k hk i j hn
  let rows := SelectedActualIntegral.selectedRows D F padding Z grid
  let cell := cellRows D F padding Z idx grid k i j
  have hsubk : cell ⊆ rows ∩ dyadicRows 1 k := Finset.filter_subset _ _
  have hsub : cell ⊆ rows := hsubk.trans Finset.inter_subset_left
  have hm (u : FreeRow) (hu : u ∈ rows) := (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu
  have hrows (u : FreeRow) (hu : u ∈ rows) :
      u.val ≠ 1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^(Geometry.h+padding) := by
    have hb := mem_rowBand.mp (hm u hu).1
    exact ⟨hb.1, hb.2.1, hb.2.2.le⟩
  have hh := hg rows hrows k (hn.mono hsubk)
  obtain ⟨u, hu⟩ := hn
  have hup := hh.2.2.2.2.2 u (hsubk hu)
  have hlow := (hrows u (hsub hu)).2.1
  have hd' := (Real.rpow_le_rpow_left_iff hZ).mp (hlow.trans hup)
  refine ⟨by linarith [D.t_pos], hh.2.2.2.1, ?_⟩
  intro r hr
  refine ⟨?_,hh.2.2.2.2.2 r (hsubk hr)⟩
  apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans (hh.2.2.2.2.1 r (hsubk hr)).1
  unfold sourceDyadConductor; linarith [D.t_pos]

#print axioms actual_cell_conductor
end QRH.Cycle092.SelectedNonfloor
