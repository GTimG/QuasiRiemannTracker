/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual nonfloor cell inherits all required geometric and buffered events. -/
import Candidate.C092.transport.SelectedNonfloorAssembly

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

/-- Geometry and detector facts on every literal dyadic/height/grid cell.
These facts are consequences of selection, rather than source assumptions. -/
theorem actual_cell_geometry (D : BaselineData) (F : BaselineSourceData D)
    (padding : ℝ) (hpadding : 0 < padding) (hpad : padding+2*D.t ≤ 1/10000000000) :
    ∀ᶠ Z : ℝ in atTop, ∀ (tau : ℝ) (n : ℕ) (η : Character) (idx grid : FreeRow → ℕ),
      selected D F padding tau n η Z idx grid →
      ∀ k ∈ smallDyadicIndices (Z^(Geometry.h+padding)), ∀ i j : ℕ,
      (cellRows D F padding Z idx grid k i j).Nonempty →
      let d := sourceDyadConductor Z D.t k
      let a : ℝ := 51/100+D.e*j
      0 < d ∧ 51/100 ≤ a ∧ a ≤ 7/8 ∧
      (∀ u ∈ cellRows D F padding Z idx grid k i j, u.val ≠ 1 ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        Z^(d-2*D.t) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) ∧
      (∀ u ∈ cellRows D F padding Z idx grid k i j, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^tau) < a+2*D.e) := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) (Geometry.h+padding+2*D.t) D.t
    (Geometry.h+padding) (by norm_num) (by norm_num) D.t_pos (le_refl _),
    eventually_gt_atTop (1:ℝ)] with Z hg hZ
  intro tau n η idx grid hs k hk i j hn
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
  have hbin := (mem_cubeBinRows (rows∩dyadicRows 1 k) idx grid i j u).mp hu
  have ha := hs.2.1 u
  have halpha : (51/100:ℝ) ≤ 51/100+D.e*j ∧ 51/100+D.e*j ≤ 7/8 := by
    simpa only [hbin.2.2] using And.intro ha.1 ha.2.1
  refine ⟨lt_of_lt_of_le (by norm_num : (0:ℝ)<1/200) hh.2.2.1, halpha.1, halpha.2, ?_, ?_⟩
  · intro v hv
    have hlo := (hh.2.2.2.2.1 v (hsubk hv)).1
    have hlow : Z^(sourceDyadConductor Z D.t k-2*D.t) ≤ rowNorm v := by
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans hlo
      unfold sourceDyadConductor
      linarith [D.t_pos]
    have hup := hh.2.2.2.2.2 v (hsubk hv)
    refine ⟨(hrows v (hsub hv)).1, (hm v (hsub hv)).2.1, hlow, ?_⟩
    exact hup.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [D.t_pos]))
  · intro v hv
    have hbin := (mem_cubeBinRows (rows∩dyadicRows 1 k) idx grid i j v).mp hv
    simpa only [hbin.2.1, hbin.2.2] using (hs.2.1 v).2.2.2.2.1

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.actual_cell_geometry
