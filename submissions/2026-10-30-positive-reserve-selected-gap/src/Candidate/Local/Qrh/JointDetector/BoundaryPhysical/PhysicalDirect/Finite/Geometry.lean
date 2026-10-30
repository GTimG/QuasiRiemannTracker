/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Finite.Geometry (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Finite.Cells
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.GenericScalar

set_option autoImplicit false
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.FiniteNumerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
variable [scheme : QRH.Record1252270103Return.CountScheme] [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record1252270103Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly

/-- All cell geometry is uniform before the live row labels. -/
theorem actual_cell_geometry (A : ChosenData) (η : Character) (τ : ℝ) (n : ℕ) :
    ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ∀k i j : ℕ,(cellRows A.D A.F Z idx grid k i j).Nonempty →
        CellFacts A.D A.F η Z τ (cellRows A.D A.F Z idx grid k i j)
          (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.dp A.D.t
    (Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h+rowPadding) (by norm_num) (by norm_num) A.D.t_pos
    (padded_row_cutoff A.D A.P),eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  intro idx grid hsel k i j hne
  let R := selectedRows A.D A.F Z grid
  let Rij := cellRows A.D A.F Z idx grid k i j
  have hsubk : Rij⊆R∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsub : Rij⊆R := hsubk.trans Finset.inter_subset_left
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hg:=hgeo R (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
    (hne.mono hsubk)
  obtain ⟨u,hu⟩ := hne
  have hmem := (mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
  have hgu := ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).2.2
  have hjpos : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero (hmem.2.2 ▸ hgu)
  have ha : (51/100:ℝ)<51/100+A.D.e*j := by nlinarith [A.D.e_pos]
  have hai : 51/100+A.D.e*j≤7/8 := by simpa only [hmem.2.2] using (hsel.2.1 u).2.1
  have hZp : 0< Z := zero_lt_one.trans hZ
  refine ⟨hg.2.2.1,hg.2.2.2.1,ha,hai,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
      (hrows u (hsub hu)).2.2.1,hg.2.2.2.2.2 u (hsubk hu)⟩
  · intro u hu
    constructor
    · rw [←Real.rpow_mul hZp.le]
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans (hrows u (hsub hu)).2.1
      have hd:=hg.2.2.2.1
      have hcap : Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.dp≤1 := by
        change QRH.Record1252270103Return.Geometry.h+1/10000000000000000000000≤1
        linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.h_interval.2]
      nlinarith
    · exact (hg.2.2.2.2.2 u (hsubk hu)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [A.D.t_pos]))
  · intro u hu
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 u (hsubk hu)).1
  · intro u hu
    exact (hsel.2.2 u ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).1
      (hrows u (hsub hu)).2.2.1).1
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    rwa [hm.2.1,hm.2.2] at hb
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    simpa only [hm.2.1,hm.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.FiniteNumerator
