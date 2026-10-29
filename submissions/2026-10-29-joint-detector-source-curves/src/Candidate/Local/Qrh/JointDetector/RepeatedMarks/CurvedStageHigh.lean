/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedHighCells
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveThreshold
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceFromCores

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set HighTemplates CurveHighTemplates BernsteinBox

/-- A complete finite cell cover, including the affine divider on each cell.
Its hypotheses are scalar conditions on a closed physical width interval. -/
def CellsCover (p : Params) (phi ray : ℝ) (combined : Bool)
    {n : ℕ} (cells : Fin n → HighCell) : Prop :=
  ∀ ν v : ℝ, v ∈ Icc (0:ℝ) (p.c-crossing p) →
    matchedCut p phi v ≤ ν → ν ≤ 3/4 → ∃ i : Fin n,
      ν ∈ Icc (cells i).lo (cells i).hi ∧
      v ∈ Icc (cells i).vl (cells i).vh ∧
      0 < (cells i).e0+(cells i).ev*v ∧
      (cells i).k/((cells i).e0+(cells i).ev*v) ≤ ν ∧
      (cells i).a0+(cells i).a1*ν =
        if combined then max (250001/500000:ℝ) (ray*ν) else ν

structure StageHighCertificate (p : Params) (phi floor ray : ℝ) (combined : Bool)
    {n : ℕ} (bank : Fin n → HighCell) : Prop where
  geometry : GeometryCertificate p phi floor
  parent_slope : (3/2:ℝ) ≤ p.L0
  selected_cap : combined = true → p.c0 ≤ 1/10
  cells : ∀ i, HighCellCertificate p (bank i) combined
  cover : CellsCover p phi ray combined bank

namespace StageHighCertificate
variable {p : Params} {phi floor ray : ℝ} {combined : Bool} {n : ℕ} {cells : Fin n → HighCell}
    (g : StageHighCertificate p phi floor ray combined cells)
include g

theorem all_amplitudes (ν v : ℝ) (hv : v ∈ Icc (0:ℝ) (p.c-crossing p))
    (hνlo : matchedCut p phi v ≤ ν) (hνhi : ν ≤ 3/4) :
    ∀ a ∈ Icc (0:ℝ) ν,
      ν*(p.B-p.L*(crossing p+v))+
        ((if combined then combineSelected (rawRepeatedCountRate p.B0 p.L0 (1/10)) ν a
          else rawRepeatedCountRate p.B0 p.L0 (1/10) ν a)-1)*(1-6*(p.A*v/(1+p.D*v)))+
        a*(crossing p+v-p.A*v/(1+p.D*v)) ≤ p.A*v/(1+p.D*v)-highReserve := by
  obtain ⟨i,hν,hvcell,hE,hcut,halpha⟩ := g.cover ν v hv hνlo hνhi
  let cell := cells i
  have hc := g.cells i
  have hνp : 0 < ν := hc.density_pos.trans_le hν.1
  have ha := hc.alpha_bounds hν
  have hamp := hc.amplitude_nonneg hν
  have hp := hc.polynomials_nonneg hvcell hE hcut hν.2
  have hv0 := hv.1
  have hDv := mul_nonneg g.geometry.D_nonneg hv0
  have hW : 0 < 1+p.D*v := by linarith
  let u := p.A*v/(1+p.D*v)
  have hu0 : 0 ≤ u := div_nonneg (mul_nonneg g.geometry.A_pos.le hv0) hW.le
  have huv : u ≤ v := by
    apply (div_le_iff₀ hW).2
    have hAv := mul_le_mul_of_nonneg_right g.geometry.A_lt.le hv0
    nlinarith [mul_nonneg hv0 hDv]
  have hs0 : 0 ≤ crossing p := g.geometry.face.cross_nonneg
  have hS0 : 0 ≤ crossing p+v-u := by linarith
  have hratio : crossing p*(1-6*u) ≤ crossing p+v-u := by
    nlinarith [mul_nonneg hs0 hu0]
  obtain ⟨rg,hrg,hgeom⟩ := g.geometry.signs.nominal_uniform
    g.geometry.width_pos g.geometry.D_nonneg
  have hheight := hgeom v hv 0
  norm_num [nominalGeometry] at hheight
  have hH : 0 ≤ 1-6*u := by dsimp [u]; linarith
  have hcapPoly : 0 ≤ powerEval
      (CurveHighTemplates.capPower p.B0 p.L0 (1/10) cell.a0 cell.a1
        p.B p.L (crossing p) p.A p.D highReserve) ν v := by
    simpa [cellPower,cell] using hp 0 (Or.inl (by norm_num))
  have hbudgetPoly : 0 ≤ powerEval
      (CurveHighTemplates.budgetPower p.B0 p.L0 (1/10) cell.a0 cell.a1
        p.B p.L (crossing p) p.A p.D highReserve) ν v := by
    simpa [cellPower,cell] using hp 1 (Or.inl (by norm_num))
  have htailPoly : 0 ≤ powerEval
      (CurveHighTemplates.tailPower p.B0 p.L0 (1/10) cell.a0 cell.a1
        p.B p.L (crossing p) p.A p.D highReserve) ν v := by
    simpa [cellPower,cell] using hp 2 (Or.inl (by norm_num))
  have hcap := cap_weighted_divider p.B0 p.L0 (1/10) cell.a0 cell.a1
    p.B p.L (crossing p) p.A p.D highReserve ν v hW hνp hνhi ha.1 ha.2 hcapPoly
  have hbudget := budget_weighted_divider p.B0 p.L0 (1/10) cell.a0 cell.a1
    p.B p.L (crossing p) p.A p.D highReserve ν v hW hνp hνhi ha.1 ha.2 g.parent_slope hbudgetPoly
  have htail := tail_weighted_divider p.B0 p.L0 (1/10) cell.a0 cell.a1
    p.B p.L (crossing p) p.A p.D highReserve ν v hW htailPoly
  have hraw := raw_divider_bound_of_branches hH hcap hbudget htail
  cases combined with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at halpha ⊢
    intro a ha'
    apply affine_raw_weighted_bound hνp hνhi ha.1 ha.2 g.parent_slope
      hH hS0 hratio hamp.1 hamp.2 hraw a
    simpa only [halpha] using ha'
  | true =>
    simp only [ite_true] at halpha ⊢
    have hapos : (500001/1000000:ℝ) ≤ cell.a0+cell.a1*ν := by
      rw [halpha]
      exact (by norm_num : (500001/1000000:ℝ) ≤ 250001/500000).trans (le_max_left _ _)
    have hcapGeom := hgeom v hv 1
    norm_num [nominalGeometry] at hcapGeom
    have hSup : crossing p+v-u ≤ (1-6*u)/10 := by
      have hsc := mul_le_mul_of_nonneg_right (g.selected_cap rfl) hH
      dsimp [u] at *
      nlinarith
    have hselectedPoly : 0 ≤ powerEval
        (CurveHighTemplates.selectedPower p.B0 p.L0 (1/10) cell.a0 cell.a1
          p.B p.L (crossing p) p.A p.D highReserve) ν v := by
      simpa [cellPower,cell] using hp 3 (Or.inr rfl)
    have hselected := selected_weighted_divider p.B0 p.L0 (1/10) cell.a0 cell.a1
      p.B p.L (crossing p) p.A p.D highReserve ν v hW hνhi ha.2 hselectedPoly
    exact affine_combined_weighted_bound hνp hνhi hapos ha.2 g.parent_slope
      hH hS0 hratio hSup hamp.1 hamp.2 hraw hselected

/-- The literal count family at the live bounded density cut. -/
def family (w : ℝ) : WeightedFamily :=
  repeatedFamily p.B0 p.L0 (1/10) (cut p phi w) g.geometry.B0_pos.le
    g.geometry.face.B₀_lt.le g.parent_slope (by norm_num) (by norm_num)
    ⟨g.geometry.floor_pos.trans_le (g.geometry.cut_bounds w).1,
      (g.geometry.cut_bounds w).2⟩ combined

/-- Every label in the full affine supremum has the certified reserve. -/
theorem highReserve (w : ℝ) (hw : w∈Icc (crossing p) p.c) :
    HighReserve (g.family w) p.B p.L w
      (QRH.SilDensitySplit.Hybrid.sel p.A p.D (w-crossing p))
      CurvedSourceStep.highReserve := by
  unfold family repeatedFamily
  apply familyOfRate_highReserve
  intro ν hν a ha
  have hv : w-crossing p∈Icc (0:ℝ) (p.c-crossing p) :=
    ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have hcut : cut p phi w=matchedCut p phi (w-crossing p) := by
    unfold cut
    rw [clippedExcess_eq hw]
  have hh := g.all_amplitudes ν (w-crossing p) hv
    (by rw [←hcut];exact hν.1) hν.2 a ha
  have he : crossing p+(w-crossing p)=w := by ring
  simpa only [he,QRH.SilDensitySplit.Hybrid.sel] using hh

/-- The finite geometry and whole-amplitude certificates supply the
actual source-step ledger without another HIGH assumption. -/
theorem gates : Gates p (cut p phi) g.family := by
  apply g.geometry.gates g.family
  exact ⟨CurvedSourceStep.highReserve,by norm_num [CurvedSourceStep.highReserve],
    fun w hw=>g.highReserve w hw⟩

/-- Compose the certified curved stage with the genuine packed supplier.
The physical core count and selected norm remain explicit analytic inlets
here; the final source chain instantiates both with their proved providers. -/
theorem source_step
    (hf : (2/5:ℝ)≤floor)
    (hselectedFloor : combined=true → (50001/100000:ℝ)≤floor)
    (hnorm : FineNaturalCount.ActualSelectedSlotNorm)
    (hcore : PhysicalCoreCount floor p.B0 p.L0 (1/10))
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  exact CurvedSourceStep.source_step_of_physicalCoreCount p (1/10) floor
    g.geometry.face.B₀_lt.le g.parent_slope (by norm_num) (by norm_num) hf
    (cut p phi) g.geometry.cut_bounds combined hselectedFloor hnorm
    g.geometry.B0_pos.le g.gates hcore hβ hp

end StageHighCertificate
#print axioms StageHighCertificate.all_amplitudes
#print axioms StageHighCertificate.gates
#print axioms StageHighCertificate.source_step
end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
