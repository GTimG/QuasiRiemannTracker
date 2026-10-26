/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite width cells selected from the checked scalar slack and source fee. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyCells
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103StepScalar.UniformMargins
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph QRH.Record1252270103StepScalar

structure FiniteReferenceCells (cross cap K δ : ℝ) (cell : ℝ→ℝ) : Prop where
  finite_range : (Set.range cell).Finite
  bounds : ∀s∈Set.Icc cross cap,s≤cell s ∧ cell s≤cap ∧ 0≤cell s-s ∧ cell s-s≤δ
  radius_pos : ∀s∈Set.Icc cross cap,0<49/100-K*cell s

theorem FiniteReferenceCells.reference {cross cap K δ : ℝ} {cell : ℝ→ℝ}
    (h : FiniteReferenceCells cross cap K δ cell) : ReferenceWidthCells cross cap K cell := by
  intro s hlo hhi
  exact ⟨(h.bounds s ⟨hlo,hhi⟩).1,(h.bounds s ⟨hlo,hhi⟩).2.1,
    (h.radius_pos s ⟨hlo,hhi⟩).le⟩

theorem finite_reference_cells_from_margin (cross cap K margin δ : ℝ)
    (hm : 0<margin) (hδ : 0<δ)
    (hr : ∀b∈Set.Icc cross cap,margin≤49/100-K*b) :
    FiniteReferenceCells cross cap K δ (upperWidthCell cross cap δ) := by
  refine ⟨upperWidthCell_finite_range cross cap δ hδ,?_,?_⟩
  · intro s hs
    exact upperWidthCell_bounds cross cap δ s hδ hs.1 hs.2
  · intro s hs
    have hb:=upperWidthCell_bounds cross cap δ s hδ hs.1 hs.2
    exact hm.trans_le (hr _ ⟨hs.1.trans hb.1,hb.2.1⟩)

theorem nf_finite_width_cells (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ) :
    ∃margin δ : ℝ,0<margin ∧ 0<δ ∧ δ≤1 ∧
      |loss| *δ≤(n.allowance:ℝ) ∧ 2*(|loss| *δ)≤margin ∧
      FiniteReferenceCells (crossing n low) n.cap (11243277/2500000) δ
        (upperWidthCell (crossing n low) n.cap δ) ∧
      ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
        (∀j,margin/2≤sourceScalarReal (11243277/2500000) n low
          (upperWidthCell (crossing n low) n.cap δ s) j-|loss| *δ) ∧
        0≤sourceWeakReal n low (upperWidthCell (crossing n low) n.cap δ s) ∧
        ∀j,margin/2≤sourceDensityWidthReal n low high
          (upperWidthCell (crossing n low) n.cap δ s) ν j-|loss| *δ := by
  obtain ⟨margin,hm,hg⟩:=nf_uniform_margin n low high hv
  have ha' : 0<(n.allowance:ℝ) := by exact_mod_cast (nf_accounting_positive ha).1
  let δ:=widthRoundingScale margin n.allowance loss
  obtain ⟨hδ,hδ1,hfee,hslack⟩:=widthRoundingScale_spec margin n.allowance loss hm ha'
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have hh : (n.q:ℝ)≤((3/4:ℚ):ℝ):=Rat.cast_le.mpr hv.2.2.2.2.2.2.1
    norm_num at hh ⊢
    exact hh⟩
  have hcells : FiniteReferenceCells (crossing n low) n.cap (11243277/2500000) δ
      (upperWidthCell (crossing n low) n.cap δ) := by
    apply finite_reference_cells_from_margin _ _ _ margin δ hm hδ
    intro b hb
    simpa [sourceScalarReal] using (hg b hb _ hν).1 (9:Fin 16)
  refine ⟨margin,δ,hm,hδ,hδ1,hfee,hslack,hcells,?_⟩
  intro s hs ν hν'
  have hb:=hcells.bounds s hs
  obtain ⟨hg',hw,hd⟩:=hg _ ⟨hs.1.trans hb.1,hb.2.1⟩ ν hν'
  exact ⟨fun j=>by linarith [hg' j],hw,fun j=>by linarith [hd j]⟩

theorem seed_finite_width_cells (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ) :
    ∃margin δ : ℝ,0<margin ∧ 0<δ ∧ δ≤1 ∧
      |loss| *δ≤(n.allowance:ℝ) ∧ 2*(|loss| *δ)≤margin ∧
      FiniteReferenceCells (crossing n low) n.cap (112445673/25000000) δ
        (upperWidthCell (crossing n low) n.cap δ) ∧
      ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
        (∀j,margin/2≤sourceScalarReal (112445673/25000000) n low
          (upperWidthCell (crossing n low) n.cap δ s) j-|loss| *δ) ∧
        0≤sourceWeakReal n low (upperWidthCell (crossing n low) n.cap δ s) ∧
        ∀j : Fin 6,margin/2≤sourceDensityWidthReal n low none
          (upperWidthCell (crossing n low) n.cap δ s) ν (Fin.castLE (by decide) j)-|loss| *δ := by
  obtain ⟨margin,hm,hg⟩:=seed_uniform_margin n low hv
  have ha0 : n.allowance=1/10^12:=hv.2.2.2.2.2.2.2.2.2.2.2.1
  have ha' : 0<(n.allowance:ℝ) := by rw [ha0];norm_num
  let δ:=widthRoundingScale margin n.allowance loss
  obtain ⟨hδ,hδ1,hfee,hslack⟩:=widthRoundingScale_spec margin n.allowance loss hm ha'
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have hh : (n.q:ℝ)≤((3/4:ℚ):ℝ):=Rat.cast_le.mpr hv.2.2.2.2.2.2.1.le
    norm_num at hh ⊢
    exact hh⟩
  have hcells : FiniteReferenceCells (crossing n low) n.cap (112445673/25000000) δ
      (upperWidthCell (crossing n low) n.cap δ) := by
    apply finite_reference_cells_from_margin _ _ _ margin δ hm hδ
    intro b hb
    simpa [sourceScalarReal] using (hg b hb _ hν).1 (9:Fin 16)
  refine ⟨margin,δ,hm,hδ,hδ1,hfee,hslack,hcells,?_⟩
  intro s hs ν hν'
  have hb:=hcells.bounds s hs
  obtain ⟨hg',hw,hd⟩:=hg _ ⟨hs.1.trans hb.1,hb.2.1⟩ ν hν'
  exact ⟨fun j=>by linarith [hg' j],hw,fun j=>by linarith [hd j]⟩

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.nf_finite_width_cells
#print axioms QRH.Record1252270103Low.seed_finite_width_cells
