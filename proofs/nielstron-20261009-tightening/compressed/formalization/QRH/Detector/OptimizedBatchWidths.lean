import QRH.NumericFacts
import OAI.NumberTheory.DirichletL.Detector.DetectorBatch
import QRH.Geometry
/-! Width gates for the optimized positive slot vector. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.QRHProbeHighRowFamily
lemma physical_slot_widths {N : ℕ} (lengths : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<lengths j) (hsmall : ∀j,lengths j≤dmin*mesh)
    (hsum : ∑j,lengths j=QRH.ell) :
    (∀j,0<lengths j/d) ∧ (∀j,lengths j/d≤mesh) ∧ 7/37≤∑j,lengths j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hell0 := QRH.NumericFacts.ell_bounds.1
  have hellmin : (1/6:ℝ)≤QRH.ell := by norm_num [QRH.ell,QRH.tightTheta]
  have hm : 0≤mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,lengths j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    linarith
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith
end SevenEighths.QRHProbeHighRowFamily
end
end OAI
