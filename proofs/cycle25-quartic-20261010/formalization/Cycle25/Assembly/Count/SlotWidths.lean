import OAI.NumberTheory.DirichletL.Detector.DetectorBatch
namespace OAI.SevenEighths.Cycle25WeightedHighRowFamily
noncomputable section
open scoped BigOperators
lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin dmax mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdmax : d≤dmax)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsupply : (7/37)*dmax≤∑j,ell j) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤mesh := by
    by_contra hn
    have hneg : mesh<0 := lt_of_not_ge hn
    have hsum : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hneg.le)
    have hmax : 0<dmax := hd0.trans_le hdmax
    nlinarith
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div]
    apply (le_div_iff₀ hd0).mpr
    nlinarith
end
end OAI.SevenEighths.Cycle25WeightedHighRowFamily
