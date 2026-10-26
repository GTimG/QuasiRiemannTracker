/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact six rational facets of the actual detector root, C31 HF6 / NF12. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.Domains

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

def facet (nu B lam h S Q : ℝ) : Branch → ℝ := fun k =>
  (![ ![3*nu*w nu/densityDenom nu*S,
       2*nu*w nu/densityDenom nu*S+nu*w nu*h/densityDenom nu*Q,
       2*nu*w nu*(lam-1)/(lam*densityDenom nu-10)*S+
         nu*w nu*(B*densityDenom nu-10)/(densityDenom nu*(lam*densityDenom nu-10))*Q],
      ![nu*w nu/(10+3*w nu)*S+
          2*nu*(w nu)^2/(densityDenom nu*(10+3*w nu))*Q,
        (2*nu*(w nu)^2/(densityDenom nu*(10+3*w nu))+nu*w nu*h/(10+3*w nu))*Q,
        nu*w nu*(2*w nu*(lam-1)+B*densityDenom nu-10)/
          (densityDenom nu*(lam*(10+3*w nu)-(10+2*w nu)))*Q] ] k.1) k.2

theorem facet_denominators {nu lam : ℝ} (hnu0 : 1/2≤nu)
    (hnu1 : nu≤3/4) (hlam : 1<lam) :
    0<densityDenom nu ∧ 0<10+3*w nu ∧ 0<lam*densityDenom nu-10 ∧
      0<lam*(10+3*w nu)-(10+2*w nu) := by
  have hw : 0<w nu := by dsimp [w]; linarith
  have ht : densityDenom nu=10+w nu := by dsimp [w,densityDenom]; ring
  have hx : 0<(lam-1)*densityDenom nu := by rw [ht]; positivity
  have hy : 0<(lam-1)*(10+3*w nu) := by positivity
  rw [ht] at *
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> nlinarith

theorem branch_gain_eq_facet {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) (k : Branch) :
    nu*(branchRoot nu B lam h S Q k-baseXi nu*Q)=facet nu B lam h S Q k := by
  have hd := facet_denominators hnu0 hnu1 hlam
  have hl : lam-1≠0 := by linarith
  have hs := (branchSlope_pos hnu0 hnu1 hlam k).ne'
  rcases k with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [branchRoot,branchSlope,branchOffset,inverseSlope,inverseOffset,
      plainSlope,plainOffset,baseXi,facet] at hs ⊢ <;>
    dsimp [densityDenom,w] at hd hs ⊢ <;>
    field_simp (discharger := nlinarith [hd.1,hd.2.1,hd.2.2.1,hd.2.2.2]) <;> ring

theorem gain_eq_min_facets {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) :
    gain nu B lam h S Q=Finset.univ.inf' Finset.univ_nonempty (facet nu B lam h S Q) := by
  have hn : 0≤nu := by linarith
  apply le_antisymm
  · apply Finset.le_inf'
    intro k _
    rw [←branch_gain_eq_facet hnu0 hnu1 hlam k]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Finset.inf'_le _ (Finset.mem_univ k)) _) hn
  · obtain ⟨k,_,hk⟩ := (Finset.inf'_le_iff (f:=branchRoot nu B lam h S Q)
      Finset.univ_nonempty).mp (le_refl (xi nu B lam h S Q))
    have he : branchRoot nu B lam h S Q k=xi nu B lam h S Q :=
      le_antisymm hk (Finset.inf'_le _ (Finset.mem_univ k))
    have hh := Finset.inf'_le (facet nu B lam h S Q) (Finset.mem_univ k)
    rw [←branch_gain_eq_facet hnu0 hnu1 hlam k,he] at hh
    exact hh

/-- Six certified inequalities apply to the same earlier face and the same
width/radius/density point, so their minimum pays the actual detector gain. -/
theorem regular_gate_of_six {nu B lam h S Q H fee : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam)
    (hgates : ∀k : Branch,fee<H+facet nu B lam h S Q k) :
    fee<H+gain nu B lam h S Q := by
  rw [gain_eq_min_facets hnu0 hnu1 hlam]
  obtain ⟨k,_,hk⟩ := (Finset.inf'_le_iff (f:=facet nu B lam h S Q)
    Finset.univ_nonempty).mp
    (le_refl (Finset.univ.inf' Finset.univ_nonempty (facet nu B lam h S Q)))
  linarith [hgates k]


end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.branch_gain_eq_facet
#print axioms QRH.Record1252270103Source.High.gain_eq_min_facets
#print axioms QRH.Record1252270103Source.High.regular_gate_of_six
