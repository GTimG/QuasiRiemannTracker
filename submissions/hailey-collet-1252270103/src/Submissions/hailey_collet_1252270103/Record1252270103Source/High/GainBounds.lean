/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.Facets
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

def phi (nu : ℝ) := 3*nu*w nu/densityDenom nu
def cmax (nu : ℝ) := nu*(1-baseXi nu)
def rowCoefficient (nu B lam h : ℝ) (k : Branch) :=
  nu*(branchRoot nu B lam h 0 1 k-baseXi nu)

theorem branchRoot_linear (nu B lam h S Q : ℝ) (k : Branch) :
    branchRoot nu B lam h S Q k=
      branchRoot nu B lam h 1 0 k*S+branchRoot nu B lam h 0 1 k*Q := by
  rcases k with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [branchRoot,branchOffset,inverseOffset,plainOffset] <;> ring

theorem rowCoefficient_bounds {nu B lam h : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (k : Branch) :
    0≤rowCoefficient nu B lam h k ∧ rowCoefficient nu B lam h k≤cmax nu := by
  have hn : 0≤nu := by linarith
  have hw : 0≤w nu := by dsimp [w]; linarith
  have hb : baseXi nu≤branchRoot nu B lam h 0 1 k := by
    have hx := xi_lower hn0 hn1 hB0 hl hh0 (show (0:ℝ)≤0 by rfl) (show (0:ℝ)≤1 by norm_num)
    simp only [mul_one] at hx
    exact hx.trans (Finset.inf'_le _ (Finset.mem_univ k))
  have hv : 5≤branchValue nu B lam h 0 1 1 k := by
    have hp (j : Fin 3) : 0≤plainSlope lam j+plainOffset B lam h 0 1 j := by
      fin_cases j
      · norm_num [plainSlope,plainOffset]
      · norm_num [plainSlope,plainOffset]; linarith
      · norm_num [plainSlope,plainOffset]
        have he : lam/(lam-1)+ -B/(lam-1)=(lam-B)/(lam-1) := by ring
        rw [he]
        exact div_nonneg (by linarith) (by linarith)
    have hi (i : Fin 2) : inverseSlope i+inverseOffset 0 1 i=1 := by
      fin_cases i <;> norm_num [inverseSlope,inverseOffset]
    have he : branchValue nu B lam h 0 1 1 k=
      5+w nu*(plainSlope lam k.2+plainOffset B lam h 0 1 k.2)/2 := by
      dsimp [branchValue,branchSlope,branchOffset]
      have hh := hi k.1
      dsimp [w] at *
      nlinarith
    rw [he]
    nlinarith [mul_nonneg hw (hp k.2)]
  have hu : branchRoot nu B lam h 0 1 k≤1 := by
    rw [branchRoot,div_le_iff₀ (branchSlope_pos hn0 hn1 hl k)]
    dsimp [branchValue] at hv
    linarith
  constructor
  · exact mul_nonneg hn (sub_nonneg.mpr hb)
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right hu _) hn

theorem branch_gain_affine (nu B lam h S Q : ℝ) (k : Branch) :
    nu*(branchRoot nu B lam h S Q k-baseXi nu*Q)=
      nu*branchRoot nu B lam h 1 0 k*S+rowCoefficient nu B lam h k*Q := by
  rw [branchRoot_linear nu B lam h S Q k]
  dsimp [rowCoefficient]
  ring

theorem gain_le_branch {nu B lam h S Q : ℝ} (hn : 0≤nu) (k : Branch) :
    gain nu B lam h S Q≤nu*(branchRoot nu B lam h S Q k-baseXi nu*Q) :=
  mul_le_mul_of_nonneg_left (sub_le_sub_right (Finset.inf'_le _ (Finset.mem_univ k)) _) hn

theorem gain_eq_some_branch (nu B lam h S Q : ℝ) :
    ∃k : Branch,gain nu B lam h S Q=nu*(branchRoot nu B lam h S Q k-baseXi nu*Q) := by
  obtain ⟨k,_,hk⟩ := (Finset.inf'_le_iff (f:=branchRoot nu B lam h S Q)
    Finset.univ_nonempty).mp (le_refl (xi nu B lam h S Q))
  have he : xi nu B lam h S Q=branchRoot nu B lam h S Q k :=
    le_antisymm (Finset.inf'_le _ (Finset.mem_univ k)) hk
  exact ⟨k,by rw [gain,he]⟩

theorem gain_row_loss {nu B lam h S q F : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hq : q≤F) :
    gain nu B lam h S F≤gain nu B lam h S q+cmax nu*(F-q) := by
  obtain ⟨k,hk⟩ := gain_eq_some_branch nu B lam h S q
  have hu := gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=F)
    (show 0≤nu by linarith) k
  rw [branch_gain_affine] at hu hk
  have hc := (rowCoefficient_bounds hn0 hn1 hB0 hB1 hl hh0 hh1 k).2
  have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hq)
  linarith

theorem gain_le_cmax {nu B lam h S Q : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hQ : 0≤Q) :
    gain nu B lam h S Q≤cmax nu*Q := by
  have hu := gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=Q)
    (show 0≤nu by linarith) (1,1)
  rw [branch_gain_affine] at hu
  have hz : branchRoot nu B lam h 1 0 (1,1)=0 := by
    simp [branchRoot,branchOffset,inverseOffset,plainOffset]
  rw [hz,mul_zero,zero_mul,zero_add] at hu
  exact hu.trans (mul_le_mul_of_nonneg_right
    (rowCoefficient_bounds hn0 hn1 hB0 hB1 hl hh0 hh1 (1,1)).2 hQ)

theorem root_reserves {nu : ℝ} (hn0 : 1/2≤nu) (hn1 : nu≤3/4) :
    nu-phi nu-2*cmax nu≥1/12 ∧ 6*(rho nu-cmax nu)≥3/2 ∧
      (rho nu-1/6)/2-cmax nu≥1/42 := by
  have hd : 0<15-6*nu := by linarith
  have he : nu-phi nu-2*cmax nu-1/12=
      (2*nu-1)*(48*nu+5)/(4*(15-6*nu)) := by
    dsimp [phi,cmax,baseXi,densityDenom,w]
    field_simp (discharger := linarith)
    ring
  have he2 : 6*(rho nu-cmax nu)=6*(1-nu) := by dsimp [rho,cmax]; ring
  have he3 : (rho nu-1/6)/2-cmax nu-1/42=
      (3-4*nu)*(55-42*nu)/(28*(15-6*nu)) := by
    dsimp [rho,cmax,baseXi,densityDenom]
    field_simp (discharger := linarith)
    ring
  constructor
  · have hp : 0≤(2*nu-1)*(48*nu+5)/(4*(15-6*nu)) := by
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  constructor
  · rw [he2]; linarith
  · have hp : 0≤(3-4*nu)*(55-42*nu)/(28*(15-6*nu)) := by
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.gain_row_loss
#print axioms QRH.Record1252270103Source.High.gain_le_cmax
#print axioms QRH.Record1252270103Source.High.root_reserves
