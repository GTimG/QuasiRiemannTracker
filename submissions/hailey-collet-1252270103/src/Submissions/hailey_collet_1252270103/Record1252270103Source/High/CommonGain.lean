/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GainBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

theorem slotCoefficient_bounds {nu B lam h : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hl : 1<lam) (k : Branch) :
    0≤nu*branchRoot nu B lam h 1 0 k ∧ nu*branchRoot nu B lam h 1 0 k≤phi nu := by
  have hn : 0≤nu := by linarith
  have hw : 0≤w nu := by dsimp [w]; linarith
  have hd : 0<densityDenom nu := by dsimp [densityDenom]; linarith
  have hs : 0<branchSlope nu lam k := branchSlope_pos hn0 hn1 hl k
  let n := -(inverseOffset 1 0 k.1+plainOffset B lam h 1 0 k.2/2)
  have hn' : 0≤n ∧ n≤3/2 := by
    rcases k with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> norm_num [n,inverseOffset,plainOffset]
  have hp (j : Fin 3) : 1≤plainSlope lam j := by
    fin_cases j <;> norm_num [plainSlope]
    exact (le_div_iff₀ (by linarith : 0<lam-1)).mpr (by linarith)
  have hi (i : Fin 2) : 1≤ inverseSlope i := by fin_cases i <;> norm_num [inverseSlope]
  have hsl : densityDenom nu/2≤branchSlope nu lam k := by
    have hm := mul_le_mul_of_nonneg_left
      (show 3/2≤ inverseSlope k.1+plainSlope lam k.2/2 by linarith [hi k.1,hp k.2]) hw
    dsimp [branchSlope,densityDenom,w] at *
    nlinarith
  have he : branchRoot nu B lam h 1 0 k=w nu*n/branchSlope nu lam k := by
    dsimp [branchRoot,branchOffset,n]
    ring
  have hratio : branchRoot nu B lam h 1 0 k≤3*w nu/densityDenom nu := by
    rw [he,div_le_div_iff₀ hs hd]
    have hnD := mul_le_mul_of_nonneg_right hn'.2 hd.le
    have hm := mul_le_mul_of_nonneg_left
      (show n*densityDenom nu≤3*branchSlope nu lam k by linarith) hw
    nlinarith
  refine ⟨?_,?_⟩
  · rw [he]
    exact mul_nonneg hn (div_nonneg (mul_nonneg hw hn'.1) hs.le)
  · have hm := mul_le_mul_of_nonneg_left hratio hn
    dsimp [phi]
    convert hm using 1 <;> ring

theorem gain_slot_loss {nu B lam h S L Q : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hl : 1<lam) (hLS : L≤S) :
    gain nu B lam h S Q≤gain nu B lam h L Q+phi nu*(S-L) := by
  obtain ⟨k,hk⟩ := gain_eq_some_branch nu B lam h L Q
  have hu := gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=Q)
    (show 0≤nu by linarith) k
  rw [branch_gain_affine] at hu hk
  have hc := (slotCoefficient_bounds (B:=B) (h:=h) hn0 hn1 hl k).2
  have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hLS)
  linarith

theorem gain_mono {nu B lam h S L Q F : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hSL : S≤L) (hQF : Q≤F) :
    gain nu B lam h S Q≤gain nu B lam h L F := by
  obtain ⟨k,hk⟩ := gain_eq_some_branch nu B lam h L F
  have hu := gain_le_branch (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=Q)
    (show 0≤nu by linarith) k
  rw [branch_gain_affine] at hu hk
  have hs := (slotCoefficient_bounds (B:=B) (h:=h) hn0 hn1 hl k).1
  have hr := (rowCoefficient_bounds hn0 hn1 hB0 hB1 hl hh0 hh1 k).1
  linarith [mul_le_mul_of_nonneg_left hSL hs,mul_le_mul_of_nonneg_left hQF hr]

/-- The original restricted common-prime relations pay both lost widths.
No independent gain is substituted for the actual face. -/
theorem common_gain_loss {nu B lam h S L Q F c b : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1)
    (hc : 0≤c) (hb : 0≤b) (hslots : S≤L+c+b) (hrows : F≤Q+2*c+2*b) :
    gain nu B lam h S F-gain nu B lam h L Q≤
      (phi nu+2*cmax nu)*(c+b) := by
  have hm := gain_mono hn0 hn1 hB0 hB1 hl hh0 hh1 hslots hrows
  have hs := gain_slot_loss (B:=B) (h:=h) (Q:=Q+2*c+2*b) hn0 hn1 hl
    (show L≤L+c+b by linarith)
  have hr := gain_row_loss (S:=L) hn0 hn1 hB0 hB1 hl hh0 hh1
    (show Q≤Q+2*c+2*b by linarith)
  nlinarith

theorem common_gain_reserve {nu B lam h S L Q F c b : ℝ}
    (hn0 : 1/2≤nu) (hn1 : nu≤3/4) (hB0 : 22/23≤B) (hB1 : B≤1)
    (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1)
    (hc : 0≤c) (hb : 0≤b) (hslots : S≤L+c+b) (hrows : F≤Q+2*c+2*b) :
    gain nu B lam h S F-gain nu B lam h L Q-nu*(c+b)≤-(c+b)/12 := by
  have hg := common_gain_loss hn0 hn1 hB0 hB1 hl hh0 hh1 hc hb hslots hrows
  have hr := (root_reserves hn0 hn1).1
  have hm := mul_le_mul_of_nonneg_right hr (show 0≤c+b by linarith)
  nlinarith

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.common_gain_loss
#print axioms QRH.Record1252270103Source.High.common_gain_reserve
