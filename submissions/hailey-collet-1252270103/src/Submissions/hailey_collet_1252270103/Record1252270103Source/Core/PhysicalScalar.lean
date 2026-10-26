/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The cleared supplied density gates are the actual detector-gain exponent gaps. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.Facets
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.DensityGeometry
import Submissions.hailey_collet_1252270103.Record12518109Gain.Homogeneous
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalScalar
noncomputable section
open Record1252270103Finite Record1252270103StepScalar High

def physicalBase (ν a T : ℝ) : ℝ := rho ν+ν*T+a*(5-6*rho ν)
def sourceBase (n low : Source) (b ν : ℝ) : ℝ :=
  physicalBase ν (sourceAReal n low b) (sourceTReal n b+b)
def regularIndex (k : Branch) : Fin 9 := ⟨3*k.1.val+k.2.val,by omega⟩
def regularFactor (ν L : ℝ) (k : Branch) : ℝ :=
  (![ ![1,1,L*densityDenom ν-10],
      ![10+3*w ν,10+3*w ν,L*(10+3*w ν)-(10+2*w ν)] ] k.1) k.2
def regularDenominator (ν L : ℝ) (k : Branch) : ℝ := densityDenom ν*regularFactor ν L k

theorem cleared_base (ν a T : ℝ) (ht : densityDenom ν≠0) :
    (a-ν*T)*densityDenom ν+(10-60*a)*ν=densityDenom ν*(1-physicalBase ν a T) := by
  unfold physicalBase rho baseXi
  field_simp
  ring

theorem regular_factor_positive {ν L : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4)
    (hL : 1<L) (k : Branch) : 0<regularFactor ν L k := by
  have hd := facet_denominators hν0 hν1 hL
  rcases k with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [regularFactor] <;> linarith [hd.1,hd.2.1,hd.2.2.1,hd.2.2.2]

theorem regular_denominator_positive {ν L : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4)
    (hL : 1<L) (k : Branch) : 0<regularDenominator ν L k :=
  mul_pos (facet_denominators hν0 hν1 hL).1 (regular_factor_positive hν0 hν1 hL k)

theorem regular_denominator_upper {ν L : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4)
    (hL : 1<L) (k : Branch) : regularDenominator ν L k≤192*L := by
  have hLp : 0<L := by linarith
  have ht : densityDenom ν≤12 := by dsimp [densityDenom];linarith
  have hw : 0<w ν := by dsimp [w];linarith
  have hwu : w ν≤2 := by dsimp [w];linarith
  have hfactor : regularFactor ν L k≤16*L := by
    have htL := mul_le_mul_of_nonneg_left ht hLp.le
    have hwL := mul_le_mul_of_nonneg_left (show 10+3*w ν≤16 by linarith) hLp.le
    rcases k with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> norm_num [regularFactor] <;> nlinarith
  exact (mul_le_mul ht hfactor (regular_factor_positive hν0 hν1 hL k).le
    (by norm_num : (0:ℝ)≤12)).trans_eq (by ring)

theorem source_some_facet_identity (n low h : Source) (b ν : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hL : 1<(h.L:ℝ)) (k : Branch) :
    sourceDensityWidthReal n low (some h) b ν (regularIndex k)=
      regularDenominator ν (h.L:ℝ) k*
        (1-sourceBase n low b ν+
          facet ν (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)
            (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ)) k-(n.highFee:ℝ)) := by
  have hd := facet_denominators hν0 hν1 hL
  have ht : densityDenom ν≠0 := ne_of_gt hd.1
  have h13 : (h.L:ℝ)*densityDenom ν-10≠0 := ne_of_gt hd.2.2.1
  have h4 : 10+3*w ν≠0 := ne_of_gt hd.2.1
  have h23 : (h.L:ℝ)*(10+3*w ν)-(10+2*w ν)≠0 := ne_of_gt hd.2.2.2
  rcases k with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceDensityWidthReal,regularIndex,regularDenominator,regularFactor,facet,
      sourceBase,physicalBase,rho,baseXi] <;>
    dsimp [densityDenom,w] at hd ht h13 h4 h23 ⊢ <;>
    field_simp (discharger := nlinarith [hd.1,hd.2.1,hd.2.2.1,hd.2.2.2]) <;> ring

/-- The other three gates retain their exact actual family exponent. -/
def familyGap (n low : Source) (b ν : ℝ) : Fin 3→ℝ :=
  let F:=sourceFReal n low b-(n.allowance:ℝ)
  ![1-sourceBase n low b ν+ν*F/2-(1-ν)*b-(n.highFee:ℝ),
    1-sourceBase n low b ν+(rho ν-1/6)*F-(1-ν)*b-(n.highFee:ℝ),
    1-sourceBase n low b ν+ν*(F-1/50)/2-(1-rho ν)/50-(1-ν)*b-(n.highFee:ℝ)]
def familyIndex (high : Option Source) (j : Fin 3) : Fin 9 :=
  ⟨(if high.isSome then 6 else 3)+j.val,by split_ifs <;> omega⟩

theorem source_family_identity (n low : Source) (high : Option Source) (b ν : ℝ)
    (ht : densityDenom ν≠0) (j : Fin 3) :
    sourceDensityWidthReal n low high b ν (familyIndex high j)=densityDenom ν*familyGap n low b ν j := by
  cases high <;> fin_cases j <;>
    norm_num [sourceDensityWidthReal,familyIndex,familyGap,sourceBase,physicalBase,rho,baseXi] <;>
    simp only [densityDenom] at ht ⊢
  all_goals
    have ht2 : 15-ν*6≠0 := by simpa [mul_comm] using ht
    field_simp [ht,ht2] <;> ring

end
end QRH.Record1252270103Source.PhysicalScalar
#print axioms QRH.Record1252270103Source.PhysicalScalar.source_some_facet_identity
#print axioms QRH.Record1252270103Source.PhysicalScalar.source_family_identity
#print axioms QRH.Record1252270103Source.PhysicalScalar.regular_denominator_upper
