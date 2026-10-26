/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
    Exact rational coefficients generated from the preserved seven-face calculation.
    These algebraic lemmas do not assert the auxiliary source moment. -/
import Candidate.Uneven.FiniteGain
import Candidate.Uneven.SaturatedMonotone

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

def slope (d : ℝ) : Fin 7 → ℝ :=
  ![((-6*(d^2))+(5*d))/(5+(-2*d)),
    ((-38293836*(d^2))+(31911530*d))/(52867295+(-25146918*d)),
    ((-12*(d^2))+(10*d))/(15+(-6*d)),
    ((-6*(d^2))+(5*d))/(25+(-18*d)),
    0/1,
    0/1,
    0/1]

theorem slope_0_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 0 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-6*(d^2))+(5*d)) := by
    have he : ((-6*(d^2))+(5*d))=496*(d-31/50)^0*(33/50-d)^2+931*(d-31/50)^1*(33/50-d)^1+429*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (5+(-2*d)) := by
    have he : (5+(-2*d))=(92/25:ℝ)+2*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem slope_1_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 1 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-38293836*(d^2))+(31911530*d)) := by
    have he : ((-38293836*(d^2))+(31911530*d))=3165623776*(d-31/50)^0*(33/50-d)^2+5941926886*(d-31/50)^1*(33/50-d)^1+2738009274*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (52867295+(-25146918*d)) := by
    have he : (52867295+(-25146918*d))=(906758228/25:ℝ)+25146918*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem slope_2_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 2 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-12*(d^2))+(10*d)) := by
    have he : ((-12*(d^2))+(10*d))=992*(d-31/50)^0*(33/50-d)^2+1862*(d-31/50)^1*(33/50-d)^1+858*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (15+(-6*d)) := by
    have he : (15+(-6*d))=(276/25:ℝ)+6*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem slope_3_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 3 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-6*(d^2))+(5*d)) := by
    have he : ((-6*(d^2))+(5*d))=496*(d-31/50)^0*(33/50-d)^2+931*(d-31/50)^1*(33/50-d)^1+429*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (25+(-18*d)) := by
    have he : (25+(-18*d))=(328/25:ℝ)+18*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem slope_4_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 4 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ 0 := by
    norm_num
  have hden : (0:ℝ) < 1 := by
    norm_num
  exact div_nonneg hn hden.le

theorem slope_5_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 5 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ 0 := by
    norm_num
  have hden : (0:ℝ) < 1 := by
    norm_num
  exact div_nonneg hn hden.le

theorem slope_6_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ slope d 6 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ 0 := by
    norm_num
  have hden : (0:ℝ) < 1 := by
    norm_num
  exact div_nonneg hn hden.le

def offset (d : ℝ) : Fin 7 → ℝ :=
  ![0/1,
    ((-118578360*(d^2))+(49111475*d)+(71573508*(d^3)))/(1586018850+(-1388815080*d)+(301763016*(d^2))),
    ((-42*(d^2))+(35*d))/(3750+(-1500*d)),
    ((-120*(d^2))+(50*d)+(72*(d^3)))/(375+(-420*d)+(108*(d^2))),
    ((-884455080*(d^2))+(368226775*d)+(531099540*(d^3)))/(2543364750+(-2920568520*d)+(761289048*(d^2))),
    ((-30840*(d^2))+(13025*d)+(18252*(d^3)))/(93750+(-105000*d)+(27000*(d^2))),
    ((-1375736966*(d^2))+(939342415*d))/(3750000000+(-1500000000*d))]

theorem offset_0_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 0 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ 0 := by
    norm_num
  have hden : (0:ℝ) < 1 := by
    norm_num
  exact div_nonneg hn hden.le

theorem offset_1_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 1 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-118578360*(d^2))+(49111475*d)+(71573508*(d^3))) := by
    have he : ((-118578360*(d^2))+(49111475*d)+(71573508*(d^3)))=30086936416*(d-31/50)^0*(33/50-d)^3+80643858014*(d-31/50)^1*(33/50-d)^2+71390615902*(d-31/50)^2*(33/50-d)^1+20905267812*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1586018850+(-1388815080*d)+(301763016*(d^2))) := by
    have he : (1586018850+(-1388815080*d)+(301763016*(d^2)))=(500530541856/625:ℝ)+25063960488*(d-31/50)^0*(33/50-d)^2+24762197472*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem offset_2_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 2 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-42*(d^2))+(35*d)) := by
    have he : ((-42*(d^2))+(35*d))=3472*(d-31/50)^0*(33/50-d)^2+6517*(d-31/50)^1*(33/50-d)^1+3003*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (3750+(-1500*d)) := by
    have he : (3750+(-1500*d))=2760+1500*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem offset_3_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 3 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-120*(d^2))+(50*d)+(72*(d^3))) := by
    have he : ((-120*(d^2))+(50*d)+(72*(d^3)))=31744*(d-31/50)^0*(33/50-d)^3+85376*(d-31/50)^1*(33/50-d)^2+75868*(d-31/50)^2*(33/50-d)^1+22308*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (375+(-420*d)+(108*(d^2))) := by
    have he : (375+(-420*d)+(108*(d^2)))=(90528/625:ℝ)+7044*(d-31/50)^0*(33/50-d)^2+6936*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem offset_4_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 4 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-884455080*(d^2))+(368226775*d)+(531099540*(d^3))) := by
    have he : ((-884455080*(d^2))+(368226775*d)+(531099540*(d^3)))=232686858080*(d-31/50)^0*(33/50-d)^3+625539615070*(d-31/50)^1*(33/50-d)^2+555603407510*(d-31/50)^2*(33/50-d)^1+163281750060*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2543364750+(-2920568520*d)+(761289048*(d^2))) := by
    have he : (2543364750+(-2920568520*d)+(761289048*(d^2)))=(592129397568/625:ℝ)+48652963464*(d-31/50)^0*(33/50-d)^2+47891674416*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem offset_5_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 5 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-30840*(d^2))+(13025*d)+(18252*(d^3))) := by
    have he : ((-30840*(d^2))+(13025*d)+(18252*(d^3)))=8915104*(d-31/50)^0*(33/50-d)^3+24140066*(d-31/50)^1*(33/50-d)^2+21612538*(d-31/50)^2*(33/50-d)^1+6405828*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (93750+(-105000*d)+(27000*(d^2))) := by
    have he : (93750+(-105000*d)+(27000*(d^2)))=(181056/5:ℝ)+1761000*(d-31/50)^0*(33/50-d)^2+1734000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem offset_6_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ offset d 6 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-1375736966*(d^2))+(939342415*d)) := by
    have he : ((-1375736966*(d^2))+(939342415*d))=33474379731*(d-31/50)^0*(33/50-d)^2+47784473891*(d-31/50)^1*(33/50-d)^1+12934357194*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (3750000000+(-1500000000*d)) := by
    have he : (3750000000+(-1500000000*d))=2760000000+1500000000*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  exact div_nonneg hn hden.le

theorem coefficient_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    (∀i,0 ≤ slope d i) ∧ (∀i,0 ≤ offset d i) := by
  constructor
  · intro i
    fin_cases i
    · exact slope_0_nonneg hd0 hd1
    · exact slope_1_nonneg hd0 hd1
    · exact slope_2_nonneg hd0 hd1
    · exact slope_3_nonneg hd0 hd1
    · exact slope_4_nonneg hd0 hd1
    · exact slope_5_nonneg hd0 hd1
    · exact slope_6_nonneg hd0 hd1
  · intro i
    fin_cases i
    · exact offset_0_nonneg hd0 hd1
    · exact offset_1_nonneg hd0 hd1
    · exact offset_2_nonneg hd0 hd1
    · exact offset_3_nonneg hd0 hd1
    · exact offset_4_nonneg hd0 hd1
    · exact offset_5_nonneg hd0 hd1
    · exact offset_6_nonneg hd0 hd1


theorem saturated_cap {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    offset d 4 ≤ 3/200 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  change ((-884455080*(d^2))+(368226775*d)+(531099540*(d^3)))/(2543364750+(-2920568520*d)+(761289048*(d^2))) ≤ 3/200
  have hn : (0:ℝ) ≤ ((152601885/4:ℝ)+(-531099540*(d^3))+((-2060176514/5:ℝ)*d)+((22396860393/25:ℝ)*(d^2))) := by
    have he : ((152601885/4:ℝ)+(-531099540*(d^3))+((-2060176514/5:ℝ)*d)+((22396860393/25:ℝ)*(d^2)))=7606527307*(d-31/50)^0*(33/50-d)^3+76810196399*(d-31/50)^1*(33/50-d)^2+128501542660*(d-31/50)^2*(33/50-d)^1+58766774028*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2543364750+(-2920568520*d)+(761289048*(d^2))) := by
    have he : (2543364750+(-2920568520*d)+(761289048*(d^2)))=(592129397568/625:ℝ)+48652963464*(d-31/50)^0*(33/50-d)^2+47891674416*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hn]

def physicalGain (d S D : ℝ) : ℝ := FiniteGain.gain (slope d) (offset d) S D

theorem physicalGain_cap {d S D : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hD : 0 ≤ D) : physicalGain d S D ≤ (3/200)*D := by
  have h := FiniteGain.gain_le (slope d) (offset d) S D 4
  have hc := mul_le_mul_of_nonneg_right (saturated_cap hd0 hd1) hD
  have hz : slope d 4=0 := by norm_num [slope]
  rw [hz,zero_mul,zero_add] at h
  exact h.trans hc

theorem physicalGain_root {d S D q pad : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hpad : 0 ≤ pad) :
    physicalGain d S D-(3/200)*D*(1-q) ≤ physicalGain d S (D*q+pad) :=
  FiniteGain.root_gain_lower (coefficient_nonneg hd0 hd1).1 (coefficient_nonneg hd0 hd1).2
    hS hq0 hq1 hpad (physicalGain_cap hd0 hd1 hD)

end Sil.Uneven.Bootstrap
