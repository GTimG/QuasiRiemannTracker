/- Rational Bernstein certificate adapted from WeightedQRH upstream PR6. Coefficients below are checked by Lean ring arithmetic. -/
import Cycle25.Assembly.Transport.GeometryFacts
import Cycle25.Arithmetic.AlgebraicForms
import OAI.NumberTheory.DirichletL.Endpoint
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount
noncomputable section
namespace Cycle25.Transport
lemma tight_geometry : (79394:ℝ)/100000 < h ∧ h < 7940/10000 ∧ (4597:ℝ)/10000 < ly := by
  have he := Cycle25.ell_interval
  have he2 : (16712/100000:ℝ)^2 ≤ ell^2 ∧ ell^2 ≤ (167121/1000000:ℝ)^2 := by constructor <;> nlinarith
  have he3 : (16712/100000:ℝ)^3 ≤ ell^3 ∧ ell^3 ≤ (167121/1000000:ℝ)^3 := by
    constructor
    · exact pow_le_pow_left₀ (by norm_num) he.1.le 3
    · exact pow_le_pow_left₀ (Cycle25.ell_pos.le) he.2.le 3
  have hh : h = (181525300/284324837) + (393539385/284324837)*ell + (-813066675/284324837)*ell^2 + (247160448/284324837)*ell^3 := Arithmetic.h0_poly
  have hhi : h < 7940/10000 := by linarith
  have hlo : 79394/100000 < h := by linarith
  refine ⟨hlo,hhi,?_⟩
  rw [Cycle25.y_endpoint]
  linarith

def oldCount (delta x : ℝ) := OAI.SevenEighths.Endpoint.balancedRowCount delta (1/2-x)
def countD (x : ℝ) : ℝ := 3-17/9*x
def countP (x : ℝ) : ℝ := (2-8/9*x)*(1-x)
def countDen (delta x : ℝ) : ℝ := (5/6-delta)*countD x+delta*countP x
def countNum (delta x : ℝ) : ℝ := (1-delta)*countDen delta x+(5/6-delta)*delta*countP x/2
lemma countDen_pos {delta x : ℝ} (hd : 0≤delta) (hd1 : delta≤3/4) (_hx : 0≤x) (hx1 : x≤1/2) : 0<countDen delta x := by
  have ha : 0<5/6-delta := by linarith
  have hb : 0<countD x := by dsimp [countD];linarith
  have hc : 0≤countP x := by dsimp [countP];apply mul_nonneg <;> linarith
  exact add_pos_of_pos_of_nonneg (mul_pos ha hb) (mul_nonneg hd hc)
lemma oldCount_formula {delta x : ℝ} (hj : countDen delta x≠0) : oldCount delta x=countNum delta x/countDen delta x := by
  have hd : OAI.SevenEighths.Endpoint.balanceDenominator delta (1/2-x)=countDen delta x := by
    unfold OAI.SevenEighths.Endpoint.balanceDenominator OAI.SevenEighths.Endpoint.denominator OAI.SevenEighths.Endpoint.primeWeight countDen countD countP
    ring
  unfold oldCount OAI.SevenEighths.Endpoint.balancedRowCount OAI.SevenEighths.Endpoint.balancedCutoff
  rw [hd]
  unfold countNum countP
  simp only [OAI.SevenEighths.Endpoint.primeWeight]
  field_simp
  ring

def conservativeRest (delta x : ℝ) : ℝ :=
  (1+delta)*(1-4597/10000)/2-16712/100000/2+delta*x*(167121/1000000)+(794001/1000000)*(delta/2-1/6)-87488/100000

def conservativeCert (delta x : ℝ) : ℝ :=
  -((conservativeRest delta x+1/2000)*countDen delta x+(794001/1000000)*countNum delta x)
lemma conservativeCert_identity (delta x : ℝ) : conservativeCert delta x =
  (94041/20000:ℝ)*delta^0*(1/3-delta)^2*x^0*(1/2-x)^3
  + (101007/8000:ℝ)*delta^0*(1/3-delta)^2*x^1*(1/2-x)^2
  + (6966/625:ℝ)*delta^0*(1/3-delta)^2*x^2*(1/2-x)^1
  + (128871/40000:ℝ)*delta^0*(1/3-delta)^2*x^3*(1/2-x)^0
  + (50817/100000:ℝ)*delta^1*(1/3-delta)^1*x^0*(1/2-x)^3
  + (1385819/600000:ℝ)*delta^1*(1/3-delta)^1*x^1*(1/2-x)^2
  + (4877/1600:ℝ)*delta^1*(1/3-delta)^1*x^2*(1/2-x)^1
  + (373979/300000:ℝ)*delta^1*(1/3-delta)^1*x^3*(1/2-x)^0
  + (285831/250000:ℝ)*delta^2*(1/3-delta)^0*x^0*(1/2-x)^3
  + (317239/250000:ℝ)*delta^2*(1/3-delta)^0*x^1*(1/2-x)^2
  + (326711/1000000:ℝ)*delta^2*(1/3-delta)^0*x^2*(1/2-x)^1
  + (52527/1000000:ℝ)*delta^2*(1/3-delta)^0*x^3*(1/2-x)^0
  := by
  unfold conservativeCert conservativeRest countNum countDen countD countP
  ring
lemma conservativeCert_nonneg {delta x : ℝ} (hd : 0≤delta) (hd1 : delta≤1/3) (hx : 0≤x) (hx1 : x≤1/2) : 0≤conservativeCert delta x := by
  rw [conservativeCert_identity]
  have ha : 0≤1/3-delta := by linarith
  have hb : 0≤1/2-x := by linarith
  positivity
lemma oldCount_bounds {delta x : ℝ} (hd : 0≤delta) (hd1 : delta≤3/4) (hx : 0≤x) (hx1 : x≤1/2) :
    1-delta≤oldCount delta x ∧ oldCount delta x≤1-2*delta/3 := by
  have hj := countDen_pos hd hd1 hx hx1
  have ha : 0≤5/6-delta := by linarith
  have hp : 0≤countP x := by unfold countP;apply mul_nonneg <;> linarith
  have hdp : 0≤2*countD x-3*countP x := by
    unfold countD countP
    nlinarith [mul_nonneg hx (show 0≤1/2-x by linarith)]
  have hn := mul_nonneg (mul_nonneg ha hd) hp
  have hprod := mul_nonneg hd (add_nonneg (mul_nonneg ha hdp) (mul_nonneg (by linarith : 0≤2*delta) hp))
  rw [oldCount_formula hj.ne']
  constructor
  · apply (le_div_iff₀ hj).2
    unfold countNum
    linarith
  · apply (div_le_iff₀ hj).2
    unfold countNum countDen at *
    nlinarith

def genericOldExponent (d delta q R : ℝ) : ℝ :=
  (1+delta)/2-theta+h*(17/50-1/6)-(1+delta)/2*ly-ell/2+q*ell+d*(R+delta/2-17/50)
def OriginalBranch (d a : ℝ) : Prop := d≤h+rowExtension ∧ (2*a-1≤1/3 ∨ d≤1/2)

lemma low_delta_bound {d delta x : ℝ} (_hd : 0≤d) (hd1 : d≤h+rowExtension)
    (hdelta : 0≤delta) (hdelta1 : delta≤1/3) (hx : 0≤x) (hx1 : x≤1/2) :
    genericOldExponent d delta (delta*x) (oldCount delta x)≤-1/2000 := by
  have hr := oldCount_bounds hdelta (by linarith) hx hx1
  have hj := countDen_pos hdelta (by linarith) hx hx1
  have hc := conservativeCert_nonneg hdelta hdelta1 hx hx1
  have he : conservativeRest delta x+(794001/1000000)*oldCount delta x≤-1/2000 := by
    rw [oldCount_formula hj.ne']
    have hi : conservativeCert delta x = -countDen delta x*(conservativeRest delta x+(794001/1000000)*(countNum delta x/countDen delta x)+1/2000) := by
      unfold conservativeCert
      field_simp
      ring
    rw [hi] at hc
    nlinarith [hj]
  have hh := tight_geometry
  have hdy : d≤794001/1000000 := by norm_num [rowExtension] at hd1;linarith
  have hs : 0≤oldCount delta x+delta/2-17/50 := by linarith [hr.1]
  have hm := mul_le_mul_of_nonneg_right hdy hs
  have ht : 87488/100000≤theta := by rw [theta_eq];linarith [ell_interval.2]
  have hly := mul_le_mul_of_nonneg_left hh.2.2.le (show 0≤(1+delta)/2 by positivity)
  have hq := mul_le_mul_of_nonneg_left ell_interval.2.le (mul_nonneg hdelta hx)
  have hfreq := mul_le_mul_of_nonneg_right hh.2.1.le (by norm_num : (0:ℝ)≤17/50-1/6)
  unfold genericOldExponent conservativeRest at *
  nlinarith [ell_interval.1]

lemma intermediate_bound {d delta q : ℝ} (hd : 0≤d) (hd1 : d≤1/2)
    (hdelta : 0≤delta) (hdelta1 : delta≤3/4) (hq : 0≤q) (hq1 : q≤delta/2) :
    genericOldExponent d delta q (oldCount delta (q/delta))≤-1/2000 := by
  by_cases hz : delta=0
  · subst delta
    have hqz : q=0 := by linarith
    subst q
    have hr := oldCount_bounds (delta:=0) (x:=0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hr.2 hd
    unfold genericOldExponent
    rw [show (0:ℝ)/0=0 by simp] at *
    rw [theta_eq]
    nlinarith [tight_geometry,ell_interval.1,ell_interval.2]
  have hp : 0<delta := lt_of_le_of_ne hdelta (Ne.symm hz)
  have hx : 0≤q/delta := div_nonneg hq hp.le
  have hx1 : q/delta≤1/2 := (div_le_iff₀ hp).2 (by linarith)
  have hr := oldCount_bounds hdelta hdelta1 hx hx1
  have hm := mul_le_mul_of_nonneg_left hr.2 hd
  have hs : 0≤1-2*delta/3+delta/2-17/50 := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hd1 hs
  have hqell := mul_le_mul_of_nonneg_right hq1 ell_pos.le
  have hly := mul_le_mul_of_nonneg_left tight_geometry.2.2.le (show 0≤(1+delta)/2 by positivity)
  have hfreq := mul_le_mul_of_nonneg_right tight_geometry.2.1.le (by norm_num : (0:ℝ)≤17/50-1/6)
  unfold genericOldExponent
  rw [theta_eq]
  have hdel := mul_le_mul_of_nonneg_left ell_interval.2.le hdelta
  nlinarith [ell_interval.1,ell_interval.2]

lemma original_branch_exponent {d a q : ℝ} (hd : 0≤d) (ha : 51/100<a) (ha1 : a≤7/8)
    (hq : 0≤q) (hq1 : q≤(2*a-1)/2) (hb : OriginalBranch d a) :
    genericOldExponent d (2*a-1) q (oldCount (2*a-1) (q/(2*a-1)))≤-1/2000 := by
  have hp : 0<2*a-1 := by linarith
  rcases hb with ⟨ht,hb|hb⟩
  · have hh := low_delta_bound hd ht hp.le hb (div_nonneg hq hp.le) ((div_le_iff₀ hp).2 (by linarith))
    simpa only [mul_div_cancel₀ q hp.ne'] using hh
  · exact intermediate_bound hd hb hp.le (by linarith) hq hq1
end Cycle25.Transport
