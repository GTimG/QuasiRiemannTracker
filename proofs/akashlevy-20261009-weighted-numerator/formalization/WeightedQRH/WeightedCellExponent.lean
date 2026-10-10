import WeightedQRH.ExponentCertificate
import WeightedQRH.FullWBound

/-! Exact exponent bookkeeping after integration of the physical numerator. -/
noncomputable section
namespace WeightedQRH

def numeratorExponent (d delta x : ℝ) : ℝ :=
  -ly/2+ell*(17/50-1/2)+delta*x*ell+
    d*((3*rowCount delta x+1)/4-17/50)-delta*x*(2*ly-d)/(12*kappa)

theorem numerator_kernel_exponent (d delta x e : ℝ) :
    lx*(1/2-17/50)+(1+delta)/2+16*e+17/50-1+numeratorExponent d delta x=
      signal theta+weightedExponent d delta x+16*e := by
  unfold numeratorExponent weightedExponent signal
  norm_num [theta,lx,ly,ell,h,b,kappa]
  ring

theorem weighted_cell_exponent_bound {d delta x e loss nu : ℝ}
    (hd : d≤h+rowExtension) (hdelta : 1/3≤delta) (hdelta' : delta≤3/4)
    (hx : 0≤x) (hx' : x≤1/2) :
    lx*(1/2-17/50)+(1+delta)/2+16*e+17/50-1+numeratorExponent d delta x+loss+nu≤
      signal theta-1/20000+16*e+loss+nu := by
  rw [numerator_kernel_exponent]
  linarith [weighted_extended_bound hd hdelta hdelta' hx hx']

/-- The analytic hypothesis is the actual full-w numerator estimate supplied
upstream of this bookkeeping lemma, not an assumed zero-free conclusion. -/
theorem normalized_weighted_cell_bound (F normer : ℂ) (Z C A Cn d delta x e loss nu : ℝ)
    (hZ : 1≤Z) (hC : 0≤C) (hA : 0≤A) (hCn : 0≤Cn)
    (hd : d≤h+rowExtension) (hdelta : 1/3≤delta) (hdelta' : delta≤3/4)
    (hx : 0≤x) (hx' : x≤1/2)
    (hF : ‖F‖≤C*(Z^lx)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1)*
      (A*Z^(numeratorExponent d delta x+loss)))
    (hn : ‖normer⁻¹‖≤Cn*Z^nu) :
    ‖F/normer‖≤(C*A*Cn)*Z^(signal theta-1/20000+16*e+loss+nu) := by
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (C*(Z^lx)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1)*
        (A*Z^(numeratorExponent d delta x+loss)))*(Cn*Z^nu) :=
      mul_le_mul hF hn (norm_nonneg _) (by positivity)
    _ = (C*A*Cn)*Z^(lx*(1/2-17/50)+(1+delta)/2+16*e+17/50-1+
        numeratorExponent d delta x+loss+nu) := by
      rw [←Real.rpow_mul hZ0.le]
      calc
        _ = (C*A*Cn)*(Z^(lx*(1/2-17/50))*Z^((1+delta)/2+16*e+17/50-1)*
            Z^(numeratorExponent d delta x+loss)*Z^nu) := by ring
        _ = _ := by
          rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
          congr 2
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (weighted_cell_exponent_bound hd hdelta hdelta' hx hx'))
      (by positivity)

end WeightedQRH
