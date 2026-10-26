/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def c : ℝ := (1252270103/10000000000:ℝ)
def h : ℝ := (8001009617/10000000000:ℝ)
def physicalB : ℝ := (48369515545621/50000000000000:ℝ)
def physicalLambda : ℝ := (163653997694883/50000000000000:ℝ)
def countCB : ℝ := (48113075876991/50000000000000:ℝ)
def countCL : ℝ := (157406588190789/50000000000000:ℝ)
def naturalK : ℝ := (11243277/2500000:ℝ)
def theta : ℝ := 1-c
def ell : ℝ := 4*c-1/3
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 1-2*c
def ds : ℝ := 2*y/(1+6*kappa/25)
def dk : ℝ := 2*y/(2-physicalB+physicalLambda/25)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (d/25) ((2*y-(2-physicalB)*d)/physicalLambda)
def rowFee : ℝ := 1/1000000000
inductive Edge | oldSmall | oldPeak | oldSwitch | newSwitch | newTop | newKink
 deriving DecidableEq
def edgeD : Edge → ℝ
 | .oldSmall => d0
 | .oldPeak => y
 | .oldSwitch | .newSwitch => ds
 | .newTop => dp
 | .newKink => dk
def edgeC (e : Edge) : ℝ := match e with
 | .oldSmall | .oldPeak | .oldSwitch => oldCapacity (edgeD e)
 | .newSwitch | .newTop | .newKink => newCapacity (edgeD e)
theorem c_value : c = (1252270103/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem theta_value : theta = (8747729897/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem h_value : h = (8001009617/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ell_value : ell = (1256810309/7500000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem x_value : x = (2204842477/6000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem y_value : y = (13948546379/30000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem kappa_value : kappa = (3747729897/5000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ds_value : ds = (348713659475/442459138146:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dk_value : dk = (1743568297375000/2181624163581537:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dp_value : dp = (4000504809/5000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem d0_value : d0 = (1/200:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSmall : edgeC .oldSmall = (12500000/11243189691:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldPeak : edgeD .oldPeak = (13948546379/30000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldPeak : edgeC .oldPeak = (13948546379/134918276292:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (348713659475/442459138146:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (13948546379/442459138146:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newSwitch : edgeD .newSwitch = (348713659475/442459138146:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newSwitch : edgeC .newSwitch = (13948546379/442459138146:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newTop : edgeD .newTop = (4000504809/5000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newTop : edgeC .newTop = (77783314897771208174167/2454809965423245000000000:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newKink : edgeD .newKink = (1743568297375000/2181624163581537:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newKink : edgeC .newKink = (69742731895000/2181624163581537:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = ds/25 := by
 norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
def reserve_Gram_x_above_ell : ℝ := x-ell
theorem reserve_Gram_x_above_ell_exact : reserve_Gram_x_above_ell = (1998990383/10000000000:ℝ) := by norm_num [reserve_Gram_x_above_ell,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_x_above_ell_pos : 0<reserve_Gram_x_above_ell := by rw [reserve_Gram_x_above_ell_exact]; norm_num
def reserve_Gram_y_above_x : ℝ := y-x
theorem reserve_Gram_y_above_x_exact : reserve_Gram_y_above_x = (487388999/5000000000:ℝ) := by norm_num [reserve_Gram_y_above_x,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_y_above_x_pos : 0<reserve_Gram_y_above_x := by rw [reserve_Gram_y_above_x_exact]; norm_num
def reserve_Gram_ell_below_one_fifth : ℝ := 1/5-ell
theorem reserve_Gram_ell_below_one_fifth_exact : reserve_Gram_ell_below_one_fifth = (243189691/7500000000:ℝ) := by norm_num [reserve_Gram_ell_below_one_fifth,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_ell_below_one_fifth_pos : 0<reserve_Gram_ell_below_one_fifth := by rw [reserve_Gram_ell_below_one_fifth_exact]; norm_num
def reserve_Gram_2x_above_y_plus_ell : ℝ := 2*x-y-ell
theorem reserve_Gram_2x_above_y_plus_ell_exact : reserve_Gram_2x_above_y_plus_ell = (204842477/2000000000:ℝ) := by norm_num [reserve_Gram_2x_above_y_plus_ell,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_2x_above_y_plus_ell_pos : 0<reserve_Gram_2x_above_y_plus_ell := by rw [reserve_Gram_2x_above_y_plus_ell_exact]; norm_num
def reserve_conductor_small_before_peak : ℝ := y-d0
theorem reserve_conductor_small_before_peak_exact : reserve_conductor_small_before_peak = (13798546379/30000000000:ℝ) := by norm_num [reserve_conductor_small_before_peak,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_small_before_peak_pos : 0<reserve_conductor_small_before_peak := by rw [reserve_conductor_small_before_peak_exact]; norm_num
def reserve_conductor_peak_before_switch : ℝ := ds-y
theorem reserve_conductor_peak_before_switch_exact : reserve_conductor_peak_before_switch = (714957995834691821111/2212295690730000000000:ℝ) := by norm_num [reserve_conductor_peak_before_switch,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_peak_before_switch_pos : 0<reserve_conductor_peak_before_switch := by rw [reserve_conductor_peak_before_switch_exact]; norm_num
def reserve_conductor_switch_before_kink : ℝ := dk-ds
theorem reserve_conductor_switch_before_kink_exact : reserve_conductor_switch_before_kink = (3565193491209114783878975/321759849058924993872670134:ℝ) := by norm_num [reserve_conductor_switch_before_kink,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_switch_before_kink_pos : 0<reserve_conductor_switch_before_kink := by rw [reserve_conductor_switch_before_kink_exact]; norm_num
def reserve_conductor_kink_before_top : ℝ := dp-dk
theorem reserve_conductor_kink_before_top_exact : reserve_conductor_kink_before_top = (9756470963541432111433/10908120817907685000000000:ℝ) := by norm_num [reserve_conductor_kink_before_top,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_kink_before_top_pos : 0<reserve_conductor_kink_before_top := by rw [reserve_conductor_kink_before_top_exact]; norm_num
def reserve_conductor_top_before_twoy : ℝ := 2*y-dp
theorem reserve_conductor_top_before_twoy_exact : reserve_conductor_top_before_twoy = (121689497/937500000:ℝ) := by norm_num [reserve_conductor_top_before_twoy,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_top_before_twoy_pos : 0<reserve_conductor_top_before_twoy := by rw [reserve_conductor_top_before_twoy_exact]; norm_num
def reserve_physical_plain_lower : ℝ := 1-y/ds-2/5-1/10000000
theorem reserve_physical_plain_lower_exact : reserve_physical_plain_lower = (1256797809/125000000000:ℝ) := by norm_num [reserve_physical_plain_lower,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_plain_lower_pos : 0<reserve_physical_plain_lower := by rw [reserve_physical_plain_lower_exact]; norm_num
def reserve_physical_plain_upper : ℝ := 11/25-(1-y/dp+1/400)-1/10000000
theorem reserve_physical_plain_upper_exact : reserve_physical_plain_upper = (2234201241610573/120015144270000000:ℝ) := by norm_num [reserve_physical_plain_upper,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_plain_upper_pos : 0<reserve_physical_plain_upper := by rw [reserve_physical_plain_upper_exact]; norm_num
def reserve_physical_width_lower : ℝ := min (1/25) ((physicalB-2*(1-y/dp+1/400))/physicalLambda)-17/500-1/10000000
theorem reserve_physical_width_lower_exact : reserve_physical_width_lower = (80034821928134267062407482959/19640958143713630685770410000000:ℝ) := by norm_num [reserve_physical_width_lower,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_width_lower_pos : 0<reserve_physical_width_lower := by rw [reserve_physical_width_lower_exact]; norm_num
def reserve_physical_width_upper : ℝ := 43/1000-1/25-1/10000000
theorem reserve_physical_width_upper_exact : reserve_physical_width_upper = (29999/10000000:ℝ) := by norm_num [reserve_physical_width_upper,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_width_upper_pos : 0<reserve_physical_width_upper := by rw [reserve_physical_width_upper_exact]; norm_num
def reserve_small_width_shortening : ℝ := 1-2*(1-y/dp+1/400)-9/2*(17/500)-1/10000000
theorem reserve_small_width_shortening_exact : reserve_small_width_shortening = (507914723825573/120015144270000000:ℝ) := by norm_num [reserve_small_width_shortening,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_width_shortening_pos : 0<reserve_small_width_shortening := by rw [reserve_small_width_shortening_exact]; norm_num
def reserve_short_plain_shortening : ℝ := 1-2/5-physicalB/2-(9/2-physicalLambda/2)*(1/25)-1/10000000
theorem reserve_short_plain_shortening_exact : reserve_short_plain_shortening = (2207929527179/1250000000000000:ℝ) := by norm_num [reserve_short_plain_shortening,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_short_plain_shortening_pos : 0<reserve_short_plain_shortening := by rw [reserve_short_plain_shortening_exact]; norm_num
def reserve_large_shift : ℝ := (7/18-1/500)*(1/400)+(1-physicalB)/18+(physicalLambda/18-1/4)*(1/25)-1/10000000
theorem reserve_large_shift_exact : reserve_large_shift = (196059842393/3750000000000000:ℝ) := by norm_num [reserve_large_shift,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_large_shift_pos : 0<reserve_large_shift := by rw [reserve_large_shift_exact]; norm_num
def reserve_large_shift_clipped : ℝ := 1/2-1/500-1/(2*physicalLambda)
theorem reserve_large_shift_clipped_exact : reserve_large_shift_clipped = (28249845426025867/81826998847441500:ℝ) := by norm_num [reserve_large_shift_clipped,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_large_shift_clipped_pos : 0<reserve_large_shift_clipped := by rw [reserve_large_shift_clipped_exact]; norm_num
def reserve_small_shift_cost : ℝ := 1/2-1/(2*physicalLambda)-1/500
theorem reserve_small_shift_cost_exact : reserve_small_shift_cost = (28249845426025867/81826998847441500:ℝ) := by norm_num [reserve_small_shift_cost,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_shift_cost_pos : 0<reserve_small_shift_cost := by rw [reserve_small_shift_cost_exact]; norm_num
def reserve_prime_supply : ℝ := ell/dp-1/5
theorem reserve_prime_supply_exact : reserve_prime_supply = (566588663/60007572135:ℝ) := by norm_num [reserve_prime_supply,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_prime_supply_pos : 0<reserve_prime_supply := by rw [reserve_prime_supply_exact]; norm_num
def reserve_capacity_domain : ℝ := y-dp/2
theorem reserve_capacity_domain_exact : reserve_capacity_domain = (121689497/1875000000:ℝ) := by norm_num [reserve_capacity_domain,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_capacity_domain_pos : 0<reserve_capacity_domain := by rw [reserve_capacity_domain_exact]; norm_num
def reserve_incumbent : ℝ := naturalK/6-kappa
theorem reserve_incumbent_exact : reserve_incumbent = (29103/5000000000:ℝ) := by norm_num [reserve_incumbent,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_incumbent_pos : 0<reserve_incumbent := by rw [reserve_incumbent_exact]; norm_num
def reserve_feedback_kappa : ℝ := kappa-7/10
theorem reserve_feedback_kappa_exact : reserve_feedback_kappa = (247729897/5000000000:ℝ) := by norm_num [reserve_feedback_kappa,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_kappa_pos : 0<reserve_feedback_kappa := by rw [reserve_feedback_kappa_exact]; norm_num
def reserve_feedback_d : ℝ := 1-dp
theorem reserve_feedback_d_exact : reserve_feedback_d = (999495191/5000000000:ℝ) := by norm_num [reserve_feedback_d,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_d_pos : 0<reserve_feedback_d := by rw [reserve_feedback_d_exact]; norm_num
def reserve_feedback_y : ℝ := 1/2-y
theorem reserve_feedback_y_exact : reserve_feedback_y = (1051453621/30000000000:ℝ) := by norm_num [reserve_feedback_y,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_y_pos : 0<reserve_feedback_y := by rw [reserve_feedback_y_exact]; norm_num
def reserve_floor : ℝ := theta-(4+y-x)/6-1/200-(4/25*x-3/20-51/100*y+67/100*dp-3/20*ell)
theorem reserve_floor_exact : reserve_floor = (4258073897/1000000000000:ℝ) := by norm_num [reserve_floor,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_floor_pos : 0<reserve_floor := by rw [reserve_floor_exact]; norm_num
def reserve_small_row : ℝ := -1/20-(13/75*h-y/2+63/50*d0)
theorem reserve_small_row_exact : reserve_small_row = (56237409433/1500000000000:ℝ) := by norm_num [reserve_small_row,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_row_pos : 0<reserve_small_row := by rw [reserve_small_row_exact]; norm_num
def reserve_principal_w : ℝ := y/20-(1+h)/1000-1/4000
theorem reserve_principal_w_exact : reserve_principal_w = (635924290099/30000000000000:ℝ) := by norm_num [reserve_principal_w,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_principal_w_pos : 0<reserve_principal_w := by rw [reserve_principal_w_exact]; norm_num
def reserve_principal_z : ℝ := h/600-1/1000-1/4000
theorem reserve_principal_z_exact : reserve_principal_z = (501009617/6000000000000:ℝ) := by norm_num [reserve_principal_z,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_principal_z_pos : 0<reserve_principal_z := by rw [reserve_principal_z_exact]; norm_num
def reserve_holomorphic_box : ℝ := theta-17/20
theorem reserve_holomorphic_box_exact : reserve_holomorphic_box = (247729897/10000000000:ℝ) := by norm_num [reserve_holomorphic_box,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_holomorphic_box_pos : 0<reserve_holomorphic_box := by rw [reserve_holomorphic_box_exact]; norm_num
def reserve_source_lambda : ℝ := physicalLambda-3
theorem reserve_source_lambda_exact : reserve_source_lambda = (13653997694883/50000000000000:ℝ) := by norm_num [reserve_source_lambda,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_lambda_pos : 0<reserve_source_lambda := by rw [reserve_source_lambda_exact]; norm_num
def reserve_source_intercept : ℝ := 1-physicalB
theorem reserve_source_intercept_exact : reserve_source_intercept = (1630484454379/50000000000000:ℝ) := by norm_num [reserve_source_intercept,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_intercept_pos : 0<reserve_source_intercept := by rw [reserve_source_intercept_exact]; norm_num
def reserve_source_C_cap : ℝ := (549989/10000000:ℝ)-11/250
theorem reserve_source_C_cap_exact : reserve_source_C_cap = (109989/10000000:ℝ) := by norm_num [reserve_source_C_cap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_C_cap_pos : 0<reserve_source_C_cap := by rw [reserve_source_C_cap_exact]; norm_num
def reserve_source_P_cap : ℝ := (549989/10000000:ℝ)-43/1000
theorem reserve_source_P_cap_exact : reserve_source_P_cap = (119989/10000000:ℝ) := by norm_num [reserve_source_P_cap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_P_cap_pos : 0<reserve_source_P_cap := by rw [reserve_source_P_cap_exact]; norm_num
end
end Record1252270103Finite
