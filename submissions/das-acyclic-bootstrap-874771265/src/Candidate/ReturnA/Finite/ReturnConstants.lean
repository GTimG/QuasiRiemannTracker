/- Adapted 2026-10-24 for Subhanjan Das, AI-assisted with OpenAI Codex.
Original Hailey Collet/Mark Lewko notices and Apache-2.0 license retained. -/
/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109.Bernstein
set_option autoImplicit false
namespace DasStageAFinite
noncomputable section
def c : ℝ := (12522873/100000000:ℝ)
def h : ℝ := (80008783/100000000:ℝ)
def physicalB : ℝ := (48385438492991/50000000000000:ℝ)
def physicalLambda : ℝ := (8191783441/2500000000:ℝ)
def countCB : ℝ := (96259356104003/100000000000000:ℝ)
def countCL : ℝ := (7879595941/2500000000:ℝ)
def naturalK : ℝ := (11243189691/2500000000:ℝ)
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
theorem c_value : c = (12522873/100000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem theta_value : theta = (87477127/100000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem h_value : h = (80008783/100000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ell_value : ell = (12568619/75000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem x_value : x = (110248127/300000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem y_value : y = (139477397/300000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem kappa_value : kappa = (37477127/50000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ds_value : ds = (3486934925/4424588286:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dk_value : dk = (139477397000000/174503964779427:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dp_value : dp = (8000878301/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem d0_value : d0 = (1/200:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSmall : edgeC .oldSmall = (125000/112431381:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldPeak : edgeD .oldPeak = (139477397/300000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldPeak : edgeC .oldPeak = (139477397/1349176572:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (3486934925/4424588286:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (139477397/4424588286:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newSwitch : edgeD .newSwitch = (3486934925/4424588286:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newSwitch : edgeC .newSwitch = (139477397/4424588286:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newTop : edgeD .newTop = (8000878301/10000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newTop : edgeC .newTop = (155888494468825497464873/4915070064600000000000000:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newKink : edgeD .newKink = (139477397000000/174503964779427:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newKink : edgeC .newKink = (5579095880000/174503964779427:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = ds/25 := by
 norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
def reserve_Gram_x_above_ell : ℝ := x-ell
theorem reserve_Gram_x_above_ell_exact : reserve_Gram_x_above_ell = (19991217/100000000:ℝ) := by norm_num [reserve_Gram_x_above_ell,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_x_above_ell_pos : 0<reserve_Gram_x_above_ell := by rw [reserve_Gram_x_above_ell_exact]; norm_num
def reserve_Gram_y_above_x : ℝ := y-x
theorem reserve_Gram_y_above_x_exact : reserve_Gram_y_above_x = (974309/10000000:ℝ) := by norm_num [reserve_Gram_y_above_x,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_y_above_x_pos : 0<reserve_Gram_y_above_x := by rw [reserve_Gram_y_above_x_exact]; norm_num
def reserve_Gram_ell_below_one_fifth : ℝ := 1/5-ell
theorem reserve_Gram_ell_below_one_fifth_exact : reserve_Gram_ell_below_one_fifth = (2431381/75000000:ℝ) := by norm_num [reserve_Gram_ell_below_one_fifth,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_ell_below_one_fifth_pos : 0<reserve_Gram_ell_below_one_fifth := by rw [reserve_Gram_ell_below_one_fifth_exact]; norm_num
def reserve_Gram_2x_above_y_plus_ell : ℝ := 2*x-y-ell
theorem reserve_Gram_2x_above_y_plus_ell_exact : reserve_Gram_2x_above_y_plus_ell = (10248127/100000000:ℝ) := by norm_num [reserve_Gram_2x_above_y_plus_ell,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_Gram_2x_above_y_plus_ell_pos : 0<reserve_Gram_2x_above_y_plus_ell := by rw [reserve_Gram_2x_above_y_plus_ell_exact]; norm_num
def reserve_conductor_small_before_peak : ℝ := y-d0
theorem reserve_conductor_small_before_peak_exact : reserve_conductor_small_before_peak = (137977397/300000000:ℝ) := by norm_num [reserve_conductor_small_before_peak,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_small_before_peak_pos : 0<reserve_conductor_small_before_peak := by rw [reserve_conductor_small_before_peak_exact]; norm_num
def reserve_conductor_peak_before_switch : ℝ := ds-y
theorem reserve_conductor_peak_before_switch_exact : reserve_conductor_peak_before_switch = (71491736762004743/221229414300000000:ℝ) := by norm_num [reserve_conductor_peak_before_switch,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_peak_before_switch_pos : 0<reserve_conductor_peak_before_switch := by rw [reserve_conductor_peak_before_switch_exact]; norm_num
def reserve_conductor_switch_before_kink : ℝ := dk-ds
theorem reserve_conductor_switch_before_kink_exact : reserve_conductor_switch_before_kink = (2882029195872538070675/257369399474536425997374:ℝ) := by norm_num [reserve_conductor_switch_before_kink,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_switch_before_kink_pos : 0<reserve_conductor_switch_before_kink := by rw [reserve_conductor_switch_before_kink_exact]; norm_num
def reserve_conductor_kink_before_top : ℝ := dp-dk
theorem reserve_conductor_kink_before_top_exact : reserve_conductor_kink_before_top = (1411015242185735513527/1745039647794270000000000:ℝ) := by norm_num [reserve_conductor_kink_before_top,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_kink_before_top_pos : 0<reserve_conductor_kink_before_top := by rw [reserve_conductor_kink_before_top_exact]; norm_num
def reserve_conductor_top_before_twoy : ℝ := 2*y-dp
theorem reserve_conductor_top_before_twoy_exact : reserve_conductor_top_before_twoy = (3892844497/30000000000:ℝ) := by norm_num [reserve_conductor_top_before_twoy,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_conductor_top_before_twoy_pos : 0<reserve_conductor_top_before_twoy := by rw [reserve_conductor_top_before_twoy_exact]; norm_num
def reserve_physical_plain_lower : ℝ := 1-y/ds-2/5-1/10000000
theorem reserve_physical_plain_lower_exact : reserve_physical_plain_lower = (6284247/625000000:ℝ) := by norm_num [reserve_physical_plain_lower,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_plain_lower_pos : 0<reserve_physical_plain_lower := by rw [reserve_physical_plain_lower_exact]; norm_num
def reserve_physical_plain_upper : ℝ := 11/25-(1-y/dp+1/400)-1/10000000
theorem reserve_physical_plain_upper_exact : reserve_physical_plain_upper = (4462551667990097/240026349030000000:ℝ) := by norm_num [reserve_physical_plain_upper,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_plain_upper_pos : 0<reserve_physical_plain_upper := by rw [reserve_physical_plain_upper_exact]; norm_num
def reserve_physical_width_lower : ℝ := min (1/25) ((physicalB-2*(1-y/dp+1/400))/physicalLambda)-17/500-1/10000000
theorem reserve_physical_width_lower_exact : reserve_physical_width_lower = (8091429619970835952575277/1966243871387640412230000000:ℝ) := by norm_num [reserve_physical_width_lower,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_width_lower_pos : 0<reserve_physical_width_lower := by rw [reserve_physical_width_lower_exact]; norm_num
def reserve_physical_width_upper : ℝ := 43/1000-1/25-1/10000000
theorem reserve_physical_width_upper_exact : reserve_physical_width_upper = (29999/10000000:ℝ) := by norm_num [reserve_physical_width_upper,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_physical_width_upper_pos : 0<reserve_physical_width_upper := by rw [reserve_physical_width_upper_exact]; norm_num
def reserve_small_width_shortening : ℝ := 1-2*(1-y/dp+1/400)-9/2*(17/500)-1/10000000
theorem reserve_small_width_shortening_exact : reserve_small_width_shortening = (1004257820625097/240026349030000000:ℝ) := by norm_num [reserve_small_width_shortening,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_width_shortening_pos : 0<reserve_small_width_shortening := by rw [reserve_small_width_shortening_exact]; norm_num
def reserve_short_plain_shortening : ℝ := 1-2/5-physicalB/2-(9/2-physicalLambda/2)*(1/25)-1/10000000
theorem reserve_short_plain_shortening_exact : reserve_short_plain_shortening = (167978259809/100000000000000:ℝ) := by norm_num [reserve_short_plain_shortening,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_short_plain_shortening_pos : 0<reserve_short_plain_shortening := by rw [reserve_short_plain_shortening_exact]; norm_num
def reserve_large_shift : ℝ := (7/18-1/500)*(1/400)+(1-physicalB)/18+(physicalLambda/18-1/4)*(1/25)-1/10000000
theorem reserve_large_shift_exact : reserve_large_shift = (38398259809/900000000000000:ℝ) := by norm_num [reserve_large_shift,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_large_shift_pos : 0<reserve_large_shift := by rw [reserve_large_shift_exact]; norm_num
def reserve_large_shift_clipped : ℝ := 1/2-1/500-1/(2*physicalLambda)
theorem reserve_large_shift_clipped_exact : reserve_large_shift_clipped = (1414754076809/4095891720500:ℝ) := by norm_num [reserve_large_shift_clipped,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_large_shift_clipped_pos : 0<reserve_large_shift_clipped := by rw [reserve_large_shift_clipped_exact]; norm_num
def reserve_small_shift_cost : ℝ := 1/2-1/(2*physicalLambda)-1/500
theorem reserve_small_shift_cost_exact : reserve_small_shift_cost = (1414754076809/4095891720500:ℝ) := by norm_num [reserve_small_shift_cost,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_shift_cost_pos : 0<reserve_small_shift_cost := by rw [reserve_small_shift_cost_exact]; norm_num
def reserve_prime_supply : ℝ := ell/dp-1/5
theorem reserve_prime_supply_exact : reserve_prime_supply = (1134603097/120013174515:ℝ) := by norm_num [reserve_prime_supply,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_prime_supply_pos : 0<reserve_prime_supply := by rw [reserve_prime_supply_exact]; norm_num
def reserve_capacity_domain : ℝ := y-dp/2
theorem reserve_capacity_domain_exact : reserve_capacity_domain = (3892844497/60000000000:ℝ) := by norm_num [reserve_capacity_domain,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_capacity_domain_pos : 0<reserve_capacity_domain := by rw [reserve_capacity_domain_exact]; norm_num
def reserve_incumbent : ℝ := naturalK/6-kappa
theorem reserve_incumbent_exact : reserve_incumbent = (17197/5000000000:ℝ) := by norm_num [reserve_incumbent,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_incumbent_pos : 0<reserve_incumbent := by rw [reserve_incumbent_exact]; norm_num
def reserve_feedback_kappa : ℝ := kappa-7/10
theorem reserve_feedback_kappa_exact : reserve_feedback_kappa = (2477127/50000000:ℝ) := by norm_num [reserve_feedback_kappa,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_kappa_pos : 0<reserve_feedback_kappa := by rw [reserve_feedback_kappa_exact]; norm_num
def reserve_feedback_d : ℝ := 1-dp
theorem reserve_feedback_d_exact : reserve_feedback_d = (1999121699/10000000000:ℝ) := by norm_num [reserve_feedback_d,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_d_pos : 0<reserve_feedback_d := by rw [reserve_feedback_d_exact]; norm_num
def reserve_feedback_y : ℝ := 1/2-y
theorem reserve_feedback_y_exact : reserve_feedback_y = (10522603/300000000:ℝ) := by norm_num [reserve_feedback_y,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_feedback_y_pos : 0<reserve_feedback_y := by rw [reserve_feedback_y_exact]; norm_num
def reserve_floor : ℝ := theta-(4+y-x)/6-1/200-(4/25*x-3/20-51/100*y+67/100*dp-3/20*ell)
theorem reserve_floor_exact : reserve_floor = (12771256999/3000000000000:ℝ) := by norm_num [reserve_floor,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_floor_pos : 0<reserve_floor := by rw [reserve_floor_exact]; norm_num
def reserve_small_row : ℝ := -1/20-(13/75*h-y/2+63/50*d0)
theorem reserve_small_row_exact : reserve_small_row = (187402189/5000000000:ℝ) := by norm_num [reserve_small_row,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_small_row_pos : 0<reserve_small_row := by rw [reserve_small_row_exact]; norm_num
def reserve_principal_w : ℝ := y/20-(1+h)/1000-1/4000
theorem reserve_principal_w_exact : reserve_principal_w = (6358843501/300000000000:ℝ) := by norm_num [reserve_principal_w,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_principal_w_pos : 0<reserve_principal_w := by rw [reserve_principal_w_exact]; norm_num
def reserve_principal_z : ℝ := h/600-1/1000-1/4000
theorem reserve_principal_z_exact : reserve_principal_z = (5008783/60000000000:ℝ) := by norm_num [reserve_principal_z,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_principal_z_pos : 0<reserve_principal_z := by rw [reserve_principal_z_exact]; norm_num
def reserve_holomorphic_box : ℝ := theta-17/20
theorem reserve_holomorphic_box_exact : reserve_holomorphic_box = (2477127/100000000:ℝ) := by norm_num [reserve_holomorphic_box,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_holomorphic_box_pos : 0<reserve_holomorphic_box := by rw [reserve_holomorphic_box_exact]; norm_num
def reserve_source_lambda : ℝ := physicalLambda-3
theorem reserve_source_lambda_exact : reserve_source_lambda = (691783441/2500000000:ℝ) := by norm_num [reserve_source_lambda,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_lambda_pos : 0<reserve_source_lambda := by rw [reserve_source_lambda_exact]; norm_num
def reserve_source_intercept : ℝ := 1-physicalB
theorem reserve_source_intercept_exact : reserve_source_intercept = (1614561507009/50000000000000:ℝ) := by norm_num [reserve_source_intercept,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_intercept_pos : 0<reserve_source_intercept := by rw [reserve_source_intercept_exact]; norm_num
def reserve_source_C_cap : ℝ := (44001/1000000:ℝ)-11/250
theorem reserve_source_C_cap_exact : reserve_source_C_cap = (1/1000000:ℝ) := by norm_num [reserve_source_C_cap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_C_cap_pos : 0<reserve_source_C_cap := by rw [reserve_source_C_cap_exact]; norm_num
def reserve_source_P_cap : ℝ := (43001/1000000:ℝ)-43/1000
theorem reserve_source_P_cap_exact : reserve_source_P_cap = (1/1000000:ℝ) := by norm_num [reserve_source_P_cap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem reserve_source_P_cap_pos : 0<reserve_source_P_cap := by rw [reserve_source_P_cap_exact]; norm_num
end
end DasStageAFinite
