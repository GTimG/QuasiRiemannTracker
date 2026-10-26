/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
set_option autoImplicit false
namespace QRH.RepeatedMarks.Return
noncomputable section
def c : ℝ := (626963/5000000:ℝ)
def h : ℝ := (4009/5000:ℝ)
def physicalB : ℝ := (335106151738000623869543064163/344806846470553600000000000000:ℝ)
def physicalLambda : ℝ := (631360617375411063383/210453397504000000000:ℝ)
def countCB : ℝ := (1272915379989926835893023/1315333734400000000000000:ℝ)
def countCL : ℝ := (3063363697870470065773/1052266987520000000000:ℝ)
def naturalK : ℝ := (9/2:ℝ)
def theta : ℝ := 1-c
def ell : ℝ := 4*c-1/3
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 1-2*c
def numeratorCap : ℝ := (9/200:ℝ)
def ds : ℝ := 2*y/(1+6*kappa*numeratorCap)
def dk : ℝ := 2*y/(2-physicalB+physicalLambda*numeratorCap)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
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
theorem c_value : c = (626963/5000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem theta_value : theta = (4373037/5000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem h_value : h = (4009/5000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem ell_value : ell = (630889/3750000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem x_value : x = (1374139/3750000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem y_value : y = (436243/937500:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem kappa_value : kappa = (1873037/2500000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem ds_value : ds = (697988800/901715997:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem dk_value : dk = (962685267999063770398720000000/1203169490402882649034676279511:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem dp_value : dp = (8018000001/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem d0_value : d0 = (1/200:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldSmall : edgeC .oldSmall = (6250/5619111:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldPeak : edgeD .oldPeak = (436243/937500:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldPeak : edgeC .oldPeak = (1744972/16857333:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (697988800/901715997:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (10469832/300571999:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newSwitch : edgeD .newSwitch = (697988800/901715997:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newSwitch : edgeC .newSwitch = (10469832/300571999:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newTop : edgeD .newTop = (8018000001/10000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newTop : edgeC .newTop = (1099528282827589498135869136985431192489/31032637065236204587401216000000000000000:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newKink : edgeD .newKink = (962685267999063770398720000000/1203169490402882649034676279511:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newKink : edgeC .newKink = (14440279019985956555980800000/401056496800960883011558759837:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = numeratorCap*ds := by
 norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h,numeratorCap]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.RepeatedMarks.Return
