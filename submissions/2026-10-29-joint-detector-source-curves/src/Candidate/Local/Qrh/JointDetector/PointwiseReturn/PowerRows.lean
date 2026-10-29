/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Facts
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def power_oldSmall_capP (δ p : ℝ) : ℝ := (513910423/375000000:ℝ)*δ^0*p^0 + (-513910423/1125000000:ℝ)*δ^0*p^1 + (-52497689/29296875:ℝ)*δ^1*p^0 + (-833140961839726583/1495754840000000000:ℝ)*δ^1*p^1 + (8470444457926351/59830193600000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (99077259243779053/149575484000000000:ℝ)*δ^2*p^1 + (25550438349535827/149575484000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_capP_expanded (δ p : ℝ) : rowMargin .oldSmall .capP δ p = power_oldSmall_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_capP] <;> ring

def power_oldSmall_old (δ p : ℝ) : ℝ := (513910423/375000000:ℝ)*δ^0*p^0 + (-109042342489652299/126204314625000000:ℝ)*δ^0*p^1 + (-52497689/29296875:ℝ)*δ^1*p^0 + (-78819846660888071/420681048750000000:ℝ)*δ^1*p^1 + (95110533074454351054067/125847142952817690000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (618105073322859/934846775000000:ℝ)*δ^2*p^1 + (-758170890093923/2804540325000000:ℝ)*δ^2*p^2 + (-212340715513812/1398301588364641:ℝ)*δ^2*p^3
theorem power_oldSmall_old_expanded (δ p : ℝ) : rowMargin .oldSmall .old δ p = power_oldSmall_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_old] <;> ring

def power_oldSwitch_C (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-6359560991665920699/53023904745875000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (177894835680763570059729718878503/571037487547258809252000000000000:ℝ)*δ^1*p^1 + (4725421688359287998117257139699/190345829182419603084000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1442466656788813048100144685742709/1427593718868147023130000000000000:ℝ)*δ^2*p^1 + (1152290872274917079040365787342709/1427593718868147023130000000000000:ℝ)*δ^2*p^2 + (-41021034550983392000/142759371886814702313:ℝ)*δ^2*p^3
theorem power_oldSwitch_C_expanded (δ p : ℝ) : rowMargin .oldSwitch .C δ p = power_oldSwitch_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_C] <;> ring

def power_oldSwitch_Cphys (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-7375717118710521821/64974677149125000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (22606590966934560649793393550857/77748950258592896412000000000000:ℝ)*δ^1*p^1 + (6363407298962776165621262464229/233246850775778689236000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-189451847103339926253578737535771/194372375646482241030000000000000:ℝ)*δ^2*p^1 + (147841187114552352105040567135771/194372375646482241030000000000000:ℝ)*δ^2*p^2 + (-5127629318872924000/19437237564648224103:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cphys δ p = power_oldSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cphys] <;> ring

def power_oldSwitch_capP (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-46754173/1125000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (75374374951649191/1682724195000000000:ℝ)*δ^1*p^1 + (13744671167160443/201926903400000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-93949677312839557/168272419500000000:ℝ)*δ^2*p^1 + (37531622021568797/168272419500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_capP_expanded (δ p : ℝ) : rowMargin .oldSwitch .capP δ p = power_oldSwitch_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_capP] <;> ring

def power_oldSwitch_old (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-9920375841621049/126204314625000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (61253019931236929/420681048750000000:ℝ)*δ^1*p^1 + (82560569148199159486603/1132624286575359210000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-6240310094281769/8413620975000000:ℝ)*δ^2*p^1 + (3944407329718231/8413620975000000:ℝ)*δ^2*p^2 + (-5127629318872924/37754142885845307:ℝ)*δ^2*p^3
theorem power_oldSwitch_old_expanded (δ p : ℝ) : rowMargin .oldSwitch .old δ p = power_oldSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_old] <;> ring

def power_newSwitch_C (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-6359560991665920699/53023904745875000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (1639848636355421081234531/5090294855604000000000000:ℝ)*δ^1*p^1 + (10621631626751008548667/727184979372000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-12912389539364628820477993/12725737139010000000000000:ℝ)*δ^2*p^1 + (10217582117075452203677993/12725737139010000000000000:ℝ)*δ^2*p^2 + (-355468384000/1272573713901:ℝ)*δ^2*p^3
theorem power_newSwitch_C_expanded (δ p : ℝ) : rowMargin .newSwitch .C δ p = power_newSwitch_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_C] <;> ring

def power_newSwitch_Cphys (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-7375717118710521821/64974677149125000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (69626693053745185334063/231021074308000000000000:ℝ)*δ^1*p^1 + (36614482739005054867033/2079189668772000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1696158178259394945132967/1732658057310000000000000:ℝ)*δ^2*p^1 + (1310511321294799184332967/1732658057310000000000000:ℝ)*δ^2*p^2 + (-44433548000/173265805731:ℝ)*δ^2*p^3
theorem power_newSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p = power_newSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cphys] <;> ring

def power_newSwitch_capP (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-46754173/1125000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (831238307/15000000000:ℝ)*δ^1*p^1 + (116147911/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-843852089/1500000000:ℝ)*δ^2*p^1 + (328187569/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_capP_expanded (δ p : ℝ) : rowMargin .newSwitch .capP δ p = power_newSwitch_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_capP] <;> ring

def power_newSwitch_old (δ p : ℝ) : ℝ := (46754173/375000000:ℝ)*δ^0*p^0 + (-9920375841621049/126204314625000000:ℝ)*δ^0*p^1 + (-328004173/937500000:ℝ)*δ^1*p^0 + (65721839709986929/420681048750000000:ℝ)*δ^1*p^1 + (668335532288231/10096345170000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2092020217503923/2804540325000000:ℝ)*δ^2*p^1 + (1302885590496077/2804540325000000:ℝ)*δ^2*p^2 + (-44433548/336544839:ℝ)*δ^2*p^3
theorem power_newSwitch_old_expanded (δ p : ℝ) : rowMargin .newSwitch .old δ p = power_newSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_old] <;> ring

def power_newTop_C (δ p : ℝ) : ℝ := (30191019901/600000000000:ℝ)*δ^0*p^0 + (-586660032191928948909/12119749656200000000000:ℝ)*δ^0*p^1 + (-791383339427/3000000000000:ℝ)*δ^1*p^0 + (770591779624966635622903691327079115907033/2351930772172243628444064000000000000000000:ℝ)*δ^1*p^1 + (-294998906331662543487887803995509491997069/4199876378879006479364400000000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-3900564898658251539219734696953859491997069/3499896982399172066137000000000000000000000:ℝ)*δ^2*p^1 + (43924140413716153358012332810320393478242107/48998557753588408925918000000000000000000000:ℝ)*δ^2*p^2 + (-4848087894785251103599321371389/17499484911995860330685000000000:ℝ)*δ^2*p^3
theorem power_newTop_C_expanded (δ p : ℝ) : rowMargin .newTop .C δ p = power_newTop_C δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_C] <;> ring

def power_newTop_Cphys (δ p : ℝ) : ℝ := (30191019901/600000000000:ℝ)*δ^0*p^0 + (-4762792453095806950877/103959483438600000000000:ℝ)*δ^0*p^1 + (-791383339427/3000000000000:ℝ)*δ^1*p^0 + (42895468758430459623011051200831/138612644584800000000000000000000:ℝ)*δ^1*p^1 + (-81015572203518552195702913510123796731943/1334268419360561441971600000000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-62180932121369084481354750400277/57755268577000000000000000000000:ℝ)*δ^2*p^1 + (97323231479217266194804750400277/115510537154000000000000000000000:ℝ)*δ^2*p^2 + (-33936615263496757725195249599723/133426841936056144197160000000000:ℝ)*δ^2*p^3
theorem power_newTop_Cphys_expanded (δ p : ℝ) : rowMargin .newTop .Cphys δ p = power_newTop_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cphys] <;> ring

def power_newTop_capP (δ p : ℝ) : ℝ := (30191019901/600000000000:ℝ)*δ^0*p^0 + (-30191019901/1800000000000:ℝ)*δ^0*p^1 + (-791383339427/3000000000000:ℝ)*δ^1*p^0 + (8472557198862803559740050860277/92408429723200000000000000000000:ℝ)*δ^1*p^1 + (16639825548831491627582948219723/277225289169600000000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-146830566535203829358617051780277/231021074308000000000000000000000:ℝ)*δ^2*p^1 + (51233404978162023822807550979723/231021074308000000000000000000000:ℝ)*δ^2*p^2
theorem power_newTop_capP_expanded (δ p : ℝ) : rowMargin .newTop .capP δ p = power_newTop_capP δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_capP] <;> ring

def power_newTop_old (δ p : ℝ) : ℝ := (30191019901/600000000000:ℝ)*δ^0*p^0 + (-6405979300709280313/201926903400000000000:ℝ)*δ^0*p^1 + (-791383339427/3000000000000:ℝ)*δ^1*p^0 + (5487544112945730876541978881173208520403/31099580103437158564800000000000000000000:ℝ)*δ^1*p^1 + (784183483576937274027778800006830493199/31099580103437158564800000000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-7168610417553636859992350966855156502267/8638772250954766268000000000000000000000:ℝ)*δ^2*p^1 + (13179580217472135375847613840034530493199/25916316752864298804000000000000000000000:ℝ)*δ^2*p^2 + (-33936615263496757725195249599723/259163167528642988040000000000000:ℝ)*δ^2*p^3
theorem power_newTop_old_expanded (δ p : ℝ) : rowMargin .newTop .old δ p = power_newTop_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_old] <;> ring

end
end Qrh.JointDetector.PointwiseReturn.FinalEdges
