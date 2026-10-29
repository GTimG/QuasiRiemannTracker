/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.Facts
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FirstRestartReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def power_oldSmall_Pcount (δ p : ℝ) : ℝ := (8250922141/6000000000:ℝ)*δ^0*p^0 + (-8250922141/18000000000:ℝ)*δ^0*p^1 + (-26907172141/15000000000:ℝ)*δ^1*p^0 + (-418450176194121137/747673480000000000:ℝ)*δ^1*p^1 + (4236940952818177/29906939200000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (49533741748454531/74767348000000000:ℝ)*δ^2*p^1 + (12824084063421309/74767348000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_Pcount_expanded (δ p : ℝ) : rowMargin .oldSmall .Pcount δ p = power_oldSmall_Pcount δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_Pcount] <;> ring

def power_oldSmall_Pcountmid (δ p : ℝ) : ℝ := (8250922141/6000000000:ℝ)*δ^0*p^0 + (-8250922141/18000000000:ℝ)*δ^0*p^1 + (-26907172141/15000000000:ℝ)*δ^1*p^0 + (-418452512673746137/747673480000000000:ℝ)*δ^1*p^1 + (4237034412003177/29906939200000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (49534022126009531/74767348000000000:ℝ)*δ^2*p^1 + (12823803685866309/74767348000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_Pcountmid_expanded (δ p : ℝ) : rowMargin .oldSmall .Pcountmid δ p = power_oldSmall_Pcountmid δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_Pcountmid] <;> ring

def power_oldSmall_Pnew (δ p : ℝ) : ℝ := (8250922141/6000000000:ℝ)*δ^0*p^0 + (-8250922141/18000000000:ℝ)*δ^0*p^1 + (-26907172141/15000000000:ℝ)*δ^1*p^0 + (-418632374875278637/747673480000000000:ℝ)*δ^1*p^1 + (4244228900064477/29906939200000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (49555605590193431/74767348000000000:ℝ)*δ^2*p^1 + (12802220221682409/74767348000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_Pnew_expanded (δ p : ℝ) : rowMargin .oldSmall .Pnew δ p = power_oldSmall_Pnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_Pnew] <;> ring

def power_oldSmall_Pwide (δ p : ℝ) : ℝ := (8250922141/6000000000:ℝ)*δ^0*p^0 + (-8250922141/18000000000:ℝ)*δ^0*p^1 + (-26907172141/15000000000:ℝ)*δ^1*p^0 + (-418501532016278637/747673480000000000:ℝ)*δ^1*p^1 + (4238995185704477/29906939200000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (49539904447113431/74767348000000000:ℝ)*δ^2*p^1 + (12817921364762409/74767348000000000:ℝ)*δ^2*p^2
theorem power_oldSmall_Pwide_expanded (δ p : ℝ) : rowMargin .oldSmall .Pwide δ p = power_oldSmall_Pwide δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_Pwide] <;> ring

def power_oldSmall_old (δ p : ℝ) : ℝ := (8250922141/6000000000:ℝ)*δ^0*p^0 + (-875220782327789051/1009359198000000000:ℝ)*δ^0*p^1 + (-26907172141/15000000000:ℝ)*δ^1*p^0 + (-159959235116668051/841132665000000000:ℝ)*δ^1*p^1 + (11921571810346614610241/15722314669555605000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (154579288596681/233647962500000:ℝ)*δ^2*p^1 + (-189289498803707/700943887500000:ℝ)*δ^2*p^2 + (-53197722753908/349384770434569:ℝ)*δ^2*p^3
theorem power_oldSmall_old_expanded (δ p : ℝ) : rowMargin .oldSmall .old δ p = power_oldSmall_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSmall_old] <;> ring

def power_oldSwitch_Cbridge0 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-802334187052456032403/6600725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (282198364997259794969597630201/925347683612040350085000000000:ℝ)*δ^1*p^1 + (23153359605629253029002507/925347683612040350085000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2309260541364869107048992479/2313369209030100875212500000:ℝ)*δ^2*p^1 + (1823805918758589950125165021/2313369209030100875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/185069536722408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge0_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge0 δ p = power_oldSwitch_Cbridge0 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge0] <;> ring

def power_oldSwitch_Cbridge1 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-215289223100669827019/1718379769662000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (280122059181559234517223880201/883291050362040350085000000000:ℝ)*δ^1*p^1 + (61495680775370698094128771/2649873151086121050255000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2249934326206386168041871229/2208227625905100875212500000:ℝ)*δ^2*p^1 + (1799923580972469111118043771/2208227625905100875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/176658210072408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge1_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge1 δ p = power_oldSwitch_Cbridge1 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge1] <;> ring

def power_oldSwitch_Cbridge2 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2329360347057368097209/18002177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (92571613724058169985197960067/280411472370680116695000000000:ℝ)*δ^1*p^1 + (54524019314906129429018771/2523703251336121050255000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-243290597162983415189664581/233676226975566763912500000:ℝ)*δ^2*p^1 + (197227611845032864420350419/233676226975566763912500000:ℝ)*δ^2*p^2 + (-50954777324220640000/168246883422408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge2_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge2 δ p = power_oldSwitch_Cbridge2 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge2] <;> ring

def power_oldSwitch_Cbridge3 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-763513080002456032403/5700725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (274995361718003223373570130201/799177783862040350085000000000:ℝ)*δ^1*p^1 + (16163047396267082275030007/799177783862040350085000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2128359638392955619310909979/1997944459655100875212500000:ℝ)*δ^2*p^1 + (1749236647903762762387082521/1997944459655100875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/159835556772408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge3_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge3 δ p = power_oldSwitch_Cbridge3 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge3] <;> ring

def power_oldSwitch_Cbridge4 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2251718132957368097209/16202177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (272003852414644828749105130201/757121150612040350085000000000:ℝ)*δ^1*p^1 + (43270354610257688348485021/2271363451836121050255000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2066287812771499177787514979/1892802876530100875212500000:ℝ)*δ^2*p^1 + (1722608699654668420863687521/1892802876530100875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/151424230122408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge4_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge4 δ p = power_oldSwitch_Cbridge4 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge4] <;> ring

def power_oldSwitch_Cbridge5 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2271128686482368097209/16652177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (30392427695563021895062236689/86461051915226705565000000000:ℝ)*δ^1*p^1 + (45783021818299954604120021/2334448401711121050255000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-699140150721152303843959993/648457889364200291737500000:ℝ)*δ^2*p^1 + (578673133453481701536017507/648457889364200291737500000:ℝ)*δ^2*p^2 + (-50954777324220640000/155629893447408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge5_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge5 δ p = power_oldSwitch_Cbridge5 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge5] <;> ring

def power_oldSwitch_Cbridge6 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-744102526477456032403/5250725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (270411859362207095959487630201/736092833987040350085000000000:ℝ)*δ^1*p^1 + (13649892007753838514112507/736092833987040350085000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2034963184758495350593662479/1840232084967600875212500000:ℝ)*δ^2*p^1 + (1709006010327845643669835021/1840232084967600875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/147218566797408070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cbridge6_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cbridge6 δ p = power_oldSwitch_Cbridge6 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cbridge6] <;> ring

def power_oldSwitch_Cnew (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-739638099166706032403/5147225822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (269276183214993214206471380201/721583295515790350085000000000:ℝ)*δ^1*p^1 + (13153336873776564896878757/721583295515790350085000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2013237588606427171445363729/1803958238789475875212500000:ℝ)*δ^2*p^1 + (1699508551869242389021536271/1803958238789475875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/144316659103158070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cnew_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cnew δ p = power_oldSwitch_Cnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cnew] <;> ring

def power_oldSwitch_Cphys (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-266797710566652010801/2185241940698000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (281908807036930422096250130201/919039188624540350085000000000:ℝ)*δ^1*p^1 + (2525916865725298753872223/102115465402726705565000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-2300427272827173799781449979/2297597971561350875212500000:ℝ)*δ^2*p^1 + (1820289231826748957857622521/2297597971561350875212500000:ℝ)*δ^2*p^2 + (-50954777324220640000/183807837724908070017:ℝ)*δ^2*p^3
theorem power_oldSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .oldSwitch .Cphys δ p = power_oldSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Cphys] <;> ring

def power_oldSwitch_Pcount (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (34582462852080637/420566332500000000:ℝ)*δ^1*p^1 + (3054861306395641/100935919800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-50777629253604359/84113266500000000:ℝ)*δ^2*p^1 + (22422527355714679/84113266500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_Pcount_expanded (δ p : ℝ) : rowMargin .oldSwitch .Pcount δ p = power_oldSwitch_Pcount δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Pcount] <;> ring

def power_oldSwitch_Pcountmid (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (34382693844143137/420566332500000000:ℝ)*δ^1*p^1 + (3102805868300641/100935919800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-50729684691699359/84113266500000000:ℝ)*δ^2*p^1 + (22374582793809679/84113266500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_Pcountmid_expanded (δ p : ℝ) : rowMargin .oldSwitch .Pcountmid δ p = power_oldSwitch_Pcountmid δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Pcountmid] <;> ring

def power_oldSwitch_Pnew (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (19004475613114387/420566332500000000:ℝ)*δ^1*p^1 + (6793578243747541/100935919800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-47038912316252459/84113266500000000:ℝ)*δ^2*p^1 + (18683810418362779/84113266500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_Pnew_expanded (δ p : ℝ) : rowMargin .oldSwitch .Pnew δ p = power_oldSwitch_Pnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Pnew] <;> ring

def power_oldSwitch_Pwide (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (30191540057614387/420566332500000000:ℝ)*δ^1*p^1 + (4108682777067541/100935919800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-49723807782932459/84113266500000000:ℝ)*δ^2*p^1 + (21368705885042779/84113266500000000:ℝ)*δ^2*p^2
theorem power_oldSwitch_Pwide_expanded (δ p : ℝ) : rowMargin .oldSwitch .Pwide δ p = power_oldSwitch_Pwide δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_Pwide] <;> ring

def power_oldSwitch_old (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-82359375358289051/1009359198000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (122841317165331949/841132665000000000:ℝ)*δ^1*p^1 + (10346976821605339304669/141500832026000445000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1561719905723621/2102831662500000:ℝ)*δ^2*p^1 + (984092358276379/2102831662500000:ℝ)*δ^2*p^2 + (-1273869433105516/9433388801733363:ℝ)*δ^2*p^3
theorem power_oldSwitch_old_expanded (δ p : ℝ) : rowMargin .oldSwitch .old δ p = power_oldSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_oldSwitch_old] <;> ring

def power_newSwitch_Cbridge0 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-802334187052456032403/6600725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (5231614730520430241791/16501814555235000000000:ℝ)*δ^1*p^1 + (75278218136547129/5500604851745000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-41380410171147075839/41254536388087500000:ℝ)*δ^2*p^1 + (32324962930552506661/41254536388087500000:ℝ)*δ^2*p^2 + (-879718240000/3300362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge0_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge0 δ p = power_newSwitch_Cbridge0 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge0] <;> ring

def power_newSwitch_Cbridge1 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-215289223100669827019/1718379769662000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (1728512253865431330597/5250604851745000000000:ℝ)*δ^1*p^1 + (544525091151332911/47255443665705000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-40313389043224667089/39379536388087500000:ℝ)*δ^2*p^1 + (31908117902630097911/39379536388087500000:ℝ)*δ^2*p^2 + (-879718240000/3150362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge1_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge1 δ p = power_newSwitch_Cbridge1 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge1] <;> ring

def power_newSwitch_Cbridge2 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2329360347057368097209/18002177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (5133557603582963991791/15001814555235000000000:ℝ)*δ^1*p^1 + (429249786341322911/45005443665705000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1452913494371654707/1389056903262500000:ℝ)*δ^2*p^1 + (10491189769146702637/12501512129362500000:ℝ)*δ^2*p^2 + (-879718240000/3000362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge2_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge2 δ p = power_newSwitch_Cbridge2 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge2] <;> ring

def power_newSwitch_Cbridge3 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-763513080002456032403/5700725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (5076009857085677741791/14251814555235000000000:ℝ)*δ^1*p^1 + (110226748994393887/14251814555235000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-38127233887392818339/35629536388087500000:ℝ)*δ^2*p^1 + (31022314946798249161/35629536388087500000:ℝ)*δ^2*p^2 + (-879718240000/2850362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge3_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge3 δ p = power_newSwitch_Cbridge3 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge3] <;> ring

def power_newSwitch_Cbridge4 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2251718132957368097209/16202177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (1671203658677287580597/4500604851745000000000:ℝ)*δ^1*p^1 + (246664111294626661/40505443665705000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-37011250023081373339/33754536388087500000:ℝ)*δ^2*p^1 + (30556507182486804161/33754536388087500000:ℝ)*δ^2*p^2 + (-879718240000/2700362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge4_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge4 δ p = power_newSwitch_Cbridge4 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge4] <;> ring

def power_newSwitch_Cbridge5 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-2271128686482368097209/16652177466282000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (5045385394711767741791/13876814555235000000000:ℝ)*δ^1*p^1 + (286947244679911661/41630443665705000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-12523655629898696113/11564012129362500000:ℝ)*δ^2*p^1 + (3421237333233502129/3854670709787500000:ℝ)*δ^2*p^2 + (-879718240000/2775362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge5_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge5 δ p = power_newSwitch_Cbridge5 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge5] <;> ring

def power_newSwitch_Cbridge6 (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-744102526477456032403/5250725822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (4980695306815420241791/13126814555235000000000:ℝ)*δ^1*p^1 + (23311636613217129/4375604851745000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-36448109404857045839/32817036388087500000:ℝ)*δ^2*p^1 + (30318454614262476661/32817036388087500000:ℝ)*δ^2*p^2 + (-879718240000/2625362911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cbridge6_expanded (δ p : ℝ) : rowMargin .newSwitch .Cbridge6 δ p = power_newSwitch_Cbridge6 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cbridge6] <;> ring

def power_newSwitch_Cnew (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-739638099166706032403/5147225822094000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (4957320087084066491791/12868064555235000000000:ℝ)*δ^1*p^1 + (62120660003255137/12868064555235000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-36057552154366234589/32170161388087500000:ℝ)*δ^2*p^1 + (30152208118271665411/32170161388087500000:ℝ)*δ^2*p^2 + (-879718240000/2573612911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cnew_expanded (δ p : ℝ) : rowMargin .newSwitch .Cnew δ p = power_newSwitch_Cnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cnew] <;> ring

def power_newSwitch_Cphys (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-266797710566652010801/2185241940698000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (5225093364429557741791/16389314555235000000000:ℝ)*δ^1*p^1 + (218795381558013887/16389314555235000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-41221527989701958339/40973286388087500000:ℝ)*δ^2*p^1 + (32263607164107389161/40973286388087500000:ℝ)*δ^2*p^2 + (-879718240000/3277862911047:ℝ)*δ^2*p^3
theorem power_newSwitch_Cphys_expanded (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p = power_newSwitch_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Cphys] <;> ring

def power_newSwitch_Pcount (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (707222467/7500000000:ℝ)*δ^1*p^1 + (47236831/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-912763169/1500000000:ℝ)*δ^2*p^1 + (392622289/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_Pcount_expanded (δ p : ℝ) : rowMargin .newSwitch .Pcount δ p = power_newSwitch_Pcount δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Pcount] <;> ring

def power_newSwitch_Pcountmid (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (703659967/7500000000:ℝ)*δ^1*p^1 + (48091831/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-911908169/1500000000:ℝ)*δ^2*p^1 + (391767289/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_Pcountmid_expanded (δ p : ℝ) : rowMargin .newSwitch .Pcountmid δ p = power_newSwitch_Pcountmid δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Pcountmid] <;> ring

def power_newSwitch_Pnew (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (429418717/7500000000:ℝ)*δ^1*p^1 + (113909731/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-846090269/1500000000:ℝ)*δ^2*p^1 + (325949389/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_Pnew_expanded (δ p : ℝ) : rowMargin .newSwitch .Pnew δ p = power_newSwitch_Pnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Pnew] <;> ring

def power_newSwitch_Pwide (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-776422141/18000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (628918717/7500000000:ℝ)*δ^1*p^1 + (66029731/1800000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-893970269/1500000000:ℝ)*δ^2*p^1 + (373829389/1500000000:ℝ)*δ^2*p^2
theorem power_newSwitch_Pwide_expanded (δ p : ℝ) : rowMargin .newSwitch .Pwide δ p = power_newSwitch_Pwide δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_Pwide] <;> ring

def power_newSwitch_old (δ p : ℝ) : ℝ := (776422141/6000000000:ℝ)*δ^0*p^0 + (-82359375358289051/1009359198000000000:ℝ)*δ^0*p^1 + (-5276422141/15000000000:ℝ)*δ^1*p^0 + (132992113916581949/841132665000000000:ℝ)*δ^1*p^1 + (165316832675129/2523397995000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-523956900824957/700943887500000:ℝ)*δ^2*p^1 + (324647187175043/700943887500000:ℝ)*δ^2*p^2 + (-21992956/168226533:ℝ)*δ^2*p^3
theorem power_newSwitch_old_expanded (δ p : ℝ) : rowMargin .newSwitch .old δ p = power_newSwitch_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newSwitch_old] <;> ring

def power_newTop_Cbridge1 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-7312115977185975946859/171837976966200000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (9209967168142125216758138538076618609/27537220646557388092363224000000000000:ℝ)*δ^1*p^1 + (-1424428958627477133199646239272064049/16522332387934432855417934400000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-15676648280745823949631628952727925849/13768610323278694046181612000000000000:ℝ)*δ^2*p^1 + (12658119823749987379110251025853148603/13768610323278694046181612000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/6884305161639347023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge1_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge1 δ p = power_newTop_Cbridge1 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge1] <;> ring

def power_newTop_Cbridge2 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-79114749753995735415449/1800217746628200000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (9064529363697320952218460717044764889/26226075482138588092363224000000000000:ℝ)*δ^1*p^1 + (-1460247664531550200085096726652951817/15735645289283152855417934400000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1693552531229527327662963271123201513/1457004193452143782909068000000000000:ℝ)*δ^2*p^1 + (4167687952993626141534791404411345457/4371012580356431348727204000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/6556518870534647023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge2_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge2 δ p = power_newTop_Cbridge2 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge2] <;> ring

def power_newTop_Cbridge3 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-25932074586315245138483/570072582209400000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (1484782201169443459091016571565008349/4152488386286631348727204000000000000:ℝ)*δ^1*p^1 + (-8276818661633942817171872967000683/83049767725732626974544080000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-740052913502207719421104992375799237/622873257942994702309080600000000000:ℝ)*δ^2*p^1 + (6170884441435127955109443660320603747/6228732579429947023090806000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/6228732579429947023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge3_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge3 δ p = power_newTop_Cbridge3 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge3] <;> ring

def power_newTop_Cbridge4 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-76477697763895735415449/1620217746628200000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (4371899208088128676324172563002246317/11801892576650494046181612000000000000:ℝ)*δ^1*p^1 + (-94623242072551455722596358251799279/885141943248787053463620900000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1794338572315839613167786805685581283/1475236572081311755772701500000000000:ℝ)*δ^2*p^1 + (6087519363131893736649082309304936509/5900946288325247023090806000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/5900946288325247023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge4_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge4 δ p = power_newTop_Cbridge4 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge4] <;> ring

def power_newTop_Cbridge5 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-77136960761420735415449/1665217746628200000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (4413659740705317342589570777267961827/12129678867755194046181612000000000000:ℝ)*δ^1*p^1 + (-375635954503992969568847749786911769/3638903660326558213854483600000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-1214877302181161752152612392716959073/1010806572312932837181801000000000000:ℝ)*δ^2*p^1 + (408634933548517569023589251190957721/404322628925173134872720400000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/6064839433877597023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge5_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge5 δ p = power_newTop_Cbridge5 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge5] <;> ring

def power_newTop_Cbridge6 (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-25272811588790245138483/525072582209400000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (721512188982943496165149265711774997/1912351047590965674363602000000000000:ℝ)*δ^1*p^1 + (-254020213069623310861039659925145477/2294821257109158809236322400000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-7064805440495778972585892836503367331/5737053142772897023090806000000000000:ℝ)*δ^2*p^1 + (1511218849523014129525899649516494677/1434263285693224255772701500000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/5737053142772897023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cbridge6_expanded (δ p : ℝ) : rowMargin .newTop .Cbridge6 δ p = power_newTop_Cbridge6 δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cbridge6] <;> ring

def power_newTop_Cnew (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-25121181099359495138483/514722582209400000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (2865935829527042095275345597911959333/7498622496455700697454408000000000000:ℝ)*δ^1*p^1 + (-170042343327355795011997672196402187/1499724499291140139490881600000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-13973550191593488116808635313223481483/11247933744683551046181612000000000000:ℝ)*δ^2*p^1 + (12030158846330327528768930367848704237/11247933744683551046181612000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/5623966872341775523090806:ℝ)*δ^2*p^3
theorem power_newTop_Cnew_expanded (δ p : ℝ) : rowMargin .newTop .Cnew δ p = power_newTop_Cnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cnew] <;> ring

def power_newTop_Cphys (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-9061558093870915046161/218524194069800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (1422413309294791458636681/4370483881396000000000000:ℝ)*δ^1*p^1 + (-115733372859776334776236790044939241/1432584701815668404618161200000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-3670289218881289522478777/3277862911047000000000000:ℝ)*δ^2*p^1 + (5850489399552888583366727/6555725822094000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/7162923509078342023090806:ℝ)*δ^2*p^3
theorem power_newTop_Cphys_expanded (δ p : ℝ) : rowMargin .newTop .Cphys δ p = power_newTop_Cphys δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Cphys] <;> ring

def power_newTop_Pcount (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-26370519901/1800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (36087440255640671780134226953/262229032883760000000000000000:ℝ)*δ^1*p^1 + (14819067804033610268854499141/786687098651280000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-455675137780117457281555500859/655572582209400000000000000000:ℝ)*δ^2*p^1 + (176055602869148411122472800859/655572582209400000000000000000:ℝ)*δ^2*p^2
theorem power_newTop_Pcount_expanded (δ p : ℝ) : rowMargin .newTop .Pcount δ p = power_newTop_Pcount δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Pcount] <;> ring

def power_newTop_Pcountmid (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-26370519901/1800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (35954393506192529935542491953/262229032883760000000000000000:ℝ)*δ^1*p^1 + (15218208052378035802629704141/786687098651280000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-455275997531773031747780295859/655572582209400000000000000000:ℝ)*δ^2*p^1 + (175656462620803985588697595859/655572582209400000000000000000:ℝ)*δ^2*p^2
theorem power_newTop_Pcountmid_expanded (δ p : ℝ) : rowMargin .newTop .Pcountmid δ p = power_newTop_Pcountmid δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Pcountmid] <;> ring

def power_newTop_Pnew (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-26370519901/1800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (25712454733674570738870731653/262229032883760000000000000000:ℝ)*δ^1*p^1 + (45944024369931913392644985041/786687098651280000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-424550181214219154157765014959/655572582209400000000000000000:ℝ)*δ^2*p^1 + (144930646303250107998682314959/655572582209400000000000000000:ℝ)*δ^2*p^2
theorem power_newTop_Pnew_expanded (δ p : ℝ) : rowMargin .newTop .Pnew δ p = power_newTop_Pnew δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Pnew] <;> ring

def power_newTop_Pwide (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-26370519901/1800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (33163072702770514036007891653/262229032883760000000000000000:ℝ)*δ^1*p^1 + (23592170462644083501233505041/786687098651280000000000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-446902035121506984049176494959/655572582209400000000000000000:ℝ)*δ^2*p^1 + (167282500210537937890093794959/655572582209400000000000000000:ℝ)*δ^2*p^2
theorem power_newTop_Pwide_expanded (δ p : ℝ) : rowMargin .newTop .Pwide δ p = power_newTop_Pwide δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_Pwide] <;> ring

def power_newTop_old (δ p : ℝ) : ℝ := (26370519901/600000000000:ℝ)*δ^0*p^0 + (-2797266373834244411/100935919800000000000:ℝ)*δ^0*p^1 + (-758530076927/3000000000000:ℝ)*δ^1*p^0 + (265365425261752006573928434701461/1470462701799264560136000000000000:ℝ)*δ^1*p^1 + (16731389974494555262792763157503/882277621079558736081600000000000:ℝ)*δ^1*p^2 + (1/2:ℝ)*δ^2*p^0 + (-206733412412021766904660529010899/245077116966544093356000000000000:ℝ)*δ^2*p^1 + (41995336484610251013124843684167/81692372322181364452000000000000:ℝ)*δ^2*p^2 + (-1908746706731820213913273/14704627017992645601360000:ℝ)*δ^2*p^3
theorem power_newTop_old_expanded (δ p : ℝ) : rowMargin .newTop .old δ p = power_newTop_old δ p := by
  norm_num [rowMargin, Ebase, edgeD, edgeC, oldCapacity, newCapacity,
    admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, power_newTop_old] <;> ring

end
end Qrh.JointDetector.FirstRestartReturn.FinalEdges
