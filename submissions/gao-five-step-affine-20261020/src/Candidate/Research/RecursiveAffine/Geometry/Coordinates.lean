import Candidate.Research.RecursiveAffine.Geometry.Constraints

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Geometry
noncomputable section
namespace Coordinates

/-- Literal fixed scalar prices; these definitions carry no physical hypotheses. -/
def kappa : ℝ := (4499 / 6000)

def alpha : ℝ := (1 / 100000000)

def mesh : ℝ := (1 / 100000000)

def mu : ℝ := (397 / 1000)

def outerLambda : ℝ := (329956163680853485282867923636152689767654715507615953261620968235438902692223089116358959199861693000368331363955693 / 88192178367938882647736127702504050241299135674720205790519673580377960007184113093769047066398565099317579025603487)

def outerB : ℝ := (18767487223416391834064569594363209332507915203299559923866443891942888098667853973693252077030625996356624104246276902412635109875927755490474333178781015079084539556698361407568181709371343649701393698420472934209822921806477506758480866628067754095992378338031176149156952588250753650209798776733040486658858005166457451154051 / 19110919888706709812766290819916485826208191340940770791940702158912085371003996164860792695046462830308466233784371844086544474228752143390838017296992738341176272874121327652590702574747109891599960269958366455044116610842062086316294176128155115437457794003213275776601341582216676004415608049429998920487638804738048000000000)

def top : ℝ := (2019049 / 50000000)

def q0 : ℝ := (127604383 / 200000000)

def q1 : ℝ := (676506091 / 1000000000)

def q2 : ℝ := (693781289 / 1000000000)

def q3 : ℝ := (142343339 / 200000000)

def q4 : ℝ := (730301837 / 1000000000)

def k0 : ℝ := (348304162270373263705960301936971458826525120191792362365107385589339077 / 520061477653773063826255649074195179732561721150754174190644313536034462)

def inner0 : ℝ := (1287143469639679686937537996934217729594808245187419539924946711845151667 / 1300153694134432659565639122685487949331404302876885435476610783840086155)

def k1 : ℝ := (3492140652204252985490844368535924067892717648044679111 / 5069587694592831216226672748036094407356305888268074666)

def inner1 : ℝ := (2516744594931318608918280476140232670724949148588757925 / 2534793847296415608113336374018047203678152944134037333)

def k2 : ℝ := (269813837551089325202799031444440059 / 380807241088706305360974188666640354)

def inner2 : ℝ := (135393878749136580688352305134408113 / 136002586103109394771776495952371555)

def k3 : ℝ := (12550898365191723707 / 17222127978271342242)

def inner3 : ℝ := (8592952672500196895 / 8611063989135671121)

def k4 : ℝ := (4499 / 6000)

def inner4 : ℝ := 1

def rho (q : ℝ) : ℝ := 1 - 10*q/(3*(5-2*q))

def lossCoefficient (q : ℝ) : ℝ := 5 - 6*rho q

def b (x : Fin 14 → ℝ) : ℝ := x 0

def rootSlack (x : Fin 14 → ℝ) : ℝ := x 13

def V0 (x : Fin 14 → ℝ) : ℝ := x 1

def Red0 (x : Fin 14 → ℝ) : ℝ := x 5

def ell0 (x : Fin 14 → ℝ) : ℝ := x 9

def V1 (x : Fin 14 → ℝ) : ℝ := x 2

def Red1 (x : Fin 14 → ℝ) : ℝ := x 6

def ell1 (x : Fin 14 → ℝ) : ℝ := x 10

def V2 (x : Fin 14 → ℝ) : ℝ := x 3

def Red2 (x : Fin 14 → ℝ) : ℝ := x 7

def ell2 (x : Fin 14 → ℝ) : ℝ := x 11

def V3 (x : Fin 14 → ℝ) : ℝ := x 4

def Red3 (x : Fin 14 → ℝ) : ℝ := x 8

def ell3 (x : Fin 14 → ℝ) : ℝ := x 12

def U0 (x : Fin 14 → ℝ) : ℝ := 1

def A0 (x : Fin 14 → ℝ) : ℝ := outerB - (outerLambda-1)*(b x-rootSlack x)

def z0 (x : Fin 14 → ℝ) : ℝ := b x-rootSlack x

def capA0 (x : Fin 14 → ℝ) : ℝ := A0 x

def gap0 (x : Fin 14 → ℝ) : ℝ := (outerB-inner0)+(6*k0-outerLambda)*b x

def a0 (x : Fin 14 → ℝ) : ℝ := q0/(6*(k0-q0*inner0))*gap0 x + alpha*U0 x

def d0 (x : Fin 14 → ℝ) : ℝ := (gap0 x+6*inner0*a0 x)/(6*k0)

def oldcap0 (x : Fin 14 → ℝ) : ℝ := capA0 x+(6*kappa-1)*z0 x-U0 x

def lowres0 (x : Fin 14 → ℝ) : ℝ := alpha*(1-q0*inner0/k0)*U0 x

def loss0_0 (x : Fin 14 → ℝ) : ℝ := 0

def loss0_1 (x : Fin 14 → ℝ) : ℝ := (51/200)*U0 x-A0 x/2+(1+6*kappa)*z0 x/2

def loss0_2 (x : Fin 14 → ℝ) : ℝ := (51/200)*U0 x-A0 x/2+(11/4)*z0 x

def gate0_first_error (x : Fin 14 → ℝ) : ℝ := (49/100)*a0 x-oldcap0 x/6-lowres0 x

def gate0_zero (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-6*a0 x-(1/380+1/100)*U0 x

def gate0_short_positive (x : Fin 14 → ℝ) : ℝ := (A0 x-(1+6*kappa)*z0 x-(1/100)*U0 x)/2

def gate0_comparison_positive (x : Fin 14 → ℝ) : ℝ := (A0 x-(11/2)*z0 x-(1/100)*U0 x)/2

def gate0_fixed_0 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-4*a0 x-(1/50)*U0 x-(2/3)*loss0_0 x

def gate0_exceptional_0 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-(9/2)*a0 x-(1/50)*U0 x-(2/3)*loss0_0 x

def gate0_fixed_1 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-4*a0 x-(1/50)*U0 x-(2/3)*loss0_1 x

def gate0_exceptional_1 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-(9/2)*a0 x-(1/50)*U0 x-(2/3)*loss0_1 x

def gate0_fixed_2 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-4*a0 x-(1/50)*U0 x-(2/3)*loss0_2 x

def gate0_exceptional_2 (x : Fin 14 → ℝ) : ℝ := U0 x-capA0 x-(9/2)*a0 x-(1/50)*U0 x-(2/3)*loss0_2 x

def gate0_direct_width_floor (x : Fin 14 → ℝ) : ℝ := (q0/(6*kappa))*((1-2*mu)*U0 x-oldcap0 x)+a0 x*(1-12*(q0/(6*kappa)))-lowres0 x

def historicalMissing0 (x : Fin 14 → ℝ) : ℝ := 0

def historicalReduction0 (x : Fin 14 → ℝ) : ℝ := 0

def totalAmplification0 (x : Fin 14 → ℝ) : ℝ := a0 x

def totalDeletion0 (x : Fin 14 → ℝ) : ℝ := 0

def outgoing0 (x : Fin 14 → ℝ) : ℝ := 1-historicalMissing0 x-6*totalAmplification0 x

def upperRootLength0 (x : Fin 14 → ℝ) : ℝ := outerB-(outerLambda-1)*(b x-mesh)

def returnedLength0 (x : Fin 14 → ℝ) : ℝ := upperRootLength0 x-historicalMissing0 x-historicalReduction0 x-totalDeletion0 x

def joint0 (x : Fin 14 → ℝ) : ℝ := (1-rho q0)-q0*upperRootLength0 x+(0)-lossCoefficient q0*totalAmplification0 x+(q0-(1-rho q0))*historicalMissing0 x+q0*historicalReduction0 x

def allBinGrowth0 (x : Fin 14 → ℝ) : ℝ := ((50/3)/(5-2*q0)^2)*outgoing0 x-returnedLength0 x

def U1 (x : Fin 14 → ℝ) : ℝ := U0 x - 6*a0 x - V0 x

def A1 (x : Fin 14 → ℝ) : ℝ := A0 x - d0 x - V0 x - Red0 x

def z1 (x : Fin 14 → ℝ) : ℝ := z0 x - d0 x - ell0 x

def capA1 (x : Fin 14 → ℝ) : ℝ := inner0*U1 x - (6*k0-1)*z1 x

def gap1 (x : Fin 14 → ℝ) : ℝ := capA1 x+(6*k1-1)*z1 x-inner1*U1 x

def a1 (x : Fin 14 → ℝ) : ℝ := q1/(6*(k1-q1*inner1))*gap1 x + alpha*U1 x

def d1 (x : Fin 14 → ℝ) : ℝ := (gap1 x+6*inner1*a1 x)/(6*k1)

def oldcap1 (x : Fin 14 → ℝ) : ℝ := capA1 x+(6*kappa-1)*z1 x-U1 x

def lowres1 (x : Fin 14 → ℝ) : ℝ := alpha*(1-q1*inner1/k1)*U1 x

def loss1_0 (x : Fin 14 → ℝ) : ℝ := 0

def loss1_1 (x : Fin 14 → ℝ) : ℝ := (51/200)*U1 x-A1 x/2+(1+6*kappa)*z1 x/2

def loss1_2 (x : Fin 14 → ℝ) : ℝ := (51/200)*U1 x-A1 x/2+(11/4)*z1 x

def gate1_first_error (x : Fin 14 → ℝ) : ℝ := (49/100)*a1 x-oldcap1 x/6-lowres1 x

def gate1_zero (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-6*a1 x-(1/380+1/100)*U1 x

def gate1_short_positive (x : Fin 14 → ℝ) : ℝ := (A1 x-(1+6*kappa)*z1 x-(1/100)*U1 x)/2

def gate1_comparison_positive (x : Fin 14 → ℝ) : ℝ := (A1 x-(11/2)*z1 x-(1/100)*U1 x)/2

def gate1_fixed_0 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-4*a1 x-(1/50)*U1 x-(2/3)*loss1_0 x

def gate1_exceptional_0 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-(9/2)*a1 x-(1/50)*U1 x-(2/3)*loss1_0 x

def gate1_fixed_1 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-4*a1 x-(1/50)*U1 x-(2/3)*loss1_1 x

def gate1_exceptional_1 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-(9/2)*a1 x-(1/50)*U1 x-(2/3)*loss1_1 x

def gate1_fixed_2 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-4*a1 x-(1/50)*U1 x-(2/3)*loss1_2 x

def gate1_exceptional_2 (x : Fin 14 → ℝ) : ℝ := U1 x-capA1 x-(9/2)*a1 x-(1/50)*U1 x-(2/3)*loss1_2 x

def gate1_direct_width_floor (x : Fin 14 → ℝ) : ℝ := (q1/(6*kappa))*((1-2*mu)*U1 x-oldcap1 x)+a1 x*(1-12*(q1/(6*kappa)))-lowres1 x

def historicalMissing1 (x : Fin 14 → ℝ) : ℝ := V0 x

def historicalReduction1 (x : Fin 14 → ℝ) : ℝ := Red0 x

def totalAmplification1 (x : Fin 14 → ℝ) : ℝ := a0 x + a1 x

def totalDeletion1 (x : Fin 14 → ℝ) : ℝ := d0 x

def outgoing1 (x : Fin 14 → ℝ) : ℝ := 1-historicalMissing1 x-6*totalAmplification1 x

def upperRootLength1 (x : Fin 14 → ℝ) : ℝ := outerB-(outerLambda-1)*(b x-mesh)

def returnedLength1 (x : Fin 14 → ℝ) : ℝ := upperRootLength1 x-historicalMissing1 x-historicalReduction1 x-totalDeletion1 x

def joint1 (x : Fin 14 → ℝ) : ℝ := (1-rho q1)-q1*upperRootLength1 x+((q1-q0)*d0 x)-lossCoefficient q1*totalAmplification1 x+(q1-(1-rho q1))*historicalMissing1 x+q1*historicalReduction1 x

def allBinGrowth1 (x : Fin 14 → ℝ) : ℝ := ((50/3)/(5-2*q1)^2)*outgoing1 x-returnedLength1 x

def U2 (x : Fin 14 → ℝ) : ℝ := U1 x - 6*a1 x - V1 x

def A2 (x : Fin 14 → ℝ) : ℝ := A1 x - d1 x - V1 x - Red1 x

def z2 (x : Fin 14 → ℝ) : ℝ := z1 x - d1 x - ell1 x

def capA2 (x : Fin 14 → ℝ) : ℝ := inner1*U2 x - (6*k1-1)*z2 x

def gap2 (x : Fin 14 → ℝ) : ℝ := capA2 x+(6*k2-1)*z2 x-inner2*U2 x

def a2 (x : Fin 14 → ℝ) : ℝ := q2/(6*(k2-q2*inner2))*gap2 x + alpha*U2 x

def d2 (x : Fin 14 → ℝ) : ℝ := (gap2 x+6*inner2*a2 x)/(6*k2)

def oldcap2 (x : Fin 14 → ℝ) : ℝ := capA2 x+(6*kappa-1)*z2 x-U2 x

def lowres2 (x : Fin 14 → ℝ) : ℝ := alpha*(1-q2*inner2/k2)*U2 x

def loss2_0 (x : Fin 14 → ℝ) : ℝ := 0

def loss2_1 (x : Fin 14 → ℝ) : ℝ := (51/200)*U2 x-A2 x/2+(1+6*kappa)*z2 x/2

def loss2_2 (x : Fin 14 → ℝ) : ℝ := (51/200)*U2 x-A2 x/2+(11/4)*z2 x

def gate2_first_error (x : Fin 14 → ℝ) : ℝ := (49/100)*a2 x-oldcap2 x/6-lowres2 x

def gate2_zero (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-6*a2 x-(1/380+1/100)*U2 x

def gate2_short_positive (x : Fin 14 → ℝ) : ℝ := (A2 x-(1+6*kappa)*z2 x-(1/100)*U2 x)/2

def gate2_comparison_positive (x : Fin 14 → ℝ) : ℝ := (A2 x-(11/2)*z2 x-(1/100)*U2 x)/2

def gate2_fixed_0 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-4*a2 x-(1/50)*U2 x-(2/3)*loss2_0 x

def gate2_exceptional_0 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-(9/2)*a2 x-(1/50)*U2 x-(2/3)*loss2_0 x

def gate2_fixed_1 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-4*a2 x-(1/50)*U2 x-(2/3)*loss2_1 x

def gate2_exceptional_1 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-(9/2)*a2 x-(1/50)*U2 x-(2/3)*loss2_1 x

def gate2_fixed_2 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-4*a2 x-(1/50)*U2 x-(2/3)*loss2_2 x

def gate2_exceptional_2 (x : Fin 14 → ℝ) : ℝ := U2 x-capA2 x-(9/2)*a2 x-(1/50)*U2 x-(2/3)*loss2_2 x

def gate2_direct_width_floor (x : Fin 14 → ℝ) : ℝ := (q2/(6*kappa))*((1-2*mu)*U2 x-oldcap2 x)+a2 x*(1-12*(q2/(6*kappa)))-lowres2 x

def historicalMissing2 (x : Fin 14 → ℝ) : ℝ := V0 x + V1 x

def historicalReduction2 (x : Fin 14 → ℝ) : ℝ := Red0 x + Red1 x

def totalAmplification2 (x : Fin 14 → ℝ) : ℝ := a0 x + a1 x + a2 x

def totalDeletion2 (x : Fin 14 → ℝ) : ℝ := d0 x + d1 x

def outgoing2 (x : Fin 14 → ℝ) : ℝ := 1-historicalMissing2 x-6*totalAmplification2 x

def upperRootLength2 (x : Fin 14 → ℝ) : ℝ := outerB-(outerLambda-1)*(b x-mesh)

def returnedLength2 (x : Fin 14 → ℝ) : ℝ := upperRootLength2 x-historicalMissing2 x-historicalReduction2 x-totalDeletion2 x

def joint2 (x : Fin 14 → ℝ) : ℝ := (1-rho q2)-q2*upperRootLength2 x+((q2-q0)*d0 x + (q2-q1)*d1 x)-lossCoefficient q2*totalAmplification2 x+(q2-(1-rho q2))*historicalMissing2 x+q2*historicalReduction2 x

def allBinGrowth2 (x : Fin 14 → ℝ) : ℝ := ((50/3)/(5-2*q2)^2)*outgoing2 x-returnedLength2 x

def U3 (x : Fin 14 → ℝ) : ℝ := U2 x - 6*a2 x - V2 x

def A3 (x : Fin 14 → ℝ) : ℝ := A2 x - d2 x - V2 x - Red2 x

def z3 (x : Fin 14 → ℝ) : ℝ := z2 x - d2 x - ell2 x

def capA3 (x : Fin 14 → ℝ) : ℝ := inner2*U3 x - (6*k2-1)*z3 x

def gap3 (x : Fin 14 → ℝ) : ℝ := capA3 x+(6*k3-1)*z3 x-inner3*U3 x

def a3 (x : Fin 14 → ℝ) : ℝ := q3/(6*(k3-q3*inner3))*gap3 x + alpha*U3 x

def d3 (x : Fin 14 → ℝ) : ℝ := (gap3 x+6*inner3*a3 x)/(6*k3)

def oldcap3 (x : Fin 14 → ℝ) : ℝ := capA3 x+(6*kappa-1)*z3 x-U3 x

def lowres3 (x : Fin 14 → ℝ) : ℝ := alpha*(1-q3*inner3/k3)*U3 x

def loss3_0 (x : Fin 14 → ℝ) : ℝ := 0

def loss3_1 (x : Fin 14 → ℝ) : ℝ := (51/200)*U3 x-A3 x/2+(1+6*kappa)*z3 x/2

def loss3_2 (x : Fin 14 → ℝ) : ℝ := (51/200)*U3 x-A3 x/2+(11/4)*z3 x

def gate3_first_error (x : Fin 14 → ℝ) : ℝ := (49/100)*a3 x-oldcap3 x/6-lowres3 x

def gate3_zero (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-6*a3 x-(1/380+1/100)*U3 x

def gate3_short_positive (x : Fin 14 → ℝ) : ℝ := (A3 x-(1+6*kappa)*z3 x-(1/100)*U3 x)/2

def gate3_comparison_positive (x : Fin 14 → ℝ) : ℝ := (A3 x-(11/2)*z3 x-(1/100)*U3 x)/2

def gate3_fixed_0 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-4*a3 x-(1/50)*U3 x-(2/3)*loss3_0 x

def gate3_exceptional_0 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-(9/2)*a3 x-(1/50)*U3 x-(2/3)*loss3_0 x

def gate3_fixed_1 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-4*a3 x-(1/50)*U3 x-(2/3)*loss3_1 x

def gate3_exceptional_1 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-(9/2)*a3 x-(1/50)*U3 x-(2/3)*loss3_1 x

def gate3_fixed_2 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-4*a3 x-(1/50)*U3 x-(2/3)*loss3_2 x

def gate3_exceptional_2 (x : Fin 14 → ℝ) : ℝ := U3 x-capA3 x-(9/2)*a3 x-(1/50)*U3 x-(2/3)*loss3_2 x

def gate3_direct_width_floor (x : Fin 14 → ℝ) : ℝ := (q3/(6*kappa))*((1-2*mu)*U3 x-oldcap3 x)+a3 x*(1-12*(q3/(6*kappa)))-lowres3 x

def historicalMissing3 (x : Fin 14 → ℝ) : ℝ := V0 x + V1 x + V2 x

def historicalReduction3 (x : Fin 14 → ℝ) : ℝ := Red0 x + Red1 x + Red2 x

def totalAmplification3 (x : Fin 14 → ℝ) : ℝ := a0 x + a1 x + a2 x + a3 x

def totalDeletion3 (x : Fin 14 → ℝ) : ℝ := d0 x + d1 x + d2 x

def outgoing3 (x : Fin 14 → ℝ) : ℝ := 1-historicalMissing3 x-6*totalAmplification3 x

def upperRootLength3 (x : Fin 14 → ℝ) : ℝ := outerB-(outerLambda-1)*(b x-mesh)

def returnedLength3 (x : Fin 14 → ℝ) : ℝ := upperRootLength3 x-historicalMissing3 x-historicalReduction3 x-totalDeletion3 x

def joint3 (x : Fin 14 → ℝ) : ℝ := (1-rho q3)-q3*upperRootLength3 x+((q3-q0)*d0 x + (q3-q1)*d1 x + (q3-q2)*d2 x)-lossCoefficient q3*totalAmplification3 x+(q3-(1-rho q3))*historicalMissing3 x+q3*historicalReduction3 x

def allBinGrowth3 (x : Fin 14 → ℝ) : ℝ := ((50/3)/(5-2*q3)^2)*outgoing3 x-returnedLength3 x

def U4 (x : Fin 14 → ℝ) : ℝ := U3 x - 6*a3 x - V3 x

def A4 (x : Fin 14 → ℝ) : ℝ := A3 x - d3 x - V3 x - Red3 x

def z4 (x : Fin 14 → ℝ) : ℝ := z3 x - d3 x - ell3 x

def capA4 (x : Fin 14 → ℝ) : ℝ := A4 x

def gap4 (x : Fin 14 → ℝ) : ℝ := capA4 x+(6*k4-1)*z4 x-inner4*U4 x

def a4 (x : Fin 14 → ℝ) : ℝ := q4/(6*(k4-q4*inner4))*gap4 x + alpha*U4 x

def d4 (x : Fin 14 → ℝ) : ℝ := (gap4 x+6*inner4*a4 x)/(6*k4)

def oldcap4 (x : Fin 14 → ℝ) : ℝ := capA4 x+(6*kappa-1)*z4 x-U4 x

def lowres4 (x : Fin 14 → ℝ) : ℝ := alpha*(1-q4*inner4/k4)*U4 x

def loss4_0 (x : Fin 14 → ℝ) : ℝ := 0

def loss4_1 (x : Fin 14 → ℝ) : ℝ := (51/200)*U4 x-A4 x/2+(1+6*kappa)*z4 x/2

def loss4_2 (x : Fin 14 → ℝ) : ℝ := (51/200)*U4 x-A4 x/2+(11/4)*z4 x

def gate4_first_error (x : Fin 14 → ℝ) : ℝ := (49/100)*a4 x-oldcap4 x/6-lowres4 x

def gate4_zero (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-6*a4 x-(1/380+1/100)*U4 x

def gate4_short_positive (x : Fin 14 → ℝ) : ℝ := (A4 x-(1+6*kappa)*z4 x-(1/100)*U4 x)/2

def gate4_comparison_positive (x : Fin 14 → ℝ) : ℝ := (A4 x-(11/2)*z4 x-(1/100)*U4 x)/2

def gate4_fixed_0 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-4*a4 x-(1/50)*U4 x-(2/3)*loss4_0 x

def gate4_exceptional_0 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-(9/2)*a4 x-(1/50)*U4 x-(2/3)*loss4_0 x

def gate4_fixed_1 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-4*a4 x-(1/50)*U4 x-(2/3)*loss4_1 x

def gate4_exceptional_1 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-(9/2)*a4 x-(1/50)*U4 x-(2/3)*loss4_1 x

def gate4_fixed_2 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-4*a4 x-(1/50)*U4 x-(2/3)*loss4_2 x

def gate4_exceptional_2 (x : Fin 14 → ℝ) : ℝ := U4 x-capA4 x-(9/2)*a4 x-(1/50)*U4 x-(2/3)*loss4_2 x

def historicalMissing4 (x : Fin 14 → ℝ) : ℝ := V0 x + V1 x + V2 x + V3 x

def historicalReduction4 (x : Fin 14 → ℝ) : ℝ := Red0 x + Red1 x + Red2 x + Red3 x

def totalAmplification4 (x : Fin 14 → ℝ) : ℝ := a0 x + a1 x + a2 x + a3 x + a4 x

def totalDeletion4 (x : Fin 14 → ℝ) : ℝ := d0 x + d1 x + d2 x + d3 x

def outgoing4 (x : Fin 14 → ℝ) : ℝ := 1-historicalMissing4 x-6*totalAmplification4 x

def upperRootLength4 (x : Fin 14 → ℝ) : ℝ := outerB-(outerLambda-1)*(b x-mesh)

def returnedLength4 (x : Fin 14 → ℝ) : ℝ := upperRootLength4 x-historicalMissing4 x-historicalReduction4 x-totalDeletion4 x

def joint4 (x : Fin 14 → ℝ) : ℝ := (1-rho q4)-q4*upperRootLength4 x+((q4-q0)*d0 x + (q4-q1)*d1 x + (q4-q2)*d2 x + (q4-q3)*d3 x)-lossCoefficient q4*totalAmplification4 x+(q4-(1-rho q4))*historicalMissing4 x+q4*historicalReduction4 x

def allBinGrowth4 (x : Fin 14 → ℝ) : ℝ := ((50/3)/(5-2*q4)^2)*outgoing4 x-returnedLength4 x

def row00 (x : Fin 14 → ℝ) : ℝ := b x-(17/500+mesh)

def row01 (x : Fin 14 → ℝ) : ℝ := top-b x

def row02 (x : Fin 14 → ℝ) : ℝ := mesh-rootSlack x

def row03 (x : Fin 14 → ℝ) : ℝ := a0 x

def row04 (x : Fin 14 → ℝ) : ℝ := U0 x-1/1000000

def row05 (x : Fin 14 → ℝ) : ℝ := A0 x-z0 x

def row06 (x : Fin 14 → ℝ) : ℝ := z0 x

def row07 (x : Fin 14 → ℝ) : ℝ := V0 x+Red0 x-ell0 x

def row08 (x : Fin 14 → ℝ) : ℝ := U1 x-mu*U0 x

def row09 (x : Fin 14 → ℝ) : ℝ := A1 x+(6*kappa-1)*z1 x-U1 x

def row10 (x : Fin 14 → ℝ) : ℝ := a1 x

def row11 (x : Fin 14 → ℝ) : ℝ := U1 x-1/1000000

def row12 (x : Fin 14 → ℝ) : ℝ := A1 x-z1 x

def row13 (x : Fin 14 → ℝ) : ℝ := z1 x

def row14 (x : Fin 14 → ℝ) : ℝ := V1 x+Red1 x-ell1 x

def row15 (x : Fin 14 → ℝ) : ℝ := U2 x-mu*U1 x

def row16 (x : Fin 14 → ℝ) : ℝ := A2 x+(6*kappa-1)*z2 x-U2 x

def row17 (x : Fin 14 → ℝ) : ℝ := a2 x

def row18 (x : Fin 14 → ℝ) : ℝ := U2 x-1/1000000

def row19 (x : Fin 14 → ℝ) : ℝ := A2 x-z2 x

def row20 (x : Fin 14 → ℝ) : ℝ := z2 x

def row21 (x : Fin 14 → ℝ) : ℝ := V2 x+Red2 x-ell2 x

def row22 (x : Fin 14 → ℝ) : ℝ := U3 x-mu*U2 x

def row23 (x : Fin 14 → ℝ) : ℝ := A3 x+(6*kappa-1)*z3 x-U3 x

def row24 (x : Fin 14 → ℝ) : ℝ := a3 x

def row25 (x : Fin 14 → ℝ) : ℝ := U3 x-1/1000000

def row26 (x : Fin 14 → ℝ) : ℝ := A3 x-z3 x

def row27 (x : Fin 14 → ℝ) : ℝ := z3 x

def row28 (x : Fin 14 → ℝ) : ℝ := V3 x+Red3 x-ell3 x

def row29 (x : Fin 14 → ℝ) : ℝ := U4 x-mu*U3 x

def row30 (x : Fin 14 → ℝ) : ℝ := A4 x+(6*kappa-1)*z4 x-U4 x

def row31 (x : Fin 14 → ℝ) : ℝ := a4 x

def row32 (x : Fin 14 → ℝ) : ℝ := U4 x-1/1000000

def row33 (x : Fin 14 → ℝ) : ℝ := A4 x-z4 x

def row34 (x : Fin 14 → ℝ) : ℝ := z4 x

def row35 (x : Fin 14 → ℝ) : ℝ := V0 x

def row36 (x : Fin 14 → ℝ) : ℝ := V1 x

def row37 (x : Fin 14 → ℝ) : ℝ := V2 x

def row38 (x : Fin 14 → ℝ) : ℝ := V3 x

def row39 (x : Fin 14 → ℝ) : ℝ := Red0 x

def row40 (x : Fin 14 → ℝ) : ℝ := Red1 x

def row41 (x : Fin 14 → ℝ) : ℝ := Red2 x

def row42 (x : Fin 14 → ℝ) : ℝ := Red3 x

def row43 (x : Fin 14 → ℝ) : ℝ := ell0 x

def row44 (x : Fin 14 → ℝ) : ℝ := ell1 x

def row45 (x : Fin 14 → ℝ) : ℝ := ell2 x

def row46 (x : Fin 14 → ℝ) : ℝ := ell3 x

def row47 (x : Fin 14 → ℝ) : ℝ := rootSlack x

def rows (i : Fin 48) (x : Fin 14 → ℝ) : ℝ :=
  ![row00 x, row01 x, row02 x, row03 x, row04 x, row05 x, row06 x, row07 x, row08 x, row09 x, row10 x, row11 x, row12 x, row13 x, row14 x, row15 x, row16 x, row17 x, row18 x, row19 x, row20 x, row21 x, row22 x, row23 x, row24 x, row25 x, row26 x, row27 x, row28 x, row29 x, row30 x, row31 x, row32 x, row33 x, row34 x, row35 x, row36 x, row37 x, row38 x, row39 x, row40 x, row41 x, row42 x, row43 x, row44 x, row45 x, row46 x, row47 x] i

def objective00 (x : Fin 14 → ℝ) : ℝ := gate1_first_error x

def objective01 (x : Fin 14 → ℝ) : ℝ := gate1_zero x

def objective02 (x : Fin 14 → ℝ) : ℝ := gate1_short_positive x

def objective03 (x : Fin 14 → ℝ) : ℝ := gate1_comparison_positive x

def objective04 (x : Fin 14 → ℝ) : ℝ := gate1_fixed_0 x

def objective05 (x : Fin 14 → ℝ) : ℝ := gate1_exceptional_0 x

def objective06 (x : Fin 14 → ℝ) : ℝ := gate1_fixed_1 x

def objective07 (x : Fin 14 → ℝ) : ℝ := gate1_exceptional_1 x

def objective08 (x : Fin 14 → ℝ) : ℝ := gate1_fixed_2 x

def objective09 (x : Fin 14 → ℝ) : ℝ := gate1_exceptional_2 x

def objective10 (x : Fin 14 → ℝ) : ℝ := gate1_direct_width_floor x

def objective11 (x : Fin 14 → ℝ) : ℝ := U1 x

def objective12 (x : Fin 14 → ℝ) : ℝ := gap1 x

def objective13 (x : Fin 14 → ℝ) : ℝ := joint1 x

def objective14 (x : Fin 14 → ℝ) : ℝ := outgoing1 x

def objective15 (x : Fin 14 → ℝ) : ℝ := allBinGrowth1 x

def objective16 (x : Fin 14 → ℝ) : ℝ := gate2_first_error x

def objective17 (x : Fin 14 → ℝ) : ℝ := gate2_zero x

def objective18 (x : Fin 14 → ℝ) : ℝ := gate2_short_positive x

def objective19 (x : Fin 14 → ℝ) : ℝ := gate2_comparison_positive x

def objective20 (x : Fin 14 → ℝ) : ℝ := gate2_fixed_0 x

def objective21 (x : Fin 14 → ℝ) : ℝ := gate2_exceptional_0 x

def objective22 (x : Fin 14 → ℝ) : ℝ := gate2_fixed_1 x

def objective23 (x : Fin 14 → ℝ) : ℝ := gate2_exceptional_1 x

def objective24 (x : Fin 14 → ℝ) : ℝ := gate2_fixed_2 x

def objective25 (x : Fin 14 → ℝ) : ℝ := gate2_exceptional_2 x

def objective26 (x : Fin 14 → ℝ) : ℝ := gate2_direct_width_floor x

def objective27 (x : Fin 14 → ℝ) : ℝ := U2 x

def objective28 (x : Fin 14 → ℝ) : ℝ := gap2 x

def objective29 (x : Fin 14 → ℝ) : ℝ := joint2 x

def objective30 (x : Fin 14 → ℝ) : ℝ := outgoing2 x

def objective31 (x : Fin 14 → ℝ) : ℝ := allBinGrowth2 x

def objective32 (x : Fin 14 → ℝ) : ℝ := gate3_first_error x

def objective33 (x : Fin 14 → ℝ) : ℝ := gate3_zero x

def objective34 (x : Fin 14 → ℝ) : ℝ := gate3_short_positive x

def objective35 (x : Fin 14 → ℝ) : ℝ := gate3_comparison_positive x

def objective36 (x : Fin 14 → ℝ) : ℝ := gate3_fixed_0 x

def objective37 (x : Fin 14 → ℝ) : ℝ := gate3_exceptional_0 x

def objective38 (x : Fin 14 → ℝ) : ℝ := gate3_fixed_1 x

def objective39 (x : Fin 14 → ℝ) : ℝ := gate3_exceptional_1 x

def objective40 (x : Fin 14 → ℝ) : ℝ := gate3_fixed_2 x

def objective41 (x : Fin 14 → ℝ) : ℝ := gate3_exceptional_2 x

def objective42 (x : Fin 14 → ℝ) : ℝ := gate3_direct_width_floor x

def objective43 (x : Fin 14 → ℝ) : ℝ := U3 x

def objective44 (x : Fin 14 → ℝ) : ℝ := gap3 x

def objective45 (x : Fin 14 → ℝ) : ℝ := joint3 x

def objective46 (x : Fin 14 → ℝ) : ℝ := outgoing3 x

def objective47 (x : Fin 14 → ℝ) : ℝ := allBinGrowth3 x

def objective48 (x : Fin 14 → ℝ) : ℝ := gate4_first_error x

def objective49 (x : Fin 14 → ℝ) : ℝ := gate4_zero x

def objective50 (x : Fin 14 → ℝ) : ℝ := gate4_short_positive x

def objective51 (x : Fin 14 → ℝ) : ℝ := gate4_comparison_positive x

def objective52 (x : Fin 14 → ℝ) : ℝ := gate4_fixed_0 x

def objective53 (x : Fin 14 → ℝ) : ℝ := gate4_exceptional_0 x

def objective54 (x : Fin 14 → ℝ) : ℝ := gate4_fixed_1 x

def objective55 (x : Fin 14 → ℝ) : ℝ := gate4_exceptional_1 x

def objective56 (x : Fin 14 → ℝ) : ℝ := gate4_fixed_2 x

def objective57 (x : Fin 14 → ℝ) : ℝ := gate4_exceptional_2 x

def objective58 (x : Fin 14 → ℝ) : ℝ := U4 x

def objective59 (x : Fin 14 → ℝ) : ℝ := joint4 x

def objective60 (x : Fin 14 → ℝ) : ℝ := outgoing4 x

def objective61 (x : Fin 14 → ℝ) : ℝ := allBinGrowth4 x

def objectives (i : Fin 62) (x : Fin 14 → ℝ) : ℝ :=
  ![objective00 x, objective01 x, objective02 x, objective03 x, objective04 x, objective05 x, objective06 x, objective07 x, objective08 x, objective09 x, objective10 x, objective11 x, objective12 x, objective13 x, objective14 x, objective15 x, objective16 x, objective17 x, objective18 x, objective19 x, objective20 x, objective21 x, objective22 x, objective23 x, objective24 x, objective25 x, objective26 x, objective27 x, objective28 x, objective29 x, objective30 x, objective31 x, objective32 x, objective33 x, objective34 x, objective35 x, objective36 x, objective37 x, objective38 x, objective39 x, objective40 x, objective41 x, objective42 x, objective43 x, objective44 x, objective45 x, objective46 x, objective47 x, objective48 x, objective49 x, objective50 x, objective51 x, objective52 x, objective53 x, objective54 x, objective55 x, objective56 x, objective57 x, objective58 x, objective59 x, objective60 x, objective61 x] i

end Coordinates
end
end OAI.SevenEighths.Cycle153Geometry
