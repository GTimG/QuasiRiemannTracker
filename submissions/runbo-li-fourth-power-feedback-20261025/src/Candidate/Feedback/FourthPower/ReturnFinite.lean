/- REVIEW STATUS: Regenerated: 108 return rows, 21 upward windows, 423 Bernstein certificates. Full Mathlib compilation NOT RUN. -/
/- Copyright (c) 2026 Sil and predecessors. Apache-2.0.
Adapted for an acyclic feedback return at 0.87469284.
The generating Python code is untrusted: all equalities and bounds below
are explicit proof obligations. Full Mathlib build is not claimed locally. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Generated exact certificate for the independently audited 86-box return.
The generator is untrusted: identities and inequalities below are Lean proofs. -/
import Candidate.Feedback.FourthPower.ReturnCountData
import Candidate.Feedback.FourthPower.ReturnBernstein

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Candidate.Feedback.FourthPower.ReturnFinite
noncomputable section
open ReturnCertificate ReturnCountData ReturnBernstein
def branchC : ImprovedBranch := ⟨.count, false, 0⟩
def branchPcap : ImprovedBranch := ⟨.physical, true, 0⟩
def branchX8 : ImprovedBranch := ⟨.x, false, 8⟩
def branchP : ImprovedBranch := ⟨.physical, false, 0⟩
def branchY : ImprovedBranch := ⟨.y, false, 0⟩
def branchY3 : ImprovedBranch := ⟨.y, false, 3⟩

inductive Edge where
  | oldsmall | oldpeak | oldswitch | newswitch | newtop | newkink
  deriving DecidableEq
def edgeD : Edge → ℝ
  | .oldsmall => d0
  | .oldpeak => y
  | .oldswitch => ds
  | .newswitch => ds
  | .newtop => dplus
  | .newkink => dk
def edgeC (e : Edge) : ℝ :=
  match e with
  | .oldsmall | .oldpeak | .oldswitch => oldCapacity kappa (edgeD e)
  | _ => newCapacity (edgeD e)
def clearedEdge (e : Edge) (b : Branch) (δ p : ℝ) : ℝ :=
  clearedReturn b (edgeD e) (edgeC e) δ p
theorem edgeD_positive (e : Edge) : 0 < edgeD e := by
  cases e <;> norm_num [edgeD, d0, ds, dk, dplus, y, ell, kappa, theta, h,
    physical_intercept_exact, physicalSlope]

private def poly000 : Coeff :=
  ![![3, -1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly001 : Coeff :=
  ![![2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly002 : Coeff :=
  ![![1, (-429999/5000000), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly003 : Coeff :=
  ![![(5/2), (-5/6), 0, 0],
    ![-1, -1, 0, 0],
    ![0, 0, 0, 0]]

private def poly004 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-5429999/5000000), (429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly005 : Coeff :=
  ![![(2499/4000), (-833/4000), 0, 0],
    ![(-12499/10000), (4180499/5000000), (-429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly006 : Coeff :=
  ![![(25/74), (-187270111/222000000), (54090037/222000000), 0],
    ![(69/37), (-372729889/185000000), (85909963/185000000), 0],
    ![0, 0, 0, 0]]

private def poly007 : Coeff :=
  ![![(5/2), (-6289997/6000000), (143333/2000000), 0],
    ![-3, (6289997/5000000), (-429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly008 : Coeff :=
  ![![(-2000003/4000000), (2855003/3000000), (-3140003/12000000), 0],
    ![(12000003/10000000), (-10999999/5000000), (8579993/10000000), (-429999/5000000)],
    ![0, 0, 0, 0]]

private def poly009 : Coeff :=
  ![![(159789448507659461/254840352000000000), (-396154066117923461/382260528000000000), (632518683728187461/2293563168000000000), 0],
    ![(-796890328507659461/637100880000000000), (2070063631492340539/955651320000000000), (-1607527245830756539/1911302640000000000), (429999/5000000)],
    ![0, 0, 0, 0]]

private def poly010 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-182281213/300000000), (89999/6000000), 0],
    ![(-211781263/250000000), (292718687/250000000), (-769999/5000000), 0]]

private def poly011 : Coeff :=
  ![![(11289997/6000000), (-429999/1000000), (143333/2000000), 0],
    ![(-10429999/5000000), (429999/2500000), (429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly012 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly013 : Coeff :=
  ![![(14355311686773899/955651320000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly014 : Coeff :=
  ![![(134997/2000000), (-44999/1000000), (44999/6000000), 0],
    ![(-134997/5000000), (-44999/2500000), (44999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly015 : Coeff :=
  ![![3, (-193/93), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly016 : Coeff :=
  ![![2, (-100/93), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly017 : Coeff :=
  ![![1, (-33333/62000), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly018 : Coeff :=
  ![![(5/2), (-965/558), 0, 0],
    ![-1, -1, (100/93), 0],
    ![0, 0, 0, 0]]

private def poly019 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-95333/62000), (33333/62000), 0],
    ![0, 0, 0, 0]]

private def poly020 : Coeff :=
  ![![(2499/4000), (-160769/372000), 0, 0],
    ![(-12499/10000), (99799/77500), (-16673/62000), 0],
    ![0, 0, 0, 0]]

private def poly021 : Coeff :=
  ![![(25/74), (-7042111/8258400), (328879141/768031200), 0],
    ![(69/37), (-27789889/6882000), (665954953/213342000), (-270200/320013)],
    ![0, 0, 0, 0]]

private def poly022 : Coeff :=
  ![![(5/2), (-685997/223200), (2144423/2306400), 0],
    ![-3, (685997/186000), (-2144423/1922000), 0],
    ![0, 0, 0, 0]]

private def poly023 : Coeff :=
  ![![(-2000003/4000000), (601008079/558000000), (-52497002249/103788000000), 0],
    ![(12000003/10000000), (-1222999957/465000000), (1457984507/930000000), (-192990157/864900000)],
    ![0, 0, 0, 0]]

private def poly024 : Coeff :=
  ![![(135343639/200000000), (-36871697327/27900000000), (3063686653037/5189400000000), 0],
    ![(-635343639/500000000), (60643407841/23250000000), (-22363703997/15500000000), (7375743391/43245000000)],
    ![0, 0, 0, 0]]

private def poly025 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-2625628751/3100000000), (73751/223200), 0],
    ![(-211781263/250000000), (12574405847/7750000000), (-59675829/77500000), (34/465)]]

private def poly026 : Coeff :=
  ![![(471997/223200), (-33333/12400), (2144423/2306400), 0],
    ![(-157333/62000), (299999/93000), (-6433331/5766000), 0],
    ![0, 0, 0, 0]]

private def poly027 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly028 : Coeff :=
  ![![(3298047/125000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly029 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly030 : Coeff :=
  ![![3, (-28567/12567), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly031 : Coeff :=
  ![![2, (-16000/12567), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly032 : Coeff :=
  ![![1, (-4629970866922/7506043836525), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly033 : Coeff :=
  ![![(5/2), (-142835/75402), 0, 0],
    ![-1, -1, (16000/12567), 0],
    ![0, 0, 0, 0]]

private def poly034 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-12136014703447/7506043836525), (4629970866922/7506043836525), 0],
    ![0, 0, 0, 0]]

private def poly035 : Coeff :=
  ![![(2499/4000), (-23796311/50268000), 0, 0],
    ![(-12499/10000), (4104101739479761/3002417534610000), (-2241798218242/7506043836525), 0],
    ![0, 0, 0, 0]]

private def poly036 : Coeff :=
  ![![(25/74), (-96004471496111/111089448780570), (965091479562693406/2094091654238134785), 0],
    ![(69/37), (-407206473067489/92574540650475), (12939795594985284088/3490152757063557975), (-6399008000/5843391093)],
    ![0, 0, 0, 0]]

private def poly037 : Coeff :=
  ![![(5/2), (-10317489879097/3002417534610), (66132188877680387/56597071736165805), 0],
    ![-3, (10317489879097/2502014612175), (-132264377755360774/94328452893609675), 0],
    ![0, 0, 0, 0]]

private def poly038 : Coeff :=
  ![![(-159789830768187461/254840352000000000), (6256793127959611198387/4803868055376000000000), (-1282911716786045958781477/2046447791590176000000000), 0],
    ![(796890710768187461/637100880000000000), (-32389610539241687865613/12009670138440000000000), (38032371787943390673613/24019340276880000000000), (-154370052732511/789647445000000)],
    ![0, 0, 0, 0]]

private def poly039 : Coeff :=
  ![![(135343639/200000000), (-41366262252107992193/30024175346100000000), (1483819792410393522977431/2263882869446632200000000), 0],
    ![(-635343639/500000000), (8458045200229/3141750000000), (-1087518482615777539/704792848500000000), (20789311151122975307/117910566117012093750)],
    ![0, 0, 0, 0]]

private def poly040 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-1126245667759169933/1268627127300000000), (34697169884383/90072526038300), 0],
    ![(-211781263/250000000), (127730897837577798757/75060438365250000000), (-8251666632896267/9382554795656250), (1088/12567)]]

private def poly041 : Coeff :=
  ![![(3224247845636/1501208767305), (-4629970866922/1501208767305), (66132188877680387/56597071736165805), 0],
    ![(-19642058539972/7506043836525), (28372968133844/7506043836525), (-135991391370543226/94328452893609675), 0],
    ![0, 0, 0, 0]]

private def poly042 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly043 : Coeff :=
  ![![(14355311686773899/955651320000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly044 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly045 : Coeff :=
  ![![3, (-363653997694883/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly046 : Coeff :=
  ![![2, (-200000000000000/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly047 : Coeff :=
  ![![1, (-96739031091242/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly048 : Coeff :=
  ![![(5/2), (-1818269988474415/981923986169298), 0, 0],
    ![-1, -1, (200000000000000/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly049 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-260393028786125/163653997694883), (96739031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly050 : Coeff :=
  ![![(2499/4000), (-302923780079837539/654615990779532000), 0, 0],
    ![(-12499/10000), (2194958947621737383/1636539976948830000), (-46759031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly051 : Coeff :=
  ![![(25/74), (-31768527202658195/36331187488264026), (1374441027856423644630173320660/2972872036728361500809646589479), 0],
    ![(69/37), (-25975542301295257/6055197914710671), (3509524417053934509919733415028/990957345576120500269882196493), (-1018231193545672400000000000000/990957345576120500269882196493)],
    ![0, 0, 0, 0]]

private def poly052 : Coeff :=
  ![![(5/2), (-3269355454843045/981923986169298), (87948838473649332840123786715/80347892884550310832693151067), 0],
    ![-3, (653871090968609/163653997694883), (-35179535389459733136049514686/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly053 : Coeff :=
  ![![(-2000003/4000000), (1094493608457544084649/981923986169298000000), (-177181698507512589219732665460383689/321391571538201243330772604268000000), 0],
    ![(12000003/10000000), (-2200193910989715305117/818269988474415000000), (2684093955252560305117/1636539976948830000000), (-6087208300789139238389514686/26782630961516770277564383689)],
    ![0, 0, 0, 0]]

private def poly054 : Coeff :=
  ![![(135343639/200000000), (-67577481490212326899237/49096199308464900000000), (1157452861697791290492419391139314973/1785508730767784685170958912600000000), 0],
    ![(-635343639/500000000), (109259777427040724366921/40913499423720750000000), (-40950577646727658122307/27275666282480500000000), (1457833830603707627605971562/8927543653838923425854794563)],
    ![0, 0, 0, 0]]

private def poly055 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-42853506817192877377229/49096199308464900000000), (18002639811997489/49096199308464900), 0],
    ![(-211781263/250000000), (68570788332617578622771/40913499423720750000000), (-34610623133623511/40913499423720750), (13600000000000/163653997694883)]]

private def poly056 : Coeff :=
  ![![(1043812721658730/490961993084649), (-483695155456210/163653997694883), (87948838473649332840123786715/80347892884550310832693151067), 0],
    ![(-424047026481008/163653997694883), (593478062182484/163653997694883), (-36246876586013666863950485314/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly057 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly058 : Coeff :=
  ![![(4490006585952085117/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly059 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly060 : Coeff :=
  ![![3, (-363653997694883/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly061 : Coeff :=
  ![![2, (-200000000000000/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly062 : Coeff :=
  ![![1, (-96664031091242/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly063 : Coeff :=
  ![![(5/2), (-1818269988474415/981923986169298), 0, 0],
    ![-1, -1, (200000000000000/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly064 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-260318028786125/163653997694883), (96664031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly065 : Coeff :=
  ![![(2499/4000), (-302923780079837539/654615990779532000), 0, 0],
    ![(-12499/10000), (2194208947621737383/1636539976948830000), (-46684031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly066 : Coeff :=
  ![![(25/74), (-31810152202658195/36331187488264026), (1376963877465431895442673320660/2972872036728361500809646589479), 0],
    ![(69/37), (-25967217301295257/6055197914710671), (3508515277210331209594733415028/990957345576120500269882196493), (-1018231193545672400000000000000/990957345576120500269882196493)],
    ![0, 0, 0, 0]]

private def poly067 : Coeff :=
  ![![(5/2), (-3268230454843045/981923986169298), (87880653349081542277623786715/80347892884550310832693151067), 0],
    ![-3, (653646090968609/163653997694883), (-35152261339632616911049514686/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly068 : Coeff :=
  ![![(-2000003/4000000), (1095618608457544084649/981923986169298000000), (-177454439005783751469732665460383689/321391571538201243330772604268000000), 0],
    ![(12000003/10000000), (-2200193910989715305117/818269988474415000000), (2681843955252560305117/1636539976948830000000), (-6059934250962023013389514686/26782630961516770277564383689)],
    ![0, 0, 0, 0]]

private def poly069 : Coeff :=
  ![![(135343639/200000000), (-67633731490212326899237/49096199308464900000000), (3476904260064559908977258173417944919/5356526192303354055512876737800000000), 0],
    ![(-635343639/500000000), (109259777427040724366921/40913499423720750000000), (-40913077646727658122307/27275666282480500000000), (1448742480661335552605971562/8927543653838923425854794563)],
    ![0, 0, 0, 0]]

private def poly070 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-42834756817192877377229/49096199308464900000000), (17983889811997489/49096199308464900), 0],
    ![(-211781263/250000000), (68552038332617578622771/40913499423720750000000), (-34591873133623511/40913499423720750), (13600000000000/163653997694883)]]

private def poly071 : Coeff :=
  ![![(1043250221658730/490961993084649), (-483320155456210/163653997694883), (87880653349081542277623786715/80347892884550310832693151067), 0],
    ![(-423972026481008/163653997694883), (593328062182484/163653997694883), (-36244150635840783088950485314/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly072 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly073 : Coeff :=
  ![![(4115006585952085117/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly074 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly075 : Coeff :=
  ![![3, (-357406588190789/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly076 : Coeff :=
  ![![2, (-200000000000000/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly077 : Coeff :=
  ![![1, (-96026151753982/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly078 : Coeff :=
  ![![(5/2), (-1787032940953945/944439529144734), 0, 0],
    ![-1, -1, (200000000000000/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly079 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-253432739944771/157406588190789), (96026151753982/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly080 : Coeff :=
  ![![(2499/4000), (-42531383994703891/89946621823308000), 0, 0],
    ![(-12499/10000), (2140968335558928289/1574065881907890000), (-46046151753982/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly081 : Coeff :=
  ![![(25/74), (-30696034001375405/34944262578355158), (432082113964751697913885615640/916742858216991497673784373277), 0],
    ![(69/37), (-25490331077093287/5824043763059193), (3379683497011762944526741651820/916742858216991497673784373277), (-142962635276315600000000000000/130963265459570213953397767611)],
    ![0, 0, 0, 0]]

private def poly082 : Coeff :=
  ![![(5/2), (-3227425217263675/944439529144734), (85800948188704138751016179495/74330502017593905216793327563), 0],
    ![-3, (645485043452735/157406588190789), (-34320379275481655500406471798/24776834005864635072264442521), 0],
    ![0, 0, 0, 0]]

private def poly083 : Coeff :=
  ![![(-2000003/4000000), (1061454913245557572367/944439529144734000000), (-7988295814922555593582291636592501/14158190860494077184151110012000000), 0],
    ![(12000003/10000000), (-2131472412692090809211/787032940953945000000), (2625223124357605809211/1574065881907890000000), (-90918175747409074359150346/393283079458168810670864167)],
    ![0, 0, 0, 0]]

private def poly084 : Coeff :=
  ![![(135343639/200000000), (-65704741480526559541171/47221976457236700000000), (9892630114815541718026070394866157973/14866100403518781043358665512600000000), 0],
    ![(-635343639/500000000), (15128186323122140021849/5621663863956750000000), (-39993931048376910050981/26234431365131500000000), (4043578962986947561583671798/24776834005864635072264442521)],
    ![0, 0, 0, 0]]

private def poly085 : Coeff :=
  ![![0, 0, 0, 0],
    ![(135343789/300000000), (-41670820592331440386507/47221976457236700000000), (5976875313084029/15740658819078900), 0],
    ![(-211781263/250000000), (66698153983080407613493/39351647047697250000000), (-34326197337738913/39351647047697250), (13600000000000/157406588190789)]]

private def poly086 : Coeff :=
  ![![(1007229079108810/472219764572367), (-480130758769910/157406588190789), (85800948188704138751016179495/74330502017593905216793327563), 0],
    ![(-410839328135560/157406588190789), (197350767835988/52468862730263), (-35571399064268944499593528202/24776834005864635072264442521), 0],
    ![0, 0, 0, 0]]

private def poly087 : Coeff :=
  ![![(8218687/500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly088 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly089 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly090 : Coeff :=
  ![![(547594679/400000000), (-29078352383254877/33722355600000000), 0, 0],
    ![(-1791344679/1000000000), (-15174410193417031/84305889000000000), (4437828706316576233051/5922902433400267500000), 0],
    ![(1/2), (28899850739563/43909317187500), (-47855076901123/175637268750000), (-117564067395508/789720324453369)]]

private def poly091 : Coeff :=
  ![![(1234541619/2000000000), (-7284064819344233/18734642000000000), 0, 0],
    ![(-13817648857/15000000000), (50876101459443709/421529445000000000), (4892402509334421299153/17768707300200802500000), 0],
    ![(1/2), (-120059594609701/526911806250000), (69990419296631/526911806250000), (-245914377186524/2369160973360107)]]

private def poly092 : Coeff :=
  ![![(6562779479904877/73740785200000000), (-348496473119068021973551/6216782451844042800000000), 0, 0],
    ![(-171259699689714631/553055889000000000), (797756927663390434806049/5180652043203369000000000), (2114078787370507483051/38854890324025267500000), 0],
    ![(1/2), (-25233318592086803829449/32379075270021056250000), (15828908854291418045551/32379075270021056250000), (-233943089131836/1726884014401123)]]

private def poly093 : Coeff :=
  ![![(6562779479904877/73740785200000000), (-348496473119068021973551/6216782451844042800000000), 0, 0],
    ![(-171259699689714631/553055889000000000), (797756927663390434806049/5180652043203369000000000), (2114078787370507483051/38854890324025267500000), 0],
    ![(1/2), (-25233318592086803829449/32379075270021056250000), (15828908854291418045551/32379075270021056250000), (-233943089131836/1726884014401123)]]

private def poly094 : Coeff :=
  ![![(12643259467/200000000000), (-671381896416033721/16861177800000000000), 0, 0],
    ![(-279816518809/1000000000000), (150689529845265323728315039217/937486960757349327000000000000), (7574760641412911334136486891/187497392151469865400000000000), 0],
    ![(1/2), (-10524234876794156556865853857/13020652232740962875000000000), (78778256929708496764406486891/156247826792891554500000000000), (-844945903200019975057/6249913071715662180000)]]

private def poly095 : Coeff :=
  ![![(12643259467/200000000000), (-12643259467/600000000000), 0, 0],
    ![(-279816518809/1000000000000), (144825300570601444767955171/2668815586320000000000000000), (223739415314547583803564829/2668815586320000000000000000), 0],
    ![(1/2), (-1320979942433024764486435171/2224012988600000000000000000), (452217307245468396242035171/2224012988600000000000000000), 0]]

private def poly096 : Coeff :=
  ![![(12643259467/200000000000), (-2440149077131/55800000000000), 0, 0],
    ![(-279816518809/1000000000000), (3810109594050063678775511/19855987962220800000000000), (2224338877119497759410189/99279939811104000000000000), 0],
    ![(1/2), (-23819252638827970951068337/27577761058640000000000000), (47794045156458262920313331/82733283175920000000000000), (-844945903200019975057/5170830198495000000000)]]

private def poly097 : Coeff :=
  ![![(12643259467/200000000000), (-5087042157659/106200000000000), 0, 0],
    ![(-279816518809/1000000000000), (1795324526516079939001/8340048707250000000000), (273546679495470155208119/20961878420802150000000000), 0],
    ![(1/2), (-15195886939471518951491/16680097414500000000000), (5373057718714799194829/8340048707250000000000), (-844945903200019975057/4367058004333781250000)]]

private def poly098 : Coeff :=
  ![![(12643259467/200000000000), (-4597771849068225667207361/98192398616929800000000000), 0, 0],
    ![(-279816518809/1000000000000), (563992720389722739122251119500176811/2729764623823006888180003500000000000), (9874563729673887659240352082844053/545952924764601377636000700000000000), 0],
    ![(1/2), (-271660442212743199556487207967104023/303307180424778543131111500000000000), (141929586689790152339843740536844639/227480385318583907348333625000000000), (-337978361280007990022800/1819843082548671258786669)]]

private def poly099 : Coeff :=
  ![![(12643259467/200000000000), (-4597771849068225667207361/98192398616929800000000000), 0, 0],
    ![(-279816518809/1000000000000), (563370050268149089353120650750176811/2729764623823006888180003500000000000), (9999097753988617613066445832844053/545952924764601377636000700000000000), 0],
    ![(1/2), (-271577419529866712920603145467104023/303307180424778543131111500000000000), (141867319677632787362930693661844639/227480385318583907348333625000000000), (-337978361280007990022800/1819843082548671258786669)]]

private def poly100 : Coeff :=
  ![![(12643259467/200000000000), (-4518784229711363426449463/94443952914473400000000000), 0, 0],
    ![(-279816518809/1000000000000), (556879920609720623474482210126419563/2625557224706445831615040500000000000), (8418905299556079667735026957080749/525111444941289166323008100000000000), 0],
    ![(1/2), (-264588802502196602266438411426863509/291728580522938425735004500000000000), (5000644798992875338413054635358379/7814158406864422117901906250000000), (-337978361280007990022800/1750371483137630554410027)]]

private def poly101 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-92768804020417856765267/2329804134835858800000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (936218605979843149751159/5824510337089647000000000), (8823986735278177874413/218419137640861762500000), 0],
    ![(1/2), (-49039486536007110012329/60671982678017156250000), (1456670083717535754951/2889142032286531250000), (-3937171367874604/29122551685448235)]]

private def poly102 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-1746993873285209/82905387600000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (669482419278427219/12337111250000000000), (65159528429770283953/777238008750000000000), 0],
    ![(1/2), (-384708350997259716047/647698340625000000000), (131699039963959916047/647698340625000000000), 0]]

private def poly103 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-337169817544045337/7710201046800000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (3698722017789813947/19275502617000000000), (647794857286003723/28913253925500000000), 0],
    ![(1/2), (-990981374678688587/1147351346250000000), (1546559631122700863/2677153141250000000), (-984292841968651/6023594567812500)]]

private def poly104 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-7129481996876937929/148838857995600000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (62299744989334342619/289408890547000000000), (1274644622853639913/97675500559612500000), 0],
    ![(1/2), (-24717842076051004129/27132083488781250000), (17479780946586875507/27132083488781250000), (-7874342735749208/40698125233171875)]]

private def poly105 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-90757329424090588211488412221/1938256873026254521664400000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (7008058213654189867430290484719/33919495277959454129127000000000), (23006200380392722014928131533/1271981072923479529842262500000), 0],
    ![(1/2), (-316462166396595130157700247789/353328075812077647178406250000), (73482817362004397332507788237/117776025270692549059468750000), (-6299474188599366400000/33919495277959454129127)]]

private def poly106 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-90757329424090588211488412221/1938256873026254521664400000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (7000321043156794567430290484719/33919495277959454129127000000000), (23296344274045045764928131533/1271981072923479529842262500000), 0],
    ![(1/2), (-316365451765377688907700247789/353328075812077647178406250000), (73450579151598583582507788237/117776025270692549059468750000), (-6299474188599366400000/33919495277959454129127)]]

private def poly107 : Coeff :=
  ![![(1746993873285209/27635129200000000), (-624387119841078113647103739901/13049854204750944794816400000000), 0, 0],
    ![(-19331923757549209/69087823000000000), (6919676052941440514492883457177/32624635511877361987041000000000), (19614754412891471170443413339/1223423831695401074514037500000), 0],
    ![(1/2), (-308224285500698744181997617787/339839953248722520698343750000), (72493137923787504347538499771/113279984416240840232781250000), (-6299474188599366400000/32624635511877361987041)]]

private theorem eq000 (δ p : ℝ) :
    admissionGuard branchPcap δ p (0 : Fin 15) = eval poly000 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly000, Fin.sum_univ_succ]
  <;> ring

private theorem eq001 (δ p : ℝ) :
    admissionGuard branchPcap δ p (1 : Fin 15) = eval poly001 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly001, Fin.sum_univ_succ]
  <;> ring

private theorem eq002 (δ p : ℝ) :
    admissionGuard branchPcap δ p (2 : Fin 15) = eval poly002 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly002, Fin.sum_univ_succ]
  <;> ring

private theorem eq003 (δ p : ℝ) :
    admissionGuard branchPcap δ p (3 : Fin 15) = eval poly003 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly003, Fin.sum_univ_succ]
  <;> ring

private theorem eq004 (δ p : ℝ) :
    admissionGuard branchPcap δ p (4 : Fin 15) = eval poly004 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly004, Fin.sum_univ_succ]
  <;> ring

private theorem eq005 (δ p : ℝ) :
    admissionGuard branchPcap δ p (5 : Fin 15) = eval poly005 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly005, Fin.sum_univ_succ]
  <;> ring

private theorem eq006 (δ p : ℝ) :
    admissionGuard branchPcap δ p (6 : Fin 15) = eval poly006 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly006, Fin.sum_univ_succ]
  <;> ring

private theorem eq007 (δ p : ℝ) :
    admissionGuard branchPcap δ p (7 : Fin 15) = eval poly007 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly007, Fin.sum_univ_succ]
  <;> ring

private theorem eq008 (δ p : ℝ) :
    admissionGuard branchPcap δ p (8 : Fin 15) = eval poly008 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly008, Fin.sum_univ_succ]
  <;> ring

private theorem eq009 (δ p : ℝ) :
    admissionGuard branchPcap δ p (9 : Fin 15) = eval poly009 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly009, Fin.sum_univ_succ]
  <;> ring

private theorem eq010 (δ p : ℝ) :
    admissionGuard branchPcap δ p (10 : Fin 15) = eval poly010 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly010, Fin.sum_univ_succ]
  <;> ring

private theorem eq011 (δ p : ℝ) :
    admissionGuard branchPcap δ p (11 : Fin 15) = eval poly011 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly011, Fin.sum_univ_succ]
  <;> ring

private theorem eq012 (δ p : ℝ) :
    admissionGuard branchPcap δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem eq013 (δ p : ℝ) :
    admissionGuard branchPcap δ p (13 : Fin 15) = eval poly013 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly013, Fin.sum_univ_succ]
  <;> ring

private theorem eq014 (δ p : ℝ) :
    admissionGuard branchPcap δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

private theorem eq015 (δ p : ℝ) :
    admissionGuard branchC δ p (0 : Fin 15) = eval poly015 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly015, Fin.sum_univ_succ]
  <;> ring

private theorem eq016 (δ p : ℝ) :
    admissionGuard branchC δ p (1 : Fin 15) = eval poly016 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly016, Fin.sum_univ_succ]
  <;> ring

private theorem eq017 (δ p : ℝ) :
    admissionGuard branchC δ p (2 : Fin 15) = eval poly017 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly017, Fin.sum_univ_succ]
  <;> ring

private theorem eq018 (δ p : ℝ) :
    admissionGuard branchC δ p (3 : Fin 15) = eval poly018 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly018, Fin.sum_univ_succ]
  <;> ring

private theorem eq019 (δ p : ℝ) :
    admissionGuard branchC δ p (4 : Fin 15) = eval poly019 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly019, Fin.sum_univ_succ]
  <;> ring

private theorem eq020 (δ p : ℝ) :
    admissionGuard branchC δ p (5 : Fin 15) = eval poly020 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly020, Fin.sum_univ_succ]
  <;> ring

private theorem eq021 (δ p : ℝ) :
    admissionGuard branchC δ p (6 : Fin 15) = eval poly021 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly021, Fin.sum_univ_succ]
  <;> ring

private theorem eq022 (δ p : ℝ) :
    admissionGuard branchC δ p (7 : Fin 15) = eval poly022 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly022, Fin.sum_univ_succ]
  <;> ring

private theorem eq023 (δ p : ℝ) :
    admissionGuard branchC δ p (8 : Fin 15) = eval poly023 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly023, Fin.sum_univ_succ]
  <;> ring

private theorem eq024 (δ p : ℝ) :
    admissionGuard branchC δ p (9 : Fin 15) = eval poly024 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly024, Fin.sum_univ_succ]
  <;> ring

private theorem eq025 (δ p : ℝ) :
    admissionGuard branchC δ p (10 : Fin 15) = eval poly025 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly025, Fin.sum_univ_succ]
  <;> ring

private theorem eq026 (δ p : ℝ) :
    admissionGuard branchC δ p (11 : Fin 15) = eval poly026 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly026, Fin.sum_univ_succ]
  <;> ring

private theorem eq027 (δ p : ℝ) :
    admissionGuard branchC δ p (12 : Fin 15) = eval poly027 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly027, Fin.sum_univ_succ]
  <;> ring

private theorem eq028 (δ p : ℝ) :
    admissionGuard branchC δ p (13 : Fin 15) = eval poly028 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly028, Fin.sum_univ_succ]
  <;> ring

private theorem eq029 (δ p : ℝ) :
    admissionGuard branchC δ p (14 : Fin 15) = eval poly029 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly029, Fin.sum_univ_succ]
  <;> ring

private theorem eq030 (δ p : ℝ) :
    admissionGuard branchP δ p (0 : Fin 15) = eval poly030 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly030, Fin.sum_univ_succ]
  <;> ring

private theorem eq031 (δ p : ℝ) :
    admissionGuard branchP δ p (1 : Fin 15) = eval poly031 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly031, Fin.sum_univ_succ]
  <;> ring

private theorem eq032 (δ p : ℝ) :
    admissionGuard branchP δ p (2 : Fin 15) = eval poly032 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly032, Fin.sum_univ_succ]
  <;> ring

private theorem eq033 (δ p : ℝ) :
    admissionGuard branchP δ p (3 : Fin 15) = eval poly033 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly033, Fin.sum_univ_succ]
  <;> ring

private theorem eq034 (δ p : ℝ) :
    admissionGuard branchP δ p (4 : Fin 15) = eval poly034 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly034, Fin.sum_univ_succ]
  <;> ring

private theorem eq035 (δ p : ℝ) :
    admissionGuard branchP δ p (5 : Fin 15) = eval poly035 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly035, Fin.sum_univ_succ]
  <;> ring

private theorem eq036 (δ p : ℝ) :
    admissionGuard branchP δ p (6 : Fin 15) = eval poly036 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly036, Fin.sum_univ_succ]
  <;> ring

private theorem eq037 (δ p : ℝ) :
    admissionGuard branchP δ p (7 : Fin 15) = eval poly037 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly037, Fin.sum_univ_succ]
  <;> ring

private theorem eq038 (δ p : ℝ) :
    admissionGuard branchP δ p (8 : Fin 15) = eval poly038 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly038, Fin.sum_univ_succ]
  <;> ring

private theorem eq039 (δ p : ℝ) :
    admissionGuard branchP δ p (9 : Fin 15) = eval poly039 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly039, Fin.sum_univ_succ]
  <;> ring

private theorem eq040 (δ p : ℝ) :
    admissionGuard branchP δ p (10 : Fin 15) = eval poly040 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly040, Fin.sum_univ_succ]
  <;> ring

private theorem eq041 (δ p : ℝ) :
    admissionGuard branchP δ p (11 : Fin 15) = eval poly041 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly041, Fin.sum_univ_succ]
  <;> ring

private theorem eq042 (δ p : ℝ) :
    admissionGuard branchP δ p (12 : Fin 15) = eval poly042 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly042, Fin.sum_univ_succ]
  <;> ring

private theorem eq043 (δ p : ℝ) :
    admissionGuard branchP δ p (13 : Fin 15) = eval poly043 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly043, Fin.sum_univ_succ]
  <;> ring

private theorem eq044 (δ p : ℝ) :
    admissionGuard branchP δ p (14 : Fin 15) = eval poly044 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly044, Fin.sum_univ_succ]
  <;> ring

private theorem eq045 (δ p : ℝ) :
    admissionGuard branchY δ p (0 : Fin 15) = eval poly045 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly045, Fin.sum_univ_succ]
  <;> ring

private theorem eq046 (δ p : ℝ) :
    admissionGuard branchY δ p (1 : Fin 15) = eval poly046 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly046, Fin.sum_univ_succ]
  <;> ring

private theorem eq047 (δ p : ℝ) :
    admissionGuard branchY δ p (2 : Fin 15) = eval poly047 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly047, Fin.sum_univ_succ]
  <;> ring

private theorem eq048 (δ p : ℝ) :
    admissionGuard branchY δ p (3 : Fin 15) = eval poly048 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly048, Fin.sum_univ_succ]
  <;> ring

private theorem eq049 (δ p : ℝ) :
    admissionGuard branchY δ p (4 : Fin 15) = eval poly049 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly049, Fin.sum_univ_succ]
  <;> ring

private theorem eq050 (δ p : ℝ) :
    admissionGuard branchY δ p (5 : Fin 15) = eval poly050 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly050, Fin.sum_univ_succ]
  <;> ring

private theorem eq051 (δ p : ℝ) :
    admissionGuard branchY δ p (6 : Fin 15) = eval poly051 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly051, Fin.sum_univ_succ]
  <;> ring

private theorem eq052 (δ p : ℝ) :
    admissionGuard branchY δ p (7 : Fin 15) = eval poly052 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly052, Fin.sum_univ_succ]
  <;> ring

private theorem eq053 (δ p : ℝ) :
    admissionGuard branchY δ p (8 : Fin 15) = eval poly053 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly053, Fin.sum_univ_succ]
  <;> ring

private theorem eq054 (δ p : ℝ) :
    admissionGuard branchY δ p (9 : Fin 15) = eval poly054 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly054, Fin.sum_univ_succ]
  <;> ring

private theorem eq055 (δ p : ℝ) :
    admissionGuard branchY δ p (10 : Fin 15) = eval poly055 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly055, Fin.sum_univ_succ]
  <;> ring

private theorem eq056 (δ p : ℝ) :
    admissionGuard branchY δ p (11 : Fin 15) = eval poly056 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly056, Fin.sum_univ_succ]
  <;> ring

private theorem eq057 (δ p : ℝ) :
    admissionGuard branchY δ p (12 : Fin 15) = eval poly057 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly057, Fin.sum_univ_succ]
  <;> ring

private theorem eq058 (δ p : ℝ) :
    admissionGuard branchY δ p (13 : Fin 15) = eval poly058 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly058, Fin.sum_univ_succ]
  <;> ring

private theorem eq059 (δ p : ℝ) :
    admissionGuard branchY δ p (14 : Fin 15) = eval poly059 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly059, Fin.sum_univ_succ]
  <;> ring

private theorem eq060 (δ p : ℝ) :
    admissionGuard branchY3 δ p (0 : Fin 15) = eval poly060 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly060, Fin.sum_univ_succ]
  <;> ring

private theorem eq061 (δ p : ℝ) :
    admissionGuard branchY3 δ p (1 : Fin 15) = eval poly061 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly061, Fin.sum_univ_succ]
  <;> ring

private theorem eq062 (δ p : ℝ) :
    admissionGuard branchY3 δ p (2 : Fin 15) = eval poly062 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly062, Fin.sum_univ_succ]
  <;> ring

private theorem eq063 (δ p : ℝ) :
    admissionGuard branchY3 δ p (3 : Fin 15) = eval poly063 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly063, Fin.sum_univ_succ]
  <;> ring

private theorem eq064 (δ p : ℝ) :
    admissionGuard branchY3 δ p (4 : Fin 15) = eval poly064 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly064, Fin.sum_univ_succ]
  <;> ring

private theorem eq065 (δ p : ℝ) :
    admissionGuard branchY3 δ p (5 : Fin 15) = eval poly065 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly065, Fin.sum_univ_succ]
  <;> ring

private theorem eq066 (δ p : ℝ) :
    admissionGuard branchY3 δ p (6 : Fin 15) = eval poly066 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly066, Fin.sum_univ_succ]
  <;> ring

private theorem eq067 (δ p : ℝ) :
    admissionGuard branchY3 δ p (7 : Fin 15) = eval poly067 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly067, Fin.sum_univ_succ]
  <;> ring

private theorem eq068 (δ p : ℝ) :
    admissionGuard branchY3 δ p (8 : Fin 15) = eval poly068 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly068, Fin.sum_univ_succ]
  <;> ring

private theorem eq069 (δ p : ℝ) :
    admissionGuard branchY3 δ p (9 : Fin 15) = eval poly069 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly069, Fin.sum_univ_succ]
  <;> ring

private theorem eq070 (δ p : ℝ) :
    admissionGuard branchY3 δ p (10 : Fin 15) = eval poly070 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly070, Fin.sum_univ_succ]
  <;> ring

private theorem eq071 (δ p : ℝ) :
    admissionGuard branchY3 δ p (11 : Fin 15) = eval poly071 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly071, Fin.sum_univ_succ]
  <;> ring

private theorem eq072 (δ p : ℝ) :
    admissionGuard branchY3 δ p (12 : Fin 15) = eval poly072 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly072, Fin.sum_univ_succ]
  <;> ring

private theorem eq073 (δ p : ℝ) :
    admissionGuard branchY3 δ p (13 : Fin 15) = eval poly073 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly073, Fin.sum_univ_succ]
  <;> ring

private theorem eq074 (δ p : ℝ) :
    admissionGuard branchY3 δ p (14 : Fin 15) = eval poly074 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly074, Fin.sum_univ_succ]
  <;> ring

private theorem eq075 (δ p : ℝ) :
    admissionGuard branchX8 δ p (0 : Fin 15) = eval poly075 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly075, Fin.sum_univ_succ]
  <;> ring

private theorem eq076 (δ p : ℝ) :
    admissionGuard branchX8 δ p (1 : Fin 15) = eval poly076 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly076, Fin.sum_univ_succ]
  <;> ring

private theorem eq077 (δ p : ℝ) :
    admissionGuard branchX8 δ p (2 : Fin 15) = eval poly077 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly077, Fin.sum_univ_succ]
  <;> ring

private theorem eq078 (δ p : ℝ) :
    admissionGuard branchX8 δ p (3 : Fin 15) = eval poly078 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly078, Fin.sum_univ_succ]
  <;> ring

private theorem eq079 (δ p : ℝ) :
    admissionGuard branchX8 δ p (4 : Fin 15) = eval poly079 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly079, Fin.sum_univ_succ]
  <;> ring

private theorem eq080 (δ p : ℝ) :
    admissionGuard branchX8 δ p (5 : Fin 15) = eval poly080 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly080, Fin.sum_univ_succ]
  <;> ring

private theorem eq081 (δ p : ℝ) :
    admissionGuard branchX8 δ p (6 : Fin 15) = eval poly081 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly081, Fin.sum_univ_succ]
  <;> ring

private theorem eq082 (δ p : ℝ) :
    admissionGuard branchX8 δ p (7 : Fin 15) = eval poly082 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly082, Fin.sum_univ_succ]
  <;> ring

private theorem eq083 (δ p : ℝ) :
    admissionGuard branchX8 δ p (8 : Fin 15) = eval poly083 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly083, Fin.sum_univ_succ]
  <;> ring

private theorem eq084 (δ p : ℝ) :
    admissionGuard branchX8 δ p (9 : Fin 15) = eval poly084 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly084, Fin.sum_univ_succ]
  <;> ring

private theorem eq085 (δ p : ℝ) :
    admissionGuard branchX8 δ p (10 : Fin 15) = eval poly085 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly085, Fin.sum_univ_succ]
  <;> ring

private theorem eq086 (δ p : ℝ) :
    admissionGuard branchX8 δ p (11 : Fin 15) = eval poly086 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly086, Fin.sum_univ_succ]
  <;> ring

private theorem eq087 (δ p : ℝ) :
    admissionGuard branchX8 δ p (12 : Fin 15) = eval poly087 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly087, Fin.sum_univ_succ]
  <;> ring

private theorem eq088 (δ p : ℝ) :
    admissionGuard branchX8 δ p (13 : Fin 15) = eval poly088 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly088, Fin.sum_univ_succ]
  <;> ring

private theorem eq089 (δ p : ℝ) :
    admissionGuard branchX8 δ p (14 : Fin 15) = eval poly089 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly089, Fin.sum_univ_succ]
  <;> ring

private theorem eq090 (δ p : ℝ) :
    clearedEdge .oldsmall .old δ p = eval poly090 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly090, Fin.sum_univ_succ]
  <;> ring

private theorem eq091 (δ p : ℝ) :
    clearedEdge .oldpeak .old δ p = eval poly091 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly091, Fin.sum_univ_succ]
  <;> ring

private theorem eq092 (δ p : ℝ) :
    clearedEdge .oldswitch .old δ p = eval poly092 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly092, Fin.sum_univ_succ]
  <;> ring

private theorem eq093 (δ p : ℝ) :
    clearedEdge .newswitch .old δ p = eval poly093 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly093, Fin.sum_univ_succ]
  <;> ring

private theorem eq094 (δ p : ℝ) :
    clearedEdge .newtop .old δ p = eval poly094 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly094, Fin.sum_univ_succ]
  <;> ring

private theorem eq095 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchPcap) δ p = eval poly095 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchPcap,
    eval, poly095, Fin.sum_univ_succ]
  <;> ring

private theorem eq096 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchC) δ p = eval poly096 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchC,
    eval, poly096, Fin.sum_univ_succ]
  <;> ring

private theorem eq097 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchP) δ p = eval poly097 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchP,
    eval, poly097, Fin.sum_univ_succ]
  <;> ring

private theorem eq098 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchY) δ p = eval poly098 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchY,
    eval, poly098, Fin.sum_univ_succ]
  <;> ring

private theorem eq099 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchY3) δ p = eval poly099 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchY3,
    eval, poly099, Fin.sum_univ_succ]
  <;> ring

private theorem eq100 (δ p : ℝ) :
    clearedEdge .newtop (.improved branchX8) δ p = eval poly100 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchX8,
    eval, poly100, Fin.sum_univ_succ]
  <;> ring

private theorem eq101 (δ p : ℝ) :
    clearedEdge .newkink .old δ p = eval poly101 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly101, Fin.sum_univ_succ]
  <;> ring

private theorem eq102 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchPcap) δ p = eval poly102 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchPcap,
    eval, poly102, Fin.sum_univ_succ]
  <;> ring

private theorem eq103 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchC) δ p = eval poly103 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchC,
    eval, poly103, Fin.sum_univ_succ]
  <;> ring

private theorem eq104 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchP) δ p = eval poly104 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchP,
    eval, poly104, Fin.sum_univ_succ]
  <;> ring

private theorem eq105 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchY) δ p = eval poly105 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchY,
    eval, poly105, Fin.sum_univ_succ]
  <;> ring

private theorem eq106 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchY3) δ p = eval poly106 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchY3,
    eval, poly106, Fin.sum_univ_succ]
  <;> ring

private theorem eq107 (δ p : ℝ) :
    clearedEdge .newkink (.improved branchX8) δ p = eval poly107 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h, branchX8,
    eval, poly107, Fin.sum_univ_succ]
  <;> ring

private def bern000 : Coeff :=
  ![![(41/16), (61/24), (121/48), (5/2)],
    ![(41/16), (61/24), (121/48), (5/2)],
    ![(41/16), (61/24), (121/48), (5/2)]]

private theorem tensor000 (u v : ℝ) :
    eval poly000 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern000 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly000, bern000, Fin.sum_univ_succ]
  <;> ring

private theorem cert000 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly000 δ p := by
  apply positive_on_box_from_tensor (β := bern000) (m := (1/1000000000000000))
    tensor000 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern000]

private def bern001 : Coeff :=
  ![![2, 2, 2, 2],
    ![2, 2, 2, 2],
    ![2, 2, 2, 2]]

private theorem tensor001 (u v : ℝ) :
    eval poly001 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern001 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly001, bern001, Fin.sum_univ_succ]
  <;> ring

private theorem cert001 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly001 δ p := by
  apply positive_on_box_from_tensor (β := bern001) (m := (1/1000000000000000))
    tensor001 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern001]

private def bern002 : Coeff :=
  ![![(76990007/80000000), (38423337/40000000), (76703341/80000000), (9570001/10000000)],
    ![(76990007/80000000), (38423337/40000000), (76703341/80000000), (9570001/10000000)],
    ![(76990007/80000000), (38423337/40000000), (76703341/80000000), (9570001/10000000)]]

private theorem tensor002 (u v : ℝ) :
    eval poly002 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern002 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly002, bern002, Fin.sum_univ_succ]
  <;> ring

private theorem cert002 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly002 δ p := by
  apply positive_on_box_from_tensor (β := bern002) (m := (1/1000000000000000))
    tensor002 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern002]

private def bern003 : Coeff :=
  ![![(613/384), (905/576), (1781/1152), (73/48)],
    ![(9601/6144), (14165/9216), (27857/18432), (1141/768)],
    ![(4697/3072), (6925/4608), (13609/9216), (557/384)]]

private theorem tensor003 (u v : ℝ) :
    eval poly003 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern003 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly003, bern003, Fin.sum_univ_succ]
  <;> ring

private theorem cert003 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly003 δ p := by
  apply positive_on_box_from_tensor (β := bern003) (m := (1/1000000000000000))
    tensor003 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern003]

private def bern004 : Coeff :=
  ![![(2078730189/10240000000), (1997870191/10240000000), (29960003/160000000), (28710003/160000000)],
    ![(35338413213/163840000000), (33963793247/163840000000), (509320051/2560000000), (488070051/2560000000)],
    ![(18708571701/81920000000), (17980831719/81920000000), (269640027/1280000000), (258390027/1280000000)]]

private theorem tensor004 (u v : ℝ) :
    eval poly004 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern004 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern004, Fin.sum_univ_succ]
  <;> ring

private theorem cert004 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern004) (m := (1/1000000000000000))
    tensor004 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern004]

private def bern005 : Coeff :=
  ![![(2006301811/10240000000), (6068229427/30720000000), (11945827/60000000), (32098997/160000000)],
    ![(28642650787/163840000000), (86899740259/491520000000), (343162493/1920000000), (462382949/2560000000)],
    ![(12592236299/81920000000), (38353904843/245760000000), (152029261/960000000), (205590973/1280000000)]]

private theorem tensor005 (u v : ℝ) :
    eval poly005 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern005 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern005, Fin.sum_univ_succ]
  <;> ring

private theorem cert005 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern005) (m := (1/1000000000000000))
    tensor005 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern005]

private def bern006 : Coeff :=
  ![![(158192584397/378880000000), (267220717147/681984000000), (13024259399/35520000000), (1215009593/3552000000)],
    ![(2683432872209/6062080000000), (4541194523959/10911744000000), (221786483603/568320000000), (20736963821/56832000000)],
    ![(1417892197033/3031040000000), (2403428786783/5455872000000), (117592408411/284160000000), (11016887077/28416000000)]]

private theorem tensor006 (u v : ℝ) :
    eval poly006 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern006 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly006, bern006, Fin.sum_univ_succ]
  <;> ring

private theorem cert006 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly006 δ p := by
  apply positive_on_box_from_tensor (β := bern006) (m := (1/1000000000000000))
    tensor006 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern006]

private def bern007 : Coeff :=
  ![![(34722493157/30720000000), (20625331969/18432000000), (3190330319/2880000000), (105270011/96000000)],
    ![(527150577929/491520000000), (313130039893/294912000000), (48435014843/46080000000), (1598190167/1536000000)],
    ![(249370632673/245760000000), (148127384141/147456000000), (22912372291/23040000000), (756030079/768000000)]]

private theorem tensor007 (u v : ℝ) :
    eval poly007 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern007 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly007, bern007, Fin.sum_univ_succ]
  <;> ring

private theorem cert007 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly007 δ p := by
  apply positive_on_box_from_tensor (β := bern007) (m := (1/1000000000000000))
    tensor007 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern007]

private def bern008 : Coeff :=
  ![![(465833513/32768000000), (101171401/5760000000), (160788221/7680000000), (2334979/96000000)],
    ![(12301261529/524288000000), (19227826391/737280000000), (3531802277/122880000000), (48294673/1536000000)],
    ![(342983737/10485760000), (12752856727/368640000000), (2245496509/61440000000), (29614841/768000000)]]

private theorem tensor008 (u v : ℝ) :
    eval poly008 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern008 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern008, Fin.sum_univ_succ]
  <;> ring

private theorem cert008 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern008) (m := (1/1000000000000000))
    tensor008 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern008]

private def bern009 : Coeff :=
  ![![(646591717908572436313/11743043420160000000000), (1763485951496018095217/35229130260480000000000), (99207563611397708429/2201820641280000000000), (1470372635140956653/36697010688000000000)],
    ![(8333403755784051058501/187888694722560000000000), (22586805404949787098269/563666084167680000000000), (96936835257911600861/2709933096960000000000), (18471974651040877001/587152171008000000000)],
    ![(3160670012515471567997/93944347361280000000000), (8478917792981642336533/281833042083840000000000), (466518349461669143761/17614565130240000000000), (6708993569913223777/293576085504000000000)]]

private theorem tensor009 (u v : ℝ) :
    eval poly009 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern009 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern009, Fin.sum_univ_succ]
  <;> ring

private theorem cert009 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern009) (m := (1/1000000000000000))
    tensor009 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern009]

private def bern010 : Coeff :=
  ![![(39599081077/2048000000000), (21782498153/1228800000000), (4120812001/256000000000), (231141237/16000000000)],
    ![(284126671303/16384000000000), (155536948451/9830400000000), (29242196599/2048000000000), (1626989433/128000000000)],
    ![(1906754516217/131072000000000), (13803769623/1048576000000), (192573766701/16384000000000), (10563369597/1024000000000)]]

private theorem tensor010 (u v : ℝ) :
    eval poly010 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern010 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern010, Fin.sum_univ_succ]
  <;> ring

private theorem cert010 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern010) (m := (1/1000000000000000))
    tensor010 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern010]

private def bern011 : Coeff :=
  ![![(29472786947/30720000000), (29297060689/30720000000), (1820343193/1920000000), (452469971/480000000)],
    ![(448590380999/491520000000), (445838100733/491520000000), (27697101061/30720000000), (6883389527/7680000000)],
    ![(212808085423/245760000000), (211461615221/245760000000), (13134355517/15360000000), (3263629759/3840000000)]]

private theorem tensor011 (u v : ℝ) :
    eval poly011 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern011 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly011, bern011, Fin.sum_univ_succ]
  <;> ring

private theorem cert011 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly011 δ p := by
  apply positive_on_box_from_tensor (β := bern011) (m := (1/1000000000000000))
    tensor011 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern011]

private def bern012 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor012 (u v : ℝ) :
    eval poly012 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern012 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly012, bern012, Fin.sum_univ_succ]
  <;> ring

private theorem cert012 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly012 δ p := by
  apply positive_on_box_from_tensor (β := bern012) (m := (1/1000000000000000))
    tensor012 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern012]

private def bern013 : Coeff :=
  ![![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)]]

private theorem tensor013 (u v : ℝ) :
    eval poly013 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern013 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly013, bern013, Fin.sum_univ_succ]
  <;> ring

private theorem cert013 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly013 δ p := by
  apply positive_on_box_from_tensor (β := bern013) (m := (1/1000000000000000))
    tensor013 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern013]

private def bern014 : Coeff :=
  ![![(1130959867/30720000000), (3311791403/92160000000), (202000511/5760000000), (3284927/96000000)],
    ![(17713451359/491520000000), (51835653071/1474560000000), (3159514787/92160000000), (51343859/1536000000)],
    ![(8665772423/245760000000), (25341321847/737280000000), (1543510699/46080000000), (25064443/768000000)]]

private theorem tensor014 (u v : ℝ) :
    eval poly014 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern014 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly014, bern014, Fin.sum_univ_succ]
  <;> ring

private theorem cert014 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly014 δ p := by
  apply positive_on_box_from_tensor (β := bern014) (m := (1/1000000000000000))
    tensor014 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern014]

private def bern015 : Coeff :=
  ![![(2011/992), (8953/4464), (17713/8928), (365/186)],
    ![(2011/992), (8953/4464), (17713/8928), (365/186)],
    ![(2011/992), (8953/4464), (17713/8928), (365/186)]]

private theorem tensor015 (u v : ℝ) :
    eval poly015 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern015 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern015, Fin.sum_univ_succ]
  <;> ring

private theorem cert015 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern015) (m := (1/1000000000000000))
    tensor015 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern015]

private def bern016 : Coeff :=
  ![![(371/248), (1657/1116), (3289/2232), (136/93)],
    ![(371/248), (1657/1116), (3289/2232), (136/93)],
    ![(371/248), (1657/1116), (3289/2232), (136/93)]]

private theorem tensor016 (u v : ℝ) :
    eval poly016 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern016 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern016, Fin.sum_univ_succ]
  <;> ring

private theorem cert016 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern016) (m := (1/1000000000000000))
    tensor016 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern016]

private def bern017 : Coeff :=
  ![![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)],
    ![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)],
    ![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)]]

private theorem tensor017 (u v : ℝ) :
    eval poly017 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern017 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern017, Fin.sum_univ_succ]
  <;> ring

private theorem cert017 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern017) (m := (1/1000000000000000))
    tensor017 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern017]

private def bern018 : Coeff :=
  ![![(1781819/1523712), (15789817/13713408), (1943161/1714176), (39851/35712)],
    ![(7039247/6094848), (62367061/54853632), (7673653/6856704), (157343/142848)],
    ![(3475609/3047424), (30787427/27426816), (3787331/3428352), (77641/71424)]]

private theorem tensor018 (u v : ℝ) :
    eval poly018 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern018 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern018, Fin.sum_univ_succ]
  <;> ring

private theorem cert018 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern018) (m := (1/1000000000000000))
    tensor018 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern018]

private def bern019 : Coeff :=
  ![![(136231659/812646400), (662702301/4063232000), (2517759/15872000), (2448009/15872000)],
    ![(560063487/3250585600), (2724442793/16252928000), (10350787/63488000), (10064037/63488000)],
    ![(287600169/1625292800), (1399038191/8126464000), (5315269/31744000), (5168019/31744000)]]

private theorem tensor019 (u v : ℝ) :
    eval poly019 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern019 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern019, Fin.sum_univ_succ]
  <;> ring

private theorem cert019 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern019) (m := (1/1000000000000000))
    tensor019 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern019]

private def bern020 : Coeff :=
  ![![(2531229433/20316160000), (22790066699/182845440000), (712259873/5713920000), (29671631/238080000)],
    ![(9453183829/81264640000), (85207121567/731381760000), (2665869629/22855680000), (111172883/952320000)],
    ![(4390724963/40632320000), (39626988169/365690880000), (1241349883/11427840000), (51829621/476160000)]]

private theorem tensor020 (u v : ℝ) :
    eval poly020 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern020 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern020, Fin.sum_univ_succ]
  <;> ring

private theorem cert020 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern020) (m := (1/1000000000000000))
    tensor020 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern020]

private def bern021 : Coeff :=
  ![![(254541639249/932105420800), (32849126753657/125834231808000), (1471223271949/5898479616000), (23416142621/98307993600)],
    ![(1043112631917/3728421683200), (134661729649781/503336927232000), (6033319913017/23593918464000), (96063958793/393231974400)],
    ![(534029353419/1864210841600), (68963476142467/251668463616000), (3090873369119/11796959232000), (49231673551/196615987200)]]

private theorem tensor021 (u v : ℝ) :
    eval poly021 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern021 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern021, Fin.sum_univ_succ]
  <;> ring

private theorem cert021 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern021) (m := (1/1000000000000000))
    tensor021 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern021]

private def bern022 : Coeff :=
  ![![(47152478069/75576115200), (2083348147739/3400925184000), (31958484541/53139456000), (522876589/885657600)],
    ![(183238110977/302304460800), (8096049131087/13603700736000), (124193098153/212557824000), (2031938137/3542630400)],
    ![(88933154839/151152230400), (3929352835609/6801850368000), (60276129071/106278912000), (986184959/1771315200)]]

private theorem tensor022 (u v : ℝ) :
    eval poly022 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern022 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern022, Fin.sum_univ_succ]
  <;> ring

private theorem cert022 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern022) (m := (1/1000000000000000))
    tensor022 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern022]

private def bern023 : Coeff :=
  ![![(78108328910247/5038407680000000), (54540401271727/3400925184000000), (13214850099373/797091840000000), (227508708377/13284864000000)],
    ![(380599676056011/20153630720000000), (2096021870543/108829605888000), (62641049500489/3188367360000000), (1065085341461/53139456000000)],
    ![(224383018235517/10076815360000000), (152921931274421/6801850368000000), (36211349301743/1594183680000000), (610067924707/26569728000000)]]

private theorem tensor023 (u v : ℝ) :
    eval poly023 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern023 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern023, Fin.sum_univ_succ]
  <;> ring

private theorem cert023 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern023) (m := (1/1000000000000000))
    tensor023 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern023]

private def bern024 : Coeff :=
  ![![(30498461715287417/755761152000000000), (724885619061961/18894028800000000), (725434497676213/19927296000000000), (22897416831199/664243200000000)],
    ![(109683316879467221/3023044608000000000), (6945068794723/201536307200000), (2603401781575609/79709184000000000), (82064630610307/2656972800000000)],
    ![(48686393448892387/1511522304000000000), (1154629559897203/37788057600000000), (1152532786223183/39854592000000000), (36269796947909/1328486400000000)]]

private theorem tensor024 (u v : ℝ) :
    eval poly024 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern024 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern024, Fin.sum_univ_succ]
  <;> ring

private theorem cert024 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern024) (m := (1/1000000000000000))
    tensor024 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern024]

private def bern025 : Coeff :=
  ![![(75436499316573/8126464000000000), (70546783580121/8126464000000000), (8213962792343/1015808000000000), (476050647939/63488000000000)],
    ![(135117562659023/16252928000000000), (377581920514793/48758784000000000), (131285892132997/18284544000000000), (2522769557347/380928000000000)],
    ![(234291730569173/32505856000000000), (650998150602323/97517568000000000), (224847037002007/36569088000000000), (4286720208577/761856000000000)]]

private theorem tensor025 (u v : ℝ) :
    eval poly025 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern025 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern025, Fin.sum_univ_succ]
  <;> ring

private theorem cert025 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern025) (m := (1/1000000000000000))
    tensor025 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern025]

private def bern026 : Coeff :=
  ![![(592707706909/1133641728000), (582116603071/1133641728000), (5955155281/11808768000), (2193135229/4428288000)],
    ![(2303306838217/4534566912000), (2262149017123/4534566912000), (23142182573/47235072000), (8522688937/17713152000)],
    ![(1117891424399/2267283456000), (1097915810981/2267283456000), (3743957337/7872512000), (4136418479/8856576000)]]

private theorem tensor026 (u v : ℝ) :
    eval poly026 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern026 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern026, Fin.sum_univ_succ]
  <;> ring

private theorem cert026 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern026) (m := (1/1000000000000000))
    tensor026 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern026]

private def bern027 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor027 (u v : ℝ) :
    eval poly027 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern027 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern027, Fin.sum_univ_succ]
  <;> ring

private theorem cert027 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern027) (m := (1/1000000000000000))
    tensor027 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern027]

private def bern028 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor028 (u v : ℝ) :
    eval poly028 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern028 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern028, Fin.sum_univ_succ]
  <;> ring

private theorem cert028 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern028) (m := (1/1000000000000000))
    tensor028 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern028]

private def bern029 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor029 (u v : ℝ) :
    eval poly029 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern029 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern029, Fin.sum_univ_succ]
  <;> ring

private theorem cert029 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern029) (m := (1/1000000000000000))
    tensor029 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern029]

private def bern030 : Coeff :=
  ![![(383/192), (17713/8928), (35233/17856), (365/186)],
    ![(383/192), (17713/8928), (35233/17856), (365/186)],
    ![(383/192), (17713/8928), (35233/17856), (365/186)]]

private theorem tensor030 (u v : ℝ) :
    eval poly015 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern030 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern030, Fin.sum_univ_succ]
  <;> ring

private theorem cert030 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern030) (m := (1/1000000000000000))
    tensor030 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern030]

private def bern031 : Coeff :=
  ![![(71/48), (3289/2232), (6553/4464), (136/93)],
    ![(71/48), (3289/2232), (6553/4464), (136/93)],
    ![(71/48), (3289/2232), (6553/4464), (136/93)]]

private theorem tensor031 (u v : ℝ) :
    eval poly016 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern031 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern031, Fin.sum_univ_succ]
  <;> ring

private theorem cert031 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern031) (m := (1/1000000000000000))
    tensor031 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern031]

private def bern032 : Coeff :=
  ![![(94667/128000), (1461783/1984000), (582491/793600), (90667/124000)],
    ![(94667/128000), (1461783/1984000), (582491/793600), (90667/124000)],
    ![(94667/128000), (1461783/1984000), (582491/793600), (90667/124000)]]

private theorem tensor032 (u v : ℝ) :
    eval poly017 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern032 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern032, Fin.sum_univ_succ]
  <;> ring

private theorem cert032 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern032) (m := (1/1000000000000000))
    tensor032 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern032]

private def bern033 : Coeff :=
  ![![(1313725/1179648), (121198867/109707264), (7514099/6856704), (77641/71424)],
    ![(5220835/4718592), (481627981/438829056), (29858477/27426816), (308503/285696)],
    ![(2593385/2359296), (239230247/219414528), (14830279/13713408), (153221/142848)]]

private theorem tensor033 (u v : ℝ) :
    eval poly018 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern033 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern033, Fin.sum_univ_succ]
  <;> ring

private theorem cert033 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern033) (m := (1/1000000000000000))
    tensor033 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern033]

private def bern034 : Coeff :=
  ![![(178068627/1048576000), (5443468783/32505856000), (1310411/7936000), (5168019/31744000)],
    ![(721646541/4194304000), (22060373489/130023424000), (5310613/31744000), (20944077/126976000)],
    ![(365509287/2097152000), (11173435923/65011712000), (2689791/15872000), (10608039/63488000)]]

private theorem tensor034 (u v : ℝ) :
    eval poly019 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern034 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern034, Fin.sum_univ_succ]
  <;> ring

private theorem cert034 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern034) (m := (1/1000000000000000))
    tensor034 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern034]

private def bern035 : Coeff :=
  ![![(341260459/3145728000), (158878529609/1462763520000), (2485260787/22855680000), (51829621/476160000)],
    ![(1314224821/12582912000), (612067625687/5851054080000), (9577545901/91422720000), (199804843/1904640000)],
    ![(631703903/6291456000), (294310566469/2925527040000), (4607024327/45711360000), (3101471/30720000)]]

private theorem tensor035 (u v : ℝ) :
    eval poly020 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern035 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern035, Fin.sum_univ_succ]
  <;> ring

private theorem cert035 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern035) (m := (1/1000000000000000))
    tensor035 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern035]

private def bern036 : Coeff :=
  ![![(280862033771/1047527424000), (25534575680983/97420050432000), (6044773782179/23593918464000), (49231673551/196615987200)],
    ![(1136837272373/4190109696000), (103364365712329/389680201728000), (24471485252477/94375673856000), (199326082513/786463948800)],
    ![(575113204831/2095054848000), (52295214350363/194840100864000), (12381937688119/47187836928000), (100862735411/393231974400)]]

private theorem tensor036 (u v : ℝ) :
    eval poly021 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern036 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern036, Fin.sum_univ_succ]
  <;> ring

private theorem cert036 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern036) (m := (1/1000000000000000))
    tensor036 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern036]

private def bern037 : Coeff :=
  ![![(5402361689/9437184000), (497795083847/877658112000), (119447226611/212557824000), (986184959/1771315200)],
    ![(21283129607/37748736000), (1961112175961/3510632448000), (470573973293/850231296000), (3885171617/7085260800)],
    ![(10478406229/18874368000), (965522008267/1755316224000), (231679520071/425115648000), (1912801699/3542630400)]]

private theorem tensor037 (u v : ℝ) :
    eval poly022 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern037 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern037, Fin.sum_univ_succ]
  <;> ring

private theorem cert037 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern037) (m := (1/1000000000000000))
    tensor037 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern037]

private def bern038 : Coeff :=
  ![![(2047711951583/90596966400000), (299082016471429/13164871680000000), (72815424784163/3188367360000000), (610067924707/26569728000000)],
    ![(43804883926789/1811939328000000), (1277136516424027/52659486720000000), (310346378716829/12753469440000000), (2595322206781/106278912000000)],
    ![(23327764410959/905969664000000), (678972483481169/26329743360000000), (164715529148503/6376734720000000), (1375186357367/53139456000000)]]

private theorem tensor038 (u v : ℝ) :
    eval poly023 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern038 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern038, Fin.sum_univ_succ]
  <;> ring

private theorem cert038 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern038) (m := (1/1000000000000000))
    tensor038 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern038]

private def bern039 : Coeff :=
  ![![(134725234529371/4529848320000000), (19038690456104123/658243584000000000), (2240626694660453/79709184000000000), (36269796947909/1328486400000000)],
    ![(2521230926503193/90596966400000000), (71225912241147749/2632974336000000000), (8378419468077899/318836736000000000), (135554151077147/5313945600000000)],
    ![(1173978581209483/45298483200000000), (33148531328939503/1316487168000000000), (3897166078756993/159418368000000000), (63014557181329/2656972800000000)]]

private theorem tensor039 (u v : ℝ) :
    eval poly024 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern039 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern039, Fin.sum_univ_succ]
  <;> ring

private theorem cert039 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern039) (m := (1/1000000000000000))
    tensor039 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern039]

private def bern040 : Coeff :=
  ![![(403495655341/62914560000000), (7196647603932649/1170210816000000000), (13890632484313/2359296000000000), (4286720208577/761856000000000)],
    ![(3704612176949/629145600000000), (13185815720410789/2340421632000000000), (787071159269803/146276352000000000), (7814621511037/1523712000000000)],
    ![(2236057975411/419430400000000), (7936544683349243/1560281088000000000), (472282775410901/97517568000000000), (4673284988099/1015808000000000)]]

private theorem tensor040 (u v : ℝ) :
    eval poly025 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern040 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern040, Fin.sum_univ_succ]
  <;> ring

private theorem cert040 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern040) (m := (1/1000000000000000))
    tensor040 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern040]

private def bern041 : Coeff :=
  ![![(140408727857/292552704000), (139140592507/292552704000), (13357392773/28341043200), (4136418479/8856576000)],
    ![(553153805231/1170210816000), (548157863461/1170210816000), (10524548959/22672834560), (16295821937/35426304000)],
    ![(272336349517/585105408000), (269876678447/585105408000), (25907959249/56682086400), (8022984979/17713152000)]]

private theorem tensor041 (u v : ℝ) :
    eval poly026 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern041 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern041, Fin.sum_univ_succ]
  <;> ring

private theorem cert041 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern041) (m := (1/1000000000000000))
    tensor041 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern041]

private def bern042 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor042 (u v : ℝ) :
    eval poly027 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern042 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern042, Fin.sum_univ_succ]
  <;> ring

private theorem cert042 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern042) (m := (1/1000000000000000))
    tensor042 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern042]

private def bern043 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor043 (u v : ℝ) :
    eval poly028 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern043 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern043, Fin.sum_univ_succ]
  <;> ring

private theorem cert043 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern043) (m := (1/1000000000000000))
    tensor043 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern043]

private def bern044 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor044 (u v : ℝ) :
    eval poly029 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern044 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern044, Fin.sum_univ_succ]
  <;> ring

private theorem cert044 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern044) (m := (1/1000000000000000))
    tensor044 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern044]

private def bern045 : Coeff :=
  ![![(161/64), (241/96), (481/192), (5/2)],
    ![(161/64), (241/96), (481/192), (5/2)],
    ![(161/64), (241/96), (481/192), (5/2)]]

private theorem tensor045 (u v : ℝ) :
    eval poly000 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern045 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly000, bern045, Fin.sum_univ_succ]
  <;> ring

private theorem cert045 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly000 δ p := by
  apply positive_on_box_from_tensor (β := bern045) (m := (1/1000000000000000))
    tensor045 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern045]

private def bern046 : Coeff :=
  ![![2, 2, 2, 2],
    ![2, 2, 2, 2],
    ![2, 2, 2, 2]]

private theorem tensor046 (u v : ℝ) :
    eval poly001 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern046 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly001, bern046, Fin.sum_univ_succ]
  <;> ring

private theorem cert046 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly001 δ p := by
  apply positive_on_box_from_tensor (β := bern046) (m := (1/1000000000000000))
    tensor046 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern046]

private def bern047 : Coeff :=
  ![![(306670031/320000000), (153263349/160000000), (61276673/64000000), (9570001/10000000)],
    ![(306670031/320000000), (153263349/160000000), (61276673/64000000), (9570001/10000000)],
    ![(306670031/320000000), (153263349/160000000), (61276673/64000000), (9570001/10000000)]]

private theorem tensor047 (u v : ℝ) :
    eval poly002 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern047 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly002, bern047, Fin.sum_univ_succ]
  <;> ring

private theorem cert047 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly002 δ p := by
  apply positive_on_box_from_tensor (β := bern047) (m := (1/1000000000000000))
    tensor047 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern047]

private def bern048 : Coeff :=
  ![![(69695/49152), (104047/73728), (207103/147456), (2147/1536)],
    ![(138535/98304), (206807/147456), (411623/294912), (4267/3072)],
    ![(8605/6144), (12845/9216), (25565/18432), (265/192)]]

private theorem tensor048 (u v : ℝ) :
    eval poly003 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern048 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly003, bern048, Fin.sum_univ_succ]
  <;> ring

private theorem cert048 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly003 δ p := by
  apply positive_on_box_from_tensor (β := bern048) (m := (1/1000000000000000))
    tensor048 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern048]

private def bern049 : Coeff :=
  ![![(1184052989691/5242880000000), (1171539449769/5242880000000), (1131877617/5120000000), (1119690117/5120000000)],
    ![(2398466312451/10485760000000), (2373118372609/10485760000000), (2292777737/10240000000), (2268090237/10240000000)],
    ![(30360333069/131072000000), (30039473071/131072000000), (29022503/128000000), (28710003/128000000)]]

private theorem tensor049 (u v : ℝ) :
    eval poly004 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern049 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern049, Fin.sum_univ_succ]
  <;> ring

private theorem cert049 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern049) (m := (1/1000000000000000))
    tensor049 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern049]

private def bern050 : Coeff :=
  ![![(673736930309/5242880000000), (2032335314693/15728640000000), (7982068471/61440000000), (668760883/5120000000)],
    ![(1294322647549/10485760000000), (3905939666173/31457280000000), (15346912031/122880000000), (1286320763/10240000000)],
    ![(15514642931/131072000000), (46840108787/393216000000), (184121089/1536000000), (15438997/128000000)]]

private theorem tensor050 (u v : ℝ) :
    eval poly005 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern050 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern050, Fin.sum_univ_succ]
  <;> ring

private theorem cert050 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern050) (m := (1/1000000000000000))
    tensor050 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern050]

private def bern051 : Coeff :=
  ![![(85835934907079/193986560000000), (760495691473621/1745879040000000), (1949304012511/4546560000000), (47957979307/113664000000)],
    ![(173940419938159/387973120000000), (1541241579406541/3491758080000000), (3950910668231/9093120000000), (97212768947/227328000000)],
    ![(2202612125777/4849664000000), (19518647198323/43646976000000), (50040166393/113664000000), (1231369741/2841600000)]]

private theorem tensor051 (u v : ℝ) :
    eval poly006 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern051 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly006, bern051, Fin.sum_univ_succ]
  <;> ring

private theorem cert051 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly006 δ p := by
  apply positive_on_box_from_tensor (β := bern051) (m := (1/1000000000000000))
    tensor051 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern051]

private def bern052 : Coeff :=
  ![![(14269049872399/15728640000000), (42698514554767/47185920000000), (332734404391/368640000000), (2765730289/3072000000)],
    ![(28093734869879/31457280000000), (84067317583607/94371840000000), (655106837711/737280000000), (5445330569/6144000000)],
    ![(345617124937/393216000000), (1034220075721/1179648000000), (8059310833/9216000000), (66990007/76800000)]]

private theorem tensor052 (u v : ℝ) :
    eval poly007 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern052 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly007, bern052, Fin.sum_univ_succ]
  <;> ring

private theorem cert052 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly007 δ p := by
  apply positive_on_box_from_tensor (β := bern052) (m := (1/1000000000000000))
    tensor052 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern052]

private def bern053 : Coeff :=
  ![![(16280622261883/335544320000000), (1150251354541/23592960000000), (48163012099/983040000000), (151264391/3072000000)],
    ![(33842755617923/671088640000000), (2388550701701/47185920000000), (99909617099/1966080000000), (313463791/6144000000)],
    ![(439053333901/8388608000000), (30957483679/589824000000), (10349321/196608000), (810997/15360000)]]

private theorem tensor053 (u v : ℝ) :
    eval poly008 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern053 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern053, Fin.sum_univ_succ]
  <;> ring

private theorem cert053 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern053) (m := (1/1000000000000000))
    tensor053 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern053]

private def bern054 : Coeff :=
  ![![(14297269595229938388169/1202487646224384000000000), (15601409806005492994183/1387485745643520000000000), (2985969033839868222091/281833042083840000000000), (11674011746009606767/1174304342016000000000)],
    ![(23110844378337122324897/2404975292448768000000000), (324935585735030442729059/36074629386731520000000000), (4735078156231626620051/563666084167680000000000), (18294035980804784087/2348608684032000000000)],
    ![(1101696847888397992091/150310955778048000000000), (3052931456423975845117/450932867334144000000000), (43727728059793959949/7045826052096000000000), (165500605869879433/29357608550400000000)]]

private theorem tensor054 (u v : ℝ) :
    eval poly009 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern054 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern054, Fin.sum_univ_succ]
  <;> ring

private theorem cert054 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern054) (m := (1/1000000000000000))
    tensor054 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern054]

private def bern055 : Coeff :=
  ![![(48714733347501/6710886400000000), (233499422066027/33554432000000000), (6979876860957/1048576000000000), (104074013277/16384000000000)],
    ![(5457291893887/838860800000000), (15642481786783/2516582400000000), (31057819031/5242880000000), (2305939083/409600000000)],
    ![(119720644961/20971520000000), (341627424833/62914560000000), (3374538173/655360000000), (49828557/10240000000)]]

private theorem tensor055 (u v : ℝ) :
    eval poly010 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern055 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern055, Fin.sum_univ_succ]
  <;> ring

private theorem cert055 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern055) (m := (1/1000000000000000))
    tensor055 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern055]

private def bern056 : Coeff :=
  ![![(12333307536817/15728640000000), (12313328349947/15728640000000), (38417160019/49152000000), (11986129009/15360000000)],
    ![(24301198776137/31457280000000), (24261485501827/31457280000000), (75693930011/98304000000), (23616128009/30720000000)],
    ![(299197280983/393216000000), (298703928797/393216000000), (4659596249/6144000000), (11629999/15360000)]]

private theorem tensor056 (u v : ℝ) :
    eval poly011 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern056 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly011, bern056, Fin.sum_univ_succ]
  <;> ring

private theorem cert056 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly011 δ p := by
  apply positive_on_box_from_tensor (β := bern056) (m := (1/1000000000000000))
    tensor056 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern056]

private def bern057 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor057 (u v : ℝ) :
    eval poly012 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern057 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly012, bern057, Fin.sum_univ_succ]
  <;> ring

private theorem cert057 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly012 δ p := by
  apply positive_on_box_from_tensor (β := bern057) (m := (1/1000000000000000))
    tensor057 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern057]

private def bern058 : Coeff :=
  ![![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)]]

private theorem tensor058 (u v : ℝ) :
    eval poly013 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern058 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly013, bern058, Fin.sum_univ_succ]
  <;> ring

private theorem cert058 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly013 δ p := by
  apply positive_on_box_from_tensor (β := bern058) (m := (1/1000000000000000))
    tensor058 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern058]

private def bern059 : Coeff :=
  ![![(100985810821/3145728000000), (1504471321561/47185920000000), (23346876169/737280000000), (96612853/3072000000)],
    ![(200732754173/6291456000000), (2990332901681/94371840000000), (46402563809/1474560000000), (192010733/6144000000)],
    ![(12468367919/393216000000), (37146539503/1179648000000), (576392191/18432000000), (2384947/76800000)]]

private theorem tensor059 (u v : ℝ) :
    eval poly014 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern059 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly014, bern059, Fin.sum_univ_succ]
  <;> ring

private theorem cert059 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly014 δ p := by
  apply positive_on_box_from_tensor (β := bern059) (m := (1/1000000000000000))
    tensor059 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern059]

private def bern060 : Coeff :=
  ![![(7851/3968), (35233/17856), (70273/35712), (365/186)],
    ![(7851/3968), (35233/17856), (70273/35712), (365/186)],
    ![(7851/3968), (35233/17856), (70273/35712), (365/186)]]

private theorem tensor060 (u v : ℝ) :
    eval poly015 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern060 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern060, Fin.sum_univ_succ]
  <;> ring

private theorem cert060 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern060) (m := (1/1000000000000000))
    tensor060 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern060]

private def bern061 : Coeff :=
  ![![(1459/992), (6553/4464), (13081/8928), (136/93)],
    ![(1459/992), (6553/4464), (13081/8928), (136/93)],
    ![(1459/992), (6553/4464), (13081/8928), (136/93)]]

private theorem tensor061 (u v : ℝ) :
    eval poly016 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern061 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern061, Fin.sum_univ_succ]
  <;> ring

private theorem cert061 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern061) (m := (1/1000000000000000))
    tensor061 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern061]

private def bern062 : Coeff :=
  ![![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)],
    ![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)],
    ![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)]]

private theorem tensor062 (u v : ℝ) :
    eval poly017 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern062 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern062, Fin.sum_univ_succ]
  <;> ring

private theorem cert062 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern062) (m := (1/1000000000000000))
    tensor062 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern062]

private def bern063 : Coeff :=
  ![![(35297711/32505856), (949146631/877658112), (29539495/27426816), (153221/142848)],
    ![(140721653/130023424), (3783919933/3510632448), (117762205/109707264), (610823/571392)],
    ![(70126231/65011712), (1885626671/1755316224), (58683215/54853632), (304381/285696)]]

private theorem tensor063 (u v : ℝ) :
    eval poly018 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern063 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern063, Fin.sum_univ_succ]
  <;> ring

private theorem cert063 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern063) (m := (1/1000000000000000))
    tensor063 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern063]

private def bern064 : Coeff :=
  ![![(8876587941/52009369600), (44070835731/260046848000), (21367203/126976000), (10608039/63488000)],
    ![(35733956583/208037478400), (177413364353/1040187392000), (86016689/507904000), (42704157/253952000)],
    ![(17980780701/104018739200), (89271692891/520093696000), (43282283/253952000), (21488079/126976000)]]

private theorem tensor064 (u v : ℝ) :
    eval poly019 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern064 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern064, Fin.sum_univ_succ]
  <;> ring

private theorem cert064 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern064) (m := (1/1000000000000000))
    tensor064 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern064]

private def bern065 : Coeff :=
  ![![(130921220631/1300234240000), (1179368966597/11702108160000), (368880527/3656908800), (3101471/30720000)],
    ![(513304728813/5200936960000), (4624419820871/46808432640000), (7232780137/73138176000), (377068763/3809280000)],
    ![(251462287551/2600468480000), (2265681887677/23404216320000), (3543974867/36569088000), (184777561/1904640000)]]

private theorem tensor065 (u v : ℝ) :
    eval poly020 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern065 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern065, Fin.sum_univ_succ]
  <;> ring

private theorem cert065 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern065) (m := (1/1000000000000000))
    tensor065 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern065]

private def bern066 : Coeff :=
  ![![(39584635778587/149136867328000), (57118732512907/217659211776000), (24485465937439/94375673856000), (100862735411/393231974400)],
    ![(159269892351001/596547469312000), (8503477221493357/32213563342848000), (98522180470597/377502695424000), (405850329953/1572927897600)],
    ![(80100620793827/298273734656000), (4276691015538239/16106781671424000), (49551248595719/188751347712000), (204124859131/786463948800)]]

private theorem tensor066 (u v : ℝ) :
    eval poly021 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern066 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern066, Fin.sum_univ_succ]
  <;> ring

private theorem cert066 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern066) (m := (1/1000000000000000))
    tensor066 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern066]

private def bern067 : Coeff :=
  ![![(4413858550573/8061452288000), (118621773491093/217659211776000), (461215723951/850231296000), (1912801699/3542630400)],
    ![(565096077409/1040187392000), (15186870654569/28085059584000), (59048379883/109707264000), (244891567/457113600)],
    ![(8690261298533/16122904576000), (233549443309453/435318423552000), (908068328471/1700462592000), (3766035179/7085260800)]]

private theorem tensor067 (u v : ℝ) :
    eval poly022 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern067 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern067, Fin.sum_univ_succ]
  <;> ring

private theorem cert067 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern067) (m := (1/1000000000000000))
    tensor067 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern067]

private def bern068 : Coeff :=
  ![![(33290849255294689/1289832366080000000), (28112728299696709/1088296058880000000), (329737892032543/12753469440000000), (1375186357367/53139456000000)],
    ![(137073230413023547/5159329464320000000), (115708351779243847/4353184235520000000), (1356642308664709/51013877760000000), (5655795937421/212557824000000)],
    ![(70491531902434169/2579664732160000000), (59482895179850429/2176592117760000000), (697166524599623/25506938880000000), (2905423222687/106278912000000)]]

private theorem tensor068 (u v : ℝ) :
    eval poly023 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern068 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern068, Fin.sum_univ_succ]
  <;> ring

private theorem cert068 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern068) (m := (1/1000000000000000))
    tensor068 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern068]

private def bern069 : Coeff :=
  ![![(1600280866842543493/64491618304000000000), (1330285700608639483/54414802944000000000), (7678039509636733/318836736000000000), (63014557181329/2656972800000000)],
    ![(6162234487316591239/257966473216000000000), (5121758934426356089/217659211776000000000), (29556568525113679/1275346944000000000), (242533192010827/10627891200000000)],
    ![(2961672753631504253/128983236608000000000), (2461187533209077123/108829605888000000000), (14200489505840213/637673472000000000), (116504077648169/5313945600000000)]]

private theorem tensor069 (u v : ℝ) :
    eval poly024 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern069 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern069, Fin.sum_univ_succ]
  <;> ring

private theorem cert069 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern069) (m := (1/1000000000000000))
    tensor069 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern069]

private def bern070 : Coeff :=
  ![![(20658502893339987/4160749568000000000), (10075919746072713/2080374784000000000), (184183626853681/39007027200000000), (4673284988099/1015808000000000)],
    ![(1259989321252357/268435456000000000), (19033236691996513/4160749568000000000), (1042742711951387/234042163200000000), (26430321870817/6094848000000000)],
    ![(73475321214288547/16642998272000000000), (35765279001211513/8321499136000000000), (1957206144288611/468084326400000000), (49550117380537/12189696000000000)]]

private theorem tensor070 (u v : ℝ) :
    eval poly025 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern070 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern070, Fin.sum_univ_succ]
  <;> ring

private theorem cert070 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern070) (m := (1/1000000000000000))
    tensor070 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern070]

private def bern071 : Coeff :=
  ![![(33314067714067/72553070592000), (33162807569713/72553070592000), (28656395101/62980096000), (8022984979/17713152000)],
    ![(4265122687711/9361686528000), (4245757203829/9361686528000), (11006435059/24379392000), (1027164127/2285568000)],
    ![(65590667890907/145106141184000), (65292858179273/145106141184000), (169261116223/377880576000), (15796117979/35426304000)]]

private theorem tensor071 (u v : ℝ) :
    eval poly026 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern071 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern071, Fin.sum_univ_succ]
  <;> ring

private theorem cert071 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern071) (m := (1/1000000000000000))
    tensor071 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern071]

private def bern072 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor072 (u v : ℝ) :
    eval poly027 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern072 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern072, Fin.sum_univ_succ]
  <;> ring

private theorem cert072 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern072) (m := (1/1000000000000000))
    tensor072 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern072]

private def bern073 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor073 (u v : ℝ) :
    eval poly028 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern073 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern073, Fin.sum_univ_succ]
  <;> ring

private theorem cert073 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern073) (m := (1/1000000000000000))
    tensor073 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern073]

private def bern074 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor074 (u v : ℝ) :
    eval poly029 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern074 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern074, Fin.sum_univ_succ]
  <;> ring

private theorem cert074 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern074) (m := (1/1000000000000000))
    tensor074 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern074]

private def bern075 : Coeff :=
  ![![(7851/3968), (35233/17856), (70273/35712), (365/186)],
    ![(7851/3968), (35233/17856), (70273/35712), (365/186)],
    ![(7851/3968), (35233/17856), (70273/35712), (365/186)]]

private theorem tensor075 (u v : ℝ) :
    eval poly015 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern075 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern075, Fin.sum_univ_succ]
  <;> ring

private theorem cert075 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern075) (m := (1/1000000000000000))
    tensor075 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern075]

private def bern076 : Coeff :=
  ![![(1459/992), (6553/4464), (13081/8928), (136/93)],
    ![(1459/992), (6553/4464), (13081/8928), (136/93)],
    ![(1459/992), (6553/4464), (13081/8928), (136/93)]]

private theorem tensor076 (u v : ℝ) :
    eval poly016 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern076 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern076, Fin.sum_univ_succ]
  <;> ring

private theorem cert076 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern076) (m := (1/1000000000000000))
    tensor076 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern076]

private def bern077 : Coeff :=
  ![![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)],
    ![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)],
    ![(5836021/7936000), (582491/793600), (5813799/7936000), (90667/124000)]]

private theorem tensor077 (u v : ℝ) :
    eval poly017 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern077 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern077, Fin.sum_univ_succ]
  <;> ring

private theorem cert077 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern077) (m := (1/1000000000000000))
    tensor077 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern077]

private def bern078 : Coeff :=
  ![![(70126231/65011712), (1885626671/1755316224), (58683215/54853632), (304381/285696)],
    ![(139783271/130023424), (3758586751/3510632448), (116970655/109707264), (19571/18432)],
    ![(4353565/4063232), (117060005/109707264), (117515/110592), (18895/17856)]]

private theorem tensor078 (u v : ℝ) :
    eval poly018 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern078 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern078, Fin.sum_univ_succ]
  <;> ring

private theorem cert078 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern078) (m := (1/1000000000000000))
    tensor078 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern078]

private def bern079 : Coeff :=
  ![![(17980780701/104018739200), (89271692891/520093696000), (43282283/253952000), (21488079/126976000)],
    ![(36189166221/208037478400), (179673407211/1040187392000), (87112443/507904000), (43248159/253952000)],
    ![(227604819/1300234240), (1130021429/6501171200), (547877/3174400), (272001/1587200)]]

private theorem tensor079 (u v : ℝ) :
    eval poly019 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern079 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern079, Fin.sum_univ_succ]
  <;> ring

private theorem cert079 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern079) (m := (1/1000000000000000))
    tensor079 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern079]

private def bern080 : Coeff :=
  ![![(251462287551/2600468480000), (2265681887677/23404216320000), (3543974867/36569088000), (184777561/1904640000)],
    ![(492544421391/5200936960000), (4438307729837/46808432640000), (6943119331/73138176000), (362041481/3809280000)],
    ![(3013526673/32505856000), (27157823027/292552704000), (212446529/2285568000), (2215799/23808000)]]

private theorem tensor080 (u v : ℝ) :
    eval poly020 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern080 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern080, Fin.sum_univ_succ]
  <;> ring

private theorem cert080 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern080) (m := (1/1000000000000000))
    tensor080 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern080]

private def bern081 : Coeff :=
  ![![(80100620793827/298273734656000), (4276691015538239/16106781671424000), (49551248595719/188751347712000), (204124859131/786463948800)],
    ![(161132590824307/596547469312000), (8603286840659599/32213563342848000), (99682813912279/377502695424000), (410649106571/1572927897600)],
    ![(1012899625381/3728421683200), (54082447814017/201334770892800), (626644566457/2359391846400), (2581553093/9830799360)]]

private theorem tensor081 (u v : ℝ) :
    eval poly021 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern081 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern081, Fin.sum_univ_succ]
  <;> ring

private theorem cert081 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern081) (m := (1/1000000000000000))
    tensor081 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern081]

private def bern082 : Coeff :=
  ![![(8690261298533/16122904576000), (233549443309453/435318423552000), (908068328471/1700462592000), (3766035179/7085260800)],
    ![(17243066794453/32245809152000), (463404782946173/870636847104000), (1801773537511/3400925184000), (7472502139/14170521600)],
    ![(106910068699/201536307200), (2873191745459/5441480294400), (11171315113/21255782400), (46330837/88565760)]]

private theorem tensor082 (u v : ℝ) :
    eval poly022 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern082 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern082, Fin.sum_univ_succ]
  <;> ring

private theorem cert082 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern082) (m := (1/1000000000000000))
    tensor082 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern082]

private def bern083 : Coeff :=
  ![![(70491531902434169/2579664732160000000), (59482895179850429/2176592117760000000), (697166524599623/25506938880000000), (2905423222687/106278912000000)],
    ![(144892897196713129/5159329464320000000), (122223228940157869/4353184235520000000), (1432023789733783/51013877760000000), (192448288817/6856704000000)],
    ![(930017066178487/32245809152000000), (784254172003843/27207401472000000), (9185715814177/318836736000000), (38255921633/1328486400000)]]

private theorem tensor083 (u v : ℝ) :
    eval poly023 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern083 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern083, Fin.sum_univ_succ]
  <;> ring

private theorem cert083 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern083) (m := (1/1000000000000000))
    tensor083 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern083]

private def bern084 : Coeff :=
  ![![(2961672753631504253/128983236608000000000), (2461187533209077123/108829605888000000000), (14200489505840213/637673472000000000), (116504077648169/5313945600000000)],
    ![(5684456527209425773/257966473216000000000), (4722991198409952403/217659211776000000000), (27245389498247173/1275346944000000000), (7209132857479/342835200000000)],
    ![(34034797169724019/1612290457600000000), (28272545815010941/1360370073600000000), (163061249905087/7970918400000000), (1337238011671/66424320000000)]]

private theorem tensor084 (u v : ℝ) :
    eval poly024 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern084 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern084, Fin.sum_univ_succ]
  <;> ring

private theorem cert084 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern084) (m := (1/1000000000000000))
    tensor084 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern084]

private def bern085 : Coeff :=
  ![![(73475321214288547/16642998272000000000), (35765279001211513/8321499136000000000), (1957206144288611/468084326400000000), (49550117380537/12189696000000000)],
    ![(860391306386637/208037478400000000), (3346408461843/832149913600000), (38102643014051/9751756800000000), (192664962581/50790400000000)],
    ![(10009053868739/2600468480000000), (4859203352057/1300234240000000), (1325848752959/365690880000000), (6693330377/1904640000000)]]

private theorem tensor085 (u v : ℝ) :
    eval poly025 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern085 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern085, Fin.sum_univ_succ]
  <;> ring

private theorem cert085 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern085) (m := (1/1000000000000000))
    tensor085 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern085]

private def bern086 : Coeff :=
  ![![(65590667890907/145106141184000), (65292858179273/145106141184000), (169261116223/377880576000), (15796117979/35426304000)],
    ![(130143868244587/290212282368000), (129552959398393/290212282368000), (111948326021/251920384000), (31342383979/70852608000)],
    ![(806915004421/1813826764800), (803251265239/1813826764800), (2082298273/4723507200), (7773133/17713152)]]

private theorem tensor086 (u v : ℝ) :
    eval poly026 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern086 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern086, Fin.sum_univ_succ]
  <;> ring

private theorem cert086 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern086) (m := (1/1000000000000000))
    tensor086 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern086]

private def bern087 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor087 (u v : ℝ) :
    eval poly027 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern087 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern087, Fin.sum_univ_succ]
  <;> ring

private theorem cert087 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern087) (m := (1/1000000000000000))
    tensor087 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern087]

private def bern088 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor088 (u v : ℝ) :
    eval poly028 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern088 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern088, Fin.sum_univ_succ]
  <;> ring

private theorem cert088 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern088) (m := (1/1000000000000000))
    tensor088 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern088]

private def bern089 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor089 (u v : ℝ) :
    eval poly029 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern089 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern089, Fin.sum_univ_succ]
  <;> ring

private theorem cert089 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern089) (m := (1/1000000000000000))
    tensor089 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern089]

private def bern090 : Coeff :=
  ![![(46913/23808), (70273/35712), (140353/71424), (365/186)],
    ![(46913/23808), (70273/35712), (140353/71424), (365/186)],
    ![(46913/23808), (70273/35712), (140353/71424), (365/186)]]

private theorem tensor090 (u v : ℝ) :
    eval poly015 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern090 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern090, Fin.sum_univ_succ]
  <;> ring

private theorem cert090 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern090) (m := (1/1000000000000000))
    tensor090 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern090]

private def bern091 : Coeff :=
  ![![(8729/5952), (13081/8928), (26137/17856), (136/93)],
    ![(8729/5952), (13081/8928), (26137/17856), (136/93)],
    ![(8729/5952), (13081/8928), (26137/17856), (136/93)]]

private theorem tensor091 (u v : ℝ) :
    eval poly016 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern091 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern091, Fin.sum_univ_succ]
  <;> ring

private theorem cert091 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern091) (m := (1/1000000000000000))
    tensor091 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern091]

private def bern092 : Coeff :=
  ![![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)],
    ![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)],
    ![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)]]

private theorem tensor092 (u v : ℝ) :
    eval poly017 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern092 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern092, Fin.sum_univ_succ]
  <;> ring

private theorem cert092 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern092) (m := (1/1000000000000000))
    tensor092 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern092]

private def bern093 : Coeff :=
  ![![(2508998959/2340421632), (7511469295/7021264896), (117124367/109707264), (304381/285696)],
    ![(10019108317/9361686528), (29995218205/28085059584), (467705981/438829056), (1215463/1142784)],
    ![(5001110399/4680843264), (14972279615/14042529792), (233457247/219414528), (19571/18432)]]

private theorem tensor093 (u v : ℝ) :
    eval poly018 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern093 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern093, Fin.sum_univ_succ]
  <;> ring

private theorem cert093 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern093) (m := (1/1000000000000000))
    tensor093 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern093]

private def bern094 : Coeff :=
  ![![(355830250257/2080374784000), (354571095643/2080374784000), (86258441/507904000), (21488079/126976000)],
    ![(1427825181411/8321499136000), (1422772624289/8321499136000), (346125643/2031616000), (86224317/507904000)],
    ![(716164680897/4160749568000), (713630433003/4160749568000), (173608761/1015808000), (43248159/253952000)]]

private theorem tensor094 (u v : ℝ) :
    eval poly019 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern094 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern094, Fin.sum_univ_succ]
  <;> ring

private theorem cert094 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern094) (m := (1/1000000000000000))
    tensor094 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern094]

private def bern095 : Coeff :=
  ![![(3022530777533/31205621760000), (1814503277401/18723373056000), (35458520191/365690880000), (184777561/1904640000)],
    ![(11966291191079/124822487040000), (7183859793211/74893492224000), (140388619213/1462763520000), (731596603/7618560000)],
    ![(5921229636013/62411243520000), (3554853238409/37446746112000), (69471578831/731381760000), (362041481/3809280000)]]

private theorem tensor095 (u v : ℝ) :
    eval poly020 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern095 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern095, Fin.sum_univ_succ]
  <;> ring

private theorem cert095 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern095) (m := (1/1000000000000000))
    tensor095 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern095]

private def bern096 : Coeff :=
  ![![(34021103324988319/128854253371392000), (10148348734526297/38656276011417600), (98541214787159/377502695424000), (204124859131/786463948800)],
    ![(136482121140585517/515417013485568000), (40712245939610171/154625104045670400), (395321029063637/1510010781696000), (818898824833/3145855795200)],
    ![(68439914490608879/257708506742784000), (20415548470557577/77312552022835200), (198238599489319/755005390848000), (410649106571/1572927897600)]]

private theorem tensor096 (u v : ℝ) :
    eval poly021 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern096 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern096, Fin.sum_univ_succ]
  <;> ring

private theorem cert096 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern096) (m := (1/1000000000000000))
    tensor096 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern096]

private def bern097 : Coeff :=
  ![![(310677843775373/580424564736000), (185973125776873/348254738841600), (1811916771431/3400925184000), (3766035179/7085260800)],
    ![(1237797314303639/2321698258944000), (740950924668139/1393018955366400), (7219007593733/13603700736000), (15004572497/28341043200)],
    ![(616441626752893/1160849129472000), (369004673114393/696509477683200), (3595174050871/6801850368000), (7472502139/14170521600)]]

private theorem tensor097 (u v : ℝ) :
    eval poly022 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern097 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern097, Fin.sum_univ_succ]
  <;> ring

private theorem cert097 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern097) (m := (1/1000000000000000))
    tensor097 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern097]

private def bern098 : Coeff :=
  ![![(15228915631371627683/557207582146560000000), (713907148936447543/26119105413120000000), (1394468098044503/51013877760000000), (2905423222687/106278912000000)],
    ![(61744318578141198329/2228830328586240000000), (2894224873849476469/104476421652480000000), (5652775254621269/204055511040000000), (11776743398701/425115648000000)],
    ![(31286487315397942963/1114415164293120000000), (1466410575976581383/52238210826240000000), (2863839058532263/102027755520000000), (192448288817/6856704000000)]]

private theorem tensor098 (u v : ℝ) :
    eval poly023 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern098 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern098, Fin.sum_univ_succ]
  <;> ring

private theorem cert098 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern098) (m := (1/1000000000000000))
    tensor098 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern098]

private def bern099 : Coeff :=
  ![![(625252099927312104271/27860379107328000000000), (29082874384311112841/1305955270656000000000), (28180978823620493/1275346944000000000), (116504077648169/5313945600000000)],
    ![(2450242039269716378173/111441516429312000000000), (113964804015725990603/5223821082624000000000), (110425321375310039/5101387776000000000), (456491273878187/21255782400000000)],
    ![(1199737839415092169631/55720758214656000000000), (55799055247103764921/2611910541312000000000), (54063363728069053/2550693888000000000), (7209132857479/342835200000000)]]

private theorem tensor099 (u v : ℝ) :
    eval poly024 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern099 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern099, Fin.sum_univ_succ]
  <;> ring

private theorem cert099 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern099) (m := (1/1000000000000000))
    tensor099 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern099]

private def bern100 : Coeff :=
  ![![(1693464232627707947/399431958528000000000), (250525879673855693/59914793779200000000), (19299653258506159/4680843264000000000), (49550117380537/12189696000000000)],
    ![(105708568735602917/25769803776000000000), (484631760770882237/119829587558400000000), (37322289057610879/9361686528000000000), (95789708399977/24379392000000000)],
    ![(2110316792821087769/532575944704000000000), (311989228758818447/79886391705600000000), (24018373747636933/6241124352000000000), (61622204610739/16252928000000000)]]

private theorem tensor100 (u v : ℝ) :
    eval poly025 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern100 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern100, Fin.sum_univ_succ]
  <;> ring

private theorem cert100 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern100) (m := (1/1000000000000000))
    tensor100 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern100]

private def bern101 : Coeff :=
  ![![(260579473779803/580424564736000), (259986294680521/580424564736000), (1013259123997/2267283456000), (15796117979/35426304000)],
    ![(1038196230532769/2321698258944000), (1035832896689803/2321698258944000), (4037009469511/9069133824000), (62934619937/141705216000)],
    ![(517037282973163/1160849129472000), (515860307328761/1160849129472000), (2010491221517/4534566912000), (31342383979/70852608000)]]

private theorem tensor101 (u v : ℝ) :
    eval poly026 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern101 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern101, Fin.sum_univ_succ]
  <;> ring

private theorem cert101 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern101) (m := (1/1000000000000000))
    tensor101 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern101]

private def bern102 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor102 (u v : ℝ) :
    eval poly027 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern102 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern102, Fin.sum_univ_succ]
  <;> ring

private theorem cert102 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern102) (m := (1/1000000000000000))
    tensor102 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern102]

private def bern103 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor103 (u v : ℝ) :
    eval poly028 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern103 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern103, Fin.sum_univ_succ]
  <;> ring

private theorem cert103 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern103) (m := (1/1000000000000000))
    tensor103 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern103]

private def bern104 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor104 (u v : ℝ) :
    eval poly029 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern104 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern104, Fin.sum_univ_succ]
  <;> ring

private theorem cert104 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern104) (m := (1/1000000000000000))
    tensor104 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern104]

private def bern105 : Coeff :=
  ![![(31211/15872), (140353/71424), (280513/142848), (365/186)],
    ![(31211/15872), (140353/71424), (280513/142848), (365/186)],
    ![(31211/15872), (140353/71424), (280513/142848), (365/186)]]

private theorem tensor105 (u v : ℝ) :
    eval poly015 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern105 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern105, Fin.sum_univ_succ]
  <;> ring

private theorem cert105 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern105) (m := (1/1000000000000000))
    tensor105 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern105]

private def bern106 : Coeff :=
  ![![(5811/3968), (26137/17856), (52249/35712), (136/93)],
    ![(5811/3968), (26137/17856), (52249/35712), (136/93)],
    ![(5811/3968), (26137/17856), (52249/35712), (136/93)]]

private theorem tensor106 (u v : ℝ) :
    eval poly016 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern106 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern106, Fin.sum_univ_succ]
  <;> ring

private theorem cert106 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern106) (m := (1/1000000000000000))
    tensor106 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern106]

private def bern107 : Coeff :=
  ![![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)],
    ![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)],
    ![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)]]

private theorem tensor107 (u v : ℝ) :
    eval poly017 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern107 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern107, Fin.sum_univ_succ]
  <;> ring

private theorem cert107 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern107) (m := (1/1000000000000000))
    tensor107 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern107]

private def bern108 : Coeff :=
  ![![(3334986149/3120562176), (29983855727/28085059584), (234006671/219414528), (304381/285696)],
    ![(26657374963/24964497408), (239668225369/224680476672), (1870470457/1755316224), (2432987/2285568)],
    ![(13317430367/12482248704), (119732802461/112340238336), (934443773/877658112), (1215463/1142784)]]

private theorem tensor108 (u v : ℝ) :
    eval poly018 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern108 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern108, Fin.sum_univ_succ]
  <;> ring

private theorem cert108 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern108) (m := (1/1000000000000000))
    tensor108 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern108]

private def bern109 : Coeff :=
  ![![(283154794653/1664299827200), (1413260930651/8321499136000), (172210757/1015808000), (21488079/126976000)],
    ![(2268822595131/13314398617600), (11323976824077/66571993088000), (1379865939/8126464000), (172176633/1015808000)],
    ![(1136203416519/6657199308800), (5670933101473/33285996544000), (691022911/4063232000), (86224317/507904000)]]

private theorem tensor109 (u v : ℝ) :
    eval poly019 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern109 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern109, Fin.sum_univ_succ]
  <;> ring

private theorem cert109 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern109) (m := (1/1000000000000000))
    tensor109 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern109]

private def bern110 : Coeff :=
  ![![(4033303982143/41607495680000), (36309465403069/374467461120000), (70935811903/731381760000), (184777561/1904640000)],
    ![(32101808498441/332859965440000), (288995569846043/2995739688960000), (564598414601/5851054080000), (1470706847/15237120000)],
    ![(15968592569869/166429982720000), (143757708233767/1497869844480000), (280855166989/2925527040000), (731596603/7618560000)]]

private theorem tensor110 (u v : ℝ) :
    eval poly020 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern110 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern110, Fin.sum_univ_succ]
  <;> ring

private theorem cert110 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern110) (m := (1/1000000000000000))
    tensor110 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern110]

private def bern111 : Coeff :=
  ![![(5996769145162781/22907422821580800), (22423741443857429/85902835580928000), (5311382355947/20405551104000), (204124859131/786463948800)],
    ![(48044447641950907/183259382572646400), (179653025625448963/687222684647424000), (1574477053663633/6040043126784000), (1635398261357/6291711590400)],
    ![(24057371061299783/91629691286323200), (89958059850019247/343611342323712000), (25432014999467/97420050432000), (818898824833/3145855795200)]]

private theorem tensor111 (u v : ℝ) :
    eval poly021 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern111 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern111, Fin.sum_univ_succ]
  <;> ring

private theorem cert111 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern111) (m := (1/1000000000000000))
    tensor111 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern111]

private def bern112 : Coeff :=
  ![![(82558615383203/154779883929600), (3710809208420749/6965094776832000), (3619613657351/6801850368000), (3766035179/7085260800)],
    ![(659163075019141/1238239071436800), (29627778969869003/55720758214656000), (28899657021697/54414802944000), (30068713213/56682086400)],
    ![(328928613486329/619119535718400), (14784542136186007/27860379107328000), (14421202392293/27207401472000), (15004572497/28341043200)]]

private theorem tensor112 (u v : ℝ) :
    eval poly022 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern112 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern112, Fin.sum_univ_succ]
  <;> ring

private theorem cert112 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern112) (m := (1/1000000000000000))
    tensor112 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern112]

private def bern113 : Coeff :=
  ![![(13538409900643084811/495295628574720000000), (63463984278701683/2321698258944000000), (2789071244934263/102027755520000000), (2905423222687/106278912000000)],
    ![(109036850989029998557/3962365028597760000000), (20444832322144637/742943442862080000), (22461897065734801/816222044160000000), (23398436289449/850231296000000)],
    ![(54883211386457659313/1981182514298880000000), (257264870938809193/9286793035776000000), (11305612085997749/408111022080000000), (11776743398701/425115648000000)]]

private theorem tensor113 (u v : ℝ) :
    eval poly023 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern113 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern113, Fin.sum_univ_succ]
  <;> ring

private theorem cert113 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern113) (m := (1/1000000000000000))
    tensor113 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern113]

private def bern114 : Coeff :=
  ![![(183120058789927712669/8254927142912000000000), (7695304075859993063/348254738841600000000), (56141957459181053/2550693888000000000), (116504077648169/5313945600000000)],
    ![(1450041432490042982203/66039417143296000000000), (2437390405899370057/111441516429312000000), (444551056942799131/20405551104000000000), (922507584470863/42511564800000000)],
    ![(717561197330332131527/33019708571648000000000), (30153543844044279173/1393018955366400000000), (219983227106074919/10202775552000000000), (456491273878187/21255782400000000)]]

private theorem tensor114 (u v : ℝ) :
    eval poly024 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern114 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern114, Fin.sum_univ_succ]
  <;> ring

private theorem cert114 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern114) (m := (1/1000000000000000))
    tensor114 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern114]

private def bern115 : Coeff :=
  ![![(4422783768869278309/1065151889408000000000), (1646909566734048043/399431958528000000000), (38326898332632367/9361686528000000000), (49550117380537/12189696000000000)],
    ![(17399882207678612127/4260607557632000000000), (2159555230807858523/532575944704000000000), (50253111249488927/12482248704000000000), (64963314387017/16252928000000000)],
    ![(68426435203314542381/17042430230528000000000), (25475749786763251427/6390911336448000000000), (592773642617819783/149786984448000000000), (766225916954273/195035136000000000)]]

private theorem tensor115 (u v : ℝ) :
    eval poly025 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern115 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern115, Fin.sum_univ_succ]
  <;> ring

private theorem cert115 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern115) (m := (1/1000000000000000))
    tensor115 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern115]

private def bern116 : Coeff :=
  ![![(1038762481009499/2321698258944000), (1037578563134921/2321698258944000), (674736891551/1511522304000), (15796117979/35426304000)],
    ![(8293669427155213/18573586071552000), (8284216810666927/18573586071552000), (5387222614697/12092178432000), (126119091853/283410432000)],
    ![(4138619503117217/9286793035776000), (4133902558127243/9286793035776000), (896091682831/2015363072000), (62934619937/141705216000)]]

private theorem tensor116 (u v : ℝ) :
    eval poly026 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern116 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern116, Fin.sum_univ_succ]
  <;> ring

private theorem cert116 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern116) (m := (1/1000000000000000))
    tensor116 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern116]

private def bern117 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor117 (u v : ℝ) :
    eval poly027 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern117 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern117, Fin.sum_univ_succ]
  <;> ring

private theorem cert117 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern117) (m := (1/1000000000000000))
    tensor117 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern117]

private def bern118 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor118 (u v : ℝ) :
    eval poly028 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern118 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern118, Fin.sum_univ_succ]
  <;> ring

private theorem cert118 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern118) (m := (1/1000000000000000))
    tensor118 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern118]

private def bern119 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor119 (u v : ℝ) :
    eval poly029 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern119 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern119, Fin.sum_univ_succ]
  <;> ring

private theorem cert119 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern119) (m := (1/1000000000000000))
    tensor119 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern119]

private def bern120 : Coeff :=
  ![![(187073/95232), (280513/142848), (560833/285696), (365/186)],
    ![(187073/95232), (280513/142848), (560833/285696), (365/186)],
    ![(187073/95232), (280513/142848), (560833/285696), (365/186)]]

private theorem tensor120 (u v : ℝ) :
    eval poly015 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern120 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern120, Fin.sum_univ_succ]
  <;> ring

private theorem cert120 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern120) (m := (1/1000000000000000))
    tensor120 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern120]

private def bern121 : Coeff :=
  ![![(34841/23808), (52249/35712), (104473/71424), (136/93)],
    ![(34841/23808), (52249/35712), (104473/71424), (136/93)],
    ![(34841/23808), (52249/35712), (104473/71424), (136/93)]]

private theorem tensor121 (u v : ℝ) :
    eval poly016 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern121 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern121, Fin.sum_univ_succ]
  <;> ring

private theorem cert121 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern121) (m := (1/1000000000000000))
    tensor121 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern121]

private def bern122 : Coeff :=
  ![![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)],
    ![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)],
    ![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)]]

private theorem tensor122 (u v : ℝ) :
    eval poly017 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern122 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern122, Fin.sum_univ_succ]
  <;> ring

private theorem cert122 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern122) (m := (1/1000000000000000))
    tensor122 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern122]

private def bern123 : Coeff :=
  ![![(39957812335/37446746112), (119811433327/112340238336), (467771279/438829056), (304381/285696)],
    ![(639054842065/599147937792), (1916172483025/1797443813376), (7481174705/7021264896), (4868035/4571136)],
    ![(319392343385/299573968896), (957681016409/898721906688), (3739004473/3510632448), (2432987/2285568)]]

private theorem tensor123 (u v : ℝ) :
    eval poly018 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern123 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern123, Fin.sum_univ_succ]
  <;> ring

private theorem cert123 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern123) (m := (1/1000000000000000))
    tensor123 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern123]

private def bern124 : Coeff :=
  ![![(5648025537297/33285996544000), (5643004718683/33285996544000), (344115389/2031616000), (21488079/126976000)],
    ![(18087980518179/106515188940800), (18071901187681/106515188940800), (1102040423/6501171200), (68816253/406323200)],
    ![(45255698292519/266287972352000), (45215468188941/266287972352000), (2757279003/16252928000), (172176633/1015808000)]]

private theorem tensor124 (u v : ℝ) :
    eval poly019 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern124 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern124, Fin.sum_univ_succ]
  <;> ring

private theorem cert124 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern124) (m := (1/1000000000000000))
    tensor124 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern124]

private def bern125 : Coeff :=
  ![![(9683809528153/99857989632000), (145276483504829/1497869844480000), (141890395327/1462763520000), (184777561/1904640000)],
    ![(154546438979431/1597727834112000), (92740357848443/958636700467200), (452894601293/4680843264000), (589785467/6094848000)],
    ![(77075962754207/798863917056000), (1156297078172443/11982958755840000), (1129349843849/11702108160000), (1470706847/15237120000)]]

private theorem tensor125 (u v : ℝ) :
    eval poly020 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern125 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern125, Fin.sum_univ_succ]
  <;> ring

private theorem cert125 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern125) (m := (1/1000000000000000))
    tensor125 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern125]

private def bern126 : Coeff :=
  ![![(2149610457679856653/8246672215769088000), (804951883919094973/3092502080913408000), (392481011935799/1510010781696000), (204124859131/786463948800)],
    ![(6883799989754978903/26389351090461081600), (2577736642945861223/9896006658922905600), (1256861496010549/4832034501427200), (653679426881/2516684636160)],
    ![(17222116287336041291/65973377726152704000), (6449068143376546331/24740016647307264000), (3144459384566353/12080086253568000), (1635398261357/6291711590400)]]

private theorem tensor126 (u v : ℝ) :
    eval poly021 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern126 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern126, Fin.sum_univ_succ]
  <;> ring

private theorem cert126 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern126) (m := (1/1000000000000000))
    tensor126 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern126]

private def bern127 : Coeff :=
  ![![(4944863615875469/9286793035776000), (14825941201039757/27860379107328000), (7235007429191/13603700736000), (3766035179/7085260800)],
    ![(15807920768501719/29717737714483200), (47396110799106007/89153213143449600), (23129136227941/43531842355200), (12039398929/22672834560)],
    ![(39480694915504843/74294344286208000), (118373024387211979/222883032858624000), (57765621706177/108829605888000), (30068713213/56682086400)]]

private theorem tensor127 (u v : ℝ) :
    eval poly022 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern127 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern127, Fin.sum_univ_succ]
  <;> ring

private theorem cert127 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern127) (m := (1/1000000000000000))
    tensor127 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern127]

private def bern128 : Coeff :=
  ![![(194965933442644585159/7132257051475968000000), (11424044446997174839/417905686609920000000), (5578277538713783/204055511040000000), (2905423222687/106278912000000)],
    ![(3129910434484336788601/114116112823615488000000), (36679271187798986549/1337298197151744000000), (17910123242663221/652977635328000000), (9328364414189/340092518400000)],
    ![(1570182966943180107329/57058056411807744000000), (92004000363017534033/3343245492879360000000), (44924395903605841/1632444088320000000), (23398436289449/850231296000000)]]

private theorem tensor128 (u v : ℝ) :
    eval poly023 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern128 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern128, Fin.sum_univ_succ]
  <;> ring

private theorem cert128 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern128) (m := (1/1000000000000000))
    tensor128 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern128]

private def bern129 : Coeff :=
  ![![(7864607579623810234883/356612852573798400000000), (459915187381961542793/20895284330496000000000), (112063914730302173/5101387776000000000), (116504077648169/5313945600000000)],
    ![(125191865226466250738237/5705805641180774400000000), (1464217177268779703563/66864909857587200000000), (356773203066246151/16324440883200000000), (370908041131243/17004625920000000)],
    ![(62275004589475768859173/2852902820590387200000000), (3641764387288206175471/167162274643968000000000), (887354697488813371/40811102208000000000), (922507584470863/42511564800000000)]]

private theorem tensor129 (u v : ℝ) :
    eval poly024 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern129 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern129, Fin.sum_univ_succ]
  <;> ring

private theorem cert129 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern129) (m := (1/1000000000000000))
    tensor129 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern129]

private def bern130 : Coeff :=
  ![![(21006038154288804619/5112729069158400000000), (19623389412332339329/4793183502336000000000), (76381388480884783/18723373056000000000), (49550117380537/12189696000000000)],
    ![(166655034669083655901/40901832553267200000000), (155682405138711537463/38345468018688000000000), (605960364019693081/149786984448000000000), (393090412683199/97517568000000000)],
    ![(440685158115147461801/109071553475379200000000), (13279412741108595077/3298534883328000000000), (1602271947767363189/399431958528000000000), (1039382446777091/260046848000000000)]]

private theorem tensor130 (u v : ℝ) :
    eval poly025 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern130 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern130, Fin.sum_univ_succ]
  <;> ring

private theorem cert130 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern130) (m := (1/1000000000000000))
    tensor130 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern130]

private def bern131 : Coeff :=
  ![![(4147950077276507/9286793035776000), (4145584681851337/9286793035776000), (809222755193/1813826764800), (15796117979/35426304000)],
    ![(13260318370778209/29717737714483200), (13252756588301003/29717737714483200), (12934764361799/29021228236800), (50497607137/113364172800)],
    ![(33117991235678989/74294344286208000), (33099105486694319/74294344286208000), (1292196464051/2902122823680), (126119091853/283410432000)]]

private theorem tensor131 (u v : ℝ) :
    eval poly026 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern131 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern131, Fin.sum_univ_succ]
  <;> ring

private theorem cert131 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern131) (m := (1/1000000000000000))
    tensor131 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern131]

private def bern132 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor132 (u v : ℝ) :
    eval poly027 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern132 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern132, Fin.sum_univ_succ]
  <;> ring

private theorem cert132 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern132) (m := (1/1000000000000000))
    tensor132 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern132]

private def bern133 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor133 (u v : ℝ) :
    eval poly028 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern133 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern133, Fin.sum_univ_succ]
  <;> ring

private theorem cert133 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern133) (m := (1/1000000000000000))
    tensor133 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern133]

private def bern134 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor134 (u v : ℝ) :
    eval poly029 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern134 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern134, Fin.sum_univ_succ]
  <;> ring

private theorem cert134 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern134) (m := (1/1000000000000000))
    tensor134 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern134]

private def bern135 : Coeff :=
  ![![(187073/95232), (280513/142848), (560833/285696), (365/186)],
    ![(187073/95232), (280513/142848), (560833/285696), (365/186)],
    ![(187073/95232), (280513/142848), (560833/285696), (365/186)]]

private theorem tensor135 (u v : ℝ) :
    eval poly015 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern135 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern135, Fin.sum_univ_succ]
  <;> ring

private theorem cert135 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern135) (m := (1/1000000000000000))
    tensor135 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern135]

private def bern136 : Coeff :=
  ![![(34841/23808), (52249/35712), (104473/71424), (136/93)],
    ![(34841/23808), (52249/35712), (104473/71424), (136/93)],
    ![(34841/23808), (52249/35712), (104473/71424), (136/93)]]

private theorem tensor136 (u v : ℝ) :
    eval poly016 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern136 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern136, Fin.sum_univ_succ]
  <;> ring

private theorem cert136 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern136) (m := (1/1000000000000000))
    tensor136 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern136]

private def bern137 : Coeff :=
  ![![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)],
    ![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)],
    ![(46454837/63488000), (23221863/31744000), (9286523/12697600), (90667/124000)]]

private theorem tensor137 (u v : ℝ) :
    eval poly017 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern137 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern137, Fin.sum_univ_succ]
  <;> ring

private theorem cert137 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern137) (m := (1/1000000000000000))
    tensor137 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern137]

private def bern138 : Coeff :=
  ![![(319392343385/299573968896), (957681016409/898721906688), (3739004473/3510632448), (2432987/2285568)],
    ![(638514531475/599147937792), (1914551582611/1797443813376), (7474843187/7021264896), (4863913/4571136)],
    ![(159561094045/149786984448), (478435283101/449360953344), (1867919357/1755316224), (1215463/1142784)]]

private theorem tensor138 (u v : ℝ) :
    eval poly018 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern138 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern138, Fin.sum_univ_succ]
  <;> ring

private theorem cert138 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern138) (m := (1/1000000000000000))
    tensor138 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern138]

private def bern139 : Coeff :=
  ![![(45255698292519/266287972352000), (45215468188941/266287972352000), (2757279003/16252928000), (172176633/1015808000)],
    ![(90582890579181/532575944704000), (90502366817359/532575944704000), (5518913897/32505856000), (344625267/2031616000)],
    ![(22663596143331/133143986176000), (22643449314209/133143986176000), (1380817447/8126464000), (86224317/507904000)]]

private theorem tensor139 (u v : ℝ) :
    eval poly019 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern139 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern139, Fin.sum_univ_succ]
  <;> ring

private theorem cert139 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern139) (m := (1/1000000000000000))
    tensor139 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern139]

private def bern140 : Coeff :=
  ![![(77075962754207/798863917056000), (1156297078172443/11982958755840000), (1129349843849/11702108160000), (1470706847/15237120000)],
    ![(153757412037397/1597727834112000), (2306679366478697/23965917511680000), (2252926368931/23404216320000), (2933900053/30474240000)],
    ![(7668144928319/79886391705600), (575191144153127/5991479377920000), (561788262541/5851054080000), (731596603/7618560000)]]

private theorem tensor140 (u v : ℝ) :
    eval poly020 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern140 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern140, Fin.sum_univ_succ]
  <;> ring

private theorem cert140 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern140) (m := (1/1000000000000000))
    tensor140 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern140]

private def bern141 : Coeff :=
  ![![(17222116287336041291/65973377726152704000), (6449068143376546331/24740016647307264000), (3144459384566353/12080086253568000), (1635398261357/6291711590400)],
    ![(34469465200569270649/131946755452305408000), (12907589358776879209/49480033294614528000), (6293530058212667/24160172507136000), (3273195911023/12583423180800)],
    ![(8623674456616614679/32986688863076352000), (3229260607700166439/12370008323653632000), (1574535336823157/6040043126784000), (818898824833/3145855795200)]]

private theorem tensor141 (u v : ℝ) :
    eval poly021 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern141 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern141, Fin.sum_univ_succ]
  <;> ring

private theorem cert141 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern141) (m := (1/1000000000000000))
    tensor141 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern141]

private def bern142 : Coeff :=
  ![![(39480694915504843/74294344286208000), (118373024387211979/222883032858624000), (57765621706177/108829605888000), (30068713213/56682086400)],
    ![(78883175819510777/148588688572416000), (236511543553317881/445766065717248000), (115416805685003/217659211776000), (60077858207/113364172800)],
    ![(19701240452002967/37147172143104000), (59069259583052951/111441516429312000), (28825591989413/54414802944000), (15004572497/28341043200)]]

private theorem tensor142 (u v : ℝ) :
    eval poly022 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern142 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern142, Fin.sum_univ_succ]
  <;> ring

private theorem cert142 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern142) (m := (1/1000000000000000))
    tensor142 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern142]

private def bern143 : Coeff :=
  ![![(1570182966943180107329/57058056411807744000000), (92004000363017534033/3343245492879360000000), (44924395903605841/1632444088320000000), (23398436289449/850231296000000)],
    ![(630164286657676728143/22823222564723097600000), (184619645513075203387/6686490985758720000000), (90146967401107259/3264888176640000000), (46951923086851/1700462592000000)],
    ![(790319233172601766693/28529028205903872000000), (46307822575028834677/1671622746439680000000), (22611285748750709/816222044160000000), (11776743398701/425115648000000)]]

private theorem tensor143 (u v : ℝ) :
    eval poly023 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern143 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern143, Fin.sum_univ_succ]
  <;> ring

private theorem cert143 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern143) (m := (1/1000000000000000))
    tensor143 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern143]

private def bern144 : Coeff :=
  ![![(62275004589475768859173/2852902820590387200000000), (3641764387288206175471/167162274643968000000000), (887354697488813371/40811102208000000000), (922507584470863/42511564800000000)],
    ![(24781630626287364939691/1141161128236154880000000), (7245971662808926184069/334324549287936000000000), (1765552774624022729/81622204416000000000), (1835490132227237/85023129600000000)],
    ![(30816574270980527919641/1426451410295193600000000), (1802103637760360004299/83581137321984000000000), (439099038567604679/20405551104000000000), (456491273878187/21255782400000000)]]

private theorem tensor144 (u v : ℝ) :
    eval poly024 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern144 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern144, Fin.sum_univ_succ]
  <;> ring

private theorem cert144 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern144) (m := (1/1000000000000000))
    tensor144 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern144]

private def bern145 : Coeff :=
  ![![(440685158115147461801/109071553475379200000000), (13279412741108595077/3298534883328000000000), (1602271947767363189/399431958528000000000), (1039382446777091/260046848000000000)],
    ![(655435335669107761799/163607330213068800000000), (612255764368253192309/153381872074752000000000), (2382974387223317243/599147937792000000000), (1545785689598477/390070272000000000)],
    ![(324911807461394012099/81803665106534400000000), (303500374410724471721/76690936037376000000000), (1181235146838701447/299573968896000000000), (766225916954273/195035136000000000)]]

private theorem tensor145 (u v : ℝ) :
    eval poly025 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern145 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern145, Fin.sum_univ_succ]
  <;> ring

private theorem cert145 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern145) (m := (1/1000000000000000))
    tensor145 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern145]

private def bern146 : Coeff :=
  ![![(33117991235678989/74294344286208000), (33099105486694319/74294344286208000), (1292196464051/2902122823680), (126119091853/283410432000)],
    ![(66170373088824911/148588688572416000), (66132639005272261/148588688572416000), (12909164919221/29021228236800), (251988331727/566820864000)],
    ![(16526190926572961/37147172143104000), (16516766759288971/37147172143104000), (3224091299483/7255307059200), (62934619937/141705216000)]]

private theorem tensor146 (u v : ℝ) :
    eval poly026 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern146 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern146, Fin.sum_univ_succ]
  <;> ring

private theorem cert146 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern146) (m := (1/1000000000000000))
    tensor146 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern146]

private def bern147 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor147 (u v : ℝ) :
    eval poly027 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern147 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern147, Fin.sum_univ_succ]
  <;> ring

private theorem cert147 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern147) (m := (1/1000000000000000))
    tensor147 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern147]

private def bern148 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor148 (u v : ℝ) :
    eval poly028 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern148 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern148, Fin.sum_univ_succ]
  <;> ring

private theorem cert148 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern148) (m := (1/1000000000000000))
    tensor148 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern148]

private def bern149 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor149 (u v : ℝ) :
    eval poly029 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern149 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern149, Fin.sum_univ_succ]
  <;> ring

private theorem cert149 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern149) (m := (1/1000000000000000))
    tensor149 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern149]

private def bern150 : Coeff :=
  ![![(31211/15872), (140353/71424), (280513/142848), (365/186)],
    ![(31211/15872), (140353/71424), (280513/142848), (365/186)],
    ![(31211/15872), (140353/71424), (280513/142848), (365/186)]]

private theorem tensor150 (u v : ℝ) :
    eval poly015 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern150 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern150, Fin.sum_univ_succ]
  <;> ring

private theorem cert150 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern150) (m := (1/1000000000000000))
    tensor150 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern150]

private def bern151 : Coeff :=
  ![![(5811/3968), (26137/17856), (52249/35712), (136/93)],
    ![(5811/3968), (26137/17856), (52249/35712), (136/93)],
    ![(5811/3968), (26137/17856), (52249/35712), (136/93)]]

private theorem tensor151 (u v : ℝ) :
    eval poly016 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern151 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern151, Fin.sum_univ_succ]
  <;> ring

private theorem cert151 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern151) (m := (1/1000000000000000))
    tensor151 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern151]

private def bern152 : Coeff :=
  ![![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)],
    ![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)],
    ![(4648817/6348800), (11616487/15872000), (23221863/31744000), (90667/124000)]]

private theorem tensor152 (u v : ℝ) :
    eval poly017 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern152 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern152, Fin.sum_univ_succ]
  <;> ring

private theorem cert152 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern152) (m := (1/1000000000000000))
    tensor152 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern152]

private def bern153 : Coeff :=
  ![![(13317430367/12482248704), (119732802461/112340238336), (934443773/877658112), (1215463/1142784)],
    ![(26612346505/24964497408), (239262984475/224680476672), (1867304635/1755316224), (2428865/2285568)],
    ![(6647458069/6241124352), (59765091007/56170119168), (466430431/438829056), (19571/18432)]]

private theorem tensor153 (u v : ℝ) :
    eval poly018 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern153 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern153, Fin.sum_univ_succ]
  <;> ring

private theorem cert153 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern153) (m := (1/1000000000000000))
    tensor153 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern153]

private def bern154 : Coeff :=
  ![![(1136203416519/6657199308800), (5670933101473/33285996544000), (691022911/4063232000), (86224317/507904000)],
    ![(455198214189/2662879723520), (2271951116363/13314398617600), (276845141/1625292800), (34544127/203161600)],
    ![(569893827213/3328599654400), (2844411240171/16642998272000), (346601397/2031616000), (43248159/253952000)]]

private theorem tensor154 (u v : ℝ) :
    eval poly019 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern154 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern154, Fin.sum_univ_succ]
  <;> ring

private theorem cert154 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern154) (m := (1/1000000000000000))
    tensor154 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern154]

private def bern155 : Coeff :=
  ![![(15968592569869/166429982720000), (143757708233767/1497869844480000), (280855166989/2925527040000), (731596603/7618560000)],
    ![(6354512356207/66571993088000), (11441410523561/119829587558400), (111764450671/1170210816000), (291135913/3047424000)],
    ![(7901984605583/83214991360000), (2294799271859/24159191040000), (138983543183/1462763520000), (362041481/3809280000)]]

private theorem tensor155 (u v : ℝ) :
    eval poly020 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern155 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern155, Fin.sum_univ_succ]
  <;> ring

private theorem cert155 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern155) (m := (1/1000000000000000))
    tensor155 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern155]

private def bern156 : Coeff :=
  ![![(24057371061299783/91629691286323200), (89958059850019247/343611342323712000), (25432014999467/97420050432000), (818898824833/3145855795200)],
    ![(1927401464129929/7330375302905856), (7207168550985121/27488907385896960), (63163712250811/241601725071360), (1773185987/6801850368)],
    ![(12063832770974221/45814845643161600), (1455179902009819/5542118424576000), (395350170643399/1510010781696000), (410649106571/1572927897600)]]

private theorem tensor156 (u v : ℝ) :
    eval poly021 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern156 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern156, Fin.sum_univ_succ]
  <;> ring

private theorem cert156 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern156) (m := (1/1000000000000000))
    tensor156 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern156]

private def bern157 : Coeff :=
  ![![(328928613486329/619119535718400), (14784542136186007/27860379107328000), (14421202392293/27207401472000), (15004572497/28341043200)],
    ![(26262055157047/49529562857472), (1180415582995001/2228830328586240), (1151406101899/2176592117760), (1197983071/2267283456)],
    ![(163811382719923/309559767859200), (7362923719344509/13930189553664000), (7181975077591/13603700736000), (7472502139/14170521600)]]

private theorem tensor157 (u v : ℝ) :
    eval poly022 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern157 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern157, Fin.sum_univ_succ]
  <;> ring

private theorem cert157 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern157) (m := (1/1000000000000000))
    tensor157 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern157]

private def bern158 : Coeff :=
  ![![(54883211386457659313/1981182514298880000000), (257264870938809193/9286793035776000000), (11305612085997749/408111022080000000), (11776743398701/425115648000000)],
    ![(22099198911360127739/792473005719552000000), (517938675701620847/18573586071552000000), (4552110255651239/163244408832000000), (4741707461071/170046259200000)],
    ![(27806391585171489691/990591257149440000000), (130336902381405827/4643396517888000000), (5727469596129223/204055511040000000), (192448288817/6856704000000)]]

private theorem tensor158 (u v : ℝ) :
    eval poly023 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern158 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern158, Fin.sum_univ_succ]
  <;> ring

private theorem cert158 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern158) (m := (1/1000000000000000))
    tensor158 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern158]

private def bern159 : Coeff :=
  ![![(717561197330332131527/33019708571648000000000), (30153543844044279173/1393018955366400000000), (219983227106074919/10202775552000000000), (456491273878187/21255782400000000)],
    ![(284040671366257108781/13207883428659200000000), (59679415228692865267/2786037910732800000000), (87076370296300109/4081110220800000000), (180691502208377/8502312960000000)],
    ![(351321079750476706189/16509854285824000000000), (14762935692324293047/696509477683200000000), (107699312187712813/5101387776000000000), (7209132857479/342835200000000)]]

private theorem tensor159 (u v : ℝ) :
    eval poly024 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern159 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern159, Fin.sum_univ_succ]
  <;> ring

private theorem cert159 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern159) (m := (1/1000000000000000))
    tensor159 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern159]

private def bern160 : Coeff :=
  ![![(68426435203314542381/17042430230528000000000), (25475749786763251427/6390911336448000000000), (592773642617819783/149786984448000000000), (766225916954273/195035136000000000)],
    ![(33626670787957318127/8521215115264000000000), (12518418401916100289/3195455668224000000000), (291254975120886221/74893492224000000000), (376446030632171/97517568000000000)],
    ![(16518041448077207109/4260607557632000000000), (2049575094668380441/532575944704000000000), (47681300318160709/12482248704000000000), (61622204610739/16252928000000000)]]

private theorem tensor160 (u v : ℝ) :
    eval poly025 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern160 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern160, Fin.sum_univ_succ]
  <;> ring

private theorem cert160 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern160) (m := (1/1000000000000000))
    tensor160 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern160]

private def bern161 : Coeff :=
  ![![(4138619503117217/9286793035776000), (4133902558127243/9286793035776000), (896091682831/2015363072000), (62934619937/141705216000)],
    ![(1652161717062731/3714717214310400), (1650278684368409/3714717214310400), (214635103171/483687137280), (25123877579/56682086400)],
    ![(2061094541098219/4643396517888000), (2058745431857401/4643396517888000), (1338801265391/3023044608000), (31342383979/70852608000)]]

private theorem tensor161 (u v : ℝ) :
    eval poly026 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern161 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern161, Fin.sum_univ_succ]
  <;> ring

private theorem cert161 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern161) (m := (1/1000000000000000))
    tensor161 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern161]

private def bern162 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor162 (u v : ℝ) :
    eval poly027 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern162 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern162, Fin.sum_univ_succ]
  <;> ring

private theorem cert162 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern162) (m := (1/1000000000000000))
    tensor162 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern162]

private def bern163 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor163 (u v : ℝ) :
    eval poly028 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern163 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern163, Fin.sum_univ_succ]
  <;> ring

private theorem cert163 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern163) (m := (1/1000000000000000))
    tensor163 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern163]

private def bern164 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor164 (u v : ℝ) :
    eval poly029 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern164 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern164, Fin.sum_univ_succ]
  <;> ring

private theorem cert164 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern164) (m := (1/1000000000000000))
    tensor164 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern164]

private def bern165 : Coeff :=
  ![![(46913/23808), (70273/35712), (140353/71424), (365/186)],
    ![(46913/23808), (70273/35712), (140353/71424), (365/186)],
    ![(46913/23808), (70273/35712), (140353/71424), (365/186)]]

private theorem tensor165 (u v : ℝ) :
    eval poly015 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern165 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern165, Fin.sum_univ_succ]
  <;> ring

private theorem cert165 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern165) (m := (1/1000000000000000))
    tensor165 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern165]

private def bern166 : Coeff :=
  ![![(8729/5952), (13081/8928), (26137/17856), (136/93)],
    ![(8729/5952), (13081/8928), (26137/17856), (136/93)],
    ![(8729/5952), (13081/8928), (26137/17856), (136/93)]]

private theorem tensor166 (u v : ℝ) :
    eval poly016 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern166 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern166, Fin.sum_univ_succ]
  <;> ring

private theorem cert166 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern166) (m := (1/1000000000000000))
    tensor166 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern166]

private def bern167 : Coeff :=
  ![![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)],
    ![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)],
    ![(11638709/15872000), (5813799/7936000), (11616487/15872000), (90667/124000)]]

private theorem tensor167 (u v : ℝ) :
    eval poly017 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern167 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern167, Fin.sum_univ_succ]
  <;> ring

private theorem cert167 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern167) (m := (1/1000000000000000))
    tensor167 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern167]

private def bern168 : Coeff :=
  ![![(5001110399/4680843264), (14972279615/14042529792), (233457247/219414528), (19571/18432)],
    ![(9985333279/9361686528), (29893900255/28085059584), (466123007/438829056), (1211341/1142784)],
    ![(155756965/146276352), (466300645/438829056), (7270805/6856704), (18895/17856)]]

private theorem tensor168 (u v : ℝ) :
    eval poly018 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern168 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern168, Fin.sum_univ_succ]
  <;> ring

private theorem cert168 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern168) (m := (1/1000000000000000))
    tensor168 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern168]

private def bern169 : Coeff :=
  ![![(716164680897/4160749568000), (713630433003/4160749568000), (173608761/1015808000), (43248159/253952000)],
    ![(1436833542177/8321499136000), (1431749107723/8321499136000), (348309401/2031616000), (86768319/507904000)],
    ![(4504180383/26004684800), (4488241717/26004684800), (1091879/6348800), (272001/1587200)]]

private theorem tensor169 (u v : ℝ) :
    eval poly019 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern169 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern169, Fin.sum_univ_succ]
  <;> ring

private theorem cert169 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern169) (m := (1/1000000000000000))
    tensor169 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern169]

private def bern170 : Coeff :=
  ![![(5921229636013/62411243520000), (3554853238409/37446746112000), (69471578831/731381760000), (362041481/3809280000)],
    ![(11718627352973/124822487040000), (281422126417/2995739688960), (137497696111/1462763520000), (716569321/7618560000)],
    ![(36233735731/390070272000), (108771872563/1170210816000), (13714943/147456000), (2215799/23808000)]]

private theorem tensor170 (u v : ℝ) :
    eval poly020 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern170 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern170, Fin.sum_univ_succ]
  <;> ring

private theorem cert170 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern170) (m := (1/1000000000000000))
    tensor170 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern170]

private def bern171 : Coeff :=
  ![![(68439914490608879/257708506742784000), (20415548470557577/77312552022835200), (198238599489319/755005390848000), (410649106571/1572927897600)],
    ![(137277536821849999/515417013485568000), (40949947942620137/154625104045670400), (397633368893639/1510010781696000), (823697601451/3145855795200)],
    ![(430235139570257/1610678167142400), (4139999893561/15587208069120), (1246217308777/4718783692800), (2581553093/9830799360)]]

private theorem tensor171 (u v : ℝ) :
    eval poly021 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern171 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern171, Fin.sum_univ_succ]
  <;> ring

private theorem cert171 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern171) (m := (1/1000000000000000))
    tensor171 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern171]

private def bern172 : Coeff :=
  ![![(616441626752893/1160849129472000), (369004673114393/696509477683200), (3595174050871/6801850368000), (7472502139/14170521600)],
    ![(1227969192707933/2321698258944000), (735067767789433/1393018955366400), (7161688609751/13603700736000), (14885436059/28341043200)],
    ![(3822047287219/7255307059200), (2287894341719/4353184235520), (22290715993/42511564800), (46330837/88565760)]]

private theorem tensor172 (u v : ℝ) :
    eval poly022 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern172 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern172, Fin.sum_univ_succ]
  <;> ring

private theorem cert172 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern172) (m := (1/1000000000000000))
    tensor172 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern172]

private def bern173 : Coeff :=
  ![![(31286487315397942963/1114415164293120000000), (1466410575976581383/52238210826240000000), (2863839058532263/102027755520000000), (192448288817/6856704000000)],
    ![(63401630683450573523/2228830328586240000000), (2971417430056849063/104476421652480000000), (5802580979507783/204055511040000000), (12086844414607/425115648000000)],
    ![(200719646050328941/6965094776832000000), (9406292838001673/326488817664000000), (18367137006097/637673472000000), (38255921633/1328486400000)]]

private theorem tensor173 (u v : ℝ) :
    eval poly023 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern173 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern173, Fin.sum_univ_succ]
  <;> ring

private theorem cert173 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern173) (m := (1/1000000000000000))
    tensor173 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern173]

private def bern174 : Coeff :=
  ![![(1199737839415092169631/55720758214656000000000), (55799055247103764921/2611910541312000000000), (54063363728069053/2550693888000000000), (7209132857479/342835200000000)],
    ![(2348709318390652300351/111441516429312000000000), (109231416972689069081/5223821082624000000000), (105828133536966173/5101387776000000000), (437441200449209/21255782400000000)],
    ![(7181071743597250817/348254738841600000000), (333952260784908151/16324440883200000000), (323529811305607/15941836800000000), (1337238011671/66424320000000)]]

private theorem tensor174 (u v : ℝ) :
    eval poly024 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern174 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern174, Fin.sum_univ_succ]
  <;> ring

private theorem cert174 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern174) (m := (1/1000000000000000))
    tensor174 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern174]

private def bern175 : Coeff :=
  ![![(2110316792821087769/532575944704000000000), (311989228758818447/79886391705600000000), (24018373747636933/6241124352000000000), (61622204610739/16252928000000000)],
    ![(38174809345744661/9985798963200000000), (909951462712849/241591910400000000), (434160402316249/117021081600000000), (1113461317903/304742400000000)],
    ![(229763023356811/62411243520000000), (169710972194177/46808432640000000), (2610968185343/731381760000000), (6693330377/1904640000000)]]

private theorem tensor175 (u v : ℝ) :
    eval poly025 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern175 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern175, Fin.sum_univ_succ]
  <;> ring

private theorem cert175 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern175) (m := (1/1000000000000000))
    tensor175 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern175]

private def bern176 : Coeff :=
  ![![(517037282973163/1160849129472000), (515860307328761/1160849129472000), (2010491221517/4534566912000), (31342383979/70852608000)],
    ![(1029952901359883/2321698258944000), (1027608332625241/2321698258944000), (4004955416557/9069133824000), (62434915979/141705216000)],
    ![(3205722614917/7255307059200), (3198425158103/7255307059200), (12465401219/28341043200), (7773133/17713152)]]

private theorem tensor176 (u v : ℝ) :
    eval poly026 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern176 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern176, Fin.sum_univ_succ]
  <;> ring

private theorem cert176 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern176) (m := (1/1000000000000000))
    tensor176 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern176]

private def bern177 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor177 (u v : ℝ) :
    eval poly027 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern177 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern177, Fin.sum_univ_succ]
  <;> ring

private theorem cert177 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern177) (m := (1/1000000000000000))
    tensor177 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern177]

private def bern178 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor178 (u v : ℝ) :
    eval poly028 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern178 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern178, Fin.sum_univ_succ]
  <;> ring

private theorem cert178 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern178) (m := (1/1000000000000000))
    tensor178 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern178]

private def bern179 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor179 (u v : ℝ) :
    eval poly029 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern179 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern179, Fin.sum_univ_succ]
  <;> ring

private theorem cert179 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern179) (m := (1/1000000000000000))
    tensor179 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern179]

private def bern180 : Coeff :=
  ![![(2011/992), (8953/4464), (17713/8928), (365/186)],
    ![(2011/992), (8953/4464), (17713/8928), (365/186)],
    ![(2011/992), (8953/4464), (17713/8928), (365/186)]]

private theorem tensor180 (u v : ℝ) :
    eval poly015 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern180 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern180, Fin.sum_univ_succ]
  <;> ring

private theorem cert180 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern180) (m := (1/1000000000000000))
    tensor180 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern180]

private def bern181 : Coeff :=
  ![![(371/248), (1657/1116), (3289/2232), (136/93)],
    ![(371/248), (1657/1116), (3289/2232), (136/93)],
    ![(371/248), (1657/1116), (3289/2232), (136/93)]]

private theorem tensor181 (u v : ℝ) :
    eval poly016 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern181 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern181, Fin.sum_univ_succ]
  <;> ring

private theorem cert181 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern181) (m := (1/1000000000000000))
    tensor181 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern181]

private def bern182 : Coeff :=
  ![![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)],
    ![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)],
    ![(296801/396800), (736447/992000), (1461783/1984000), (90667/124000)]]

private theorem tensor182 (u v : ℝ) :
    eval poly017 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern182 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern182, Fin.sum_univ_succ]
  <;> ring

private theorem cert182 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern182) (m := (1/1000000000000000))
    tensor182 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern182]

private def bern183 : Coeff :=
  ![![(846895/761856), (7498805/6856704), (922085/857088), (18895/17856)],
    ![(6687131/6094848), (59198233/54853632), (7277689/6856704), (149099/142848)],
    ![(3299551/3047424), (29203013/27426816), (3589349/3428352), (73519/71424)]]

private theorem tensor183 (u v : ℝ) :
    eval poly018 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern183 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern183, Fin.sum_univ_succ]
  <;> ring

private theorem cert183 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern183) (m := (1/1000000000000000))
    tensor183 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern183]

private def bern184 : Coeff :=
  ![![(15136851/81264640), (73633589/406323200), (279751/1587200), (272001/1587200)],
    ![(620610891/3250585600), (3018977149/16252928000), (11469791/63488000), (11152041/63488000)],
    ![(317873871/1625292800), (1546305369/8126464000), (5874771/31744000), (5712021/31744000)]]

private theorem tensor184 (u v : ℝ) :
    eval poly019 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern184 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern184, Fin.sum_univ_succ]
  <;> ring

private theorem cert184 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern184) (m := (1/1000000000000000))
    tensor184 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern184]

private def bern185 : Coeff :=
  ![![(185949553/2031616000), (1683692147/18284544000), (52909001/571392000), (2215799/23808000)],
    ![(6766248217/81264640000), (61394540651/731381760000), (1933190177/22855680000), (81118319/952320000)],
    ![(3047257157/40632320000), (27720697711/365690880000), (875010157/11427840000), (36802339/476160000)]]

private theorem tensor185 (u v : ℝ) :
    eval poly020 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern185 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern185, Fin.sum_univ_succ]
  <;> ring

private theorem cert185 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern185) (m := (1/1000000000000000))
    tensor185 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern185]

private def bern186 : Coeff :=
  ![![(27948771417/93210542080), (3611434938881/12583423180800), (161965009717/589847961600), (2581553093/9830799360)],
    ![(1142896931601/3728421683200), (3992503248389/13603700736000), (6627027213901/23593918464000), (105661512029/393231974400)],
    ![(583921503261/1864210841600), (75493921412773/251668463616000), (3387727019561/11796959232000), (1460282437/5313945600)]]

private theorem tensor186 (u v : ℝ) :
    eval poly021 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern186 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern186, Fin.sum_univ_succ]
  <;> ring

private theorem cert186 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern186) (m := (1/1000000000000000))
    tensor186 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern186]

private def bern187 : Coeff :=
  ![![(4178067677/7557611520), (184600468787/340092518400), (2831764453/5313945600), (46330837/88565760)],
    ![(161750905781/302304460800), (7146675291611/13603700736000), (109629738109/212557824000), (1793665261/3542630400)],
    ![(78189552241/151152230400), (3454665915871/6801850368000), (52994449049/106278912000), (867048521/1771315200)]]

private theorem tensor187 (u v : ℝ) :
    eval poly022 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern187 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern187, Fin.sum_univ_succ]
  <;> ring

private theorem cert187 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern187) (m := (1/1000000000000000))
    tensor187 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern187]

private def bern188 : Coeff :=
  ![![(14627468932527/503840768000000), (49190765001347/1700462592000000), (2299649920237/79709184000000), (38255921633/1328486400000)],
    ![(653265117716103/20153630720000000), (14108620927153/438829056000000), (101767645912477/3188367360000000), (1685287373273/53139456000000)],
    ![(360715739065563/10076815360000000), (48120837747271/1360370073600000), (55774647507737/1594183680000000), (920168940613/26569728000000)]]

private theorem tensor188 (u v : ℝ) :
    eval poly023 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern188 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern188, Fin.sum_univ_succ]
  <;> ring

private theorem cert188 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern188) (m := (1/1000000000000000))
    tensor188 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern188]

private def bern189 : Coeff :=
  ![![(1818793173360497/75576115200000000), (71623990139207/3149004800000000), (42709828854697/1992729600000000), (1337238011671/66424320000000)],
    ![(60441196952737433/3023044608000000000), (45930131777879/2437939200000000), (1410056945058637/79709184000000000), (43964483752351/2656972800000000)],
    ![(24065333485527493/1511522304000000000), (112869240688753/7557611520000000), (555860367964697/39854592000000000), (17219723518931/1328486400000000)]]

private theorem tensor189 (u v : ℝ) :
    eval poly024 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern189 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern189, Fin.sum_univ_succ]
  <;> ring

private theorem cert189 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern189) (m := (1/1000000000000000))
    tensor189 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern189]

private def bern190 : Coeff :=
  ![![(394931045677/81264640000000), (1074746603131/243793920000000), (11677715441/2949120000000), (6693330377/1904640000000)],
    ![(1175965007213/325058560000000), (15648241116487/4875878400000000), (5124252659939/1828454400000000), (91338149957/38092800000000)],
    ![(72788060371173/32505856000000000), (61087624970561/32505856000000000), (18524187974509/12189696000000000), (294814533979/253952000000000)]]

private theorem tensor190 (u v : ℝ) :
    eval poly025 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern190 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern190, Fin.sum_univ_succ]
  <;> ring

private theorem cert190 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern190) (m := (1/1000000000000000))
    tensor190 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern190]

private def bern191 : Coeff :=
  ![![(52518371749/113364172800), (51579920791/113364172800), (527671673/1180876800), (7773133/17713152)],
    ![(2033210880541/4534566912000), (1996879436479/4534566912000), (6809476123/15745024000), (7523281021/17713152000)],
    ![(982843445561/2267283456000), (965281020659/2267283456000), (9874994909/23617536000), (3636714521/8856576000)]]

private theorem tensor191 (u v : ℝ) :
    eval poly026 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern191 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern191, Fin.sum_univ_succ]
  <;> ring

private theorem cert191 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern191) (m := (1/1000000000000000))
    tensor191 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern191]

private def bern192 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor192 (u v : ℝ) :
    eval poly027 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern192 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern192, Fin.sum_univ_succ]
  <;> ring

private theorem cert192 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern192) (m := (1/1000000000000000))
    tensor192 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern192]

private def bern193 : Coeff :=
  ![![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)],
    ![(3298047/125000000), (3298047/125000000), (3298047/125000000), (3298047/125000000)]]

private theorem tensor193 (u v : ℝ) :
    eval poly028 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern193 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern193, Fin.sum_univ_succ]
  <;> ring

private theorem cert193 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern193) (m := (1/1000000000000000))
    tensor193 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern193]

private def bern194 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor194 (u v : ℝ) :
    eval poly029 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern194 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern194, Fin.sum_univ_succ]
  <;> ring

private theorem cert194 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern194) (m := (1/1000000000000000))
    tensor194 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern194]

private def bern195 : Coeff :=
  ![![(1527287/804288), (2276647/1206432), (4524727/2412864), (46835/25134)],
    ![(1527287/804288), (2276647/1206432), (4524727/2412864), (46835/25134)],
    ![(1527287/804288), (2276647/1206432), (4524727/2412864), (46835/25134)]]

private theorem tensor195 (u v : ℝ) :
    eval poly030 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern195 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly030, bern195, Fin.sum_univ_succ]
  <;> ring

private theorem cert195 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly030 δ p := by
  apply positive_on_box_from_tensor (β := bern195) (m := (1/1000000000000000))
    tensor195 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern195]

private def bern196 : Coeff :=
  ![![(17384/12567), (51902/37701), (51652/37701), (17134/12567)],
    ![(17384/12567), (51902/37701), (51652/37701), (17134/12567)],
    ![(17384/12567), (51902/37701), (51652/37701), (17134/12567)]]

private theorem tensor196 (u v : ℝ) :
    eval poly031 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern196 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly031, bern196, Fin.sum_univ_succ]
  <;> ring

private theorem cert196 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly031 δ p := by
  apply positive_on_box_from_tensor (β := bern196) (m := (1/1000000000000000))
    tensor196 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern196]

private def bern197 : Coeff :=
  ![![(168428854331509/240193402768800), (251485788780533/360290104153200), (100131318425521/144116041661280), (5191058403064/7506043836525)],
    ![(168428854331509/240193402768800), (251485788780533/360290104153200), (100131318425521/144116041661280), (5191058403064/7506043836525)],
    ![(168428854331509/240193402768800), (251485788780533/360290104153200), (100131318425521/144116041661280), (5191058403064/7506043836525)]]

private theorem tensor197 (u v : ℝ) :
    eval poly032 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern197 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly032, bern197, Fin.sum_univ_succ]
  <;> ring

private theorem cert197 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly032 δ p := by
  apply positive_on_box_from_tensor (β := bern197) (m := (1/1000000000000000))
    tensor197 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern197]

private def bern198 : Coeff :=
  ![![(308498605/308846592), (114613589/115817472), (908368859/926539776), (9373711/9651456)],
    ![(1225411885/1235386368), (455239205/463269888), (3607782875/3706159104), (37227535/38605824)],
    ![(608414675/617693184), (226012027/231634944), (1791045157/1853079552), (18480113/19302912)]]

private theorem tensor198 (u v : ℝ) :
    eval poly033 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern198 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly033, bern198, Fin.sum_univ_succ]
  <;> ring

private theorem cert198 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly033 δ p := by
  apply positive_on_box_from_tensor (β := bern198) (m := (1/1000000000000000))
    tensor198 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern198]

private def bern199 : Coeff :=
  ![![(12969021783526193/72876457610444800), (115007432436285683/655888118494003200), (1180311184571561/6832167900979200), (4542176102681/26688155863200)],
    ![(31496195759992183/174903498265067520), (279303764488122373/1574131484385607680), (2866470019673791/16397202962350080), (11030999106511/64051574071680)],
    ![(79666848098803757/437258745662668800), (706474227822897767/3935328710964019200), (7250482990939589/40993007405875200), (27901938916469/160128935179200)]]

private theorem tensor199 (u v : ℝ) :
    eval poly034 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern199 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly034, bern199, Fin.sum_univ_succ]
  <;> ring

private theorem cert199 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly034 δ p := by
  apply positive_on_box_from_tensor (β := bern199) (m := (1/1000000000000000))
    tensor199 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern199]

private def bern200 : Coeff :=
  ![![(78334277179305287/1093146864156672000), (1179881424898056629/16397202962350080000), (592276267381218889/8198601481175040000), (6192851496264181/85402098762240000)],
    ![(296482197527751559/4372587456626688000), (2681315381022074003/39353287109640192000), (17958764014486717/262355247397601280), (14092903339596691/204965037029376000)],
    ![(9320909544609399/145752915220889600), (6327288355722030241/98383217774100480000), (353430989016133949/5465734320783360000), (33307407720398369/512412592573440000)]]

private theorem tensor200 (u v : ℝ) :
    eval poly035 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern200 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly035, bern200, Fin.sum_univ_succ]
  <;> ring

private theorem cert200 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly035 δ p := by
  apply positive_on_box_from_tensor (β := bern200) (m := (1/1000000000000000))
    tensor200 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern200]

private def bern201 : Coeff :=
  ![![(361547130811444612414537/1372383906521504012697600), (529515414359270428407523/2058575859782256019046400), (64620229061683677316889/257321982472782002380800), (131420759906044014589/536087463484962504960)],
    ![(292323351043145744046581/1097907125217203210158080), (428161502923429540520999/1646860687825804815237120), (52255125138850594804357/205857585978225601904640), (106281274675028482457/428869970787970003968)],
    ![(738522493592839495403831/2744767813043008025395200), (1081776685898606845789949/4117151719564512038092800), (132035167570885619388007/514643964945564004761600), (268564853563054383107/1072174926969925009920)]]

private theorem tensor201 (u v : ℝ) :
    eval poly036 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern201 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly036, bern201, Fin.sum_univ_succ]
  <;> ring

private theorem cert201 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly036 δ p := by
  apply positive_on_box_from_tensor (β := bern201) (m := (1/1000000000000000))
    tensor201 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern201]

private def bern202 : Coeff :=
  ![![(33698335153548367576873/74182913866027243929600), (100001528255283366334409/222548741598081731788800), (3091147323958268939653/6954648174940054118400), (796228546507070491/1811106295557305760)],
    ![(26495637563476960766549/59346331092821795143680), (78627155803772417804917/178038993278465385431040), (2430444079142761074689/5563718539952043294720), (626042292291818783/1448885036445844608)],
    ![(65081517510288068678999/148365827732054487859200), (193132722508295356355767/445097483196163463577600), (5969925747797267494139/13909296349880108236800), (1537754368444952933/3622212591114611520)]]

private theorem tensor202 (u v : ℝ) :
    eval poly037 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern202 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly037, bern202, Fin.sum_univ_succ]
  <;> ring

private theorem cert202 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly037 δ p := by
  apply positive_on_box_from_tensor (β := bern202) (m := (1/1000000000000000))
    tensor202 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern202]

private def bern203 : Coeff :=
  ![![(12289528696538679629413471/9092610336925679616000000000), (13180782201146767352885289263/8046960148179226460160000000000), (242087412767042055947003807/125733752315300413440000000000), (1159616923168486726111859/523890634647085056000000000)],
    ![(6593735654781037789961851493/2145856039514460389376000000000), (21369324991508514636425957539/6437568118543381168128000000000), (27605819553170938804969183/7737461680941563904000000000), (1599932720146228826754583/419112507717668044800000000)],
    ![(1028714253717894718738212383/214585603951446038937600000000), (80485060555249038476359209169/16093920296358452920320000000000), (1310203445422026910428989281/251467504630600826880000000000), (5680429754394170681549197/1047781269294170112000000000)]]

private theorem tensor203 (u v : ℝ) :
    eval poly038 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern203 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly038, bern203, Fin.sum_univ_succ]
  <;> ring

private theorem cert203 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly038 δ p := by
  apply positive_on_box_from_tensor (β := bern203) (m := (1/1000000000000000))
    tensor203 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern203]

private def bern204 : Coeff :=
  ![![(6657183463603316369065459633/593463310928217951436800000000), (95572580563560547317943305211/8901949663923269271552000000000), (1426615605737828793152785579/139092963498801082368000000000), (5667523011060345283153423/579554014578337843200000000)],
    ![(22335382097828636467540073521/2373853243712871805747200000000), (63865199557568813545426896383/7121559731138615417241600000000), (948948041583717707231610863/111274370799040865894400000000), (3750713357962751296629251/463643211662670274560000000)],
    ![(1804203034124400745881830851/237385324371287180574720000000), (2172556553571575815105896127/301761005556720992256000000000), (145500692034071611527114089/21398917461354012672000000000), (7418520767693065916839409/1159108029156675686400000000)]]

private theorem tensor204 (u v : ℝ) :
    eval poly039 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern204 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly039, bern204, Fin.sum_univ_succ]
  <;> ring

private theorem cert204 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly039 δ p := by
  apply positive_on_box_from_tensor (β := bern204) (m := (1/1000000000000000))
    tensor204 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern204]

private def bern205 : Coeff :=
  ![![(1525834293329341596923/874517491325337600000000), (123932769940277507435261/78706574219280384000000000), (36861813395027939757859/26235524739760128000000000), (1013431188267298864133/819860148117504000000000)],
    ![(457274398660151673067/403623457534771200000000), (35396926851095348133133/36326111178129408000000000), (9884580914575183240787/12108703726043136000000000), (249251239940193537109/378396991438848000000000)],
    ![(1030424266052237252669/2098841979180810240000000), (325609917803395124095927/944478890631364608000000000), (62579845374549138980393/314826296877121536000000000), (522489365072918514511/9838321777410048000000000)]]

private theorem tensor205 (u v : ℝ) :
    eval poly040 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern205 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly040, bern205, Fin.sum_univ_succ]
  <;> ring

private theorem cert205 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly040 δ p := by
  apply positive_on_box_from_tensor (β := bern205) (m := (1/1000000000000000))
    tensor205 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern205]

private def bern206 : Coeff :=
  ![![(27799243867564105529719/74182913866027243929600), (6345741340868388443219/17119133969083210137600), (254999544918256638511/695464817494005411840), (26273887509880058683/72444251822292230400)],
    ![(21848497768129358525003/59346331092821795143680), (12967193536328395122383/35607798655693077086208), (1002077633715761176111/2781859269976021647360), (20649901019820408383/57955401457833784320)],
    ![(53644001105518581565577/148365827732054487859200), (159190563545631778535881/445097483196163463577600), (492078543879247899089/1390929634988010823680), (50701730079341924549/144888503644584460800)]]

private theorem tensor206 (u v : ℝ) :
    eval poly041 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern206 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly041, bern206, Fin.sum_univ_succ]
  <;> ring

private theorem cert206 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly041 δ p := by
  apply positive_on_box_from_tensor (β := bern206) (m := (1/1000000000000000))
    tensor206 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern206]

private def bern207 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor207 (u v : ℝ) :
    eval poly042 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern207 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly042, bern207, Fin.sum_univ_succ]
  <;> ring

private theorem cert207 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly042 δ p := by
  apply positive_on_box_from_tensor (β := bern207) (m := (1/1000000000000000))
    tensor207 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern207]

private def bern208 : Coeff :=
  ![![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)],
    ![(14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000), (14355311686773899/955651320000000000)]]

private theorem tensor208 (u v : ℝ) :
    eval poly043 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern208 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly043, bern208, Fin.sum_univ_succ]
  <;> ring

private theorem cert208 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly043 δ p := by
  apply positive_on_box_from_tensor (β := bern208) (m := (1/1000000000000000))
    tensor208 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern208]

private def bern209 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor209 (u v : ℝ) :
    eval poly044 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern209 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly044, bern209, Fin.sum_univ_succ]
  <;> ring

private theorem cert209 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly044 δ p := by
  apply positive_on_box_from_tensor (β := bern209) (m := (1/1000000000000000))
    tensor209 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern209]

private def bern210 : Coeff :=
  ![![(52880257015715041/27930282273260032), (237779329571870243/125686270229670144), (475195005146045603/251372540459340288), (618269988474415/327307995389766)],
    ![(52880257015715041/27930282273260032), (237779329571870243/125686270229670144), (475195005146045603/251372540459340288), (618269988474415/327307995389766)],
    ![(52880257015715041/27930282273260032), (237779329571870243/125686270229670144), (475195005146045603/251372540459340288), (618269988474415/327307995389766)]]

private theorem tensor210 (u v : ℝ) :
    eval poly045 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern210 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly045, bern210, Fin.sum_univ_succ]
  <;> ring

private theorem cert210 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly045 δ p := by
  apply positive_on_box_from_tensor (β := bern210) (m := (1/1000000000000000))
    tensor210 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern210]

private def bern211 : Coeff :=
  ![![(75899540129922/54551332564961), (682705236169298/490961993084649), (682314611169298/490961993084649), (227307995389766/163653997694883)],
    ![(75899540129922/54551332564961), (682705236169298/490961993084649), (682314611169298/490961993084649), (227307995389766/163653997694883)],
    ![(75899540129922/54551332564961), (682705236169298/490961993084649), (682314611169298/490961993084649), (227307995389766/163653997694883)]]

private theorem tensor211 (u v : ℝ) :
    eval poly046 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern211 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly046, bern211, Fin.sum_univ_succ]
  <;> ring

private theorem cert211 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly046 δ p := by
  apply positive_on_box_from_tensor (β := bern211) (m := (1/1000000000000000))
    tensor211 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern211]

private def bern212 : Coeff :=
  ![![(9853732315252231/13965141136630016), (44317610660862229/62843135114835072), (88586851806178837/125686270229670144), (115284482149262/163653997694883)],
    ![(9853732315252231/13965141136630016), (44317610660862229/62843135114835072), (88586851806178837/125686270229670144), (115284482149262/163653997694883)],
    ![(9853732315252231/13965141136630016), (44317610660862229/62843135114835072), (88586851806178837/125686270229670144), (115284482149262/163653997694883)]]

private theorem tensor212 (u v : ℝ) :
    eval poly047 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern212 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly047, bern212, Fin.sum_univ_succ]
  <;> ring

private theorem cert212 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly047 δ p := by
  apply positive_on_box_from_tensor (β := bern212) (m := (1/1000000000000000))
    tensor212 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern212]

private def bern213 : Coeff :=
  ![![(20927597386757817571/21450456785863704576), (94064700740718856649/96527055536386670592), (187910577653930068457/193054111072773341184), (244390501299866437/251372540459340288)],
    ![(334541191511304155353/343207308573819273216), (1503683721847192913387/1544432888582186729472), (3003866586052659255371/3088865777164373458944), (3906729362860101151/4021960647349444608)],
    ![(167120412417241614785/171603654286909636608), (751166115921442060195/772216444291093364736), (1500581964821218707715/1544432888582186729472), (1951605352461169655/2010980323674722304)]]

private theorem tensor213 (u v : ℝ) :
    eval poly048 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern213 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly048, bern213, Fin.sum_univ_succ]
  <;> ring

private theorem cert213 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly048 δ p := by
  apply positive_on_box_from_tensor (β := bern213) (m := (1/1000000000000000))
    tensor213 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern213]

private def bern214 : Coeff :=
  ![![(326680787447557214343/1830438979060369457152), (978236699357709447559/5491316937181108371456), (1271397286799369419/7150152261954568192), (2478616366209133/13965141136630016)],
    ![(5234489826775974899589/29287023664965911314432), (15674536880406088589957/87861070994897733943296), (20371923967552686737/114402436191273091072), (39715504100420759/223442258186080256)],
    ![(2621043527195517184845/14643511832482955657216), (2616214428514804336495/14643511832482955657216), (10200745673157731385/57201218095636545536), (19886573170747695/111721129093040128)]]

private theorem tensor214 (u v : ℝ) :
    eval poly049 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern214 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly049, bern214, Fin.sum_univ_succ]
  <;> ring

private theorem cert214 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly049 δ p := by
  apply positive_on_box_from_tensor (β := bern214) (m := (1/1000000000000000))
    tensor214 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern214]

private def bern215 : Coeff :=
  ![![(74747525815984933621913/1144024361912730910720000), (673194851648896628662619/10296219257214578196480000), (42103755373780499314681/643513703575911137280000), (54860305610240762021/837908468197800960000)],
    ![(1187208858727677470301659/18304389790603694571520000), (10692436638797358193074497/164739508115433251143680000), (668747709102123353394043/10296219257214578196480000), (871375313237218718783/13406535491164815360000)],
    ![(117845730439959600265271/1830438979060369457152000), (1061375565121237032754709/16473950811543325114368000), (66383533222375871775319/1029621925721457819648000), (86498573671058524523/1340653549116481536000)]]

private theorem tensor215 (u v : ℝ) :
    eval poly050 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern215 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly050, bern215, Fin.sum_univ_succ]
  <;> ring

private theorem cert215 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly050 δ p := by
  apply positive_on_box_from_tensor (β := bern215) (m := (1/1000000000000000))
    tensor215 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern215]

private def bern216 : Coeff :=
  ![![(478146752036886156749939614219237141/1847278381501913119450652433901944832), (12871541412631654084372969281253264285/49876516300551654225167615715352510464), (300778452171429769080193192696283621/1168980850794179395902365993328574464), (390471794208803589833380030840955/1522110482804921088414539053813248)],
    ![(7660736589314790617672871757434300943/29556454104030609911210438942431117312), (206224572678207789553680702260505803815/798024260808826467602681851445640167424), (4819002045955672952882234478064460543/18703693612706870334437855893257191424), (6256055562627230619798165628735265/24353767724878737414632624861011968)],
    ![(3835562573019701363673354843680403815/14778227052015304955605219471215558656), (103252241377154556878696948010479689535/399012130404413233801340925722820083712), (2412774428584234800240688936494191575/9351846806353435167218927946628595712), (3132281208956801901131125382007625/12176883862439368707316312430505984)]]

private theorem tensor216 (u v : ℝ) :
    eval poly051 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern216 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly051, bern216, Fin.sum_univ_succ]
  <;> ring

private theorem cert216 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly051 δ p := by
  apply positive_on_box_from_tensor (β := bern216) (m := (1/1000000000000000))
    tensor216 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern216]

private def bern217 : Coeff :=
  ![![(131830178040832485017466926083137163/299558656459769695046051746038153216), (131657543728021818099076851251124185/299558656459769695046051746038153216), (13867566423523155658339002631170353/31594077048491335024388270089961472), (9016532334387444496283813663845/20569060578444879573169446673152)],
    ![(2104593237576768407057505590710636369/4792938503356315120736827936610451456), (2101837229713360171154827676692848155/4792938503356315120736827936610451456), (221387750136798520569293405641490339/505505232775861360390212321439383552), (143943771140675447907076377028735/329104969255118073170711146770432)],
    ![(1049951813250108526917770182045539065/2396469251678157560368413968305225728), (1048576879889185626362212866683854675/2396469251678157560368413968305225728), (110447218748613275302581384592127515/252752616387930680195106160719691776), (71811512465575891936805867717975/164552484627559036585355573385216)]]

private theorem tensor217 (u v : ℝ) :
    eval poly052 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern217 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly052, bern217, Fin.sum_univ_succ]
  <;> ring

private theorem cert217 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly052 δ p := by
  apply positive_on_box_from_tensor (β := bern217) (m := (1/1000000000000000))
    tensor217 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern217]

private def bern218 : Coeff :=
  ![![(156256922699672360158409318584984277856601/3994115419463595933947356613842042880000000), (84306537447034000947568517110333121994959/2156822326510341804331572571474703155200000), (12339055952903420438618546292575602315237/315940770484913350243882700899614720000000), (6421126555767344477388533948517658129/164552484627559036585355573385216000000)],
    ![(2511324737413170040107427158733936348047643/63905846711417534943157705821472686080000000), (6774699997635116261994280453412901126570193/172545786120827344346525805717976252416000000), (198306042190063072099078325501338749028351/5055052327758613603902123214393835520000000), (103195424971379313859419387737792889667/2632839754040944585365689174163456000000)],
    ![(252253871163158231768030522010812425038967/6390584671141753494315770582147268608000000), (3402438499753756224091539768999576246771833/86272893060413672173262902858988126208000000), (19918718913367141718025991032146786101291/505505232775861360390212321439383552000000), (10365282505048111608062223229930324927/263283975404094458536568917416345600000)]]

private theorem tensor218 (u v : ℝ) :
    eval poly053 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern218 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly053, bern218, Fin.sum_univ_succ]
  <;> ring

private theorem cert218 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly053 δ p := by
  apply positive_on_box_from_tensor (β := bern218) (m := (1/1000000000000000))
    tensor218 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern218]

private def bern219 : Coeff :=
  ![![(659217050710239989278468698315671744883959/149779328229884847523025873019076608000000000), (469203162919530254032384016789547735894733/107841116325517090216578628573735157760000000), (22645120035583261802569174816346122919173/5265679508081889170731378348326912000000000), (11656265992585747237438321895189689841/2742541410459317276422592889753600000000)],
    ![(10033385920899415159361279790676787261724437/2396469251678157560368413968305225728000000000), (35690873905698406083509765830751508684815891/8627289306041367217326290285898812620800000000), (344352628061768169421736604447579713610079/84250872129310226731702053573230592000000000), (177168275124150696918130343072750524643/43880662567349076422761486236057600000000)],
    ![(951929903043499049026706040830282660530553/239646925167815756036841396830522572800000000), (16922747388917195922214405159169599249026571/4313644653020683608663145142949406310400000000), (32638333555420415000236641183362146051339/8425087212931022673170205357323059200000000), (16783629436692943803724753582246601183/4388066256734907642276148623605760000000)]]

private theorem tensor219 (u v : ℝ) :
    eval poly054 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern219 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly054, bern219, Fin.sum_univ_succ]
  <;> ring

private theorem cert219 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly054 δ p := by
  apply positive_on_box_from_tensor (β := bern219) (m := (1/1000000000000000))
    tensor219 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern219]

private def bern220 : Coeff :=
  ![![(1047999182412549475610974387/3660877958120738914304000000000), (8821220390457729417642009281/32947901623086650228736000000000), (1026313858900583075306611213/4118487702885831278592000000000), (412319296004369039269011/1787538065488642048000000000)],
    ![(48839724292059313408061189/234296189319727290515456000000), (10021621211722655259080061007/52716642596938640365977600000000), (1131798389759043608880620483/6589580324617330045747200000000), (438761067537624284170653/2860060904781827276800000000)],
    ![(1220037312742483012818836307/9371847572789091620618240000000), (3149534882169278267529741451/28115542718367274861854720000000), (329874051307822021554502607/3514442839795909357731840000000), (346433751482672529101619/4576097447650923642880000000)]]

private theorem tensor220 (u v : ℝ) :
    eval poly055 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern220 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly055, bern220, Fin.sum_univ_succ]
  <;> ring

private theorem cert220 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly055 δ p := by
  apply positive_on_box_from_tensor (β := bern220) (m := (1/1000000000000000))
    tensor220 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern220]

private def bern221 : Coeff :=
  ![![(324260764858369888050221464930446943/898675969379309085138155238114459648), (971523437176427317027524930549527647/2696027908137927255414465714343378944), (5685152310574101842154730000681513/15797038524245667512194135044980736), (14785918671566281986256582084529/41138121156889759146338893346304)],
    ![(5176369772004001718169178382977971469/14378815510068945362210483809831354368), (15509014460816598148747449770998195981/43136446530206836086631451429494063104), (90755520610632641655120386863716619/252752616387930680195106160719691776), (236036567477510425349225218355747/658209938510236146341422293540864)],
    ![(2582283653137042613767406663534395925/7189407755034472681105241904915677184), (7736826963405179612527250326601974805/21568223265103418043315725714747031552), (45274302126039826917882546858264515/126376308193965340097553080359845888), (117749218104980169459172561679515/329104969255118073170711146770432)]]

private theorem tensor221 (u v : ℝ) :
    eval poly056 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern221 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly056, bern221, Fin.sum_univ_succ]
  <;> ring

private theorem cert221 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly056 δ p := by
  apply positive_on_box_from_tensor (β := bern221) (m := (1/1000000000000000))
    tensor221 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern221]

private def bern222 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor222 (u v : ℝ) :
    eval poly057 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern222 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly057, bern222, Fin.sum_univ_succ]
  <;> ring

private theorem cert222 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly057 δ p := by
  apply positive_on_box_from_tensor (β := bern222) (m := (1/1000000000000000))
    tensor222 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern222]

private def bern223 : Coeff :=
  ![![(4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000)],
    ![(4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000)],
    ![(4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000), (4490006585952085117/500000000000000000000)]]

private theorem tensor223 (u v : ℝ) :
    eval poly058 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern223 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly058, bern223, Fin.sum_univ_succ]
  <;> ring

private theorem cert223 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly058 δ p := by
  apply positive_on_box_from_tensor (β := bern223) (m := (1/1000000000000000))
    tensor223 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern223]

private def bern224 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor224 (u v : ℝ) :
    eval poly059 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern224 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly059, bern224, Fin.sum_univ_succ]
  <;> ring

private theorem cert224 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly059 δ p := by
  apply positive_on_box_from_tensor (β := bern224) (m := (1/1000000000000000))
    tensor224 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern224]

private def bern225 : Coeff :=
  ![![(316917888096595363/167581693639560192), (475195005146045603/251372540459340288), (950026356294396323/502745080918680576), (618269988474415/327307995389766)],
    ![(316917888096595363/167581693639560192), (475195005146045603/251372540459340288), (950026356294396323/502745080918680576), (618269988474415/327307995389766)],
    ![(316917888096595363/167581693639560192), (475195005146045603/251372540459340288), (950026356294396323/502745080918680576), (618269988474415/327307995389766)]]

private theorem tensor225 (u v : ℝ) :
    eval poly060 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern225 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly060, bern225, Fin.sum_univ_succ]
  <;> ring

private theorem cert225 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly060 δ p := by
  apply positive_on_box_from_tensor (β := bern225) (m := (1/1000000000000000))
    tensor225 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern225]

private def bern226 : Coeff :=
  ![![(227503307889766/163653997694883), (682314611169298/490961993084649), (682119298669298/490961993084649), (227307995389766/163653997694883)],
    ![(227503307889766/163653997694883), (682314611169298/490961993084649), (682119298669298/490961993084649), (227307995389766/163653997694883)],
    ![(227503307889766/163653997694883), (682314611169298/490961993084649), (682119298669298/490961993084649), (227307995389766/163653997694883)]]

private theorem tensor226 (u v : ℝ) :
    eval poly061 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern226 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly061, bern226, Fin.sum_univ_succ]
  <;> ring

private theorem cert226 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly061 δ p := by
  apply positive_on_box_from_tensor (β := bern226) (m := (1/1000000000000000))
    tensor226 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern226]

private def bern227 : Coeff :=
  ![![(59093186875967765/83790846819780096), (88615614306178837/125686270229670144), (177182896596812053/251372540459340288), (115321982149262/163653997694883)],
    ![(59093186875967765/83790846819780096), (88615614306178837/125686270229670144), (177182896596812053/251372540459340288), (115321982149262/163653997694883)],
    ![(59093186875967765/83790846819780096), (88615614306178837/125686270229670144), (177182896596812053/251372540459340288), (115321982149262/163653997694883)]]

private theorem tensor227 (u v : ℝ) :
    eval poly062 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern227 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly062, bern227, Fin.sum_univ_succ]
  <;> ring

private theorem cert227 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly062 δ p := by
  apply positive_on_box_from_tensor (β := bern227) (m := (1/1000000000000000))
    tensor227 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern227]

private def bern228 : Coeff :=
  ![![(1000971601036471776035/1029621925721457819648), (1500582268043874957715/1544432888582186729472), (2999414875511397002755/3088865777164373458944), (1951605352461169655/2010980323674722304)],
    ![(4002084525925544795495/4118487702885831278592), (5999626416644184240919/6177731554328746917888), (11992254516339165077191/12355463108657493835776), (7802902751906916779/8043921294698889216)],
    ![(2000141323852601243425/2059243851442915639296), (2998461880556434325489/3088865777164373458944), (5993424765316371071681/6177731554328746917888), (3899692046984577469/4021960647349444608)]]

private theorem tensor228 (u v : ℝ) :
    eval poly063 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern228 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly063, bern228, Fin.sum_univ_succ]
  <;> ring

private theorem cert228 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly063 δ p := by
  apply positive_on_box_from_tensor (β := bern228) (m := (1/1000000000000000))
    tensor228 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern228]

private def bern229 : Coeff :=
  ![![(10458607679243154888525/58574047329931822628864), (10448960615495304684655/58574047329931822628864), (20389295136580551225/114402436191273091072), (19893041920747695/111721129093040128)],
    ![(41864745521839991017545/234296189319727290515456), (125478387913034919734857/702888567959181871546368), (81616279952515192005/457609744765092364288), (79629828674065411/446884516372160512)],
    ![(20947530163353681240495/117148094659863645257728), (62784624220063091626927/351444283979590935773184), (40837689679354089555/228804872382546182144), (39843744832570021/223442258186080256)]]

private theorem tensor229 (u v : ℝ) :
    eval poly064 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern229 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly064, bern229, Fin.sum_univ_succ]
  <;> ring

private theorem cert229 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly064 δ p := by
  apply positive_on_box_from_tensor (β := bern229) (m := (1/1000000000000000))
    tensor229 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern229]

private def bern230 : Coeff :=
  ![![(1414401919729455249200917/21965267748724433485824000), (4244727682358794578903541/65895803246173300457472000), (132695205801748818608983/2059243851442915639296000), (86420948671058524523/1340653549116481536000)],
    ![(5636633453924267782163569/87861070994897733943296000), (84580106187194275749016853/1317916064923466009149440000), (2644082816384157228850103/41184877028858312785920000), (1722028271894537016907/26813070982329630720000)],
    ![(561565922893071456752347/8786107099489773394329600), (42132829363606329959981443/658958032461733004574720000), (1317130758366669042760273/20592438514429156392960000), (857818785183951771677/13406535491164815360000)]]

private theorem tensor230 (u v : ℝ) :
    eval poly065 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern230 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly065, bern230, Fin.sum_univ_succ]
  <;> ring

private theorem cert230 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly065 δ p := by
  apply positive_on_box_from_tensor (β := bern230) (m := (1/1000000000000000))
    tensor230 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern230]

private def bern231 : Coeff :=
  ![![(412168931573721980316464557318596174605/1596048521617652935205363702891280334848), (1234663414607669713579174172045579679805/4788145564852958805616091108673841004544), (4815712030067763485014982979876047575/18703693612706870334437855893257191424), (3130552641994650275743937882007625/12176883862439368707316312430505984)],
    ![(1649795220303801698112800720769381222665/6384194086470611740821454811565121339392), (4942008664483073736841206574771517277817/19152582259411835222464364434695364018176), (19275940052077262936991318848323141387/74814774450827481337751423573028765696), (12530725143911455359697149163310485/48707535449757474829265249722023936)],
    ![(825457357156357737479871606132188873455/3192097043235305870410727405782560669696), (2472681835267734309682858230680357918207/9576291129705917611232182217347682009088), (9644515991941735966961352888571046237/37407387225413740668875711786514382848), (6269619859922154808209273399295235/24353767724878737414632624861011968)]]

private theorem tensor231 (u v : ℝ) :
    eval poly066 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern231 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly066, bern231, Fin.sum_univ_succ]
  <;> ring

private theorem cert231 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly066 δ p := by
  apply positive_on_box_from_tensor (β := bern231) (m := (1/1000000000000000))
    tensor231 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern231]

private def bern232 : Coeff :=
  ![![(37736291291042737002137393406494495425/86272893060413672173262902858988126208), (113134708263942845817947563704724621505/258818679181241016519788708576964378624), (220821441544259336541688447406937115/505505232775861360390212321439383552), (71834871478577940928524617717975/164552484627559036585355573385216)],
    ![(150776615972300285659656652265849718445/345091572241654688693051611435952504832), (452033516740944839543571134186966713517/1035274716724964066079154834307857514496), (882299466934407899998577513683995391/2022020931103445441560849285757534208), (287018635371727544623102579279115/658209938510236146341422293540864)],
    ![(75304033390214811655381865452860727595/172545786120827344346525805717976252416), (225764100213059147907676006777517470507/517637358362482033039577417153928757248), (440656583845889226915200618870121161/1011010465551722720780424642878767104), (143348892414571662766053343843165/329104969255118073170711146770432)]]

private theorem tensor232 (u v : ℝ) :
    eval poly067 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern232 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly067, bern232, Fin.sum_univ_succ]
  <;> ring

private theorem cert232 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly067 δ p := by
  apply positive_on_box_from_tensor (β := bern232) (m := (1/1000000000000000))
    tensor232 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern232]

private def bern233 : Coeff :=
  ![![(54762183222026311646215821839417027168563811/1380366288966618754772206445743810019328000000), (41053771025963028589109486172867744324275563/1035274716724964066079154834307857514496000000), (40074159313963527225711272133613009961131/1011010465551722720780424642878767104000000), (10431452850564585873437223229930324927/263283975404094458536568917416345600000)],
    ![(219530325199734914806928870600564647037065127/5521465155866475019088825782975240077312000000), (822878374591274074468574718524708011566434891/20705494334499281321583096686157150289920000000), (803240940291939314167472051550489201644939/20220209311034454415608492857575342080000000), (209086039758151299459822309160116858143/5265679508081889170731378348326912000000)],
    ![(22001191751136458302899445384346118539987501/552146515586647501908882578297524007731200000), (412340664331643788577479856796030568323679261/10352747167249640660791548343078575144960000000), (402499347152304041910359330214359102033629/10110104655517227207804246428787671040000000), (104771511252505440725450076860813608873/2632839754040944585365689174163456000000)]]

private theorem tensor233 (u v : ℝ) :
    eval poly068 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern233 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly068, bern233, Fin.sum_univ_succ]
  <;> ring

private theorem cert233 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly068 δ p := by
  apply positive_on_box_from_tensor (β := bern233) (m := (1/1000000000000000))
    tensor233 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern233]

private def bern234 : Coeff :=
  ![![(4661518149501907297630142384279079751793433/1278116934228350698863154116429453721600000000), (62506712603592479652824238742424135632534027/17254578612082734434652580571797625241600000000), (20209311852934671144430431020425206774233/5616724808620681782113470238215372800000000), (15680790344751706047474753582246601183/4388066256734907642276148623605760000000)],
    ![(18100485598740054991462822455138641626809381/5112467736913402795452616465717814886400000000), (1213360390542665531730518191460408223070165739/345091572241654688693051611435952504832000000000), (392232900109411786801967101230335962918777/112334496172413635642269404764307456000000000), (304290781675183199237362264394647510847/87761325134698152845522972472115200000000)],
    ![(1755489859947248079240507537316096424644503/511246773691340279545261646571781488640000000), (588293264506740735202275804036166866744825469/172545786120827344346525805717976252416000000000), (190139781580065075357662791026083895176447/56167248086206817821134702382153728000000000), (147482878227666138762614728572181499017/43880662567349076422761486236057600000000)]]

private theorem tensor234 (u v : ℝ) :
    eval poly069 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern234 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly069, bern234, Fin.sum_univ_succ]
  <;> ring

private theorem cert234 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly069 δ p := by
  apply positive_on_box_from_tensor (β := bern234) (m := (1/1000000000000000))
    tensor234 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern234]

private def bern235 : Coeff :=
  ![![(4570886948678081646192357163/37487390291156366482472960000000), (4230527852225542293734043433/37487390291156366482472960000000), (729408772446514523904545999/7028885679591818715463680000000), (433330626482672529101619/4576097447650923642880000000)],
    ![(93264751652754959127959648023/1124621708734690994474188800000000), (83107135885841736399356048269/1124621708734690994474188800000000), (2735618009033462779765225999/42173314077550912292782080000000), (2555045856939093663159061/45760974476509236428800000000)],
    ![(19710188403092880361329615161/449848683493876397789675520000000), (391711878928078937136425052203/11246217087346909944741888000000000), (54500907434879671203289754173/2108665703877545614639104000000000), (7716219693851109360124259/457609744765092364288000000000)]]

private theorem tensor235 (u v : ℝ) :
    eval poly070 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern235 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly070, bern235, Fin.sum_univ_succ]
  <;> ring

private theorem cert235 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly070 δ p := by
  apply positive_on_box_from_tensor (β := bern235) (m := (1/1000000000000000))
    tensor235 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern235]

private def bern236 : Coeff :=
  ![![(30910012815778675127567536669534619455/86272893060413672173262902858988126208), (92670049039994324808396538656854872895/258818679181241016519788708576964378624), (90439544290427530811302748043198275/252752616387930680195106160719691776), (117683628575066153983860061679515/329104969255118073170711146770432)],
    ![(123498706006576222402689224006550893395/345091572241654688693051611435952504832), (370256441142660040564370612761702125395/1035274716724964066079154834307857514496), (361344627915501372388793180046866183/1011010465551722720780424642878767104), (470196395299490307481547651721343/1316419877020472292682844587081728)],
    ![(61678680375018872147554150667481654485/172545786120827344346525805717976252416), (184916343062671390947577535447992379605/517637358362482033039577417153928757248), (180465539334646310766187683960469633/505505232775861360390212321439383552), (234829138149357999513827528362313/658209938510236146341422293540864)]]

private theorem tensor236 (u v : ℝ) :
    eval poly071 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern236 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly071, bern236, Fin.sum_univ_succ]
  <;> ring

private theorem cert236 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly071 δ p := by
  apply positive_on_box_from_tensor (β := bern236) (m := (1/1000000000000000))
    tensor236 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern236]

private def bern237 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor237 (u v : ℝ) :
    eval poly072 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern237 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly072, bern237, Fin.sum_univ_succ]
  <;> ring

private theorem cert237 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly072 δ p := by
  apply positive_on_box_from_tensor (β := bern237) (m := (1/1000000000000000))
    tensor237 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern237]

private def bern238 : Coeff :=
  ![![(4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000)],
    ![(4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000)],
    ![(4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000), (4115006585952085117/500000000000000000000)]]

private theorem tensor238 (u v : ℝ) :
    eval poly073 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern238 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly073, bern238, Fin.sum_univ_succ]
  <;> ring

private theorem cert238 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly073 δ p := by
  apply positive_on_box_from_tensor (β := bern238) (m := (1/1000000000000000))
    tensor238 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern238]

private def bern239 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor239 (u v : ℝ) :
    eval poly074 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern239 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly074, bern239, Fin.sum_univ_succ]
  <;> ring

private theorem cert239 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly074 δ p := by
  apply positive_on_box_from_tensor (β := bern239) (m := (1/1000000000000000))
    tensor239 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern239]

private def bern240 : Coeff :=
  ![![(200493046041676823/107456230871578624), (902040003893450309/483553038922103808), (1803722601198709829/967106077844207616), (587032940953945/314813176381578)],
    ![(200493046041676823/107456230871578624), (902040003893450309/483553038922103808), (1803722601198709829/967106077844207616), (587032940953945/314813176381578)],
    ![(200493046041676823/107456230871578624), (902040003893450309/483553038922103808), (1803722601198709829/967106077844207616), (587032940953945/314813176381578)]]

private theorem tensor240 (u v : ℝ) :
    eval poly075 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern240 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern240, Fin.sum_univ_succ]
  <;> ring

private theorem cert240 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern240) (m := (1/1000000000000000))
    tensor240 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern240]

private def bern241 : Coeff :=
  ![![(71636944210526/52468862730263), (644634841644734/472219764572367), (644537185394734/472219764572367), (214813176381578/157406588190789)],
    ![(71636944210526/52468862730263), (644634841644734/472219764572367), (644537185394734/472219764572367), (214813176381578/157406588190789)],
    ![(71636944210526/52468862730263), (644634841644734/472219764572367), (644537185394734/472219764572367), (214813176381578/157406588190789)]]

private theorem tensor241 (u v : ℝ) :
    eval poly076 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern241 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern241, Fin.sum_univ_succ]
  <;> ring

private theorem cert241 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern241) (m := (1/1000000000000000))
    tensor241 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern241]

private def bern242 : Coeff :=
  ![![(37355656561735381/53728115435789312), (168076447989870719/241776519461051904), (336104882903864447/483553038922103808), (109393512313798/157406588190789)],
    ![(37355656561735381/53728115435789312), (168076447989870719/241776519461051904), (336104882903864447/483553038922103808), (109393512313798/157406588190789)],
    ![(37355656561735381/53728115435789312), (168076447989870719/241776519461051904), (336104882903864447/483553038922103808), (109393512313798/157406588190789)]]

private theorem tensor242 (u v : ℝ) :
    eval poly077 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern242 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern242, Fin.sum_univ_succ]
  <;> ring

private theorem cert242 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern242) (m := (1/1000000000000000))
    tensor242 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern242]

private def bern243 : Coeff :=
  ![![(180404349725710747019/188631737849994018816), (5681038931518153683023/5941899742274811592704), (11358682300677056419895/11883799484549623185408), (3696382599492846427/3868424311376830464)],
    ![(5050178205715867927475/5281688659799832526848), (22719009777145913172785/23767598969099246370816), (45424437687316622593865/47535197938198492741632), (14782180420090234405/15473697245507321856)],
    ![(2524517309555917469209/2640844329899916263424), (11356931914109605806739/11883799484549623185408), (22707073085962509754075/23767598969099246370816), (7389415221104541551/7736848622753660928)]]

private theorem tensor243 (u v : ℝ) :
    eval poly078 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern243 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern243, Fin.sum_univ_succ]
  <;> ring

private theorem cert243 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern243) (m := (1/1000000000000000))
    tensor243 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern243]

private def bern244 : Coeff :=
  ![![(79374232953789380933325/450704098969585708957696), (238011254123998889554637/1352112296908757126873088), (77441355001193055765/440140721649986043904), (37795458504417209/214912461743157248)],
    ![(45373114351297837147125/257545199411191833690112), (136055637306772158283765/772635598233575501070336), (44268213061463468925/251508983799992025088), (21605218681975105/122807120996089856)],
    ![(158863334551506098163225/901408197939171417915392), (158788984299802442959027/901408197939171417915392), (154994781427858170945/880281443299972087808), (75645613764991317/429824923486314496)]]

private theorem tensor244 (u v : ℝ) :
    eval poly079 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern244 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern244, Fin.sum_univ_succ]
  <;> ring

private theorem cert244 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern244) (m := (1/1000000000000000))
    tensor244 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern244]

private def bern245 : Coeff :=
  ![![(17715121251921276332210371/281690061855991068098560000), (159463993551693700383699977/2535210556703919612887040000), (498412081271322595784507/7922532989699748790272000), (811359195112508533691/12894747704589434880000)],
    ![(404158429806836076747859/6438629985279795842252800), (18190327395057750533160349/289738349337590812901376000), (284273781851793177083987/4527161708399856451584000), (92553269814446318839/1473685451953078272000)],
    ![(35297482712353760766454583/563380123711982136197120000), (317733471723633867893212261/5070421113407839225774080000), (198618462083981409603779/3169013195879899516108800), (1616646053280604091983/25789495409178869760000)]]

private theorem tensor245 (u v : ℝ) :
    eval poly080 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern245 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern245, Fin.sum_univ_succ]
  <;> ring

private theorem cert245 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern245) (m := (1/1000000000000000))
    tensor245 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern245]

private def bern246 : Coeff :=
  ![![(329024187713208923663499072314872115881/1312460198294514451339654653260190449664), (2958964063987244773257202289973706067171/11812141784650630062056891879341714046976), (641647538051070300268159594773247111/2563398824793973537772762994648809472), (1878395756222677837871020221875045/7509957494513594348943641585885184)],
    ![(1316541276757306108042909363231463087575/5249840793178057805358618613040761798656), (11839854861649882441876459477488044259485/47248567138602520248227567517366856187904), (7702372331399044313665475059212288235/30760785897527682453273155935785713664), (7516122567439359615800061557781275/30039829978054377395774566343540736)],
    ![(658492901330888260715911218601718855813/2624920396589028902679309306520380899328), (5921926733675392895362054897540632125143/23624283569301260124113783758683428093952), (3852487103092622512056517490572805569/15380392948763841226636577967892856832), (3759331054994003940058021114031185/15019914989027188697887283171770368)]]

private theorem tensor246 (u v : ℝ) :
    eval poly081 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern246 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern246, Fin.sum_univ_succ]
  <;> ring

private theorem cert246 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern246) (m := (1/1000000000000000))
    tensor246 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern246]

private def bern247 : Coeff :=
  ![![(30115478020586245328984928148080517823/70943794502406186558900251527577862144), (90315636625514559924668245826011621055/212831383507218559676700754582733586432), (793519161820855457145804441833248777/1870588331606413122158502725824806912), (129109475259876802805020279567655/304457736264064635767985469698048)],
    ![(120394506138006439607916617751901100225/283775178009624746235601006110311448576), (361060397601379395868948533114433426625/851325534028874238706803018330934345728), (3172300553660843440342901368433094775/7482353326425652488634010903299227648), (516148921860860384255334741121625/1217830945056258543071941878792192)],
    ![(60163550096833948949946761455740064579/141887589004812373117800503055155724288), (180429124350350276019612041462410184515/425662767014437119353401509165467172864), (1585262230019132526051292484766597221/3741176663212826244317005451649613824), (257929971341106778645294181986315/608915472528129271535970939396096)]]

private theorem tensor247 (u v : ℝ) :
    eval poly082 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern247 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern247, Fin.sum_univ_succ]
  <;> ring

private theorem cert247 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern247) (m := (1/1000000000000000))
    tensor247 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern247]

private def bern248 : Coeff :=
  ![![(63753541023377913344078005057695156716171779/1621572445769284264203434320630351134720000000), (71706480227093801653195292982693420239386297/1824269001490444797228863610709145026560000000), (555634935810602655652525964168167508807/14138989656888988073760413649469440000000), (4556911393435972477979642277050239957/115983899529167480292565893218304000000)],
    ![(10211708218309199817986587689585555228146437/259451591323085482272549491300856181555200000), (57427803138514969750884145584122093109065819/1459415201192355837783090888567316021248000000), (3114950070595420995766130076670605975427/79178342078578333213058316437028864000000), (3649503605919106528949446946853791471/92787119623333984234052714574643200000)],
    ![(127785623410974168761508682124248567271317367/3243144891538568528406868641260702269440000000), (143726055238387245448030141955223625066556501/3648538002980889594457727221418290053120000000), (7795861251628667799695286884998684753837/197945855196445833032645791092572160000000), (9133695242723587688787950180168477441/231967799058334960585131786436608000000)]]

private theorem tensor248 (u v : ℝ) :
    eval poly083 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern248 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern248, Fin.sum_univ_succ]
  <;> ring

private theorem cert248 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern248) (m := (1/1000000000000000))
    tensor248 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern248]

private def bern249 : Coeff :=
  ![![(36883847171748624208400346305495625835796283/13513103714744035535028619338586259456000000000), (1735111228120247565190839210248972424808332173/638494150521655679030102263748200759296000000000), (2530461290496929624623716493232204244455207/935294165803206561079251362912403456000000000), (328028263775157977319474763115378915339/121783094505625854307194187879219200000000)],
    ![(40515915049807006595411395655960648466474843/15134676160513319799232053659216610590720000000), (1361311333188293537985972560903529168543390871/510795320417324543224081810998560607436800000000), (1985172717014117784204116320307992201192261/748235332642565248863401090329922764800000000), (257322666687836249046074334465225879217/97426475604500683445755350303375360000000)],
    ![(496524015840694425967680043122077449960723113/189183452006416497490400670740207632384000000000), (3336334209700972559548184384019700993100290009/1276988301043311358060204527496401518592000000000), (4864941004076729671773148615075552517050891/1870588331606413122158502725824806912000000000), (630556805888865290591422146095371565407/243566189011251708614388375758438400000000)]]

private theorem tensor249 (u v : ℝ) :
    eval poly084 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern249 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern249, Fin.sum_univ_succ]
  <;> ring

private theorem cert249 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern249) (m := (1/1000000000000000))
    tensor249 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern249]

private def bern250 : Coeff :=
  ![![(1066615910699426851545902483773/14422531167026742686646272000000000), (9026361720528799915476699853351/129802780503240684179816448000000000), (52832499405954154197640864607/811267378145254276123852800000000), (80160096069171379826734991/1320422164949958131712000000000)],
    ![(1579690429302121931207715302089/28845062334053485373292544000000000), (13073913878955729545577149019403/259605561006481368359632896000000000), (10652367686226691022054910149/231790679470072650321100800000000), (15676485075294606301926869/377263475699988037632000000000)],
    ![(2050693694718628415774476528677/57690124668106970746585088000000000), (5391926427407477877518103560053/173070374004320912239755264000000000), (5789745135263783359765975609/216337967505401140299694080000000), (39384873180154388159358893/1760562886599944175616000000000)]]

private theorem tensor250 (u v : ℝ) :
    eval poly085 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern250 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern250, Fin.sum_univ_succ]
  <;> ring

private theorem cert250 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern250) (m := (1/1000000000000000))
    tensor250 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern250]

private def bern251 : Coeff :=
  ![![(73631962989959913037709416098408442819/212831383507218559676700754582733586432), (220821132561254223290185647472117670851/638494150521655679030102263748200759296), (323358981234845030529063662374067237/935294165803206561079251362912403456), (210448918204383556142896353169405/608915472528129271535970939396096)],
    ![(294358024522920186104507730102086676925/851325534028874238706803018330934345728), (882775225054325328888095112258654075325/2553976602086622716120409054992803037184), (1292690131789016114788068268928326235/3741176663212826244317005451649613824), (841310299215020727858735721869955/2435661890112517086143883757584384)],
    ![(147094098543000360029088897905269791287/425662767014437119353401509165467172864), (441132959931816882307723817314418733623/1276988301043311358060204527496401518592), (645972169319326053729940944180191761/1870588331606413122158502725824806912), (420412462806253615572943015531145/1217830945056258543071941878792192)]]

private theorem tensor251 (u v : ℝ) :
    eval poly086 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern251 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern251, Fin.sum_univ_succ]
  <;> ring

private theorem cert251 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern251) (m := (1/1000000000000000))
    tensor251 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern251]

private def bern252 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor252 (u v : ℝ) :
    eval poly087 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern252 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern252, Fin.sum_univ_succ]
  <;> ring

private theorem cert252 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern252) (m := (1/1000000000000000))
    tensor252 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern252]

private def bern253 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)]]

private theorem tensor253 (u v : ℝ) :
    eval poly088 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern253 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern253, Fin.sum_univ_succ]
  <;> ring

private theorem cert253 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern253) (m := (1/1000000000000000))
    tensor253 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern253]

private def bern254 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor254 (u v : ℝ) :
    eval poly089 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern254 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern254, Fin.sum_univ_succ]
  <;> ring

private theorem cert254 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern254) (m := (1/1000000000000000))
    tensor254 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern254]

private def bern255 : Coeff :=
  ![![(1202600869661870149/644737385229471744), (1803722601198709829/967106077844207616), (3607087795809228869/1934212155688415232), (587032940953945/314813176381578)],
    ![(1202600869661870149/644737385229471744), (1803722601198709829/967106077844207616), (3607087795809228869/1934212155688415232), (587032940953945/314813176381578)],
    ![(1202600869661870149/644737385229471744), (1803722601198709829/967106077844207616), (3607087795809228869/1934212155688415232), (587032940953945/314813176381578)]]

private theorem tensor255 (u v : ℝ) :
    eval poly075 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern255 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern255, Fin.sum_univ_succ]
  <;> ring

private theorem cert255 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern255) (m := (1/1000000000000000))
    tensor255 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern255]

private def bern256 : Coeff :=
  ![![(214862004506578/157406588190789), (644537185394734/472219764572367), (644488357269734/472219764572367), (214813176381578/157406588190789)],
    ![(214862004506578/157406588190789), (644537185394734/472219764572367), (644488357269734/472219764572367), (214813176381578/157406588190789)],
    ![(214862004506578/157406588190789), (644537185394734/472219764572367), (644488357269734/472219764572367), (214813176381578/157406588190789)]]

private theorem tensor256 (u v : ℝ) :
    eval poly076 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern256 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern256, Fin.sum_univ_succ]
  <;> ring

private theorem cert256 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern256) (m := (1/1000000000000000))
    tensor256 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern256]

private def bern257 : Coeff :=
  ![![(224085926294535295/322368692614735872), (336104882903864447/483553038922103808), (672161752731851903/967106077844207616), (109393512313798/157406588190789)],
    ![(224085926294535295/322368692614735872), (336104882903864447/483553038922103808), (672161752731851903/967106077844207616), (109393512313798/157406588190789)],
    ![(224085926294535295/322368692614735872), (336104882903864447/483553038922103808), (672161752731851903/967106077844207616), (109393512313798/157406588190789)]]

private theorem tensor257 (u v : ℝ) :
    eval poly077 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern257 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern257, Fin.sum_univ_succ]
  <;> ring

private theorem cert257 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern257) (m := (1/1000000000000000))
    tensor257 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern257]

private def bern258 : Coeff :=
  ![![(15140312507315131080851/15845065979399497580544), (22707073389844345691575/23767598969099246370816), (45407356645195661398747/47535197938198492741632), (7389415221104541551/7736848622753660928)],
    ![(60554388891658673296961/63380263917597990322176), (90818002044205506243085/95070395876396985483264), (181608843933340145706457/190140791752793970966528), (29554310906537014901/30947394491014643712)],
    ![(30273763877028411135259/31690131958798995161088), (45403855264516814859935/47535197938198492741632), (90794130642948822908963/95070395876396985483264), (14775480464327931799/15473697245507321856)]]

private theorem tensor258 (u v : ℝ) :
    eval poly078 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern258 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern258, Fin.sum_univ_succ]
  <;> ring

private theorem cert258 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern258) (m := (1/1000000000000000))
    tensor258 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern258]

private def bern259 : Coeff :=
  ![![(635007303097886399306265/3605632791756685671661568), (634858646862535047483571/3605632791756685671661568), (309916998418560388161/1760562886599944175616), (75645613764991317/429824923486314496)],
    ![(2540488364454523100044515/14422531167026742686646272), (7619680896074634311771363/43267593501080228059938816), (1239892084056322941211/7042251546399776702464), (302637151816122167/1719299693945257984)],
    ![(1270473758258750301431985/7211265583513371343323136), (3810529014899424026869937/21633796750540114029969408), (620058087219202164889/3521125773199888351232), (151345924286139533/859649846972628992)]]

private theorem tensor259 (u v : ℝ) :
    eval poly079 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern259 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern259, Fin.sum_univ_succ]
  <;> ring

private theorem cert259 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern259) (m := (1/1000000000000000))
    tensor259 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern259]

private def bern260 : Coeff :=
  ![![(423681987471431537665410149/6760561484543785634365440000), (50846323905430695517675949/811267378145254276123852800), (9931798227777551010666251/158450659793994975805440000), (1616646053280604091983/25789495409178869760000)],
    ![(1693135477831983569031704039/27042245938175142537461760000), (1015971123956559292150816891/16225347562905085522477056000), (39689879431403276664488681/633802639175979903221760000), (6460511876178003392533/103157981636715479040000)],
    ![(845771502889120493700883741/13521122969087571268730880000), (507507884902252336974057401/8112673781452542761238528000), (19826282975848174643156179/316901319587989951610880000), (3227219769616795208567/51578990818357739520000)]]

private theorem tensor260 (u v : ℝ) :
    eval poly080 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern260 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern260, Fin.sum_univ_succ]
  <;> ring

private theorem cert260 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern260) (m := (1/1000000000000000))
    tensor260 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern260]

private def bern261 : Coeff :=
  ![![(2630966298029837032292289865449799994641/10499681586356115610717237226081523597312), (23669683594858018265575095950079836596951/94497134277205040496455135034733712375808), (7702042103406482546675931111340739009/30760785897527682453273155935785713664), (3759331054994003940058021114031185/15019914989027188697887283171770368)],
    ![(214809017916618208695505085796102933499/857116864192335968221815283761757028352), (13527817185646774585321146974153248363243/53998362444117165997974362876990692786176), (1467303370475330796181468979698291439/5859197313814796657766315416340135936), (2148551966074952003506866446629405/8582808565158393541649876098154496)],
    ![(5263709281854618161495169473109443752169/20999363172712231221434474452163047194624), (47355353109811385566097836918913065348799/188994268554410080992910270069467424751616), (15409286573168981626458986350982642201/61521571795055364906546311871571427328), (7521201652536656144432022898343465/30039829978054377395774566343540736)]]

private theorem tensor261 (u v : ℝ) :
    eval poly081 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern261 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern261, Fin.sum_univ_succ]
  <;> ring

private theorem cert261 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern261) (m := (1/1000000000000000))
    tensor261 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern261]

private def bern262 : Coeff :=
  ![![(2164780474411097247226044357502656135515/5107953204173245432240818109985606074368), (6493234232006170186678163334986576193883/15323859612519736296722454329956818223104), (3169983973938892574047979938890516581/7482353326425652488634010903299227648), (257929971341106778645294181986315/608915472528129271535970939396096)],
    ![(1236670932039403120567697940567619694495/2918830402384711675566181777134632042496), (3709380292627451137391521417185783412639/8756491207154135026698545331403896127488), (1810912044865626543297171659351248673/4275630472243229993505149087599558656), (147347272312254326802347192970895/347951698587502440877697679654912)],
    ![(4327135575453627349521796868968025590435/10215906408346490864481636219971212148736), (12979193584379817588384323250327331500707/30647719225039472593444908659913636446208), (6336416366181600654984241737677707549/14964706652851304977268021806598455296), (515570963503566730325841986823635/1217830945056258543071941878792192)]]

private theorem tensor262 (u v : ℝ) :
    eval poly082 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern262 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern262, Fin.sum_univ_succ]
  <;> ring

private theorem cert262 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern262) (m := (1/1000000000000000))
    tensor262 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern262]

private def bern263 : Coeff :=
  ![![(1021935591257847485438325316951238139151717807/25945159132308548227254949130085618155520000000), (574773288760938385481374902405620260849613909/14594152011923558377830908885673160212480000000), (46769843576258387882383013116227356510471/1187675131178674998195874746555432960000000), (9133695242723587688787950180168477441/231967799058334960585131786436608000000)],
    ![(4089967878020942453402368121920649838531809077/103780636529234192909019796520342472622080000000), (2300344477879889987616738444650372912749502519/58376608047694233511323635542692640849920000000), (187181164242854448787253206627576518602621/4750700524714699992783498986221731840000000), (36554653426745993487980466346741907291/927871196233339842340527145746432000000)],
    ![(292299527929321068932245355431167651461196209/7412902609231013779215699751453033758720000000), (1150797900358013216653988639839132391050274701/29188304023847116755661817771346320424960000000), (93641477090337673022487180395121805581679/2375350262357349996391749493110865920000000), (18287262941298818110404565986404952409/463935598116669921170263572873216000000)]]

private theorem tensor263 (u v : ℝ) :
    eval poly083 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern263 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern263, Fin.sum_univ_succ]
  <;> ring

private theorem cert263 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern263) (m := (1/1000000000000000))
    tensor263 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern263]

private def bern264 : Coeff :=
  ![![(106519490315341445905815028592513435977188111871/40863625633385963457926544879884848594944000000000), (39853601981177044578435235903370071107664476043/15323859612519736296722454329956818223104000000000), (1386802467614745014787895813869715162768093/534453809030403749188143635949944832000000000), (630556805888865290591422146095371565407/243566189011251708614388375758438400000000)],
    ![(421795107498746610994854877219659198322235190181/163454502533543853831706179519539394379776000000000), (157808926703923888479341291666544156972980113513/61295438450078945186889817319827272892416000000000), (38438649653935789736701788137523402068365801/14964706652851304977268021806598455296000000000), (2496727501894010498318161204246099996357/974264756045006834457553503033753600000000)],
    ![(208756126868063719183224820034632326367858966439/81727251266771926915853089759769697189888000000000), (78101722741569799322470819859804014757651161427/30647719225039472593444908659913636446208000000000), (19023415107329359529671246743347389789612499/7482353326425652488634010903299227648000000000), (1235613890116279917135316912055356865543/487132378022503417228776751516876800000000)]]

private theorem tensor264 (u v : ℝ) :
    eval poly084 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern264 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern264, Fin.sum_univ_succ]
  <;> ring

private theorem cert264 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern264) (m := (1/1000000000000000))
    tensor264 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern264]

private def bern265 : Coeff :=
  ![![(6682489877352215986155616390877/230760498672427882986340352000000000), (741088368677257129070451246077/27691259840691345958360842240000000), (37961994113004123488528558503/1545271196467151002140672000000000), (39384873180154388159358893/1760562886599944175616000000000)],
    ![(26802962480103178976387975721599/1384562992034567297918042112000000000), (14259918263278233096045313967707/830737795220740378750825267200000000), (138817945852160140057169241901/9271627178802906012844032000000000), (134993067567265005207253871/10563377319599665053696000000000)],
    ![(27002738963257948063925007429671/2769125984069134595836084224000000000), (12562835499774048216728272052131/1661475590441480757501650534400000000), (99599155292858220333278209189/18543254357605812025688064000000000), (67207213816107070247773079/21126754639199330107392000000000)]]

private theorem tensor265 (u v : ℝ) :
    eval poly085 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern265 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern265, Fin.sum_univ_succ]
  <;> ring

private theorem cert265 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern265) (m := (1/1000000000000000))
    tensor265 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern265]

private def bern266 : Coeff :=
  ![![(1764233298394980838126185747396842100389/5107953204173245432240818109985606074368), (5291804141126000736610052445666079352485/15323859612519736296722454329956818223104), (1291725712189731607249981416036030481/3741176663212826244317005451649613824), (420412462806253615572943015531145/1217830945056258543071941878792192)],
    ![(1007842332413888495336803925615654348897/2918830402384711675566181777134632042496), (3023015289550878528945499528971937118305/8756491207154135026698545331403896127488), (737915931679300241531543165499372253/2137815236121614996752574543799779328), (240166353946071566511274624473845/695903397175004881755395359309824)],
    ![(3526429730107257791105255984515896241501/10215906408346490864481636219971212148736), (10577498744604148229398391811471401123165/30647719225039472593444908659913636446208), (2581960097375638476220839326423544809/7482353326425652488634010903299227648), (840339552009993734433036340254625/2435661890112517086143883757584384)]]

private theorem tensor266 (u v : ℝ) :
    eval poly086 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern266 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern266, Fin.sum_univ_succ]
  <;> ring

private theorem cert266 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern266) (m := (1/1000000000000000))
    tensor266 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern266]

private def bern267 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor267 (u v : ℝ) :
    eval poly087 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern267 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern267, Fin.sum_univ_succ]
  <;> ring

private theorem cert267 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern267) (m := (1/1000000000000000))
    tensor267 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern267]

private def bern268 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)]]

private theorem tensor268 (u v : ℝ) :
    eval poly088 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern268 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern268, Fin.sum_univ_succ]
  <;> ring

private theorem cert268 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern268) (m := (1/1000000000000000))
    tensor268 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern268]

private def bern269 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor269 (u v : ℝ) :
    eval poly089 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern269 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern269, Fin.sum_univ_succ]
  <;> ring

private theorem cert269 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern269) (m := (1/1000000000000000))
    tensor269 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern269]

private def bern270 : Coeff :=
  ![![(3206101703725875223/1719299693945257984), (14427278963472343109/7736848622753660928), (28854200520356495429/15473697245507321856), (587032940953945/314813176381578)],
    ![(3206101703725875223/1719299693945257984), (14427278963472343109/7736848622753660928), (28854200520356495429/15473697245507321856), (587032940953945/314813176381578)],
    ![(3206101703725875223/1719299693945257984), (14427278963472343109/7736848622753660928), (28854200520356495429/15473697245507321856), (587032940953945/314813176381578)]]

private theorem tensor270 (u v : ℝ) :
    eval poly075 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern270 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern270, Fin.sum_univ_succ]
  <;> ring

private theorem cert270 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern270) (m := (1/1000000000000000))
    tensor270 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern270]

private def bern271 : Coeff :=
  ![![(71606426632401/52468862730263), (644451736175984/472219764572367), (644445632660359/472219764572367), (214813176381578/157406588190789)],
    ![(71606426632401/52468862730263), (644451736175984/472219764572367), (644445632660359/472219764572367), (214813176381578/157406588190789)],
    ![(71606426632401/52468862730263), (644451736175984/472219764572367), (644445632660359/472219764572367), (214813176381578/157406588190789)]]

private theorem tensor271 (u v : ℝ) :
    eval poly076 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern271 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern271, Fin.sum_univ_succ]
  <;> ring

private theorem cert271 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern271) (m := (1/1000000000000000))
    tensor271 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern271]

private def bern272 : Coeff :=
  ![![(597450439608381141/859649846972628992), (2688502971699776639/3868424311376830464), (5376957930323676287/7736848622753660928), (109393512313798/157406588190789)],
    ![(597450439608381141/859649846972628992), (2688502971699776639/3868424311376830464), (5376957930323676287/7736848622753660928), (109393512313798/157406588190789)],
    ![(597450439608381141/859649846972628992), (2688502971699776639/3868424311376830464), (5376957930323676287/7736848622753660928), (109393512313798/157406588190789)]]

private theorem tensor272 (u v : ℝ) :
    eval poly077 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern272 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern272, Fin.sum_univ_succ]
  <;> ring

private theorem cert272 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern272) (m := (1/1000000000000000))
    tensor272 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern272]

private def bern273 : Coeff :=
  ![![(40349175124943782356683/42253509278398660214784), (726271573274878373265637/760563167011175883866112), (726257994452764513720355/760563167011175883866112), (14775480464327931799/15473697245507321856)],
    ![(645577654262285424775157/676056148454378563436544), (11620180513518613142479963/12169010672178814141857792), (11619963252748077164397725/12169010672178814141857792), (236404337451365757481/247579155928117149696)],
    ![(322784253262735165921693/338028074227189281718272), (830001132474226593764981/869215048012772438704128), (5809899297125961054634885/6084505336089407070928896), (16885784819534614727/17684225423436939264)]]

private theorem tensor273 (u v : ℝ) :
    eval poly078 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern273 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern273, Fin.sum_univ_succ]
  <;> ring

private theorem cert273 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern273) (m := (1/1000000000000000))
    tensor273 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern273]

private def bern274 : Coeff :=
  ![![(81260360485214580785860785/461520997344855765972680704), (243773945236559660661051569/1384562992034567297918042112), (4959448428351394855065/28169006185599106809856), (151345924286139533/859649846972628992)],
    ![(1300195135439792242548758415/7384335957517692255562891264), (3900471224234985853432141711/22153007872553076766688673792), (79352967209396929677735/450704098969585708957696), (2421589485334389427/13754397551562063872)],
    ![(650112251558075596261872135/3692167978758846127781445632), (650093220780836189381243053/3692167978758846127781445632), (39677379782585770837215/225352049484792854478848), (1210822091045273163/6877198775781031936)]]

private theorem tensor274 (u v : ℝ) :
    eval poly079 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern274 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern274, Fin.sum_univ_succ]
  <;> ring

private theorem cert274 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern274) (m := (1/1000000000000000))
    tensor274 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern274]

private def bern275 : Coeff :=
  ![![(18047321873092980608820500447/288450623340534853732925440000), (162427694512335689629130544029/2596055610064813683596328960000), (31724510165505460594641143/507042111340783922577408000), (3227219769616795208567/51578990818357739520000)],
    ![(288723189279120586506647430113/4615209973448557659726807040000), (2598537471146670386445002891171/41536889761037018937541263360000), (101506493627736984277886197/1622534756290508552247705600), (51629443976924310361673/825263853093723832320000)],
    ![(144344614294376741636083426537/2307604986724278829863403520000), (1299115915047984869411958538939/20768444880518509468770631680000), (253736386814641236632301841/4056336890726271380619264000), (25811685819989948693137/412631926546861916160000)]]

private theorem tensor275 (u v : ℝ) :
    eval poly080 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern275 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern275, Fin.sum_univ_succ]
  <;> ring

private theorem cert275 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern275) (m := (1/1000000000000000))
    tensor275 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern275]

private def bern276 : Coeff :=
  ![![(673081837340939489373441692862722116903039/2687918486107165596343612729876870040911872), (3028724103987684312828208057642073304946367/12095633187482245183546257284445915184103424), (13692581495992720457004051846848284049/54685841595604768805818943885841268736), (7521201652536656144432022898343465/30039829978054377395774566343540736)],
    ![(10769536654539280982831703967120620551734081/43006695777714649541497803678029920654589952), (48460608286685326385648745523514179564870913/193530130999715922936740116551134642945654784), (1971773344671285183858924488963603845159/7874761189767086708037927919561142697984), (120341765983135146575228347043776535/480637279648870038332393061496651776)],
    ![(5384881955811765067844170424218843616509769/21503347888857324770748901839014960327294976), (24230815454783851883023081062377593125299977/96765065499857961468370058275567321472827392), (985907476959809310954632755990527393631/3937380594883543354018963959780571348992), (60172152762841897419772163857028815/240318639824435019166196530748325888)]]

private theorem tensor276 (u v : ℝ) :
    eval poly081 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern276 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern276, Fin.sum_univ_succ]
  <;> ring

private theorem cert276 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern276) (m := (1/1000000000000000))
    tensor276 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern276]

private def bern277 : Coeff :=
  ![![(10252324236281838009121270952270758715417/24215481856821311678771285854746576945152), (276806853953518891080745668290501505802465/653818010134175415326824718078157577519104), (50683768362904396530691866076299495709/119717653222810439818144174452787642368), (515570963503566730325841986823635/1217830945056258543071941878792192)],
    ![(164031441319892447534239389141882962338343/387447709709140986860340573675945231122432), (4428754512126852069210737025648297212752735/10461088162146806645229195489250521240305664), (810911885391743674529758514703840651811/1915482451564967037090306791244602277888), (8248846436878420858248725412029165/19485295120900136689151070060675072)],
    ![(82012847429637743461269221523716892615007/193723854854570493430170286837972615561216), (2214299680498700940564771679324285166333015/5230544081073403322614597744625260620152832), (405441738488508502284223586093444686139/957741225782483518545153395622301138944), (4124278728849887015641989517440085/9742647560450068344575535030337536)]]

private theorem tensor277 (u v : ℝ) :
    eval poly082 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern277 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern277, Fin.sum_univ_succ]
  <;> ring

private theorem cert277 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern277) (m := (1/1000000000000000))
    tensor277 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern277]

private def bern278 : Coeff :=
  ![![(149612494296874073113268845722317982636203424929/3795406135926279054958438272743953284464640000000), (73636348463412911308929103117828771417903253389/1868051457526215472362356337366164507197440000000), (249685660302162438033128941782625099973413/6334267366286266657044665314962309120000000), (18287262941298818110404565986404952409/463935598116669921170263572873216000000)],
    ![(16757737562099026665052580750467187911603410670937/425085487223743254155345086547322767860039680000000), (1178261600938011172848439713922508616953334171571/29888823320419447557797701397858632115159040000000), (3995241904419780266130829911922316307550747/101348277860580266512714645039396945920000000), (292616079516632732499301721408547236071/7422969569866718738724217165971456000000)],
    ![(8379437881474078570709525390017380883976018874913/212542743611871627077672543273661383930019840000000), (589170813230707882377006888979878445610108144459/14944411660209723778898850698929316057579520000000), (285393803143211537409399768237330786823349/7239162704327161893765331788528353280000000), (146317975986242187616065193517307616799/3711484784933359369362108582985728000000)]]

private theorem tensor278 (u v : ℝ) :
    eval poly083 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern278 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern278, Fin.sum_univ_succ]
  <;> ring

private theorem cert278 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern278) (m := (1/1000000000000000))
    tensor278 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern278]

private def bern279 : Coeff :=
  ![![(11803501034655064072599377531764183756132567580951/4649372516509691842324086884111342773469184000000000), (553127505084157275948753340917096544882824844667/217939336711391805108941572692719192506368000000000), (151876620572631776220060521127539359972795859/59858826611405219909072087226393821184000000000), (1235613890116279917135316912055356865543/487132378022503417228776751516876800000000)],
    ![(188612604242007335527485536887675152020322671503529/74389960264155069477185390145781484375506944000000000), (1262661521782821902680015045101722095388618501459/498147055340324125963295023297643868585984000000000), (2426892379649792173445218899477644405833655021/957741225782483518545153395622301138944000000000), (19744322520199028010117543212750323583417/7794118048360054675660428024270028800000000)],
    ![(94184595964766822946690516633561681971262130855921/37194980132077534738592695072890742187753472000000000), (4413610611806495111170078588375282308657730752877/1743514693691134440871532581541753540050944000000000), (1211879415068737963684734730457329526051288149/478870612891241759272576697811150569472000000000), (1408487342752684096147858273758209808439/556722717740003905404316287447859200000000)]]

private theorem tensor279 (u v : ℝ) :
    eval poly084 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern279 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern279, Fin.sum_univ_succ]
  <;> ring

private theorem cert279 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern279) (m := (1/1000000000000000))
    tensor279 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern279]

private def bern280 : Coeff :=
  ![![(118220502629077392834490927917441/29537343830070769022251565056000000000), (1982420717103480528006830900865199/531672188941273842400528171008000000000), (102504055395804011987119201313/29669206972169299241100902400000000), (67207213816107070247773079/21126754639199330107392000000000)],
    ![(662225817710112352701289614171831/236298750640566152178012520448000000000), (10755874420989137348041491260068249/4253377511530190739204225368064000000000), (535250357368061575063858001687/237353655777354393928807219200000000), (334878789210433621815449969/169014037113594640859136000000000)],
    ![(3029295956975871766111477935555921/1890390005124529217424100163584000000000), (15071791918627510222367974265478133/11342340030747175304544600981504000000000), (667846772467159274202633252347/632943082072945050476819251200000000), (352217454948328386840262253/450704098969585708957696000000000)]]

private theorem tensor280 (u v : ℝ) :
    eval poly085 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern280 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern280, Fin.sum_univ_succ]
  <;> ring

private theorem cert280 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern280) (m := (1/1000000000000000))
    tensor280 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern280]

private def bern281 : Coeff :=
  ![![(75197083501639334704740295807631942852383/217939336711391805108941572692719192506368), (225586477196170100258332414698325783027487/653818010134175415326824718078157577519104), (20652621823798543741468852787259000809/59858826611405219909072087226393821184), (840339552009993734433036340254625/2435661890112517086143883757584384)],
    ![(1203109902699188664911715659033620135709857/3487029387382268881743065163083507080101888), (3609253337989919889424900788209175164685473/10461088162146806645229195489250521240305664), (330430020379824424891909401339367468631/957741225782483518545153395622301138944), (13444947458557386254215731753266335/38970590241800273378302140121350144)],
    ![(601533234686073987273793292572564592890793/1743514693691134440871532581541753540050944), (1804561520420559087358241470622568900465577/5230544081073403322614597744625260620152832), (165209045789436074960158579041295462159/478870612891241759272576697811150569472), (6722231042477436378751441031229335/19485295120900136689151070060675072)]]

private theorem tensor281 (u v : ℝ) :
    eval poly086 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern281 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern281, Fin.sum_univ_succ]
  <;> ring

private theorem cert281 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern281) (m := (1/1000000000000000))
    tensor281 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern281]

private def bern282 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor282 (u v : ℝ) :
    eval poly087 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern282 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern282, Fin.sum_univ_succ]
  <;> ring

private theorem cert282 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern282) (m := (1/1000000000000000))
    tensor282 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern282]

private def bern283 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)]]

private theorem tensor283 (u v : ℝ) :
    eval poly088 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern283 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern283, Fin.sum_univ_succ]
  <;> ring

private theorem cert283 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern283) (m := (1/1000000000000000))
    tensor283 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern283]

private def bern284 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor284 (u v : ℝ) :
    eval poly089 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern284 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern284, Fin.sum_univ_succ]
  <;> ring

private theorem cert284 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern284) (m := (1/1000000000000000))
    tensor284 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern284]

private def bern285 : Coeff :=
  ![![(12824049408315310103/6877198775781031936), (57708043634124800069/30947394491014643712), (115415729861661409349/61894788982029287424), (587032940953945/314813176381578)],
    ![(12824049408315310103/6877198775781031936), (57708043634124800069/30947394491014643712), (115415729861661409349/61894788982029287424), (587032940953945/314813176381578)],
    ![(12824049408315310103/6877198775781031936), (57708043634124800069/30947394491014643712), (115415729861661409349/61894788982029287424), (587032940953945/314813176381578)]]

private theorem tensor285 (u v : ℝ) :
    eval poly075 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern285 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern285, Fin.sum_univ_succ]
  <;> ring

private theorem cert285 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern285) (m := (1/1000000000000000))
    tensor285 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern285]

private def bern286 : Coeff :=
  ![![(286419603013979/209875450921052), (1288885161805093/944439529144734), (2577764220094561/1888879058289468), (214813176381578/157406588190789)],
    ![(286419603013979/209875450921052), (1288885161805093/944439529144734), (2577764220094561/1888879058289468), (214813176381578/157406588190789)],
    ![(286419603013979/209875450921052), (1288885161805093/944439529144734), (2577764220094561/1888879058289468), (214813176381578/157406588190789)]]

private theorem tensor286 (u v : ℝ) :
    eval poly076 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern286 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern286, Fin.sum_univ_succ]
  <;> ring

private theorem cert286 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern286) (m := (1/1000000000000000))
    tensor286 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern286]

private def bern287 : Coeff :=
  ![![(2389753745357647573/3438599387890515968), (10753867847571475583/15473697245507321856), (21507687682067074175/30947394491014643712), (109393512313798/157406588190789)],
    ![(2389753745357647573/3438599387890515968), (10753867847571475583/15473697245507321856), (21507687682067074175/30947394491014643712), (109393512313798/157406588190789)],
    ![(2389753745357647573/3438599387890515968), (10753867847571475583/15473697245507321856), (21507687682067074175/30947394491014643712), (109393512313798/157406588190789)]]

private theorem tensor287 (u v : ℝ) :
    eval poly077 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern287 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern287, Fin.sum_univ_succ]
  <;> ring

private theorem cert287 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern287) (m := (1/1000000000000000))
    tensor287 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern287]

private def bern288 : Coeff :=
  ![![(10328661582417003174098623/10816898375270057014984704), (92957519723410571617038929/97352085377430513134862336), (23239271301571034098926469/24338021344357628283715584), (16885784819534614727/17684225423436939264)],
    ![(82628999933291030585900783/86535187002160456119877632), (743657523254412872636167969/778816683019444105078898688), (185913511779733674689748629/194704170754861026269724672), (945600599916057273409/990316623712468598784)],
    ![(41314353603623017889506291/43267593501080228059938816), (371827444360770586168012253/389408341509722052539449344), (92956426573449538294042753/97352085377430513134862336), (472798624969088061053/495158311856234299392)]]

private theorem tensor288 (u v : ℝ) :
    eval poly078 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern288 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern288, Fin.sum_univ_succ]
  <;> ring

private theorem cert288 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern288) (m := (1/1000000000000000))
    tensor288 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern288]

private def bern289 : Coeff :=
  ![![(10401110926514380038687855111/59074687660141538044503130112), (10401034805531153332543238317/59074687660141538044503130112), (158706034620700303852767/901408197939171417915392), (1210822091045273163/6877198775781031936)],
    ![(83209357263988668821949815991/472597501281132304356025040896), (249626244878052671328555343031/1417792503843396913068075122688), (1269655446231294290618127/7211265583513371343323136), (9686631425118342203/55017590206248255488)],
    ![(41604913557931148667198395547/236298750640566152178012520448), (124813827211678831338036483227/708896251921698456534037561344), (634831307748493075207059/3605632791756685671661568), (4843343060937249551/27508795103124127744)]]

private theorem tensor289 (u v : ℝ) :
    eval poly079 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern289 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern289, Fin.sum_univ_succ]
  <;> ring

private theorem cert289 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern289) (m := (1/1000000000000000))
    tensor289 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern289]

private def bern290 : Coeff :=
  ![![(2309571371437556847300823185641/36921679787588461277814456320000), (20786199882798692809205554592443/332295118088296151500330106880000), (5074769878345644057656718677/81126737814525427612385280000), (25811685819989948693137/412631926546861916160000)],
    ![(18476027621104864747810045698361/295373438300707690222515650560000), (166284708929479386314628920030123/2658360944706369212002640855040000), (40596965151701664860929177957/649013902516203420899082240000), (206487414222975176569697/3301055412374895329280000)],
    ![(9237742135354637358606752955797/147686719150353845111257825280000), (83139909398284615077806701660351/1329180472353184606001320427520000), (20297885638319088630302303249/324506951258101710449541120000), (103240670943015381797149/1650527706187447664640000)]]

private theorem tensor290 (u v : ℝ) :
    eval poly080 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern290 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern290, Fin.sum_univ_succ]
  <;> ring

private theorem cert290 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern290) (m := (1/1000000000000000))
    tensor290 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern290]

private def bern291 : Coeff :=
  ![![(344595539176521231898052538205927476059344219/1376214264886868785327929717696957460946878464), (387665368460203675601203225714138158736025353/1548241047997727383493920932409077143565238272), (3943489129559014252931274153891207708511/15749522379534173416075855839122285395968), (60172152762841897419772163857028815/240318639824435019166196530748325888)],
    ![(2756778856777699814730360280815106957106776139/11009714119094950282623437741575659687575027712), (3101339308831872087917880436995147756383480153/12385928383981819067951367459272617148521906176), (10516026489771932873662731112017589663877/41998726345424462442868948904326094389248), (481379761645283827622493291526511615/1922549118595480153329572245986607104)],
    ![(196913814295944983876878589713056721838485609/786408151363925020187388410112547120541073408), (221525404998722483644723933448370731634196963/884709170284415647710811961376615510608707584), (2253446135868534515609013817212562593941/8999727074019527666329060479498448797696), (34384450084845176849057805156913765/137324937042534296666398017570471936)]]

private theorem tensor291 (u v : ℝ) :
    eval poly081 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern291 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern291, Fin.sum_univ_succ]
  <;> ring

private theorem cert291 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern291) (m := (1/1000000000000000))
    tensor291 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern291]

private def bern292 : Coeff :=
  ![![(3936427878420714032981829527904482149950493/9298745033019383684648173768222685546938368), (11809220703262901174025422915978921898501149/27896235099058151053944521304668056640815104), (1621741026971086381841233998660735033659/3830964903129934074180613582489204555776), (4124278728849887015641989517440085/9742647560450068344575535030337536)],
    ![(31491147210484774706525178653454148476633773/74389960264155069477185390145781484375506944), (94472938179869904090323493343586949002134189/223169880792465208431556170437344453126520832), (12973814583926431291734733363191164576299/30647719225039472593444908659913636446208), (32993940851620449298171169762371685/77941180483600546756604280242700288)],
    ![(2249347956685988367799694363119459982404543/5313568590296790676941813581841534598250496), (6748007909545471342031685954238751629732799/15940705770890372030825440745524603794751488), (926692925148869394909971052649746348809/2189122801788533756674636332850974031872), (2356689419460128747943315956087335/5567227177400039054043162874478592)]]

private theorem tensor292 (u v : ℝ) :
    eval poly082 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern292 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern292, Fin.sum_univ_succ]
  <;> ring

private theorem cert292 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern292) (m := (1/1000000000000000))
    tensor292 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern292]

private def bern293 : Coeff :=
  ![![(536266795727691475417957714072006784152300216121249/13602735591159784132971042769514328571521269760000000), (1885306224067063530904653330163161622160906915599/47822117312671116092476322236573811384254464000000), (7990940918398960766619828704130235491850483/202696555721160533025429290078793891840000000), (146317975986242187616065193517307616799/3711484784933359369362108582985728000000)],
    ![(4290207202025749435371434752106306402068078959017329/108821884729278273063768342156114628572170158080000000), (15082705853938089276472280899432328352416534841407/382576938501368928739810577892590491074035712000000), (63928612662568550676896058620485943821485923/1621572445769284264203434320630351134720000000), (1170563680345789143661350213764528931919/29691878279466874954896868663885824000000)],
    ![(2145140019114983533699603895818279265458878094532333/54410942364639136531884171078057314286085079040000000), (1077354422524262164693381082682811694824701025573/27326924178669209195700755563756463648145408000000), (31964848988972707610416743803965001854083991/810786222884642132101717160315175567360000000), (585291776400820393197089439695298464723/14845939139733437477448434331942912000000)]]

private theorem tensor293 (u v : ℝ) :
    eval poly083 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern293 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern293, Fin.sum_univ_succ]
  <;> ring

private theorem cert293 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern293) (m := (1/1000000000000000))
    tensor293 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern293]

private def bern294 : Coeff :=
  ![![(2007948047853996860720650059622722131242289333418811/793492909484320741089977494888335833338740736000000000), (42352052589961697490434687497873925620389806108891/16737741059434890632366712782800833984489062400000000), (4846452833295184220112360048724914772531958869/1915482451564967037090306791244602277888000000000), (1408487342752684096147858273758209808439/556722717740003905404316287447859200000000)],
    ![(16058392122659532469966173337607389589270526731557931/6347943275874565928719819959106686666709925888000000000), (338706897737497109285435560696849599519764112393163/133901928475479125058933702262406671875912499200000000), (5537012699922268620289807208260460576242155827/2189122801788533756674636332850974031872000000000), (78849791472488858720232535950324363007313/31176472193440218702641712097080115200000000)],
    ![(8026599931243545027083573099116501064301369397882687/3173971637937282964359909979553343333354962944000000000), (24185526768235759903385258672193413862600698279657/9564423462534223218495264447314762276850892800000000), (19373277566275143461579210262923564943567255313/7661929806259868148361227164978409111552000000000), (39412145875413704028092504285094488371021/15588236096720109351320856048540057600000000)]]

private theorem tensor294 (u v : ℝ) :
    eval poly084 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern294 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern294, Fin.sum_univ_succ]
  <;> ring

private theorem cert294 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern294) (m := (1/1000000000000000))
    tensor294 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern294]

private def bern295 : Coeff :=
  ![![(34108411065993681919937310480234807/34567131522277105690040688705536000000000), (23807608460416360983066957901914403/25925348641707829267530516529152000000000), (75311214073211285207009874610513/88612031490212307066754695168000000000), (352217454948328386840262253/450704098969585708957696000000000)],
    ![(664691289067179132799825067919551053/967879682623758959321139283755008000000000), (1346570897298686212729877994041895571/2177729285903457658472563388448768000000000), (584759017100602435979915953654423/1063344377882547684801056342016000000000), (2604231510541456828080334043/5408449187635028507492352000000000)],
    ![(1497362041080952395729965160414787241/3871518730495035837284557135020032000000000), (2773151714186608480114177807258394807/8710917143613830633890253553795072000000000), (1063105042511723541753726088466411/4253377511530190739204225368064000000000), (3927267668520791763641148511/21633796750540114029969408000000000)]]

private theorem tensor295 (u v : ℝ) :
    eval poly085 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern295 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern295, Fin.sum_univ_succ]
  <;> ring

private theorem cert295 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern295) (m := (1/1000000000000000))
    tensor295 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern295]

private def bern296 : Coeff :=
  ![![(9624073557563887299650533178348047859520425/27896235099058151053944521304668056640815104), (28872067942300115732317380161549319340233641/83688705297174453161833563914004169922445312), (660825696089212504292744823391771873039/1915482451564967037090306791244602277888), (6722231042477436378751441031229335/19485295120900136689151070060675072)],
    ![(76991893561265811414098465110235008997046265/223169880792465208431556170437344453126520832), (230974458851994026192165939421051678686885881/669509642377395625294668511312033359379562496), (5286557854287781644284721361873530914879/15323859612519736296722454329956818223104), (53777362966216977533298678559027015/155882360967201093513208560485400576)],
    ![(5499371333001466030785190342406116794137795/15940705770890372030825440745524603794751488), (16498026726113366180413774110693485903707331/47822117312671116092476322236573811384254464), (377607867132990232444820295472349060389/1094561400894266878337318166425487015936), (3841205542329604574041844919158525/11134454354800078108086325748957184)]]

private theorem tensor296 (u v : ℝ) :
    eval poly086 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern296 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern296, Fin.sum_univ_succ]
  <;> ring

private theorem cert296 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern296) (m := (1/1000000000000000))
    tensor296 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern296]

private def bern297 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor297 (u v : ℝ) :
    eval poly087 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern297 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern297, Fin.sum_univ_succ]
  <;> ring

private theorem cert297 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern297) (m := (1/1000000000000000))
    tensor297 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern297]

private def bern298 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)]]

private theorem tensor298 (u v : ℝ) :
    eval poly088 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern298 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern298, Fin.sum_univ_succ]
  <;> ring

private theorem cert298 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern298) (m := (1/1000000000000000))
    tensor298 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern298]

private def bern299 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor299 (u v : ℝ) :
    eval poly089 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern299 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern299, Fin.sum_univ_succ]
  <;> ring

private theorem cert299 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern299) (m := (1/1000000000000000))
    tensor299 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern299]

private def bern300 : Coeff :=
  ![![(7327977175239007089/3929827871874875392), (230831102316734627909/123789577964058574848), (461661847226881065029/247579155928117149696), (587032940953945/314813176381578)],
    ![(7327977175239007089/3929827871874875392), (230831102316734627909/123789577964058574848), (461661847226881065029/247579155928117149696), (587032940953945/314813176381578)],
    ![(7327977175239007089/3929827871874875392), (230831102316734627909/123789577964058574848), (461661847226881065029/247579155928117149696), (587032940953945/314813176381578)]]

private theorem tensor300 (u v : ℝ) :
    eval poly075 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern300 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern300, Fin.sum_univ_succ]
  <;> ring

private theorem cert300 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern300) (m := (1/1000000000000000))
    tensor300 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern300]

private def bern301 : Coeff :=
  ![![(163667472648613/119928829097744), (5155522336673497/3777758116578936), (10311038569831369/7555516233157872), (214813176381578/157406588190789)],
    ![(163667472648613/119928829097744), (5155522336673497/3777758116578936), (10311038569831369/7555516233157872), (214813176381578/157406588190789)],
    ![(163667472648613/119928829097744), (5155522336673497/3777758116578936), (10311038569831369/7555516233157872), (214813176381578/157406588190789)]]

private theorem tensor301 (u v : ℝ) :
    eval poly076 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern301 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern301, Fin.sum_univ_succ]
  <;> ring

private theorem cert301 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern301) (m := (1/1000000000000000))
    tensor301 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern301]

private def bern302 : Coeff :=
  ![![(1365566709764959043/1964913935937437696), (43015327351058271359/61894788982029287424), (86030606689040665727/123789577964058574848), (109393512313798/157406588190789)],
    ![(1365566709764959043/1964913935937437696), (43015327351058271359/61894788982029287424), (86030606689040665727/123789577964058574848), (109393512313798/157406588190789)],
    ![(1365566709764959043/1964913935937437696), (43015327351058271359/61894788982029287424), (86030606689040665727/123789577964058574848), (109393512313798/157406588190789)]]

private theorem tensor302 (u v : ℝ) :
    eval poly077 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern302 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern302, Fin.sum_univ_succ]
  <;> ring

private theorem cert302 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern302) (m := (1/1000000000000000))
    tensor302 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern302]

private def bern303 : Coeff :=
  ![![(31477271685010210115192027/32965785524632554712334336), (5949197396208768263495334389/6230533464155552840631189504), (371824402747216934816567425/389408341509722052539449344), (472798624969088061053/495158311856234299392)],
    ![(251817950451006121861160599/263726284197060437698674688), (47593537017180998786988928633/49844267713244422725049516032), (2974592587447547108244735605/3115266732077776420315594752), (3782385649774823337121/3961266494849874395136)],
    ![(125908863710965281400392491/131863142098530218849337344), (23796747432345925733007591077/24922133856622211362524758016), (1487294976458679368978465905/1557633366038888210157797376), (1891191149898471092909/1980633247424937197568)]]

private theorem tensor303 (u v : ℝ) :
    eval poly078 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern303 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern303, Fin.sum_univ_succ]
  <;> ring

private theorem cert303 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern303) (m := (1/1000000000000000))
    tensor303 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern303]

private def bern304 : Coeff :=
  ![![(95095379345683798773564996045/540111430035579776406885761024), (1996999312436410374725620159643/11342340030747175304544600981504), (2539311292797994594653075/14422531167026742686646272), (4843343060937249551/27508795103124127744)],
    ![(760764108694925784194084950065/4320891440284638211255086088192), (760762716760408713487666092731/4320891440284638211255086088192), (2902074145612759658316825/16482892762316277356167168), (5535257026322021901/31438622974999003136)],
    ![(380382591312190589099824965885/2160445720142319105627543044096), (7988019802222941484338507308779/45369360122988701218178403926016), (10157273848097339229605475/57690124668106970746585088), (19373426940505155103/110035180412496510976)]]

private theorem tensor304 (u v : ℝ) :
    eval poly079 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern304 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern304, Fin.sum_univ_succ]
  <;> ring

private theorem cert304 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern304) (m := (1/1000000000000000))
    tensor304 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern304]

private def bern305 : Coeff :=
  ![![(21114970696368313206255509956227/337569643772237360254303600640000), (1330244074568640206004874471811263/21266887557650953696021126840320000), (3247668445464487727336956601/51921112201296273671926579200), (103240670943015381797149/1650527706187447664640000)],
    ![(168918523638985226574482211195999/2700557150177898882034428805120000), (1520267764988308774819201115890973/24305014351601089938309859246080000), (18557968960221947326521857399/296692069721692992411009024000), (117988470743882663057399/1886317378499940188160000)],
    ![(84458640853511973749460171371091/1350278575088949441017214402560000), (5320898056643600599714909923991759/85067550230603814784084507361280000), (64952413812263876738913869773/1038422244025925473438531584000), (412956611435117114213197/6602110824749790658560000)]]

private theorem tensor305 (u v : ℝ) :
    eval poly080 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern305 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern305, Fin.sum_univ_succ]
  <;> ring

private theorem cert305 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern305) (m := (1/1000000000000000))
    tensor305 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern305]

private def bern306 : Coeff :=
  ![![(600102223745170257810208551259228777874616509/2396672461299581013904421821295381700696604672), (506334744973361456134975645752213947442921541/2022192389221521480481855911717978309962760192), (9013704098149775045548570773503064103061/35998908296078110665316241917993795190784), (34384450084845176849057805156913765/137324937042534296666398017570471936)],
    ![(4800824121648360715086279194763446624997438433/19173379690396648111235374570363053605572837376), (28354783114956876530952037028669702925310697279/113242773796405202906983931056206785357914570752), (504768095223612491786208599748717322620719/2015938864580374197257709547407652530683904), (1925531744293878551811553069457451935/7690196474381920613318288983946428416)],
    ![(2400415226667679683845444989726531513498972397/9586689845198324055617687285181526802786418688), (14177410255702755759172718947607712396908894131/56621386898202601453491965528103392678957285376), (28042708941713198945649846454514614192779/111996603587798566514317197078202918371328), (962767141918213600037934525063866515/3845098237190960306659144491973214208)]]

private theorem tensor306 (u v : ℝ) :
    eval poly081 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern306 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern306, Fin.sum_univ_succ]
  <;> ring

private theorem cert306 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern306) (m := (1/1000000000000000))
    tensor306 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern306]

private def bern307 : Coeff :=
  ![![(1713768370575495008915600367755118419713411/4048433211654697658622334157593550170095616), (46271684359305377775188890136149310760946075/109307696714676836782803022255025854592581632), (3706756885436171352163807833616258906889/8756491207154135026698545331403896127488), (2356689419460128747943315956087335/5567227177400039054043162874478592)],
    ![(13710116944078918799775984791818167142739807/32387465693237581268978673260748401360764928), (2591208650249427466453263833427442927146723425/6121231016021902859836969246281447857184571392), (207577931058873203586042790922104725439051/490363507600631561495118538558618183139328), (131974318510588563057860947163741765/311764721934402187026417120970801152)],
    ![(6855043461776938764113583320797693463886163/16193732846618790634489336630374200680382464), (1295601488188876888747974909615262225840233325/3060615508010951429918484623140723928592285696), (103788738266660405725456171580849476046159/245181753800315780747559269279309091569664), (65987014765704958115448100393296385/155882360967201093513208560485400576)]]

private theorem tensor307 (u v : ℝ) :
    eval poly082 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern307 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern307, Fin.sum_univ_succ]
  <;> ring

private theorem cert307 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern307) (m := (1/1000000000000000))
    tensor307 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern307]

private def bern308 : Coeff :=
  ![![(6537517071854475597433301355325435258470560526002041/165823824349376416097170807095031814967116431360000000), (86187892290601777013568469622374749762763307307449/2186153934293536735656060445100517091851632640000000), (42619684544827706943942625867880900771433437/1081048297179522842802289547086900756480000000), (585291776400820393197089439695298464723/14845939139733437477448434331942912000000)],
    ![(52300358545248767172377685497045456200468798734330317/1326590594795011328777366456760254519736931450880000000), (4826542452780366034203495421423466616684460885405531/122424620320438057196739384925628957143691427840000000), (340958923431469521447969032797586886371969409/8648386377436182742418316376695206051840000000), (4682354083662414788309544183188455715311/118767513117867499819587474655543296000000)],
    ![(26150290257830864782644480075743715166586556630322153/663295297397505664388683228380127259868465725440000000), (2413281468643516277823578271996973623327088280796959/61212310160219028598369692462814478571845713920000000), (170480185252158693672198529326063283286235661/4324193188718091371209158188347603025920000000), (2341186978059133215521186424407261856419/59383756558933749909793737327771648000000)]]

private theorem tensor308 (u v : ℝ) :
    eval poly083 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern308 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern308, Fin.sum_univ_succ]
  <;> ring

private theorem cert308 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern308) (m := (1/1000000000000000))
    tensor308 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern308]

private def bern309 : Coeff :=
  ![![(10481994111130252595833802868457828664898814324233071/4145595608734410402429270177375795374177910784000000000), (1934629486175089217342905607316505063687136703910541/765153877002737857479621155785180982148071424000000000), (77488851388325174873243293381552493715939981073/30647719225039472593444908659913636446208000000000), (39412145875413704028092504285094488371021/15588236096720109351320856048540057600000000)],
    ![(83849171336428798707762493661699024154478532323962427/33164764869875283219434161419006362993423286272000000000), (15475784219703661062063730595582151618933130479910897/6121231016021902859836969246281447857184571392000000000), (619860676470122696875898195146791420409641262661/245181753800315780747559269279309091569664000000000), (315271667281648181560692506900620520702897/124705888773760874810566848388320460800000000)],
    ![(41921194891907788324427282187867709494883275027030143/16582382434937641609717080709503181496711643136000000000), (7737266275003304192692108166316131364184583664268733/3060615508010951429918484623140723928592285696000000000), (309905270916821997382925021620581445545881338369/122590876900157890373779634639654545784832000000000), (157623083779993365448322489760242567218813/62352944386880437405283424194160230400000000)]]

private theorem tensor309 (u v : ℝ) :
    eval poly084 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern309 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern309, Fin.sum_univ_succ]
  <;> ring

private theorem cert309 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern309) (m := (1/1000000000000000))
    tensor309 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern309]

private def bern310 : Coeff :=
  ![![(8241822913771049223471322188007284499/35396742678811756226601665234468864000000000), (30068527956922047725663718914672734391/139374674297821290142244056860721152000000000), (135180070713173240918064114712739/680540401844830518272676058890240000000), (3927267668520791763641148511/21633796750540114029969408000000000)],
    ![(22348978684490620220063584172339995107/141586970715247024906406660937875456000000000), (26154868347183795078137039225354115181/185832899063761720189658742480961536000000000), (80136378903331699449292673696771/648133716042695731688262913228800000000), (439019633354196738375447923/4120723190579069339041792000000000)],
    ![(245667136258893877141272157192770061/2965172161575853924741500752625664000000000), (146619448693058993128336301715399809239/2229994788765140642275904909771538432000000000), (2648482943871281395001582027379791/54443232147586441461814084711219200000000), (10918869128881283536147939199/346140748008641824479510528000000000)]]

private theorem tensor310 (u v : ℝ) :
    eval poly085 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern310 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern310, Fin.sum_univ_succ]
  <;> ring

private theorem cert310 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern310) (m := (1/1000000000000000))
    tensor310 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern310]

private def bern311 : Coeff :=
  ![![(12569842008127993196290877862448158609520229/36435898904892278927601007418341951530860544), (1396647264981483150039811406437056171543423/4048433211654697658622334157593550170095616), (1510425476032498576584648864271227985189/4378245603577067513349272665701948063744), (3841205542329604574041844919158525/11134454354800078108086325748957184)],
    ![(703909564133456542342539362617685770797406111/2040410338673967619945656415427149285728190464), (78212070359012701456961924827274548505994957/226712259852663068882850712825238809525354496), (84583635800894137438340519245912653000671/245181753800315780747559269279309091569664), (215107024996855342649630465782069735/623529443868804374052834241941602304)],
    ![(351953987905872732846394782469137329730839699/1020205169336983809972828207713574642864095232), (39105946939531173255847205447036975702779113/113356129926331534441425356412619404762677248), (42291722471984177293970351046318269415379/122590876900157890373779634639654545784832), (107553269811626414576458808045631035/311764721934402187026417120970801152)]]

private theorem tensor311 (u v : ℝ) :
    eval poly086 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern311 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern311, Fin.sum_univ_succ]
  <;> ring

private theorem cert311 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern311) (m := (1/1000000000000000))
    tensor311 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern311]

private def bern312 : Coeff :=
  ![![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)],
    ![(8218687/500000000), (8218687/500000000), (8218687/500000000), (8218687/500000000)]]

private theorem tensor312 (u v : ℝ) :
    eval poly087 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern312 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern312, Fin.sum_univ_succ]
  <;> ring

private theorem cert312 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern312) (m := (1/1000000000000000))
    tensor312 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern312]

private def bern313 : Coeff :=
  ![![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)],
    ![(3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000), (3049735378453549211/500000000000000000000)]]

private theorem tensor313 (u v : ℝ) :
    eval poly088 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern313 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern313, Fin.sum_univ_succ]
  <;> ring

private theorem cert313 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern313) (m := (1/1000000000000000))
    tensor313 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern313]

private def bern314 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor314 (u v : ℝ) :
    eval poly089 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern314 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern314, Fin.sum_univ_succ]
  <;> ring

private theorem cert314 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern314) (m := (1/1000000000000000))
    tensor314 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern314]

private def bern315 : Coeff :=
  ![![(547594679/400000000), (247914384965332909/202334133600000000), (13677252036379877/12645883350000000), (12650512013254877/13488942240000000)],
    ![(5577859543/8000000000), (2194388166693143729/4046682672000000000), (108117695590111136479639/263240108151123000000000), (3823307905066378914688741/12635525191253904000000000)],
    ![(1226912753/4000000000), (409156422984726799/2023341336000000000), (624347333888293459347799/4738321946720214000000000), (59599541009306547076159/701973621736328000000000)]]

private theorem tensor315 (u v : ℝ) :
    eval poly090 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern315 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly090, bern315, Fin.sum_univ_succ]
  <;> ring

private theorem cert315 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly090 δ p := by
  apply positive_on_box_from_tensor (β := bern315) (m := (1/1000000000000000))
    tensor315 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern315]

private def bern316 : Coeff :=
  ![![(1234541619/2000000000), (62102020978851961/112407852000000000), (3426122259969233/7025490750000000), (3168926089344233/7493856800000000)],
    ![(10873183523/40000000000), (1447179018632123623/6744471120000000000), (5896368598246835563842683/35537414600401605000000000), (23856827981768137782401003/189532877868808560000000000)],
    ![(4152767333/20000000000), (460523883750744193/3372235560000000000), (6320222233842066070534517/71074829200803210000000000), (5441527917768693119654753/94766438934404280000000000)]]

private theorem tensor316 (u v : ℝ) :
    eval poly091 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern316 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly091, bern316, Fin.sum_univ_succ]
  <;> ring

private theorem cert316 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly091 δ p := by
  apply positive_on_box_from_tensor (β := bern316) (m := (1/1000000000000000))
    tensor316 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern316]

private def bern317 : Coeff :=
  ![![(6562779479904877/73740785200000000), (2971189277066961723550367/37300694711064256800000000), (163918300246743356348551/2331293419441516050000000), (151613088721921711973551/2486712980737617120000000)],
    ![(91251479506480449/2949631408000000000), (39398176038362486118697367/1492027788442570272000000000), (2119161045937036477677523/93251736777660642000000000), (9894474901348328552271323/497342596147523424000000000)],
    ![(63693869095882909/1474815704000000000), (18802500394730488704787567/746013894221285136000000000), (5464321952336877736398949/373006947110642568000000000), (2273511581534376659312533/248671298073761712000000000)]]

private theorem tensor317 (u v : ℝ) :
    eval poly092 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern317 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly092, bern317, Fin.sum_univ_succ]
  <;> ring

private theorem cert317 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly092 δ p := by
  apply positive_on_box_from_tensor (β := bern317) (m := (1/1000000000000000))
    tensor317 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern317]

private def bern318 : Coeff :=
  ![![(63693869095882909/1474815704000000000), (51021109942598698003694173/1492027788442570272000000000), (40376127121001471090639819/1492027788442570272000000000), (213720961984473453016001/9946851922950468480000000)],
    ![(163523996877051187/2949631408000000000), (118528041117877612811694359/2984055576885140544000000000), (41036966385534879940124621/1492027788442570272000000000), (3619573385407856653543171/198937038459009369600000000)],
    ![(101764053484334139/737407852000000000), (79394571505210131495048863/746013894221285136000000000), (3796591504400378260623559/46625868388830321000000000), (3074408866394957876641273/49734259614752342400000000)]]

private theorem tensor318 (u v : ℝ) :
    eval poly092 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern318 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly092, bern318, Fin.sum_univ_succ]
  <;> ring

private theorem cert318 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : 0 < eval poly092 δ p := by
  apply positive_on_box_from_tensor (β := bern318) (m := (1/1000000000000000))
    tensor318 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern318]

private def bern319 : Coeff :=
  ![![(213720961984473453016001/9946851922950468480000000), (23740161474340564814160481/1492027788442570272000000000), (17749178649276885450735497/1492027788442570272000000000), (2273511581534376659312533/248671298073761712000000000)],
    ![(7893992625097325713863191/397874076918018739200000000), (1479871834796941387087337/119362223075405621760000000), (8581014091324748680951729/1193622230754056217600000000), (29972756702863451228831/7957481538360374784000000)],
    ![(11905600738042506936985727/397874076918018739200000000), (113227034108391872798728861/5968111153770281088000000000), (33455193110956824390629041/2984055576885140544000000000), (742436050244571934294241/124335649036880856000000000)]]

private theorem tensor319 (u v : ℝ) :
    eval poly092 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern319 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly092, bern319, Fin.sum_univ_succ]
  <;> ring

private theorem cert319 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly092 δ p := by
  apply positive_on_box_from_tensor (β := bern319) (m := (1/1000000000000000))
    tensor319 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern319]

private def bern320 : Coeff :=
  ![![(11905600738042506936985727/397874076918018739200000000), (113227034108391872798728861/5968111153770281088000000000), (33455193110956824390629041/2984055576885140544000000000), (742436050244571934294241/124335649036880856000000000)],
    ![(15917208850987688160108263/397874076918018739200000000), (19057559559617084530386359/746013894221285136000000000), (90915701987203554157757519/5968111153770281088000000000), (8132382216055219545103981/994685192295046848000000000)],
    ![(3074408866394957876641273/49734259614752342400000000), (15743400960721342064630623/373006947110642568000000000), (20877247207283395413617467/746013894221285136000000000), (2233202697816510365031293/124335649036880856000000000)]]

private theorem tensor320 (u v : ℝ) :
    eval poly092 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern320 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly092, bern320, Fin.sum_univ_succ]
  <;> ring

private theorem cert320 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly092 δ p := by
  apply positive_on_box_from_tensor (β := bern320) (m := (1/1000000000000000))
    tensor320 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern320]

private def bern321 : Coeff :=
  ![![(6562779479904877/73740785200000000), (2971189277066961723550367/37300694711064256800000000), (163918300246743356348551/2331293419441516050000000), (151613088721921711973551/2486712980737617120000000)],
    ![(91251479506480449/2949631408000000000), (39398176038362486118697367/1492027788442570272000000000), (2119161045937036477677523/93251736777660642000000000), (9894474901348328552271323/497342596147523424000000000)],
    ![(63693869095882909/1474815704000000000), (18802500394730488704787567/746013894221285136000000000), (5464321952336877736398949/373006947110642568000000000), (2273511581534376659312533/248671298073761712000000000)]]

private theorem tensor321 (u v : ℝ) :
    eval poly093 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern321 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern321, Fin.sum_univ_succ]
  <;> ring

private theorem cert321 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern321) (m := (1/1000000000000000))
    tensor321 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern321]

private def bern322 : Coeff :=
  ![![(63693869095882909/1474815704000000000), (51021109942598698003694173/1492027788442570272000000000), (40376127121001471090639819/1492027788442570272000000000), (213720961984473453016001/9946851922950468480000000)],
    ![(163523996877051187/2949631408000000000), (118528041117877612811694359/2984055576885140544000000000), (41036966385534879940124621/1492027788442570272000000000), (3619573385407856653543171/198937038459009369600000000)],
    ![(101764053484334139/737407852000000000), (79394571505210131495048863/746013894221285136000000000), (3796591504400378260623559/46625868388830321000000000), (3074408866394957876641273/49734259614752342400000000)]]

private theorem tensor322 (u v : ℝ) :
    eval poly093 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern322 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern322, Fin.sum_univ_succ]
  <;> ring

private theorem cert322 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : 0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern322) (m := (1/1000000000000000))
    tensor322 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern322]

private def bern323 : Coeff :=
  ![![(213720961984473453016001/9946851922950468480000000), (23740161474340564814160481/1492027788442570272000000000), (17749178649276885450735497/1492027788442570272000000000), (2273511581534376659312533/248671298073761712000000000)],
    ![(7893992625097325713863191/397874076918018739200000000), (1479871834796941387087337/119362223075405621760000000), (8581014091324748680951729/1193622230754056217600000000), (29972756702863451228831/7957481538360374784000000)],
    ![(11905600738042506936985727/397874076918018739200000000), (113227034108391872798728861/5968111153770281088000000000), (33455193110956824390629041/2984055576885140544000000000), (742436050244571934294241/124335649036880856000000000)]]

private theorem tensor323 (u v : ℝ) :
    eval poly093 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern323 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern323, Fin.sum_univ_succ]
  <;> ring

private theorem cert323 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern323) (m := (1/1000000000000000))
    tensor323 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern323]

private def bern324 : Coeff :=
  ![![(11905600738042506936985727/397874076918018739200000000), (113227034108391872798728861/5968111153770281088000000000), (33455193110956824390629041/2984055576885140544000000000), (742436050244571934294241/124335649036880856000000000)],
    ![(15917208850987688160108263/397874076918018739200000000), (19057559559617084530386359/746013894221285136000000000), (90915701987203554157757519/5968111153770281088000000000), (8132382216055219545103981/994685192295046848000000000)],
    ![(3074408866394957876641273/49734259614752342400000000), (15743400960721342064630623/373006947110642568000000000), (20877247207283395413617467/746013894221285136000000000), (2233202697816510365031293/124335649036880856000000000)]]

private theorem tensor324 (u v : ℝ) :
    eval poly093 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern324 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern324, Fin.sum_univ_succ]
  <;> ring

private theorem cert324 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern324) (m := (1/1000000000000000))
    tensor324 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern324]

private def bern325 : Coeff :=
  ![![(12643259467/200000000000), (5724025478922573257/101167066800000000000), (315790223906658721/6322941675000000000), (292084112406033721/6744471120000000000)],
    ![(172011200933/16000000000000), (822353314233131862923525617957/89998748232705535392000000000000), (1467935570806922310389317910101/179997496465411070784000000000000), (468261974256258188314543962551/59999165488470356928000000000000)],
    ![(228780822253/8000000000000), (1175694758657262937963580563/89998748232705535392000000000), (1692062833635456109492632524429/359994992930822141568000000000000), (1086233283303318226861052417/959986647815525710848000000000)]]

private theorem tensor325 (u v : ℝ) :
    eval poly094 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern325 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern325, Fin.sum_univ_succ]
  <;> ring

private theorem cert325 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern325) (m := (1/1000000000000000))
    tensor325 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern325]

private def bern326 : Coeff :=
  ![![(228780822253/8000000000000), (937360802864912702422343661943/44999374116352767696000000000000), (21392614714103111100104453367517/1439979971723288566272000000000000), (39849142529655759208022580433/3839946591262102843392000000000)],
    ![(743112088079/16000000000000), (5708983560812770350796807745041/179997496465411070784000000000000), (70673878801042608301462505387/3461490316642520592000000000000), (143408710674222399342061367783/11999833097694071385600000000000)],
    ![(538415632913/4000000000000), (4654917957587363111047993129369/44999374116352767696000000000000), (5675242017330487096997751653159/71998998586164428313600000000000), (285861045406072969625120466659/4799933239077628554240000000000)]]

private theorem tensor326 (u v : ℝ) :
    eval poly094 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern326 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern326, Fin.sum_univ_succ]
  <;> ring

private theorem cert326 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern326) (m := (1/1000000000000000))
    tensor326 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern326]

private def bern327 : Coeff :=
  ![![(39849142529655759208022580433/3839946591262102843392000000000), (225362217613073250085778361727/27691922533140164736000000000000), (36130713444646727203964485938449/5759919886893154265088000000000000), (3036217045124289701579480846911/639991098543683807232000000000000)],
    ![(2143498248635173174937055453089/191997329563105142169600000000000), (2854029555827872294915914986281/359994992930822141568000000000000), (12056397594381346195862962331693/2303967954757261706035200000000000), (3869710075456925328186779344751/1279982197087367614464000000000000)],
    ![(9007988842150411762175955728533/383994659126210284339200000000000), (26457671959198528268880214608913/1439979971723288566272000000000000), (324186417658700920656295979118509/23039679547572617060352000000000000), (26793937453096729476390916857187/2559964394174735228928000000000000)]]

private theorem tensor327 (u v : ℝ) :
    eval poly094 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((3/8)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern327 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern327, Fin.sum_univ_succ]
  <;> ring

private theorem cert327 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern327) (m := (1/1000000000000000))
    tensor327 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern327]

private def bern328 : Coeff :=
  ![![(3036217045124289701579480846911/639991098543683807232000000000000), (11461786693427273684670374232037/2879959943446577132544000000000000), (76024641250706338621992932208313/23039679547572617060352000000000000), (20729306089488374720885991327449/7679893182524205686784000000000000)],
    ![(9942144165705504731345741038573/2559964394174735228928000000000000), (33973619403212110589772806126527/11519839773786308530176000000000000), (195132816568475156388535400951659/92158718190290468241408000000000000), (42471360554788074233013258464819/30719572730096822747136000000000000)],
    ![(10883529187084317919091191524767/2047971515339788183142400000000000), (37971960846573408284394884316869/9215871819029046824140800000000000), (224989176073376257403628339887417/73726974552232374593126400000000000), (51637608769344551944074977712169/24575658184077458197708800000000000)]]

private theorem tensor328 (u v : ℝ) :
    eval poly094 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern328 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern328, Fin.sum_univ_succ]
  <;> ring

private theorem cert328 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern328) (m := (1/1000000000000000))
    tensor328 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern328]

private def bern329 : Coeff :=
  ![![(353021198641779120693639120509/109314686415667200000000000000000), (842343681188073760024354082813/327944059247001600000000000000000), (10175906229145479057727181929/5124125925734400000000000000000), (2530242439359625318184760643/1708041975244800000000000000000)],
    ![(2194248265821949469628596811391/874517491325337600000000000000000), (4612746985281458626640749215487/2623552473976012800000000000000000), (44792891883877139569099071971/40993007405875200000000000000000), (7003849392322308990784190657/13664335801958400000000000000000)],
    ![(16804444580247215590085877843809/6996139930602700800000000000000000), (2489516776614153933959874859301/1614493830139084800000000000000000), (19554874971551731318884427633/25226466095923200000000000000000), (11099725946785232904989819743/109314686415667200000000000000000)]]

private theorem tensor329 (u v : ℝ) :
    eval poly095 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern329 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly095, bern329, Fin.sum_univ_succ]
  <;> ring

private theorem cert329 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly095 δ p := by
  apply positive_on_box_from_tensor (β := bern329) (m := (1/1000000000000000))
    tensor329 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern329]

private def bern330 : Coeff :=
  ![![(929627825716841349118656817518581/491513163681549163954176000000000000), (558030969815698523248699941910483/368634872761161872965632000000000000), (6845834029226015130492926005174721/5898157964178589967450112000000000000), (544802048584302831953032219529189/655350884908732218605568000000000000)],
    ![(428073486065875056652427922420121/245756581840774581977088000000000000), (243398028494011699662445999817171/184317436380580936482816000000000000), (546231099739931784886075850920913/589815796417858996745011200000000000), (182759649521639604160085436830521/327675442454366109302784000000000000)],
    ![(51637608769344551944074977712169/24575658184077458197708800000000000), (29968662856340588761630807440263/18431743638058093648281600000000000), (348056067104632624343413433439013/294907898208929498372505600000000000), (25006260364111094942292044091577/32767544245436610930278400000000000)]]

private theorem tensor330 (u v : ℝ) :
    eval poly094 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern330 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern330, Fin.sum_univ_succ]
  <;> ring

private theorem cert330 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern330) (m := (1/1000000000000000))
    tensor330 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern330]

private def bern331 : Coeff :=
  ![![(6520457395835207702354093743/5338592931659907072000000000000), (2824856719896352597698793831441/3123076865021045637120000000000000), (7452355110952047491895323309/12199519003988459520000000000000), (1380904032617530626338798383/4066506334662819840000000000000)],
    ![(150375466531161170817026580353/138803416223157583872000000000000), (4673464666640357891680426887611/6246153730042091274240000000000000), (10674513602755765474775187439/24399038007976919040000000000000), (1222235375058587445332034053/8133012669325639680000000000000)],
    ![(293735637583695189849015578827/277606832446315167744000000000000), (8772095913081658905813605923081/12492307460084182548480000000000000), (18153147111287711779522006469/48798076015953838080000000000000), (1082134637906944766136020023/16266025338651279360000000000000)]]

private theorem tensor331 (u v : ℝ) :
    eval poly096 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern331 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern331, Fin.sum_univ_succ]
  <;> ring

private theorem cert331 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern331) (m := (1/1000000000000000))
    tensor331 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern331]

private def bern332 : Coeff :=
  ![![(1775965853953083147439214848682813/2621403539634928874422272000000000000), (2321950069061594166577608922206271/4718526371342871973960089600000000000), (2273823956014832969705979540678403/7259271340527495344553984000000000000), (44290832288829076553426647927157/314568424756191464930672640000000000)],
    ![(432822253162750553583005877746291/655350884908732218605568000000000000), (2737242332824139889438322555077581/5898157964178589967450112000000000000), (6477660000625565229496459750998217/23592631856714359869800448000000000000), (36085555554692255361258464022013/393210530945239331163340800000000000)],
    ![(25006260364111094942292044091577/32767544245436610930278400000000000), (163556481363183469549235878516783/294907898208929498372505600000000000), (416669292566652364451267889827867/1179631592835717993490022400000000000), (15618483447284390502114189593821/98302632736309832790835200000000000)]]

private theorem tensor332 (u v : ℝ) :
    eval poly094 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern332 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern332, Fin.sum_univ_succ]
  <;> ring

private theorem cert332 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern332) (m := (1/1000000000000000))
    tensor332 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern332]

private def bern333 : Coeff :=
  ![![(291973590397272884342537006249/537303546670287421440000000000000), (18897586635973500917321336612873/49969229840336730193920000000000000), (10699775512504273038965033269/48798076015953838080000000000000), (1082134637906944766136020023/16266025338651279360000000000000)],
    ![(554157403355423498141053783429/1074607093340574842880000000000000), (34537775109327892806403359820453/99938459680673460387840000000000000), (17758106809581291306123810209/97596152031907676160000000000000), (801933163603659407743991963/32532050677302558720000000000000)],
    ![(85181056597880139251910008693/165324168206242283520000000000000), (5227104482094008178525978115541/15375147643180532367360000000000000), (2572368897119889940606230673/15014792620293488640000000000000), (45846413148428927430381931/5004930873431162880000000000000)]]

private theorem tensor333 (u v : ℝ) :
    eval poly096 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern333 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern333, Fin.sum_univ_succ]
  <;> ring

private theorem cert333 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern333) (m := (1/1000000000000000))
    tensor333 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern333]

private def bern334 : Coeff :=
  ![![(60127823820175212955734535405733/137770140171868569600000000000000000), (13509803311825963222029491889697/41331042051560570880000000000000000), (361967672609774731039982048827193/1653241682062422835200000000000000000), (4139122361162470265449367657483/36738704045831618560000000000000000)],
    ![(20538227964430391656878280283519/44775295555857285120000000000000000), (4643085412339173368218100513971/13432588666757185536000000000000000), (9683730166918079231926392282023/41331042051560570880000000000000000), (1487865835605977460922146682769/11940078814895276032000000000000000)],
    ![(578341861640390663761872618593/1119382388896432128000000000000000), (134330151996705018315102059437/335814716668929638400000000000000), (3829259179282439430786799393253/13432588666757185536000000000000000), (51294703065053423548680499343/298501970372381900800000000000000)]]

private theorem tensor334 (u v : ℝ) :
    eval poly095 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern334 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly095, bern334, Fin.sum_univ_succ]
  <;> ring

private theorem cert334 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) : 0 < eval poly095 δ p := by
  apply positive_on_box_from_tensor (β := bern334) (m := (1/1000000000000000))
    tensor334 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern334]

private def bern335 : Coeff :=
  ![![(915691815481167622934434001/3559061954439938048000000000000), (10636156164587516441953671825877/61500590572722129469440000000000000), (1354954068282588361448688233/15014792620293488640000000000000), (45846413148428927430381931/5004930873431162880000000000000)],
    ![(46867664542986834734796735227/185071221630876778496000000000000), (268070257351031503032324268331561/1599015354890775366205440000000000000), (32679302362628676567143054989/390384608127630704640000000000000), (184143785581409354296911383/130128202709210234880000000000000)],
    ![(23680304069302440494621592667/92535610815438389248000000000000), (540531450822379140176132319395521/3198030709781550732410880000000000000), (65438547039159435788107993349/780769216255261409280000000000000), (1175778419492384423234957/4411125515566448640000000000000)]]

private theorem tensor335 (u v : ℝ) :
    eval poly096 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern335 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern335, Fin.sum_univ_succ]
  <;> ring

private theorem cert335 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern335) (m := (1/1000000000000000))
    tensor335 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern335]

private def bern336 : Coeff :=
  ![![(23680304069302440494621592667/92535610815438389248000000000000), (1358922759457471483670254561967041/6396061419563101464821760000000000000), (1083745249476123836417238611060033/6396061419563101464821760000000000000), (1081648985689108511251520060325313/8528081892750801953095680000000000000)],
    ![(47853551734222927243689635441/185071221630876778496000000000000), (3429579402275168642646432506371/15990153548907753662054400000000000), (13656986751518141943027086748259/79950767744538768310272000000000000), (13599779475780160306219077307007/106601023659385024413696000000000000)],
    ![(309923429921830633814852303/1156695135192979865600000000000), (223050025638701988718567142689/999384596806734603878400000000000), (178755326633603507945957228153/999384596806734603878400000000000), (13834626427471666692065721349/102500984287870215782400000000000)]]

private theorem tensor336 (u v : ℝ) :
    eval poly096 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern336 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern336, Fin.sum_univ_succ]
  <;> ring

private theorem cert336 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern336) (m := (1/1000000000000000))
    tensor336 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern336]

private def bern337 : Coeff :=
  ![![(1081648985689108511251520060325313/8528081892750801953095680000000000000), (1079971974659496251118945219737537/10233698271300962343714816000000000000), (8630327664008843664458333211210823/102336982713009623437148160000000000000), (287625994861881105388612026269069/4548310342800427708317696000000000000)],
    ![(2169631343751521335749046244885873/17056163785501603906191360000000000000), (2164293067074678250860758800057969/20467396542601924687429632000000000000), (17271763812419427223513825647882263/204673965426019246874296320000000000000), (574312080883262069577202344776317/9096620685600855416635392000000000000)],
    ![(4408654620579576829026440445683233/34112327571003207812382720000000000000), (338866195454151314901771830881637/3148830237323373028835328000000000000), (597365546659858219158000731042117/6938100522915906673704960000000000000), (235374514117125188925207926935369/3638648274240342166654156800000000000)]]

private theorem tensor337 (u v : ℝ) :
    eval poly096 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern337 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern337, Fin.sum_univ_succ]
  <;> ring

private theorem cert337 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern337) (m := (1/1000000000000000))
    tensor337 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern337]

private def bern338 : Coeff :=
  ![![(287625994861881105388612026269069/4548310342800427708317696000000000000), (21568853978336261898545957123902669/409347930852038493748592640000000000000), (34524035444145648731266776499193809/818695861704076987497185280000000000000), (17287756560959568699262425538827847/545797241136051324998123520000000000000)],
    ![(229912814121404856070885279462891/3638648274240342166654156800000000000), (86126311251074048742986579496843607/1637391723408153974994370560000000000000), (137669159238472873976349770859368227/3274783446816307949988741120000000000000), (68780690530559109919696097094574501/2183188964544205299992494080000000000000)],
    ![(4624624873566198644489297118858389/72772965484806843333083136000000000000), (346618491614147380041633753910168021/6549566893632615899977482240000000000000), (554384290047387131264474187936226681/13099133787265231799954964480000000000000), (277249311902408654700654466422591583/8732755858176821199969976320000000000000)]]

private theorem tensor338 (u v : ℝ) :
    eval poly096 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((511/1024)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern338 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern338, Fin.sum_univ_succ]
  <;> ring

private theorem cert338 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern338) (m := (1/1000000000000000))
    tensor338 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern338]

private def bern339 : Coeff :=
  ![![(17287756560959568699262425538827847/545797241136051324998123520000000000000), (1252472857464104114888796599053/59137233581629369221120000000000000), (4180958531306906255531006567/390384608127630704640000000000000), (1175778419492384423234957/4411125515566448640000000000000)],
    ![(137931716774397384716745799249885889/4366377929088410599984988160000000000000), (34507462327034171312205130223378551/1637391723408153974994370560000000000000), (33060336549282372173856784849/3123076865021045637120000000000000), (256050769587637420143939401/2082051243347363758080000000000000)],
    ![(1104098941122234633246422051800433143/34931023432707284799879905280000000000000), (276043673076300849240931344150756497/13099133787265231799954964480000000000000), (263961035270521978903242398903/24984614920168365096960000000000000), (1373882269541672630330910127/16656409946778910064640000000000000)]]

private theorem tensor339 (u v : ℝ) :
    eval poly096 ((237/512)+((1899/4096)-(237/512))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern339 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern339, Fin.sum_univ_succ]
  <;> ring

private theorem cert339 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern339) (m := (1/1000000000000000))
    tensor339 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern339]

private def bern340 : Coeff :=
  ![![(1104098941122234633246422051800433143/34931023432707284799879905280000000000000), (276043673076300849240931344150756497/13099133787265231799954964480000000000000), (263961035270521978903242398903/24984614920168365096960000000000000), (1373882269541672630330910127/16656409946778910064640000000000000)],
    ![(552372074024645094379438854800889587/17465511716353642399939952640000000000000), (138013823768164163992110823257242293/6549566893632615899977482240000000000000), (131719689073392490207815259507/12492307460084182548480000000000000), (349679191191122949755152523/8328204973389455032320000000000000)],
    ![(277249311902408654700654466422591583/8732755858176821199969976320000000000000), (69340911414959708209372302832887017/3274783446816307949988741120000000000000), (66373679377173501600884225183/6246153730042091274240000000000000), (435410940841384164713194327/4164102486694727516160000000000000)]]

private theorem tensor340 (u v : ℝ) :
    eval poly096 ((1899/4096)+((951/2048)-(1899/4096))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern340 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern340, Fin.sum_univ_succ]
  <;> ring

private theorem cert340 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern340) (m := (1/1000000000000000))
    tensor340 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern340]

private def bern341 : Coeff :=
  ![![(4624624873566198644489297118858389/72772965484806843333083136000000000000), (2663661005839777712300295837721933/62976604746467460576706560000000000000), (264188484686169853909397317751/12492307460084182548480000000000000), (435410940841384164713194327/4164102486694727516160000000000000)],
    ![(2325496732352150083780444324229479/36386482742403421666541568000000000000), (17429629039038132196385150081538563/409347930852038493748592640000000000000), (133367867669256484873098186397/6246153730042091274240000000000000), (36790524282039597860939633/160157787949797212160000000000000)],
    ![(235374514117125188925207926935369/3638648274240342166654156800000000000), (285720942313250525449189361757631/6602385981484491834654720000000000000), (68610136032253007753644810559/3123076865021045637120000000000000), (798626397491848103554685983/1041025621673681879040000000000000)]]

private theorem tensor341 (u v : ℝ) :
    eval poly096 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern341 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern341, Fin.sum_univ_succ]
  <;> ring

private theorem cert341 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern341) (m := (1/1000000000000000))
    tensor341 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern341]

private def bern342 : Coeff :=
  ![![(4408654620579576829026440445683233/34112327571003207812382720000000000000), (4400169421390552490767923835128353/51168491356504811718574080000000000000), (134824392872030471196625563169/3123076865021045637120000000000000), (798626397491848103554685983/1041025621673681879040000000000000)],
    ![(27987790960350693665967427509967/213202047318770048827392000000000000), (28048547116639235840494952528903/319803070978155073241088000000000000), (226812701637187073272909/5089760210268979200000000000), (11985014855056434615449017/6506410135460511744000000000000)],
    ![(13834626427471666692065721349/102500984287870215782400000000000), (36407955480837597019729735261/399753838722693841551360000000000), (5808001681601923574865889/121995190039884595200000000000), (185679204073005018107503/40665063346628198400000000000)]]

private theorem tensor342 (u v : ℝ) :
    eval poly096 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern342 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern342, Fin.sum_univ_succ]
  <;> ring

private theorem cert342 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern342) (m := (1/1000000000000000))
    tensor342 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern342]

private def bern343 : Coeff :=
  ![![(10883529187084317919091191524767/2047971515339788183142400000000000), (37971960846573408284394884316869/9215871819029046824140800000000000), (224989176073376257403628339887417/73726974552232374593126400000000000), (51637608769344551944074977712169/24575658184077458197708800000000000)],
    ![(34533357604010580132764475546689/5119928788349470457856000000000000), (121912565426442820242428809331291/23039679547572617060352000000000000), (734680247229930974241070897533767/184317436380580936482816000000000000), (173245322737146611254348371631207/61439145460193645494272000000000000)],
    ![(26793937453096729476390916857187/2559964394174735228928000000000000), (19962494678745538760312938801277/2303967954757261706035200000000000), (648513179095806015951971824463701/92158718190290468241408000000000000), (482309368973306934286945971863/86534007690413585203200000000000)]]

private theorem tensor343 (u v : ℝ) :
    eval poly094 ((15/32)+((9/16)-(15/32))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern343 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern343, Fin.sum_univ_succ]
  <;> ring

private theorem cert343 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern343) (m := (1/1000000000000000))
    tensor343 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern343]

private def bern344 : Coeff :=
  ![![(51637608769344551944074977712169/24575658184077458197708800000000000), (29968662856340588761630807440263/18431743638058093648281600000000000), (348056067104632624343413433439013/294907898208929498372505600000000000), (25006260364111094942292044091577/32767544245436610930278400000000000)],
    ![(604678689321015982229071631823259/245756581840774581977088000000000000), (27382709894830775043859242229853/14178264336967764344832000000000000), (65076397590661439422121375602703/45370445878296845903462400000000000), (317365557760582294685755445001019/327675442454366109302784000000000000)],
    ![(1636048638737405051425231655131133/491513163681549163954176000000000000), (201667954074170405375919307718831/73726974552232374593126400000000000), (12841075407999353682522966643459241/5898157964178589967450112000000000000), (1083225681540073594055712252211181/655350884908732218605568000000000000)]]

private theorem tensor344 (u v : ℝ) :
    eval poly094 ((15/32)+((33/64)-(15/32))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern344 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern344, Fin.sum_univ_succ]
  <;> ring

private theorem cert344 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern344) (m := (1/1000000000000000))
    tensor344 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern344]

private def bern345 : Coeff :=
  ![![(3887532533361527417278281839/3470085405578939596800000000000), (22500232996972957201515459793/31230768650210456371200000000000), (42564750167282283218669549/121995190039884595200000000000), (185679204073005018107503/40665063346628198400000000000)],
    ![(83821215808194087175136774323/69401708111578791936000000000000), (490146195234788186647300488173/624615373004209127424000000000000), (954726655838096698272100057/2439903800797691904000000000000), (21437241878084468643901523/813301266932563968000000000000)],
    ![(78172935967822362224430755903/55521366489263033548800000000000), (386561894732515558553964816391/402977660002715566080000000000000), (26427679310683794491418732629/48798076015953838080000000000000), (2500027261636894228676137063/16266025338651279360000000000000)]]

private theorem tensor345 (u v : ℝ) :
    eval poly096 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern345 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly096, bern345, Fin.sum_univ_succ]
  <;> ring

private theorem cert345 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly096 δ p := by
  apply positive_on_box_from_tensor (β := bern345) (m := (1/1000000000000000))
    tensor345 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern345]

private def bern346 : Coeff :=
  ![![(2852813119864624671644574914046797/2621403539634928874422272000000000000), (1550149773564649450586951142704663/1814817835131873836138496000000000000), (59251325039512541558640102757765207/94370527426857439479201792000000000000), (643668213195270289122305949288121/1572842123780957324653363200000000000)],
    ![(1717956797061238183427223142213219/1310701769817464437211136000000000000), (12541913212934045072568139683973141/11796315928357179934900224000000000000), (38873101635431482861531591073532281/47185263713428719739600896000000000000), (465943589148104551810995843831011/786421061890478662326681600000000000)],
    ![(1083225681540073594055712252211181/655350884908732218605568000000000000), (8203008996791316678490632083121323/5898157964178589967450112000000000000), (5365652816536694290689687437171339/4718526371342871973960089600000000000), (70138579778015275301628499349837/78642106189047866232668160000000000)]]

private theorem tensor346 (u v : ℝ) :
    eval poly094 ((63/128)+((33/64)-(63/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern346 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern346, Fin.sum_univ_succ]
  <;> ring

private theorem cert346 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern346) (m := (1/1000000000000000))
    tensor346 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern346]

private def bern347 : Coeff :=
  ![![(2234173337922811515383983899593/3516819620315365638144000000000000), (9204664037693775453340484039563/21100917721892193828864000000000000), (32289753964428782979436739459/131880735761826211430400000000000), (209368005909071056839348931/3434394160464224256000000000000)],
    ![(4982213792251982986880166948439/7033639240630731276288000000000000), (21249672568635625296059398465013/42201835443784387657728000000000000), (404301959189848937930916206129/1318807357618262114304000000000000), (61968247884813203523654257/528368332379111424000000000000)],
    ![(11355136540910803256605446823817/14067278481261462552576000000000000), (853090518270900942126300314609/1430570693009640259584000000000000), (1037884853358901376481539275279/2637614715236524228608000000000000), (2727038589859674389900676547/13737576641856897024000000000000)]]

private theorem tensor347 (u v : ℝ) :
    eval poly097 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern347 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly097, bern347, Fin.sum_univ_succ]
  <;> ring

private theorem cert347 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly097 δ p := by
  apply positive_on_box_from_tensor (β := bern347) (m := (1/1000000000000000))
    tensor347 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern347]

private def bern348 : Coeff :=
  ![![(782042833069598800479771862321781/1258273699024765859722690560000000000), (5377207913389669881876541694285659/10633298864998021349769216000000000000), (295850732698525083915742270595517967/754964219414859515833614336000000000000), (2409347627451536315314630011046561/8603580848032587075026944000000000000)],
    ![(1167329386928257304827280837329381/1572842123780957324653363200000000000), (117589659846287889100482085274042909/188741054853714878958403584000000000000), (95485907481267551857179237443627431/188741054853714878958403584000000000000), (840628011030569481940209723022369/2150895212008146768756736000000000000)],
    ![(70138579778015275301628499349837/78642106189047866232668160000000000), (7259291543506055263603442445799321/9437052742685743947920179200000000000), (30608308445852840653834426730952511/47185263713428719739600896000000000000), (4015551756290467948306253947607/7573574690169530875904000000000000)]]

private theorem tensor348 (u v : ℝ) :
    eval poly094 ((129/256)+((33/64)-(129/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern348 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern348, Fin.sum_univ_succ]
  <;> ring

private theorem cert348 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern348) (m := (1/1000000000000000))
    tensor348 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern348]

private def bern349 : Coeff :=
  ![![(2409347627451536315314630011046561/8603580848032587075026944000000000000), (270728024182473480872667263849991373/1207942751063775225333782937600000000000), (2037838617757467452554039551780782147/12079427510637752253337829376000000000000), (183249930744963979617438099426279211/1610590334751700300445043916800000000000)],
    ![(5771859671573814243075468903136037/17207161696065174150053888000000000000), (3366590783672845232580631873522136197/12079427510637752253337829376000000000000), (5374801604478664673669036181687889999/24158855021275504506675658752000000000000), (2685667388792302406183550722622956467/16105903347517003004450439168000000000000)],
    ![(2739207702168412752022442455941413/6882864678426069660021555200000000000), (8224044841187449342460051539172429081/24158855021275504506675658752000000000000), (2738290569556086603717459359208447823/9663542008510201802670263500800000000000), (7306150925521890477392323373852527871/32211806695034006008900878336000000000000)]]

private theorem tensor349 (u v : ℝ) :
    eval poly094 ((129/256)+((261/512)-(129/256))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern349 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern349, Fin.sum_univ_succ]
  <;> ring

private theorem cert349 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern349) (m := (1/1000000000000000))
    tensor349 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern349]

private def bern350 : Coeff :=
  ![![(183249930744963979617438099426279211/1610590334751700300445043916800000000000), (4170569648008444177676635370621000201/48317710042551009013351317504000000000000), (5699237721129997435159014078178135181/96635420085102018026702635008000000000000), (682059200863164654535657877051172041/21474537796689337339267252224000000000000)],
    ![(4518166696241942202357931716885748577/32211806695034006008900878336000000000000), (21762542586190280663667154881472828607/193270840170204036053405270016000000000000), (32880238820599564683567990981009959771/386541680340408072106810540032000000000000), (76182433709929443218339020982949439/1321510018257805374724138598400000000000)],
    ![(21713819095590379694475288252869937959/128847226780136024035603513344000000000000), (108740344386863494203318394815995586233/773083360680816144213621080064000000000000), (174588824578353913030021283309528397821/1546166721361632288427242160128000000000000), (29308852553510486280317839461202594169/343592604747029397428276035584000000000000)]]

private theorem tensor350 (u v : ℝ) :
    eval poly094 ((129/256)+((519/1024)-(129/256))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern350 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern350, Fin.sum_univ_succ]
  <;> ring

private theorem cert350 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern350) (m := (1/1000000000000000))
    tensor350 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern350]

private def bern351 : Coeff :=
  ![![(666545690587476990412327172519256993275183/3908083261699185692371947997888512000000000000), (5120813355517668331277652132754481359378013/35172749355292671231347531980996608000000000000), (33180135617165410323731368301803842835547/274787104338223993994902593601536000000000000), (34359037960300119513593605727896149739/357795708773729158847529418752000000000000)],
    ![(5670366296880350755893737666244829775150437/31264666093593485538975583983108096000000000000), (43982889641560120548753238414078088926851871/281381994842341369850780255847972864000000000000), (288807138679402011398534495518251827869033/2198296834705791951959220748812288000000000000), (305038145427697145730580939371882605273/2862365670189833270780235350016000000000000)],
    ![(9633324272934131603234570686458939141902923/50023465749749576862360934372972953600000000000), (75378009202363641398832200173322886895965937/450211191747746191761248409356756582400000000000), (500874876340133221548428768026555414888039/3517274935529267123134753198099660800000000000), (538143760778210037381774688601684457143/4579785072303733233248376560025600000000000)]]

private theorem tensor351 (u v : ℝ) :
    eval poly098 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern351 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly098, bern351, Fin.sum_univ_succ]
  <;> ring

private theorem cert351 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly098 δ p := by
  apply positive_on_box_from_tensor (β := bern351) (m := (1/1000000000000000))
    tensor351 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern351]

private def bern352 : Coeff :=
  ![![(15967333059296886245284931281031011021/274874083797623517942620828467200000000000), (219590577128523772838249370024454002013/4947733508357223322967174912409600000000000), (303845324523711528245802226221383494021/9895467016714446645934349824819200000000000), (112544121817271557968867718300283135119/6596978011142964430622899883212800000000000)],
    ![(49116285318092141517085984916769448309/687185209494058794856552071168000000000000), (713920143866983477432735098285638630533/12369333770893058307417937281024000000000000), (18445149345134506256684641844458543607/419299449860781637539591094272000000000000), (99927472601390917078254875838687279707/3298489005571482215311449941606400000000000)],
    ![(29308852553510486280317839461202594169/343592604747029397428276035584000000000000), (442161369788075303508539098833413246921/6184666885446529153708968640512000000000000), (713912539441556409158763175907051698769/12369333770893058307417937281024000000000000), (72518358860323569409876065710977299607/1649244502785741107655724970803200000000000)]]

private theorem tensor352 (u v : ℝ) :
    eval poly094 ((1035/2048)+((519/1024)-(1035/2048))*u) ((255/512)+((511/1024)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern352 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern352, Fin.sum_univ_succ]
  <;> ring

private theorem cert352 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern352) (m := (1/1000000000000000))
    tensor352 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern352]

private def bern353 : Coeff :=
  ![![(86203583382055391863884062319716193734502761/600281588996994922348331212475675443200000000000), (236078568588555656818731558798437858857289393/1800844766990984767044993637427026329600000000000), (834383662788480738425619696472649077973863/7034549871058534246269506396199321600000000000), (486199996566414599991141855007934457143/4579785072303733233248376560025600000000000)],
    ![(179059001026688318563777017768096127060208227/1200563177993989844696662424951350886400000000000), (2460152162816183104310158005060339421938690407/18008447669909847670449936374270263296000000000000), (8730384325798115721204231052242874819858369/70345498710585342462695063961993216000000000000), (5112617219263373604450150141393956014961/45797850723037332332483765600256000000000000)],
    ![(74332096794537649221121179286919405678850349/480225271197595937878664969980540354560000000000), (5122616891042191826860303328351835449724244621/36016895339819695340899872748540526592000000000000), (3649567359724836034802072793680207580754543/28138199484234136985078025584797286400000000000), (10735559214650962419776085949592039101627/91595701446074664664967531200512000000000000)]]

private theorem tensor353 (u v : ℝ) :
    eval poly099 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern353 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly099, bern353, Fin.sum_univ_succ]
  <;> ring

private theorem cert353 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly099 δ p := by
  apply positive_on_box_from_tensor (β := bern353) (m := (1/1000000000000000))
    tensor353 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern353]

private def bern354 : Coeff :=
  ![![(6418619581313036031371131875991531619/211103296356574861779932796262809600000000), (18648871093212774167579338182397684244009/791637361337155731674747985985536000000000000), (26468136885670577927913553241422919472953/1583274722674311463349495971971072000000000000), (695592203330984712461967173069177259533/70367765452191620593310932087603200000000000)],
    ![(244964190322038055898007007260641878921/6596978011142964430622899883212800000000000), (5991210783999615140486474885454569610743/197909340334288932918686996496384000000000000), (9270070544295089634487156516350624507623/395818680668577865837373992992768000000000000), (112150371799003985832021067384800241051/6766131293479963518587589623808000000000000)],
    ![(72518358860323569409876065710977299607/1649244502785741107655724970803200000000000), (1835501069831447805126896605179875084777/49477335083572233229671749124096000000000000), (2991673451997306174462267155430968049401/98954670167144466459343498248192000000000000), (514025570789439492283457581195700524033/21989926703809881435409666277376000000000000)]]

private theorem tensor354 (u v : ℝ) :
    eval poly094 ((2073/4096)+((519/1024)-(2073/4096))*u) ((511/1024)+((1023/2048)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern354 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern354, Fin.sum_univ_succ]
  <;> ring

private theorem cert354 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern354) (m := (1/1000000000000000))
    tensor354 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern354]

private def bern355 : Coeff :=
  ![![(41450245064379412853556662555641643839614151/384910759727469501343816424421221990400000000000), (7075296466527222271549827092520119757415303/69702149648837535454614644261388288000000000000), (25801501592523763506392519018315093881380221/270640377933376993132370923421171712000000000000), (1122259026036514361488878764575109053213/12585583051217308088372903804928000000000000)],
    ![(60717437128315502030640471161310537663734257/549872513896385001919737749173174272000000000000), (7221807203409922213580818541392250791650734779/69283936750944510241886956395819958272000000000000), (7582317908956015605675720062398802968246639/77325822266679140894963120977477632000000000000), (16190199808777808671429431073703144252447/176198162717042313237220653268992000000000000)],
    ![(67020909433011811271398125774213853784875943/592170399580722309759717576032649216000000000000), (2964986181862335951704178002956675158504489667/27713574700377804096754782558327983308800000000000), (15589340173292250966627628762335407971233587/154651644533358281789926241954955264000000000000), (33346165126075269852275426328492609444643/352396325434084626474441306537984000000000000)]]

private theorem tensor355 (u v : ℝ) :
    eval poly100 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern355 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly100, bern355, Fin.sum_univ_succ]
  <;> ring

private theorem cert355 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly100 δ p := by
  apply positive_on_box_from_tensor (β := bern355) (m := (1/1000000000000000))
    tensor355 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern355]

private def bern356 : Coeff :=
  ![![(6751230516146307415595304297167385077/406632565456178102243923329024000000000000), (333891285098347601474720240939153824641713/25332395562788983413591935551537152000000000000), (494487294393165082346924175458370017924561/50664791125577966827183871103074304000000000000), (214193642941114358497154976136539000771323/33776527417051977884789247402049536000000000000)],
    ![(702811423308961956990020840157041045959/35183882726095810296655466043801600000000000), (52406013442141235528980363145051547794011/3166549445348622926698991943942144000000000000), (255785582972367526267384565635089055231/19486458125222294933532258116567040000000000), (40973943828383517589334672648167479223561/4222065927131497235598655925256192000000000000)],
    ![(514025570789439492283457581195700524033/21989926703809881435409666277376000000000000), (7895343507320253942728820381421978050089/395818680668577865837373992992768000000000000), (13077994089302716001920444632399626192969/791637361337155731674747985985536000000000000), (6911227581557518619766971912813726590499/527758240891437154449831990657024000000000000)]]

private theorem tensor356 (u v : ℝ) :
    eval poly094 ((4149/8192)+((519/1024)-(4149/8192))*u) ((1023/2048)+((2047/4096)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern356 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern356, Fin.sum_univ_succ]
  <;> ring

private theorem cert356 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern356) (m := (1/1000000000000000))
    tensor356 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern356]

private def bern357 : Coeff :=
  ![![(38391359195761395673865743875952765235096313137/369514329338370721290063767444373110784000000000000), (7981896309438029542992847828010425256051111161/79181642001079440276442235880937095168000000000000), (42312960096069797150516702203495430402515681/433024604693403189011793477473874739200000000000), (33346165126075269852275426328492609444643/352396325434084626474441306537984000000000000)],
    ![(77798521030164410582127707836320216992222348809/739028658676741442580127534888746221568000000000000), (113268689489663666415856796263642607814835511543/1108542988015112163870191302333119332352000000000000), (33005335622348606330848309820155084322711377/333095849764156299239841136518365184000000000000), (13531619152134038442793483367614307965807/140958530173633850589776522615193600000000000)],
    ![(31527537919877228210481869305276324334053165933/295611463470696577032051013955498488627200000000000), (229595222194681861865660266816036160251177719007/2217085976030224327740382604666238664704000000000000), (124295887567671756482330576957393594986424579/1237213156266866254319409935639642112000000000000), (137256341158366126735014269480098807462387/1409585301736338505897765226151936000000000000)]]

private theorem tensor357 (u v : ℝ) :
    eval poly100 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern357 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly100, bern357, Fin.sum_univ_succ]
  <;> ring

private theorem cert357 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly100 δ p := by
  apply positive_on_box_from_tensor (β := bern357) (m := (1/1000000000000000))
    tensor357 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern357]

private def bern358 : Coeff :=
  ![![(262419061882986366318319188185459434028047/27021221933641582307831397921639628800000000000), (6485729889604686398203898721876856168310561/810636658009247469234941937649188864000000000000), (10198563921989373425342504148908054154283361/1621273316018494938469883875298377728000000000000), (42315988826069566225882693512063709868799/9238024592697976857378255699705856000000000000)],
    ![(96263764480843666547470447950677291947553/8444131854262994471197311850512384000000000000), (490865345966710650822706949774893722540323/50664791125577966827183871103074304000000000000), (808345480820297976437783308766784941436899/101329582251155933654367742206148608000000000000), (723657588640391882621304472796886799833/115475307408724710717228196246323200000000000)],
    ![(6911227581557518619766971912813726590499/527758240891437154449831990657024000000000000), (36045060055412235574061857950524286928553/3166549445348622926698991943942144000000000000), (4711429973823186652429091352527924294477/487161453130557373338306452914176000000000000), (287237260542740292282761546078156158071/36086033565226472099133811326976000000000000)]]

private theorem tensor358 (u v : ℝ) :
    eval poly094 ((8301/16384)+((519/1024)-(8301/16384))*u) ((2047/4096)+((4095/8192)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern358 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern358, Fin.sum_univ_succ]
  <;> ring

private theorem cert358 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern358) (m := (1/1000000000000000))
    tensor358 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern358]

private def bern359 : Coeff :=
  ![![(42315988826069566225882693512063709868799/9238024592697976857378255699705856000000000000), (193292867118980051081355743763095825466229/51880746112591838031036284009548087296000000000), (37236361196100024196268973905220034297377953/12970186528147959507759071002387021824000000000000), (3486810861136364035422474251873636271408079/1729358203753061267701209466984936243200000000000)],
    ![(100208595917300916835587051335814653855439/18476049185395953714756511399411712000000000000), (59255468270689583331179090878259604075229777/12970186528147959507759071002387021824000000000000), (96332156821672130948923889772819755837869777/25940373056295919015518142004774043648000000000000), (1977507448107851807158814468754250065418579/691743281501224507080483786793974497280000000000)],
    ![(46326788341494756453935672991114714861651/7390419674158381485902604559764684800000000000), (28084004819144989005740029239380553016405069/5188074611259183803103628400954808729600000000000), (3638036123989843540126897681335236311163329/798165324809105200477481292454585958400000000000), (25614793780191886366837945260533768004272239/6917432815012245070804837867939744972800000000000)]]

private theorem tensor359 (u v : ℝ) :
    eval poly094 ((8301/16384)+((16605/32768)-(8301/16384))*u) ((4095/8192)+((8191/16384)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern359 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern359, Fin.sum_univ_succ]
  <;> ring

private theorem cert359 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (16605/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern359) (m := (1/1000000000000000))
    tensor359 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern359]

private def bern360 : Coeff :=
  ![![(3486810861136364035422474251873636271408079/1729358203753061267701209466984936243200000000000), (82433766358936333201473393523873563618607649/51880746112591838031036284009548087296000000000000), (120529565459698879967484209021848397804669729/103761492225183676062072568019096174592000000000000), (16932166620292557294599969408777461683145049/23058109383374150236016126226465816576000000000000)],
    ![(16861158962811987106639020847518522869909053/6917432815012245070804837867939744972800000000000), (417142394898795061115832262971813880280656019/207522984450367352124145136038192349184000000000000), (656912649614890491704797870692016936013362067/415045968900734704248290272076384698368000000000000), (106567359291379432778403059146606897356273851/92232437533496600944064504905863266304000000000000)],
    ![(1217110556721451979256986640663281759973479/425688173231522773587990022642445844480000000000), (403711107629878027589729263188440021277842293/166018387560293881699316108830553879347200000000000), (3327541416617492925288197650198859571032226377/1660183875602938816993161088305538793472000000000000), (581782709007111367840090734876067246674993473/368929750133986403776258019623453065216000000000000)]]

private theorem tensor360 (u v : ℝ) :
    eval poly094 ((8301/16384)+((33207/65536)-(8301/16384))*u) ((8191/16384)+((16383/32768)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern360 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern360, Fin.sum_univ_succ]
  <;> ring

private theorem cert360 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (33207/65536)) (hp : p ∈ Set.Icc (8191/16384) (16383/32768)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern360) (m := (1/1000000000000000))
    tensor360 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern360]

private def bern361 : Coeff :=
  ![![(24855382756790024284391524116162467776391634068081/252255115494994412400683531908692043628544000000000000), (1071255598515256729767730961165299005815082385307/10914884805071873613491114361433790349312000000000000), (967598847644673239142258248643120668035330307/9897705250134930034555279485117136896000000000000), (137256341158366126735014269480098807462387/1409585301736338505897765226151936000000000000)],
    ![(400785510465979630010967604176781926656546721719/4060444515009970420936555845612749193216000000000000), (22321186821176544583885786908801380950777042218389/227029603945494971160615178717822839265689600000000000), (54280909910483543047883592282449008323901038979/554271494007556081935095651166559666176000000000000), (1099990878903954756187193591644746187503413/11276682413890708047182121809215488000000000000)],
    ![(319260685051866449378224676886359998854826678013197/3228865478335928478728749208431258158445363200000000000), (894411155347986637626475106524915963938735440693519/9081184157819798846424607148712913570627584000000000000), (33462361419620340387267785714588144634632119673/341090150158496050421597323794805948416000000000000), (8815456846947830425242430527031398408386659/90213459311125664377456974473723904000000000000)]]

private theorem tensor361 (u v : ℝ) :
    eval poly100 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern361 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly100, bern361, Fin.sum_univ_succ]
  <;> ring

private theorem cert361 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly100 δ p := by
  apply positive_on_box_from_tensor (β := bern361) (m := (1/1000000000000000))
    tensor361 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern361]

private def bern362 : Coeff :=
  ![![(341047249852565549356182943717872362491101013/295143800107189123021006415698762452172800000000000), (25018747408312751286272041481743630088270959601/26562942009647021071890577412888620695552000000000000), (7737377619183677612154734309823645277371715069/10625176803858808428756230965155448278220800000000000), (18224456536526566092263698059270728067029886971/35417256012862694762520769883851494260736000000000000)],
    ![(1008052146172629098953702971462494836100088877/737859500267972807552516039246906130432000000000000), (15307023916506875887535201963553505944531050389/13281471004823510535945288706444310347776000000000000), (24938420130036579839609172564176776453126445461/26562942009647021071890577412888620695552000000000000), (12841996100005120463130232107683361347590588039/17708628006431347381260384941925747130368000000000000)],
    ![(581782709007111367840090734876067246674993473/368929750133986403776258019623453065216000000000000), (9053050309957021081106054541256096518160371017/6640735502411755267972644353222155173888000000000000), (15268124582763666243383562986343932553844600649/13281471004823510535945288706444310347776000000000000), (8286832940778054649175382346963843402833888707/8854314003215673690630192470962873565184000000000000)]]

private theorem tensor362 (u v : ℝ) :
    eval poly094 ((66411/131072)+((33207/65536)-(66411/131072))*u) ((16383/32768)+((32767/65536)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern362 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern362, Fin.sum_univ_succ]
  <;> ring

private theorem cert362 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (33207/65536)) (hp : p ∈ Set.Icc (16383/32768) (32767/65536)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern362) (m := (1/1000000000000000))
    tensor362 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern362]

private def bern363 : Coeff :=
  ![![(18224456536526566092263698059270728067029886971/35417256012862694762520769883851494260736000000000000), (86646332636902318708825939435200099829551832049/212503536077176168575124619303108965564416000000000000), (127892658968447632906923954937865461520587882481/425007072154352337150249238606217931128832000000000000), (18331879892377149636572101416986820135557328553/94446016034300519366722053023603984695296000000000000)],
    ![(43908448736536807018524162274637450762211063049/70834512025725389525041539767702988521472000000000000), (218048581916848167686733427116793498273676634907/425007072154352337150249238606217931128832000000000000), (69058911315980245773123592584190477394338669727/170002828861740934860099695442487172451532800000000000), (56554125125323301414628576750194137133317548803/188892032068601038733444106047207969390592000000000000)],
    ![(20547954539931853308297231175571909413745558791/28333804810290155810016615907081195408588800000000000), (21025272816107786163515447015933351951562585041/34000565772348186972019939088497434490306560000000000), (173930647356408216910107822738344636326976780053/340005657723481869720199390884974344903065600000000000), (30579824902207240849721454809181765547558698413/75556812827440415493377642418883187756236800000000000)]]

private theorem tensor363 (u v : ℝ) :
    eval poly094 ((66411/131072)+((132825/262144)-(66411/131072))*u) ((32767/65536)+((65535/131072)-(32767/65536))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern363 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern363, Fin.sum_univ_succ]
  <;> ring

private theorem cert363 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (132825/262144)) (hp : p ∈ Set.Icc (32767/65536) (65535/131072)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern363) (m := (1/1000000000000000))
    tensor363 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern363]

private def bern364 : Coeff :=
  ![![(101265034825811506918895629861655691674724333635179057/1033236953067497113193199746698002610702516224000000000000), (14226359095599643648336042170834063473949605002049807/145298946525116781542793714379406617130041344000000000000), (1734902703278603708219029050083587763957280745253/17736687808241794621923060837329909317632000000000000), (8815456846947830425242430527031398408386659/90213459311125664377456974473723904000000000000)],
    ![(405238023174053379299645598075353077580625204993807421/4132947812269988452772798986792010442810064896000000000000), (56930450501601537612672721127481643530582190990016003/581195786100467126171174857517626468520165376000000000000), (6942664196791857776485365966161805202599169275809/70946751232967178487692243349319637270528000000000000), (35277357203507514076714603901999022541905991/360853837244502657509827897894895616000000000000)],
    ![(1621663726892319627914738878171177697605455169742740441/16531791249079953811091195947168041771240259584000000000000), (32545981766376652190180475300146074357784917705034657/332111877771695500669242775724357982011523072000000000000), (27782872016376572947879314008629752770542621302509/283787004931868713950768973397278549082112000000000000), (141171556695514812247126189090931588886986203/1443415348978010630039311591579582464000000000000)]]

private theorem tensor364 (u v : ℝ) :
    eval poly100 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern364 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly100, bern364, Fin.sum_univ_succ]
  <;> ring

private theorem cert364 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly100 δ p := by
  apply positive_on_box_from_tensor (β := bern364) (m := (1/1000000000000000))
    tensor364 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern364]

private def bern365 : Coeff :=
  ![![(452443144581838008453409986714632656813293001489/1511136256548808309867552848377663755124736000000000000), (1338232141151750632992131214208218516550178678149/5440090523575709915523190254159589518449049600000000000), (805901187530340515670632466829734081495118553789/4184685018135161473479377118584299629576192000000000000), (1009484704529615647871573942633420607268556689879/7253454031434279887364253672212786024598732800000000000)],
    ![(266007374761682807077864427546297102004428589671/755568128274404154933776424188831877562368000000000000), (4061714418681748706538789464682765842963030726047/13600226308939274788807975635398973796122624000000000000), (6670605093339748823771130275374212976765140176287/27200452617878549577615951270797947592245248000000000000), (695705901239590488228605686362147203448332079473/3626727015717139943682126836106393012299366400000000000)],
    ![(30579824902207240849721454809181765547558698413/75556812827440415493377642418883187756236800000000000), (95558795529355813824452726874243679426026259409/272004526178785495776159512707979475922452480000000000), (810303505124043629176452907002254412459784911637/2720045261787854957761595127079794759224524800000000000), (443346897310450947790046001804945397250463162631/1813363507858569971841063418053196506149683200000000000)]]

private theorem tensor365 (u v : ℝ) :
    eval poly094 ((265647/524288)+((132825/262144)-(265647/524288))*u) ((65535/131072)+((131071/262144)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern365 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern365, Fin.sum_univ_succ]
  <;> ring

private theorem cert365 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (132825/262144)) (hp : p ∈ Set.Icc (65535/131072) (131071/262144)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern365) (m := (1/1000000000000000))
    tensor365 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern365]

private def bern366 : Coeff :=
  ![![(1009484704529615647871573942633420607268556689879/7253454031434279887364253672212786024598732800000000000), (24473380828043850746784383280930841208211968646041/217603620943028396620927610166383580737961984000000000000), (37324492679800004677886441714237635599020232305561/435207241886056793241855220332767161475923968000000000000), (146451711355037244208380497339281488383667523079/2479813344080095687987779033235140521230336000000000000)],
    ![(96035860280351864973151412614308600566608833953/580276322514742390989140293777022881967898624000000000), (60404491566247999392274373952027237611501295093463/435207241886056793241855220332767161475923968000000000000), (1374144776391400765935396706204202758188884159729/12259358926367796992728316065711751027490816000000000000), (423473950964094238936212121565539583276016072073/4959626688160191375975558066470281042460672000000000000)],
    ![(85626090749688944491479703004642938616365194743/446366401934417223837800225982325293821460480000000000), (2211167747928793438044838902583440446484347605369/13390992058032516715134006779469758814643814400000000000), (18535543622876482339922855739275852566085657782109/133909920580325167151340067794697588146438144000000000000), (1108105604121487184814289629505849762596833644007/9919253376320382751951116132940562084921344000000000000)]]

private theorem tensor366 (u v : ℝ) :
    eval poly094 ((265647/524288)+((531297/1048576)-(265647/524288))*u) ((131071/262144)+((262143/524288)-(131071/262144))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern366 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern366, Fin.sum_univ_succ]
  <;> ring

private theorem cert366 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (531297/1048576)) (hp : p ∈ Set.Icc (131071/262144) (262143/524288)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern366) (m := (1/1000000000000000))
    tensor366 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern366]

private def bern367 : Coeff :=
  ![![(4931262026045032863482282062614942517689061338566638709/50382601901957954471896978124702603493303648256000000000000), (519965708898036850714608477884882891596724247866985377/5313790044347128010707884411589727712184369152000000000000), (111049244272751901566728271362999386254220371500781/1135148019727474855803075893589114196328448000000000000), (141171556695514812247126189090931588886986203/1443415348978010630039311591579582464000000000000)],
    ![(19727216738045666180907315790230475487054174747407147301/201530407607831817887587912498810413973214593024000000000000), (83203662274651259390112922369386612903604495182350393/850206407095540481713261505854356433949499064320000000000), (63463690976540801828080490688968432081953791922619/648656011272842774744614796336636683616256000000000000), (564748354663544004928772529846661854267307051/5773661395912042520157246366318329856000000000000)],
    ![(15783508357696031891739702501604393775846119138417318033/161224326086265454310070329999048331178571674419200000000000), (4480689846925570732198722714801457712832599639997720803/45780344997452179784560234930619192597280718848000000000000), (1777178793100222762252743090444955274161824683116109/18162368315639597692849214297425827141255168000000000000), (2259241938798735029913449459625831195032601979/23094645583648170080628985465273319424000000000000)]]

private theorem tensor367 (u v : ℝ) :
    eval poly100 ((265647/524288)+((1062591/2097152)-(265647/524288))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern367 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly100, bern367, Fin.sum_univ_succ]
  <;> ring

private theorem cert367 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly100 δ p := by
  apply positive_on_box_from_tensor (β := bern367) (m := (1/1000000000000000))
    tensor367 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern367]

private def bern368 : Coeff :=
  ![![(677561650679602623478532021025026809847113604923/7935402701056306201560892906352449667937075200000000000), (99756724275134398815583042204441367724816112033/1700028288617409348600996954424871724515328000000000000), (7975257754880173054565470840467969487231/249426664002845375149212903892058112000000000000), (43452541887308622451614968917038361/8246222513928705538278624854016000000000000)],
    ![(1955053506049675662686713872636928929148865788153/19838506752640765503902232265881124169842688000000000000), (61067664862906000591116482520502729274735544383/850014144308704674300498477212435862257664000000000000), (73180922010314996817012254227301486145581/1621273316018494938469883875298377728000000000000), (76000745920191155945624731044031943/4123111256964352769139312427008000000000000)],
    ![(1108105604121487184814289629505849762596833644007/9919253376320382751951116132940562084921344000000000000), (555825570722835529788230676629984913282658721/6538570340836189802311526747787968171212800000000000), (3635513414788205642592444113477543639359/62356666000711343787303225973014528000000000000), (5010651948376873595847099296604541/158581202190936644966896631808000000000000)]]

private theorem tensor368 (u v : ℝ) :
    eval poly094 ((1062591/2097152)+((531297/1048576)-(1062591/2097152))*u) ((262143/524288)+((1/2)-(262143/524288))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern368 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern368, Fin.sum_univ_succ]
  <;> ring

private theorem cert368 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1062591/2097152) (531297/1048576)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern368) (m := (1/1000000000000000))
    tensor368 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern368]

private def bern369 : Coeff :=
  ![![(85626090749688944491479703004642938616365194743/446366401934417223837800225982325293821460480000000000), (226263766280141423504063319705516691220427169/1634642585209047450577881686946992042803200000000000), (2650379156521725278660137614970718042431/31178333000355671893651612986507264000000000000), (5010651948376873595847099296604541/158581202190936644966896631808000000000000)],
    ![(316479939172098476761739537994407599589851680947/1450690806286855977472850734442557204919746560000000000), (4376150045569922188278713869230377376892522841/26562942009647021071890577412888620695552000000000000), (191212795541988270503773304566362498977/1717450546629761587362165122138112000000000000), (29853670016626728573103035380886289/515388907120544096142414053376000000000000)],
    ![(443346897310450947790046001804945397250463162631/1813363507858569971841063418053196506149683200000000000), (253777923245756452243010301959268446919728797/1328147100482351053594528870644431034777600000000000), (697477382905947618706136292895472660519/5066479112557796682718387110307430400000000000), (86847172163127948745988600177789/1030777814241088192284828106752000000000)]]

private theorem tensor369 (u v : ℝ) :
    eval poly094 ((531297/1048576)+((132825/262144)-(531297/1048576))*u) ((131071/262144)+((1/2)-(131071/262144))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern369 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern369, Fin.sum_univ_succ]
  <;> ring

private theorem cert369 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (531297/1048576) (132825/262144)) (hp : p ∈ Set.Icc (131071/262144) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern369) (m := (1/1000000000000000))
    tensor369 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern369]

private def bern370 : Coeff :=
  ![![(20547954539931853308297231175571909413745558791/28333804810290155810016615907081195408588800000000000), (42463379356194698137388224172803741715406493/83009193780146940849658054415276939673600000000000), (377323967443792748448923917200071290919/1266619778139449170679596777576857600000000000), (86847172163127948745988600177789/1030777814241088192284828106752000000000)],
    ![(29415661981561229761480996801611048153258365453/35417256012862694762520769883851494260736000000000000), (2560337238212482574848960302185039288981207/4150459689007347042482902720763846983680000000000), (638411753772305409993988536427590866029/1583274722674311463349495971971072000000000000), (6106453146332059848284959932557959/32211806695034006008900878336000000000000)],
    ![(8286832940778054649175382346963843402833888707/8854314003215673690630192470962873565184000000000000), (18735105936661128328403484481538276669252081/25940373056295919015518142004774043648000000000000), (40260552963779598973573155515906353223/79163736133715573167474798598553600000000000), (2374949260775431927887269537661673/8052951673758501502225219584000000000000)]]

private theorem tensor370 (u v : ℝ) :
    eval poly094 ((132825/262144)+((33207/65536)-(132825/262144))*u) ((32767/65536)+((1/2)-(32767/65536))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern370 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern370, Fin.sum_univ_succ]
  <;> ring

private theorem cert370 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (132825/262144) (33207/65536)) (hp : p ∈ Set.Icc (32767/65536) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern370) (m := (1/1000000000000000))
    tensor370 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern370]

private def bern371 : Coeff :=
  ![![(1217110556721451979256986640663281759973479/425688173231522773587990022642445844480000000000), (649900582301542545447722141637109680011773/324254663203698987693976775059675545600000000000), (113752635269672472278229473343171852643/98954670167144466459343498248192000000000000), (2374949260775431927887269537661673/8052951673758501502225219584000000000000)],
    ![(45389868261270404438426089948076268658458029/13834865630024490141609675735879489945600000000000), (1966495017315406051330431409286829359183707/810636658009247469234941937649188864000000000000), (1317455181037644115629962654593940659/838598899721563275079182188544000000000000), (2884146578772549895575693877875203/4026475836879250751112609792000000000000)],
    ![(25614793780191886366837945260533768004272239/6917432815012245070804837867939744972800000000000), (46171737076105770435725259256630049949521/16212733160184949384698838752983777280000000000), (9860464988693920195536160761132920207/4947733508357223322967174912409600000000000), (458254828822809665379035706909293/402647583687925075111260979200000000000)]]

private theorem tensor371 (u v : ℝ) :
    eval poly094 ((33207/65536)+((16605/32768)-(33207/65536))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern371 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern371, Fin.sum_univ_succ]
  <;> ring

private theorem cert371 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33207/65536) (16605/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern371) (m := (1/1000000000000000))
    tensor371 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern371]

private def bern372 : Coeff :=
  ![![(46326788341494756453935672991114714861651/7390419674158381485902604559764684800000000000), (92369547744377574143817250152338188280981/20265916450231186730873548441229721600000000000), (1408989464081315522289473075576444803/494773350835722332296717491240960000000000), (458254828822809665379035706909293/402647583687925075111260979200000000000)],
    ![(8214084111885804089630707101234932528301/1154753074087247107172281962463232000000000000), (17106571998381194301833498163138564417899/3166549445348622926698991943942144000000000000), (1427017209526756497123742101026753393/386541680340408072106810540032000000000000), (124677370424049846409682553930131/62913684951238292986134528000000000000)],
    ![(287237260542740292282761546078156158071/36086033565226472099133811326976000000000000), (9512425190096253872517094973694662417/1522379541032991791682207665356800000000000), (54810177560849095162028447945522563/12079427510637752253337829376000000000000), (1111628336946595214158147086197/393210530945239331163340800000000000)]]

private theorem tensor372 (u v : ℝ) :
    eval poly094 ((16605/32768)+((519/1024)-(16605/32768))*u) ((4095/8192)+((1/2)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern372 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern372, Fin.sum_univ_succ]
  <;> ring

private theorem cert372 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16605/32768) (519/1024)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern372) (m := (1/1000000000000000))
    tensor372 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern372]

private def bern373 : Coeff :=
  ![![(21713819095590379694475288252869937959/128847226780136024035603513344000000000000), (10899721775023088779973132514346443089/96635420085102018026702635008000000000000), (21728118253318421588681990660299843/377482109707429757916807168000000000000), (1111628336946595214158147086197/393210530945239331163340800000000000)],
    ![(2535497140621299057951884963819688161/12884722678013602403560351334400000000000), (6795700526290861751676452648938651651/48317710042551009013351317504000000000000), (271952555904204246891475862332891/3199000929723980999294976000000000000), (29370652586069181963205857646187/983026327363098327908352000000000000)],
    ![(7306150925521890477392323373852527871/32211806695034006008900878336000000000000), (4113499964392619206794836662757672249/24158855021275504506675658752000000000000), (10779655946063495068212609643146619/94370527426857439479201792000000000000), (488915215258344936217122286019/8330731587822867185664000000000000)]]

private theorem tensor373 (u v : ℝ) :
    eval poly094 ((519/1024)+((261/512)-(519/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern373 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern373, Fin.sum_univ_succ]
  <;> ring

private theorem cert373 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern373) (m := (1/1000000000000000))
    tensor373 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern373]

private def bern374 : Coeff :=
  ![![(2739207702168412752022442455941413/6882864678426069660021555200000000000), (1708367661940942481330332514497624633/6039713755318876126668914688000000000000), (8010440166840229349478829015135003/47185263713428719739600896000000000000), (488915215258344936217122286019/8330731587822867185664000000000000)],
    ![(1981044709817062379259185844142757/4301790424016293537513472000000000000), (259508410616431066174940342559232757/754964219414859515833614336000000000000), (1350712793804409868788396687724799/5898157964178589967450112000000000000), (7145917564332233968403098372397/61439145460193645494272000000000000)],
    ![(4015551756290467948306253947607/7573574690169530875904000000000000), (1554197937072362817282852046656361/3774821097074297579168071680000000000), (217731082072401022537807186460947/737269745522323745931264000000000000), (1389815710476547584731992553593/7679893182524205686784000000000000)]]

private theorem tensor374 (u v : ℝ) :
    eval poly094 ((261/512)+((33/64)-(261/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern374 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern374, Fin.sum_univ_succ]
  <;> ring

private theorem cert374 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern374) (m := (1/1000000000000000))
    tensor374 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern374]

private def bern375 : Coeff :=
  ![![(1636048638737405051425231655131133/491513163681549163954176000000000000), (3158572246754601060761077343359841/1474539491044647491862528000000000000), (20197312478474205084063962391827/18431743638058093648281600000000000), (1389815710476547584731992553593/7679893182524205686784000000000000)],
    ![(515684974708194534598080011653937/122878290920387290988544000000000000), (1062403242827624201443465523462453/368634872761161872965632000000000000), (39605835782709253335085470797191/23039679547572617060352000000000000), (268121191497834714709241730497/383994659126210284339200000000000)],
    ![(482309368973306934286945971863/86534007690413585203200000000000), (378805776817337754079223095604489/92158718190290468241408000000000000), (16192811412055314166688755895791/5759919886893154265088000000000000), (799659630678905885552865063313/479993323907762855424000000000000)]]

private theorem tensor375 (u v : ℝ) :
    eval poly094 ((33/64)+((9/16)-(33/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern375 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern375, Fin.sum_univ_succ]
  <;> ring

private theorem cert375 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern375) (m := (1/1000000000000000))
    tensor375 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern375]

private def bern376 : Coeff :=
  ![![(9007988842150411762175955728533/383994659126210284339200000000000), (76541543041332049718402380943309/5759919886893154265088000000000000), (4497937367972580598356485162987/719989985861644283136000000000000), (799659630678905885552865063313/479993323907762855424000000000000)],
    ![(1716122648378809646809725068861/47999332390776285542400000000000), (15757385969403422655950893239787/719989985861644283136000000000000), (4359747878604778702598814676261/359994992930822141568000000000000), (33221152448816948177726458301/5999916548847035692800000000000)],
    ![(285861045406072969625120466659/4799933239077628554240000000000), (2900589344851701991755862346611/71998998586164428313600000000000), (148325264623610216186953937023/5624921764544095962000000000000), (498452931409841186755720788223/29999582744235178464000000000000)]]

private theorem tensor376 (u v : ℝ) :
    eval poly094 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern376 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly094, bern376, Fin.sum_univ_succ]
  <;> ring

private theorem cert376 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly094 δ p := by
  apply positive_on_box_from_tensor (β := bern376) (m := (1/1000000000000000))
    tensor376 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern376]

private def bern377 : Coeff :=
  ![![(1746993873285209/27635129200000000), (790922425368759515009539/13978824809015152800000000), (43634601334271353640267/873676550563447050000000), (40358987821861586765267/931921653934343520000000)],
    ![(11883983658760733/1105405168000000000), (5109242500402592581782619/559152992360606112000000000), (4523914312437038566867/554715270199014000000000), (1454642740960534761332591/186384330786868704000000000)],
    ![(15806006630556553/552702584000000000), (3652251834816193025260307/279576496180303056000000000), (657045185402705059483933/139788248090151528000000000), (35150509201400049862931/31064055131144784000000000)]]

private theorem tensor377 (u v : ℝ) :
    eval poly101 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern377 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern377, Fin.sum_univ_succ]
  <;> ring

private theorem cert377 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern377) (m := (1/1000000000000000))
    tensor377 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern377]

private def bern378 : Coeff :=
  ![![(15806006630556553/552702584000000000), (11647488477989981617904009/559152992360606112000000000), (2768971780601930793688697/186384330786868704000000000), (38684363071418664123491/3727686615737374080000000)],
    ![(51340042863465479/1105405168000000000), (7093874513655511297338719/223661196944242444800000000), (11416348315856210401605433/559152992360606112000000000), (890985998720433830628119/74553732314747481600000000)],
    ![(37197968335204463/276351292000000000), (28920532159876962118729027/279576496180303056000000000), (2754664306934503292658683/34947062022537882000000000), (370005367256709332331391/6212811026228956800000000)]]

private theorem tensor378 (u v : ℝ) :
    eval poly101 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern378 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern378, Fin.sum_univ_succ]
  <;> ring

private theorem cert378 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern378) (m := (1/1000000000000000))
    tensor378 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern378]

private def bern379 : Coeff :=
  ![![(38684363071418664123491/3727686615737374080000000), (3033682680110868824834953/372768661573737408000000000), (14029886573570423898220313/2236611969442424448000000000), (33685522581034052043179/7100355458547379200000000)],
    ![(554891086716269037699313/49702488209831654400000000), (35463769391372314524064207/4473223938884848896000000000), (4681607575240244659866509/894644787776969779200000000), (187831307407328124088447/62128110262289568000000000)],
    ![(3997556380542715960973/170408531005137100800000), (8218954159939917509649599/447322393888484889600000000), (125883827510808190031095973/8946447877769697792000000000), (1486325325994478779559833/142007109170947584000000000)]]

private theorem tensor379 (u v : ℝ) :
    eval poly101 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((3/8)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern379 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern379, Fin.sum_univ_succ]
  <;> ring

private theorem cert379 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern379) (m := (1/1000000000000000))
    tensor379 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern379]

private def bern380 : Coeff :=
  ![![(33685522581034052043179/7100355458547379200000000), (8901466132753377641291921/2236611969442424448000000000), (1968082210431613806806687/596429858517979852800000000), (8049446491404814240380301/2982149292589899264000000000)],
    ![(1930318519965504317865053/497024882098316544000000000), (52769389054795162068939691/17892895755539395584000000000), (75772695647062013341583203/35785791511078791168000000000), (16492353926192872059027593/11928597170359597056000000000)],
    ![(4226170456068123742758839/795239811357306470400000000), (2106410616137870903222399/511225593015411302400000000), (87365685587033980594954609/28628633208863032934400000000), (318278229613964669113791/151474249782344089600000000)]]

private theorem tensor380 (u v : ℝ) :
    eval poly101 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern380 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern380, Fin.sum_univ_succ]
  <;> ring

private theorem cert380 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern380) (m := (1/1000000000000000))
    tensor380 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern380]

private def bern381 : Coeff :=
  ![![(34270626091329170220571/10611889612800000000000000), (27257812437516053738249/10611889612800000000000000), (987866848115310260801/497432325600000000000000), (81878474261254508839/55270258400000000000000)],
    ![(71004733388985978491843/28298372300800000000000000), (447801866067706947282953/254685350707200000000000000), (724754879439275493779/663243100800000000000000), (679971996936449653183/1326486201600000000000000)],
    ![(1631348880045128602693271/679160935219200000000000000), (3141851187228687976698647/2037482805657600000000000000), (24679594615540408328251/31835668838400000000000000), (1077996065797293109417/10611889612800000000000000)]]

private theorem tensor381 (u v : ℝ) :
    eval poly102 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern381 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly102, bern381, Fin.sum_univ_succ]
  <;> ring

private theorem cert381 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly102 δ p := by
  apply positive_on_box_from_tensor (β := bern381) (m := (1/1000000000000000))
    tensor381 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern381]

private def bern382 : Coeff :=
  ![![(14439504704016755003565989/7634302189030142115840000000), (216692354348564569057662997/143143166044315164672000000000), (2658366363411332302408771001/2290290656709042634752000000000), (211559526234440746525972733/254476739634338070528000000000)],
    ![(166227058033170359006954537/95428777362876776448000000000), (1750287758738692765558993/1325399685595510784000000000), (212113077742411420918985321/229029065670904263475200000000), (70971186962492949233102017/127238369817169035264000000000)],
    ![(318278229613964669113791/151474249782344089600000000), (11637258825510498349070611/7157158302215758233600000000), (135156149554870789173285181/114514532835452131737600000000), (9710506054732150606037329/12723836981716903526400000000)]]

private theorem tensor382 (u v : ℝ) :
    eval poly101 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern382 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern382, Fin.sum_univ_succ]
  <;> ring

private theorem cert382 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern382) (m := (1/1000000000000000))
    tensor382 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern382]

private def bern383 : Coeff :=
  ![![(4114512505341797317109/3368638238687232000000000), (274237982907930413107759/303177441481850880000000000), (11304530446428787469/18504482512320000000000), (134066896099173308497/394762293596160000000000)],
    ![(58393585493150289947/53898211818995712000000), (453704486412390957059429/606354882963701760000000000), (49348792068223751351/112789226741760000000000), (118676609414921086987/789524587192320000000000)],
    ![(14257871963738984800061/13474552954748928000000000), (851604882658336304526199/1212709765927403520000000000), (881199735578356344113/2368573761576960000000000), (11677862386938875553/175449908264960000000000)]]

private theorem tensor383 (u v : ℝ) :
    eval poly103 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern383 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern383, Fin.sum_univ_succ]
  <;> ring

private theorem cert383 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern383) (m := (1/1000000000000000))
    tensor383 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern383]

private def bern384 : Coeff :=
  ![![(689654395179055555579127381/1017906958537352282112000000000), (4508458880238761748191129123/9161162626836170539008000000000), (765299702753530383385420993/2442976700489645477068800000000), (17202635564639363050057801/122148835024482273853440000000)],
    ![(168076247509814455293475307/254476739634338070528000000000), (1062965899252112648298027437/2290290656709042634752000000000), (2515624778362291186099097089/9161162626836170539008000000000), (2803474130419721827548629/30537208756120568463360000000)],
    ![(9710506054732150606037329/12723836981716903526400000000), (63513756961448638594861351/114514532835452131737600000000), (161810234312247437634442339/458058131341808526950400000000), (2021998091718830027840459/12723836981716903526400000000)]]

private theorem tensor384 (u v : ℝ) :
    eval poly101 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern384 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern384, Fin.sum_univ_succ]
  <;> ring

private theorem cert384 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern384) (m := (1/1000000000000000))
    tensor384 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern384]

private def bern385 : Coeff :=
  ![![(56691003262133273096387/104319119649669120000000000), (67950770248484989211861/179660706063319040000000000), (2077701755604062328157/9474295046307840000000000), (11677862386938875553/175449908264960000000000)],
    ![(35866040892655956324509/69546079766446080000000000), (3353119720606099873377947/9701678127419228160000000000), (1149465447819087635269/6316196697538560000000000), (77949065617507465957/3158098348769280000000000)],
    ![(215009437070396395133467/417276478598676480000000000), (6597194004377442949056047/19403356254838456320000000000), (6493824807782865775457/37897180185231360000000000), (58055124759689109937/6316196697538560000000000)]]

private theorem tensor385 (u v : ℝ) :
    eval poly103 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern385 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern385, Fin.sum_univ_succ]
  <;> ring

private theorem cert385 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern385) (m := (1/1000000000000000))
    tensor385 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern385]

private def bern386 : Coeff :=
  ![![(10841167543498526598506993/24837885630873600000000000000), (17051448354314381060961259/52159559824834560000000000000), (456887004678947964180547571/2086382392993382400000000000000), (5225450781622097766686201/46364053177630720000000000000)],
    ![(1993956256351158420218761/4346629985402880000000000000), (7155355871730500371723/20698238025728000000000000), (12222925702302785580849581/52159559824834560000000000000), (144483595396437221665511/1159101329440768000000000000)],
    ![(18715920041509209844189/36221916545024000000000000), (13041604119128737601003/32599724890521600000000000), (371783051850519417477107/1303988995620864000000000000), (711523119842670776831/4139647605145600000000000)]]

private theorem tensor386 (u v : ℝ) :
    eval poly102 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern386 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly102, bern386, Fin.sum_univ_succ]
  <;> ring

private theorem cert386 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) : 0 < eval poly102 δ p := by
  apply positive_on_box_from_tensor (β := bern386) (m := (1/1000000000000000))
    tensor386 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern386]

private def bern387 : Coeff :=
  ![![(591738979035881599965967/2299657037610483712000000000), (13425215950808862448850479/77613425019353825280000000000), (6842155556341000435079/75794360370462720000000000), (58055124759689109937/6316196697538560000000000)],
    ![(7515355497808720231381/29672994033683660800000000), (26028173640659947297862999/155226850038707650560000000000), (4231428398232795300713/50529573580308480000000000), (18267243044052397897/12632393395077120000000000)],
    ![(2354258748465747687637663/9198628150441934848000000000), (52482526021566884003693119/310453700077415301120000000000), (25419536459116357929199/303177441481850880000000000), (2503460452303972619/8421595596718080000000000)]]

private theorem tensor387 (u v : ℝ) :
    eval poly103 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern387 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern387, Fin.sum_univ_succ]
  <;> ring

private theorem cert387 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern387) (m := (1/1000000000000000))
    tensor387 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern387]

private def bern388 : Coeff :=
  ![![(2354258748465747687637663/9198628150441934848000000000), (527755035129143473845856981/2483629600619322408960000000000), (93533728950216845770958729/551917689026516090880000000000), (420113219191918428898635503/3311506134159096545280000000000)],
    ![(148672330788174506471701/574914259402620928000000000), (6659588169371405345318939/31045370007741530112000000000), (2121617827387699870294579/12418148003096612044800000000), (5282145934113611823774881/41393826676988706816000000000)],
    ![(275106037134341971373/1026632606076108800000000), (86623527746030262231541/388067125096769126400000000), (27769441167276998693437/155226850038707650560000000), (3326316003567146516563/24639182545826611200000000)]]

private theorem tensor388 (u v : ℝ) :
    eval poly103 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern388 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern388, Fin.sum_univ_succ]
  <;> ring

private theorem cert388 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern388) (m := (1/1000000000000000))
    tensor388 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern388]

private def bern389 : Coeff :=
  ![![(420113219191918428898635503/3311506134159096545280000000000), (46609152258296947471343609/441534151221212872704000000000), (3352434332074952132383043773/39738073609909158543360000000000), (22348268004649614452914261/353227320976970298163200000000)],
    ![(93631654880111930533402887/735890252035354787840000000000), (168130506491000130123708541/1589522944396366341734400000000), (958453170356892000689266859/11353735317116902440960000000000), (223117265206623168762035161/3532273209769702981632000000000)],
    ![(1712313439529520812528683663/13246024536636386181120000000000), (244439459318163896572274327/2270747063423380488192000000000), (13690542468730004371418148253/158952294439636634173440000000000), (457202676983831645819879177/7064546419539405963264000000000)]]

private theorem tensor389 (u v : ℝ) :
    eval poly103 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern389 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern389, Fin.sum_univ_succ]
  <;> ring

private theorem cert389 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern389) (m := (1/1000000000000000))
    tensor389 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern389]

private def bern390 : Coeff :=
  ![![(22348268004649614452914261/353227320976970298163200000000), (209490746121401389940333119/4967259201238644817920000000000), (25689910187965186972051/1212709765927403520000000000), (2503460452303972619/8421595596718080000000000)],
    ![(446599945253119313291177771/7064546419539405963264000000000), (835369584967777603564005517/19869036804954579271680000000000), (101745739051257390407393/4850839063709614080000000000), (4688574638040523/465710355578880000000000)],
    ![(1796637097903316609926305041/28258185678157623853056000000000), (3363962604828307315804241431/79476147219818317086720000000000), (15219933185340869012737/718642824253276160000000000), (54635172080506428233/404236588642467840000000000)]]

private theorem tensor390 (u v : ℝ) :
    eval poly103 ((237/512)+((951/2048)-(237/512))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern390 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern390, Fin.sum_univ_succ]
  <;> ring

private theorem cert390 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern390) (m := (1/1000000000000000))
    tensor390 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern390]

private def bern391 : Coeff :=
  ![![(1796637097903316609926305041/28258185678157623853056000000000), (3363962604828307315804241431/79476147219818317086720000000000), (15219933185340869012737/718642824253276160000000000), (54635172080506428233/404236588642467840000000000)],
    ![(903437207397077983343949499/14129092839078811926528000000000), (241889062127536015525175771/5676867658558451220480000000000), (207446717901688682529113/9701678127419228160000000000), (5844481187510760139/22457588257914880000000000)],
    ![(457202676983831645819879177/7064546419539405963264000000000), (860447249442802461309551839/19869036804954579271680000000000), (106714880551034649602531/4850839063709614080000000000), (80607014722334925697/101059147160616960000000000)]]

private theorem tensor391 (u v : ℝ) :
    eval poly103 ((951/2048)+((477/1024)-(951/2048))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern391 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern391, Fin.sum_univ_succ]
  <;> ring

private theorem cert391 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern391) (m := (1/1000000000000000))
    tensor391 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern391]

private def bern392 : Coeff :=
  ![![(1712313439529520812528683663/13246024536636386181120000000000), (427305094693396742805443807/4967259201238644817920000000000), (104780312197698611385803/2425419531854807040000000000), (80607014722334925697/101059147160616960000000000)],
    ![(10870356820106417971600721/82787653353977413632000000000), (302644579346387641276513/3449485556415725568000000000), (1351957832848868447729/30317744148185088000000000), (394209819748766533/210539889917952000000000)],
    ![(3326316003567146516563/24639182545826611200000000), (17677675597086309269071/194033562548384563200000000), (75223894441693139/1579049174384640000000), (3628877503562029/789524587192320000000)]]

private theorem tensor392 (u v : ℝ) :
    eval poly103 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern392 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern392, Fin.sum_univ_succ]
  <;> ring

private theorem cert392 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern392) (m := (1/1000000000000000))
    tensor392 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern392]

private def bern393 : Coeff :=
  ![![(4226170456068123742758839/795239811357306470400000000), (2106410616137870903222399/511225593015411302400000000), (87365685587033980594954609/28628633208863032934400000000), (318278229613964669113791/151474249782344089600000000)],
    ![(13409578200478601442333983/1988099528393266176000000000), (94679354074855801156628239/17892895755539395584000000000), (95094345547015292097202213/23857194340719194112000000000), (67272934476013126652788979/23857194340719194112000000000)],
    ![(1486325325994478779559833/142007109170947584000000000), (9689478693884268706607029/1118305984721212224000000000), (251822577972818678016841453/35785791511078791168000000000), (66486012589246639496254997/11928597170359597056000000000)]]

private theorem tensor393 (u v : ℝ) :
    eval poly101 ((15/32)+((9/16)-(15/32))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern393 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern393, Fin.sum_univ_succ]
  <;> ring

private theorem cert393 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern393) (m := (1/1000000000000000))
    tensor393 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern393]

private def bern394 : Coeff :=
  ![![(318278229613964669113791/151474249782344089600000000), (11637258825510498349070611/7157158302215758233600000000), (135156149554870789173285181/114514532835452131737600000000), (9710506054732150606037329/12723836981716903526400000000)],
    ![(234803511280425124076422123/95428777362876776448000000000), (9873545538451468402944757/5112255930154113024000000000), (328511520477071735774155403/229029065670904263475200000000), (123238934132150062887644563/127238369817169035264000000000)],
    ![(635293430589437935367020069/190857554725753552896000000000), (130516249538096387420608967/47714388681438388224000000000), (4986335218104538599512172641/2290290656709042634752000000000), (420630514913069201144142917/254476739634338070528000000000)]]

private theorem tensor394 (u v : ℝ) :
    eval poly101 ((15/32)+((33/64)-(15/32))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern394 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern394, Fin.sum_univ_succ]
  <;> ring

private theorem cert394 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern394) (m := (1/1000000000000000))
    tensor394 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern394]

private def bern395 : Coeff :=
  ![![(26957057827094354503/24061701704908800000000), (2184338927414848035151/3031774414818508800000000), (275493435241838353/789524587192320000000), (3628877503562029/789524587192320000000)],
    ![(4068639303038819982497/3368638238687232000000000), (47583517471999386659363/60635488296370176000000000), (185377154745403241629/473714752315392000000000), (694453431319842167/26317486239744000000000)],
    ![(18972291279668750433293/13474552954748928000000000), (166191999507790054433377/173244252275343360000000000), (1282821607584360940693/2368573761576960000000000), (242738564970715768057/1579049174384640000000000)]]

private theorem tensor395 (u v : ℝ) :
    eval poly103 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern395 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly103, bern395, Fin.sum_univ_succ]
  <;> ring

private theorem cert395 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : 0 < eval poly103 δ p := by
  apply positive_on_box_from_tensor (β := bern395) (m := (1/1000000000000000))
    tensor395 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern395]

private def bern396 : Coeff :=
  ![![(158256624648044637830781107/145415279791050326016000000000), (7825406719868523725778322451/9161162626836170539008000000000), (23008774067425476816217309951/36644650507344682156032000000000), (249958880999634434391766813/610744175122411369267200000000)],
    ![(667108383177369326919432043/508953479268676141056000000000), (974047592291371586957093849/916116262683617053900800000000), (15095204879170264177660117009/18322325253672341078016000000000), (8616081614348943396710051/14541527979105032601600000000)],
    ![(420630514913069201144142917/254476739634338070528000000000), (3185344342274164915689843059/2290290656709042634752000000000), (3472613459053333430597256949/3053720875612056846336000000000), (136180523903647148604140837/152686043780602842316800000000)]]

private theorem tensor396 (u v : ℝ) :
    eval poly101 ((63/128)+((33/64)-(63/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern396 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern396, Fin.sum_univ_succ]
  <;> ring

private theorem cert396 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern396) (m := (1/1000000000000000))
    tensor396 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern396]

private def bern397 : Coeff :=
  ![![(3470322051422627158090007/5462409902655799296000000000), (1429779808986832861688773/3277445941593479577600000000), (31349214796560921028931/128025232093495296000000000), (65067546069495575663/1066876934112460800000000)],
    ![(7738789875884506694037641/10924819805311598592000000000), (5501209625007688815289837/10924819805311598592000000000), (39251613239167441031011/128025232093495296000000000), (417179086297732859843/3556256447041536000000000)],
    ![(5879217531736802476340381/7283213203541065728000000000), (39090427073048806552983961/65548918831869591552000000000), (67173936419724927357371/170700309457993728000000000), (605178878772345549797/3048219811749888000000000)]]

private theorem tensor397 (u v : ℝ) :
    eval poly104 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern397 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly104, bern397, Fin.sum_univ_succ]
  <;> ring

private theorem cert397 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : 0 < eval poly104 δ p := by
  apply positive_on_box_from_tensor (β := bern397) (m := (1/1000000000000000))
    tensor397 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern397]

private def bern398 : Coeff :=
  ![![(101228788814635618275464963/162865113365976365137920000000), (5930270988270785385989221549/11726288162350298289930240000000), (16412743041517125741273951337/41879600579822493892608000000000), (12163600133618253154706677429/43430696897593697370112000000000)],
    ![(90659752341724421707838549/122148835024482273853440000000), (45662891474061714775811035397/73289301014689364312064000000000), (37079862052867550554181375767/73289301014689364312064000000000), (121250944181789575249080647/310219263554240695500800000000)],
    ![(136180523903647148604140837/152686043780602842316800000000), (4698217975165495485651193271/6107441751224113692672000000000), (1697987001007579868446057081/2617475036238905868288000000000), (1439276160206956243850946229/2714418556099606085632000000000)]]

private theorem tensor398 (u v : ℝ) :
    eval poly101 ((129/256)+((33/64)-(129/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern398 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern398, Fin.sum_univ_succ]
  <;> ring

private theorem cert398 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern398) (m := (1/1000000000000000))
    tensor398 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern398]

private def bern399 : Coeff :=
  ![![(12163600133618253154706677429/43430696897593697370112000000000), (525694805660598984775570234313/2345257632470059657986048000000000), (791441100321436930658620945531/4690515264940119315972096000000000), (39541754370336662414259714647/347445575180749578960896000000000)],
    ![(29138732319068793689577968009/86861393795187394740224000000000), (1307402719836211959233242759021/4690515264940119315972096000000000), (695779242631873621281303016397/3127010176626746210648064000000000), (1043040358046028191673789274571/6254020353253492421296128000000000)],
    ![(9877469009690090589437771179/24817541084339255640064000000000), (127748574447545777786316320969/375241221195209545277767680000000), (5317008858877851119983703765507/18762061059760477263888384000000000), (567475692416619793489140937291/2501608141301396968518451200000000)]]

private theorem tensor399 (u v : ℝ) :
    eval poly101 ((129/256)+((261/512)-(129/256))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern399 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern399, Fin.sum_univ_succ]
  <;> ring

private theorem cert399 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern399) (m := (1/1000000000000000))
    tensor399 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern399]

private def bern400 : Coeff :=
  ![![(39541754370336662414259714647/347445575180749578960896000000000), (323999980670879158847558999069/3752412211952095452777676800000000), (316304618682423105409134321443/5360588874217279218253824000000000), (265088321504205934992631892177/8338693804337989895061504000000000)],
    ![(1754791936712088115130464138217/12508040706506984842592256000000000), (8452687573331803585851875363447/75048244239041909055553536000000000), (1824558924770583160246607622773/21442355496869116873015296000000000), (54965565763889634296257507549/952993577638627416578457600000000)],
    ![(8433043051599331581054211512031/50032162826027939370369024000000000), (14077713040300606544500085373163/100064325652055878740738048000000000), (67811090184932517995310465882341/600385953912335272444428288000000000), (11384621577535151608220729612033/133419100869407838320984064000000000)]]

private theorem tensor400 (u v : ℝ) :
    eval poly101 ((129/256)+((519/1024)-(129/256))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern400 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern400, Fin.sum_univ_succ]
  <;> ring

private theorem cert400 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern400) (m := (1/1000000000000000))
    tensor400 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern400]

private def bern401 : Coeff :=
  ![![(147922043038221699216172918121468897/867161445926561220825075154944000000000), (1136457735511892266805404496519667299/7804453013339050987425676394496000000000), (238645235611089756779511182775031/1975953815587867365161304064000000000), (26690915391645160273990183859287/277868505317043848225808384000000000)],
    ![(8808622626829102840401840564019629421/48561040971887428366204208676864000000000), (68326727103173982224011756937772327943/437049368746986855295837878091776000000000), (56083936664893889263395546823048393/426806024166979350874841677824000000000), (26328261629000476298738449834973/246994226948483420645163008000000000)],
    ![(14964743931828118924894930736894402659/77697665555019885385926733882982400000000), (16728172860120718174270386691531771663/99896998570739852639048657849548800000000), (97264184961298416485181885735005549/682889638667166961399746684518400000000), (418021618653552991137203252841667/3556716868058161257290347315200000000)]]

private theorem tensor401 (u v : ℝ) :
    eval poly105 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern401 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly105, bern401, Fin.sum_univ_succ]
  <;> ring

private theorem cert401 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : 0 < eval poly105 δ p := by
  apply positive_on_box_from_tensor (β := bern401) (m := (1/1000000000000000))
    tensor401 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern401]

private def bern402 : Coeff :=
  ![![(6203278627098308834210988400117/106735280695526270656787251200000000), (85323520025847713413719272099461/1921235052519472871822170521600000000), (16870751698443504247674507907051/548924300719849391949191577600000000), (43775048350247958625179159919303/2561646736692630495762894028800000000)],
    ![(19079800784479700409696780668893/266838201738815676641968128000000000), (277357141023934218097382119420141/4803087631298682179555426304000000000), (422854540257665711306484512633621/9606175262597364359110852608000000000), (12946368580857562126389676852049/426941122782105082627149004800000000)],
    ![(11384621577535151608220729612033/133419100869407838320984064000000000), (171762602223584057431338767760209/2401543815649341089777713152000000000), (92451274014921447618718177488179/1601029210432894059851808768000000000), (28177609897917827860772018806031/640411684173157623940723507200000000)]]

private theorem tensor402 (u v : ℝ) :
    eval poly101 ((1035/2048)+((519/1024)-(1035/2048))*u) ((255/512)+((511/1024)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern402 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern402, Fin.sum_univ_succ]
  <;> ring

private theorem cert402 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern402) (m := (1/1000000000000000))
    tensor402 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern402]

private def bern403 : Coeff :=
  ![![(133917826427509672545939132461141390153/932371986660238624631120806595788800000000), (366755905798871123445343447210708231529/2797115959980715873893362419787366400000000), (162033715741263471072324910280605613/1365779277334333922799493369036800000000), (377681462399602158555953252841667/3556716868058161257290347315200000000)],
    ![(278167389942735275936897666573747462147/1864743973320477249262241613191577600000000), (424655186884261716366026031673167247159/3107906622200795415437069355319296000000000), (1695386175362147524494348949106030299/13657792773343339227994933690368000000000), (1323815336132597588060043468168983/11855722893527204190967824384000000000)],
    ![(38491278994665942999591022300314868783/248632529776063633234965548425543680000000), (7958028552879699212575893315889799888741/55942319199614317477867248395747328000000000), (393731471042901280568815492789677937/3035065060742964272887763042304000000000), (8339214400651157382718257816161047/71134337361163225145806946304000000000)]]

private theorem tensor403 (u v : ℝ) :
    eval poly106 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern403 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly106, bern403, Fin.sum_univ_succ]
  <;> ring

private theorem cert403 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : 0 < eval poly106 δ p := by
  apply positive_on_box_from_tensor (β := bern403) (m := (1/1000000000000000))
    tensor403 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern403]

private def bern404 : Coeff :=
  ![![(20789460727480667705662890491201/683105796451368132203438407680000000), (1035752353391280710097731881040263/43913944057587951355935326208000000000), (10295327161762684396871305395883841/614795216806231318983094566912000000000), (193488724418118938314226730086383/19517308470039089491526811648000000000)],
    ![(95194325538408342100713068168209/2561646736692630495762894028800000000), (465724056106797320098900182488803/15369880420155782974577364172800000000), (3604017117403202751210979891718111/153698804201557829745773641728000000000), (567108573513218315250459302811799/34155289822568406610171920384000000000)],
    ![(28177609897917827860772018806031/640411684173157623940723507200000000), (33965942919846360382020561016301/914873834533082319915319296000000000), (1162781880576070876655723220280577/38424701050389457436443410432000000000), (39968589882354242691480577125749/1707764491128420330508596019200000000)]]

private theorem tensor404 (u v : ℝ) :
    eval poly101 ((2073/4096)+((519/1024)-(2073/4096))*u) ((511/1024)+((1023/2048)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern404 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern404, Fin.sum_univ_succ]
  <;> ring

private theorem cert404 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern404) (m := (1/1000000000000000))
    tensor404 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern404]

private def bern405 : Coeff :=
  ![![(2575874157821169312723935016470970499249/23914110731508648840037490485100544000000000), (21852686308359618785982021845981503614179/215226996583577839560337414365904896000000000), (1670262045827104514971540735487419541/17515217820929186162136833851392000000000), (6102672358663555597981265058244801/68418819613004633445847007232000000000)],
    ![(5282462140729148769727275116724087053933/47828221463017297680074980970201088000000000), (44879371212479475409167535527121571316439/430453993167155679120674828731809792000000000), (10307601349444645909434808374527222179/105091306925575116972821003108352000000000), (1397445414892488029150103590411541/15204182136223251876854890496000000000)],
    ![(10828693999673712612601268619932903146297/95656442926034595360149961940402176000000000), (92127810483223000633315936978265436805883/860907986334311358241349657463619584000000000), (21192403212191206416518227635707345527/210182613851150233945642006216704000000000), (1036161553125911797734508093258289/10947011138080741351335521157120000000)]]

private theorem tensor405 (u v : ℝ) :
    eval poly107 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern405 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly107, bern405, Fin.sum_univ_succ]
  <;> ring

private theorem cert405 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : 0 < eval poly107 δ p := by
  apply positive_on_box_from_tensor (β := bern405) (m := (1/1000000000000000))
    tensor405 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern405]

private def bern406 : Coeff :=
  ![![(9088776849620918505521707703158993/546484637161094505762750726144000000000), (129933026559353918782984675877056889/9836723468899701103729513070592000000000), (27510625241878007600377983882815327/2810492419685628886779860877312000000000), (83547284921100809581813894457080979/13115631291866268138306017427456000000000)],
    ![(1366480371160303169080070845326779/68310579645136813220343840768000000000), (4076936148382642609898833455628439/245918086722492527593237826764800000000), (4621458904385577870259453906948181/351311552460703610847482609664000000000), (30394723378399215969018512911253/3122769355206254318644289863680000000)],
    ![(39968589882354242691480577125749/1707764491128420330508596019200000000), (3070195872965681010038431471414961/153698804201557829745773641728000000000), (113045234237949156494904049287349/6831057964513681322034384076800000000), (2689518271868762212084916394744571/204931738935410439661031522304000000000)]]

private theorem tensor406 (u v : ℝ) :
    eval poly101 ((4149/8192)+((519/1024)-(4149/8192))*u) ((1023/2048)+((2047/4096)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern406 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern406, Fin.sum_univ_succ]
  <;> ring

private theorem cert406 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern406) (m := (1/1000000000000000))
    tensor406 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern406]

private def bern407 : Coeff :=
  ![![(119290164728821611091854946096915762342483/1147877315112415144321799543284826112000000000), (347223037852285070289027724649710284847867/3443631945337245432965398629854478336000000000), (41086705032208712933020783026266494327/420365227702300467891284012433408000000000), (1036161553125911797734508093258289/10947011138080741351335521157120000000)],
    ![(34533693130596556023326230158516514909069/327964947174975755520514155224236032000000000), (234634311186938227658415618425329204962241/2295754630224830288643599086569652224000000000), (83326626982263092465221700295895895839/840730455404600935782568024866816000000000), (17519366338792866768462080788987979/182450185634679022522258685952000000000)],
    ![(163270279356623340036890998890335872956257/1530503086816553525762399391046434816000000000), (1426803835334644580330427673530383636145227/13774527781348981731861594519417913344000000000), (11264664709295989024720005974916932617/112097394053946791437675736648908800000000), (15231847725656524247711170493092543/156385873401153447876221730816000000000)]]

private theorem tensor407 (u v : ℝ) :
    eval poly107 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern407 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly107, bern407, Fin.sum_univ_succ]
  <;> ring

private theorem cert407 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : 0 < eval poly107 δ p := by
  apply positive_on_box_from_tensor (β := bern407) (m := (1/1000000000000000))
    tensor407 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern407]

private def bern408 : Coeff :=
  ![![(170330710233085001765001350725086241/17487508389155024184408023236608000000000), (505486615822809271380195939233278229/62955030200958087063868883651788800000000), (568304680429066949615738947751131343/89935757429940124376955548073984000000000), (214941136516770536428552336022352459/46633355704413397825088061964288000000000)],
    ![(37473375948609686080414050436364393/3278907822966567034576504356864000000000), (191167390224765691863763183743113723/19673446937799402207459026141184000000000), (315008181638687271530606216874691259/39346893875598804414918052282368000000000), (3669640184682772509941917875318381/582916946305167472813600774553600000000)],
    ![(2689518271868762212084916394744571/204931738935410439661031522304000000000), (519688643163090215711958633957027/45540386430091208813562560512000000000), (23853350343826759259198281928594801/2459180867224925275932378267648000000000), (1455163699713713995878219015248931/182161545720364835254250242048000000000)]]

private theorem tensor408 (u v : ℝ) :
    eval poly101 ((8301/16384)+((519/1024)-(8301/16384))*u) ((2047/4096)+((4095/8192)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern408 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern408, Fin.sum_univ_succ]
  <;> ring

private theorem cert408 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern408) (m := (1/1000000000000000))
    tensor408 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern408]

private def bern409 : Coeff :=
  ![![(214941136516770536428552336022352459/46633355704413397825088061964288000000000), (9453966531851476156092393949294710377/2518201208038323482554755346071552000000000), (2920567066797960402404012965400435861/1007280483215329393021902138428620800000000), (91540884577164279213424455645116297/44768021476236861912084539485716480000000)],
    ![(508512351291392337223905766047822939/93266711408826795650176123928576000000000), (23152973116157849331536622841367698969/5036402416076646965109510692143104000000000), (12564594207993315916898466147603354163/3357601610717764643406340461428736000000000), (3877712404662291470602532006497031767/1343040644287105857362536184571494400000000)],
    ![(234921094638544984192816652795403951/37306684563530718260070449571430400000000), (1566095394333957005280059453891485219/287794423775808398006257753836748800000000), (18479682539139625516942018157244819829/4029121932861317572087608553714483200000000), (1431858975671563919882509697820629089/383725898367744530675010338448998400000000)]]

private theorem tensor409 (u v : ℝ) :
    eval poly101 ((8301/16384)+((16605/32768)-(8301/16384))*u) ((4095/8192)+((8191/16384)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern409 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern409, Fin.sum_univ_succ]
  <;> ring

private theorem cert409 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (16605/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern409) (m := (1/1000000000000000))
    tensor409 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern409]

private def bern410 : Coeff :=
  ![![(91540884577164279213424455645116297/44768021476236861912084539485716480000000), (6516885284321256889004275581289828373/4029121932861317572087608553714483200000000), (47952133388285945887313320554513191273/40291219328613175720876085537144832000000000), (6830363936650488147025438331082807137/8953604295247372382416907897143296000000000)],
    ![(6623938941977219847005265675850520677/2686081288574211714725072369142988800000000), (164278345805055789565765899219644588267/80582438657226351441752171074289664000000000), (259681942382853264623770172037875717099/161164877314452702883504342148579328000000000), (8480537274572477439953035855598942839/7162883436197897905933526317714636800000000)],
    ![(31026315522979970074393163249439508511/10744325154296846858900289476571955200000000), (264338143159648133358849486164610583451/107443251542968468589002894765719552000000000), (1310498370846273628957486304484063333329/644659509257810811534017368594317312000000000), (32856744965332864014537042727594378991/20465381246279708302667218050613248000000000)]]

private theorem tensor410 (u v : ℝ) :
    eval poly101 ((8301/16384)+((33207/65536)-(8301/16384))*u) ((8191/16384)+((16383/32768)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern410 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern410, Fin.sum_univ_succ]
  <;> ring

private theorem cert410 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (33207/65536)) (hp : p ∈ Set.Icc (8191/16384) (16383/32768)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern410) (m := (1/1000000000000000))
    tensor410 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern410]

private def bern411 : Coeff :=
  ![![(4827000464232514771855765600532988657425089/48976098778129712824396780513485914112000000000), (17309070933318606500735717648046289473934351/176313955601266966167828409848549290803200000000), (438459919287750825450177875205290381869/4483895762157871657507029465956352000000000), (15231847725656524247711170493092543/156385873401153447876221730816000000000)],
    ![(38683439832931962848235569447641163225617271/391808790225037702595174244107887312896000000000), (693576532130114992409920982780470099301740573/7052558224050678646713136393941971632128000000000), (10541555205556540681257333474091856017537/107613498291788919780168707182952448000000000), (56966013912240255133002083755393489/583840594030972872071227795046400000000)],
    ![(310007307091035111914958424609756282958412433/3134470321800301620761393952863098503168000000000), (794046743692305125769061052253841104692127533/8060066541772204167672155878790824722432000000000), (84480661035144096894895005092744223831607/860907986334311358241349657463619584000000000), (6847982251170210817231779753698599049/70060871283716744648547335405568000000000)]]

private theorem tensor411 (u v : ℝ) :
    eval poly107 ((8301/16384)+((66411/131072)-(8301/16384))*u) ((16383/32768)+((1/2)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern411 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly107, bern411, Fin.sum_univ_succ]
  <;> ring

private theorem cert411 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : 0 < eval poly107 δ p := by
  apply positive_on_box_from_tensor (β := bern411) (m := (1/1000000000000000))
    tensor411 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern411]

private def bern412 : Coeff :=
  ![![(678504528726636956052287746614443280689/573030674895831832474682105417170944000000000), (80073969499006784424979580314171266541/82516417184999783876354223180072615936000000), (15610978372057859949391448554875243075257/20629104296249945969088555795018153984000000000), (298763227294234183033653558660403867787/550109447899998559175694821200484106240000000)],
    ![(399607960248779596900820016205139509717/286515337447915916237341052708585472000000000), (6090962645961675741417006452267634358909/5157276074062486492272138948754538496000000000), (1425434620916511047556295088925592325723/1473507449732138997792039699644153856000000000), (1727608384702414565466330357177122082773/2292122699583327329898728421668683776000000000)],
    ![(32856744965332864014537042727594378991/20465381246279708302667218050613248000000000), (3588928056755364040832528466547210962641/2578638037031243246136069474377269248000000000), (675094629233803105450984600745842209929/573030674895831832474682105417170944000000000), (3315924252938942572950604717781273551771/3438184049374990994848092632503025664000000000)]]

private theorem tensor412 (u v : ℝ) :
    eval poly101 ((66411/131072)+((33207/65536)-(66411/131072))*u) ((16383/32768)+((32767/65536)-(16383/32768))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern412 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern412, Fin.sum_univ_succ]
  <;> ring

private theorem cert412 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (33207/65536)) (hp : p ∈ Set.Icc (16383/32768) (32767/65536)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern412) (m := (1/1000000000000000))
    tensor412 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern412]

private def bern413 : Coeff :=
  ![![(298763227294234183033653558660403867787/550109447899998559175694821200484106240000000), (5142824199583853040541307655548626300223/11788059597857111982336317597153230848000000000), (54370422708417146367508559594355327123641/165032834369999567752708446360145231872000000000), (8164804428545828050294847553509498825521/36673963193333237278379654746698940416000000000)],
    ![(2547818712938620281234188729938975598759/3929353199285703994112105865717743616000000000), (29792817595118349495798243462162797150353/55010944789999855917569482120048410624000000000), (819986662193873462371043166489660963901/1886089535657137917173810815544516935680000000), (24053122849202218971670830730183178650331/73347926386666474556759309493397880832000000000)],
    ![(2764271887369373310215981474917377059669/3667396319333323727837965474669894041600000000), (8540943838983649388990047430822464301977/13202626749599965420216675708811618549760000000), (71305339491185449287903393227991018909181/132026267495999654202166757088116185497600000000), (1815920357057438138740573367990143528643/4191310079238084260386246256765593190400000000)]]

private theorem tensor413 (u v : ℝ) :
    eval poly101 ((66411/131072)+((132825/262144)-(66411/131072))*u) ((32767/65536)+((65535/131072)-(32767/65536))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern413 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern413, Fin.sum_univ_succ]
  <;> ring

private theorem cert413 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (132825/262144)) (hp : p ∈ Set.Icc (32767/65536) (65535/131072)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern413) (m := (1/1000000000000000))
    tensor413 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern413]

private def bern414 : Coeff :=
  ![![(39332086769280855375582570479151516758361638749/401212201190438607457458425966476608405504000000000), (88409988248806473092179588996967980752560067131/902727452678486866779281458424572368912384000000000), (336924678742282748461327333933089379173943/3443631945337245432965398629854478336000000000), (6847982251170210817231779753698599049/70060871283716744648547335405568000000000)],
    ![(157397420110486641313338125462981968189139414137/1604848804761754429829833703865906433622016000000000), (14151814493966980626581317672075254696064751639/144436392428557898684685033347931579025981440000000), (449430511881220815009939781335217659436633/4591509260449660577287198173139304448000000000), (5480797917276444694039729743569155313/56048697026973395718837868324454400000000)],
    ![(629866010906218740105334327050111842394466023397/6419395219047017719319334815463625734488064000000000), (202257596150905807949832482463190664036034785333/2063377034693684266924071904970451128942592000000000), (5395537754265057642472140059666409907377359/55098111125395926927446378077671653376000000000), (36554735788553695711388865905632749563/373657980179822638125585788829696000000000)]]

private theorem tensor414 (u v : ℝ) :
    eval poly107 ((66411/131072)+((265647/524288)-(66411/131072))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern414 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly107, bern414, Fin.sum_univ_succ]
  <;> ring

private theorem cert414 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly107 δ p := by
  apply positive_on_box_from_tensor (β := bern414) (m := (1/1000000000000000))
    tensor414 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern414]

private def bern415 : Coeff :=
  ![![(192428921608002522943782781014425733405913/586783411093331796454074475947183046656000000000), (570176994772183057543714461005559104377/2578638037031243246136069474377269248000000000), (1124282743973787942267722701142953/9836723468899701103729513070592000000000), (71238238403879969128878103/9529935776386274165784576000000000)],
    ![(111663458195414772799261729340021380803167/293391705546665898227037237973591523328000000000), (352977631381787106371067860985210932927/1289319018515621623068034737188634624000000000), (821110359254988807098061306633487/4918361734449850551864756535296000000000), (6016586317929439462591650053/100064325652055878740738048000000000)],
    ![(1815920357057438138740573367990143528643/4191310079238084260386246256765593190400000000), (42087541995540188918703836870496116597/128931901851562162306803473718863462400000000), (12001248455019420310688989759741/54648463716109450576275072614400000000), (45143371238041386821385103/400257302608223514962952192000000)]]

private theorem tensor415 (u v : ℝ) :
    eval poly101 ((265647/524288)+((132825/262144)-(265647/524288))*u) ((65535/131072)+((1/2)-(65535/131072))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern415 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern415, Fin.sum_univ_succ]
  <;> ring

private theorem cert415 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (132825/262144)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern415) (m := (1/1000000000000000))
    tensor415 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern415]

private def bern416 : Coeff :=
  ![![(2764271887369373310215981474917377059669/3667396319333323727837965474669894041600000000), (17408468953704967922857816288921804661/32232975462890540576700868429715865600000000), (26758382935507384911047300184823/81972695574164175864412608921600000000), (45143371238041386821385103/400257302608223514962952192000000)],
    ![(11814673659985128842300200507093913351861/13752736197499963979392370530012102656000000000), (1040177758385261976241313522295112031/1611648773144527028835043421485793280000000), (18960017792581336361847128335217/43913944057587951355935326208000000000), (2728044474084020148856940893/12508040706506984842592256000000000)],
    ![(3315924252938942572950604717781273551771/3438184049374990994848092632503025664000000000), (2520781963354557141792286944421380707/3357601610717764643406340461428736000000000), (41276141684166665719944828941401/76849402100778914872886820864000000000), (22476080196807503819742751/69489115036149915792179200000000)]]

private theorem tensor416 (u v : ℝ) :
    eval poly101 ((132825/262144)+((33207/65536)-(132825/262144))*u) ((32767/65536)+((1/2)-(32767/65536))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern416 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern416, Fin.sum_univ_succ]
  <;> ring

private theorem cert416 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (132825/262144) (33207/65536)) (hp : p ∈ Set.Icc (32767/65536) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern416) (m := (1/1000000000000000))
    tensor416 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern416]

private def bern417 : Coeff :=
  ![![(31026315522979970074393163249439508511/10744325154296846858900289476571955200000000), (426588146659172980417514335614894691/209850100669860290212896278839296000000000), (22633581725726649751697401551961/19212350525194728718221705216000000000), (22476080196807503819742751/69489115036149915792179200000000)],
    ![(5926145879675176793460877299246155719/1790720859049474476483381579428659200000000), (772582708138476036090926490579943619/314775151004790435319344418258944000000000), (243897617673655187375303523437/152478972422180386652553216000000000), (1164536785098834105292589041/1563505088313373105324032000000000)],
    ![(1431858975671563919882509697820629089/383725898367744530675010338448998400000000), (18108368671817526250922946089044361/6295503020095808706386888365178880000000), (1941843591290135536484281309597/960617526259736435911085260800000000), (182403344266170683065716191/156350508831337310532403200000000)]]

private theorem tensor417 (u v : ℝ) :
    eval poly101 ((33207/65536)+((16605/32768)-(33207/65536))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern417 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern417, Fin.sum_univ_succ]
  <;> ring

private theorem cert417 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33207/65536) (16605/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern417) (m := (1/1000000000000000))
    tensor417 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern417]

private def bern418 : Coeff :=
  ![![(234921094638544984192816652795403951/37306684563530718260070449571430400000000), (36092173477320191123080988685660077/7869378775119760882983610456473600000000), (276300103540891839621280234169/96061752625973643591108526080000000), (182403344266170683065716191/156350508831337310532403200000000)],
    ![(41630820118833286483761093620574801/5829169463051674728136007745536000000000), (6677661813571614302871418750364243/1229590433612462637966189133824000000000), (31022273805382741452815031667/8338693804337989895061504000000000), (49109793090428941896661057/24429767004896454770688000000000)],
    ![(1455163699713713995878219015248931/182161545720364835254250242048000000000), (241188586694429978586150491923849/38424701050389457436443410432000000000), (10708451404610052479816880553/2345257632470059657986048000000000), (103811076555106667507911/36353819947762581504000000000)]]

private theorem tensor418 (u v : ℝ) :
    eval poly101 ((16605/32768)+((519/1024)-(16605/32768))*u) ((4095/8192)+((1/2)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern418 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern418, Fin.sum_univ_succ]
  <;> ring

private theorem cert418 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16605/32768) (519/1024)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern418) (m := (1/1000000000000000))
    tensor418 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern418]

private def bern419 : Coeff :=
  ![![(8433043051599331581054211512031/50032162826027939370369024000000000), (470389165725106246953822821761/4169346902168994947530752000000000), (4220674364222106187242474697/73289301014689364312064000000000), (103811076555106667507911/36353819947762581504000000000)],
    ![(1641153059391718450264427745199/8338693804337989895061504000000000), (377049515704026657479166274493/2680294437108639609126912000000000), (207751133600045406270989521/2442976700489645477068800000000), (11415641481129989343160633/381715109451507105792000000000)],
    ![(567475692416619793489140937291/2501608141301396968518451200000000), (1597563263685722891176705146929/9381030529880238631944192000000000), (2093421932973123255913309673/18322325253672341078016000000000), (1600924539331343906691709/27265364960821936128000000000)]]

private theorem tensor419 (u v : ℝ) :
    eval poly101 ((519/1024)+((261/512)-(519/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern419 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern419, Fin.sum_univ_succ]
  <;> ring

private theorem cert419 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern419) (m := (1/1000000000000000))
    tensor419 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern419]

private def bern420 : Coeff :=
  ![![(9877469009690090589437771179/24817541084339255640064000000000), (663436359178608661627084635697/2345257632470059657986048000000000), (1555511287757791703264895449/9161162626836170539008000000000), (1600924539331343906691709/27265364960821936128000000000)],
    ![(10000887687190460109121607561/21715348448796848685056000000000), (100776971391982849204941456077/293157204058757457248256000000000), (174851470863911125350129493/763430218903014211584000000000), (2775471730603529087170657/23857194340719194112000000000)],
    ![(1439276160206956243850946229/2714418556099606085632000000000), (15088638311481700425730749049/36644650507344682156032000000000), (21138571183094018454841913/71571583022157582336000000000), (287870247489599750669/1590479622714612940800000)]]

private theorem tensor420 (u v : ℝ) :
    eval poly101 ((261/512)+((33/64)-(261/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern420 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern420, Fin.sum_univ_succ]
  <;> ring

private theorem cert420 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern420) (m := (1/1000000000000000))
    tensor420 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern420]

private def bern421 : Coeff :=
  ![![(635293430589437935367020069/190857554725753552896000000000), (45426285079481462666427963/21206394969528172544000000000), (4901840094095514136125019/4473223938884848896000000000), (287870247489599750669/1590479622714612940800000)],
    ![(66748319884835468548432991/15904796227146129408000000000), (412541565340355201546504293/143143166044315164672000000000), (6835299950426676119216453/3976199056786532352000000000), (1041169347891733352684359/1491074646294949632000000000)],
    ![(66486012589246639496254997/11928597170359597056000000000), (147093497562661158960688529/35785791511078791168000000000), (2515128934599539012477977/894644787776969779200000000), (19407322116948616838377/11649020674179294000000000)]]

private theorem tensor421 (u v : ℝ) :
    eval poly101 ((33/64)+((9/16)-(33/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern421 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern421, Fin.sum_univ_succ]
  <;> ring

private theorem cert421 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern421) (m := (1/1000000000000000))
    tensor421 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern421]

private def bern422 : Coeff :=
  ![![(3997556380542715960973/170408531005137100800000), (5944322820955205621745073/447322393888484889600000000), (6986335903316493412937309/1118305984721212224000000000), (19407322116948616838377/11649020674179294000000000)],
    ![(5331050405800945818604811/149107464629494963200000000), (2039564905017160349577317/93192165393434352000000000), (1083468309655041976189739/89464478777696977920000000), (32761939536826116531047/5916962882122816000000000)],
    ![(370005367256709332331391/6212811026228956800000000), (5631584298813906784277863/139788248090151528000000000), (819137827131170730366839/31064055131144784000000000), (154841941068188975221669/9319216539343435200000000)]]

private theorem tensor422 (u v : ℝ) :
    eval poly101 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern422 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly101, bern422, Fin.sum_univ_succ]
  <;> ring

private theorem cert422 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : 0 < eval poly101 δ p := by
  apply positive_on_box_from_tensor (β := bern422) (m := (1/1000000000000000))
    tensor422 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern422]

structure Window where
  branch : ImprovedBranch
  deltaLo : ℝ
  deltaHi : ℝ
  pLo : ℝ
def window : Fin 21 → Window :=
  ![⟨branchPcap, (3/8), (27/64), (7/16)⟩,
    ⟨branchC, (27/64), (57/128), (15/32)⟩,
    ⟨branchC, (57/128), (117/256), (31/64)⟩,
    ⟨branchPcap, (117/256), (15/32), (31/64)⟩,
    ⟨branchC, (117/256), (237/512), (63/128)⟩,
    ⟨branchC, (237/512), (15/32), (63/128)⟩,
    ⟨branchC, (237/512), (477/1024), (127/256)⟩,
    ⟨branchC, (237/512), (951/2048), (255/512)⟩,
    ⟨branchC, (237/512), (1899/4096), (511/1024)⟩,
    ⟨branchC, (1899/4096), (951/2048), (511/1024)⟩,
    ⟨branchC, (951/2048), (477/1024), (255/512)⟩,
    ⟨branchC, (477/1024), (15/32), (127/256)⟩,
    ⟨branchC, (15/32), (63/128), (15/32)⟩,
    ⟨branchP, (63/128), (129/256), (31/64)⟩,
    ⟨branchY, (129/256), (1035/2048), (255/512)⟩,
    ⟨branchY3, (1035/2048), (2073/4096), (511/1024)⟩,
    ⟨branchX8, (2073/4096), (4149/8192), (1023/2048)⟩,
    ⟨branchX8, (4149/8192), (8301/16384), (2047/4096)⟩,
    ⟨branchX8, (8301/16384), (66411/131072), (16383/32768)⟩,
    ⟨branchX8, (66411/131072), (265647/524288), (65535/131072)⟩,
    ⟨branchX8, (265647/524288), (1062591/2097152), (262143/524288)⟩]

def Window.Contains (w : Window) (δ p : ℝ) : Prop :=
  δ ∈ Set.Icc w.deltaLo w.deltaHi ∧ p ∈ Set.Icc w.pLo (1/2)

theorem window_bounds (i : Fin 21) :
    0 ≤ (window i).deltaLo ∧ (window i).deltaLo < (window i).deltaHi ∧
    (window i).deltaHi ≤ 3/4 ∧ 0 ≤ (window i).pLo ∧ (window i).pLo < 1/2 := by
  fin_cases i <;> norm_num [window]

private theorem admission000 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : Admitted branchPcap δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchPcap δ p (0 : Fin 15)
    rw [eq000]
    exact cert000 hδ hp

  · change 0 < admissionGuard branchPcap δ p (1 : Fin 15)
    rw [eq001]
    exact cert001 hδ hp

  · change 0 < admissionGuard branchPcap δ p (2 : Fin 15)
    rw [eq002]
    exact cert002 hδ hp

  · change 0 < admissionGuard branchPcap δ p (3 : Fin 15)
    rw [eq003]
    exact cert003 hδ hp

  · change 0 < admissionGuard branchPcap δ p (4 : Fin 15)
    rw [eq004]
    exact cert004 hδ hp

  · change 0 < admissionGuard branchPcap δ p (5 : Fin 15)
    rw [eq005]
    exact cert005 hδ hp

  · change 0 < admissionGuard branchPcap δ p (6 : Fin 15)
    rw [eq006]
    exact cert006 hδ hp

  · change 0 < admissionGuard branchPcap δ p (7 : Fin 15)
    rw [eq007]
    exact cert007 hδ hp

  · change 0 < admissionGuard branchPcap δ p (8 : Fin 15)
    rw [eq008]
    exact cert008 hδ hp

  · change 0 < admissionGuard branchPcap δ p (9 : Fin 15)
    rw [eq009]
    exact cert009 hδ hp

  · change 0 < admissionGuard branchPcap δ p (10 : Fin 15)
    rw [eq010]
    exact cert010 hδ hp

  · change 0 < admissionGuard branchPcap δ p (11 : Fin 15)
    rw [eq011]
    exact cert011 hδ hp

  · change 0 < admissionGuard branchPcap δ p (12 : Fin 15)
    rw [eq012]
    exact cert012 hδ hp

  · change 0 < admissionGuard branchPcap δ p (13 : Fin 15)
    rw [eq013]
    exact cert013 hδ hp

  · change 0 < admissionGuard branchPcap δ p (14 : Fin 15)
    rw [eq014]
    exact cert014 hδ hp

private theorem admission001 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert015 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert016 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert017 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert018 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert019 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert020 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert021 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert022 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert023 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert024 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert025 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert026 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert027 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert028 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert029 hδ hp

private theorem admission002 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert030 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert031 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert032 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert033 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert034 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert035 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert036 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert037 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert038 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert039 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert040 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert041 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert042 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert043 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert044 hδ hp

private theorem admission003 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Admitted branchPcap δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchPcap δ p (0 : Fin 15)
    rw [eq000]
    exact cert045 hδ hp

  · change 0 < admissionGuard branchPcap δ p (1 : Fin 15)
    rw [eq001]
    exact cert046 hδ hp

  · change 0 < admissionGuard branchPcap δ p (2 : Fin 15)
    rw [eq002]
    exact cert047 hδ hp

  · change 0 < admissionGuard branchPcap δ p (3 : Fin 15)
    rw [eq003]
    exact cert048 hδ hp

  · change 0 < admissionGuard branchPcap δ p (4 : Fin 15)
    rw [eq004]
    exact cert049 hδ hp

  · change 0 < admissionGuard branchPcap δ p (5 : Fin 15)
    rw [eq005]
    exact cert050 hδ hp

  · change 0 < admissionGuard branchPcap δ p (6 : Fin 15)
    rw [eq006]
    exact cert051 hδ hp

  · change 0 < admissionGuard branchPcap δ p (7 : Fin 15)
    rw [eq007]
    exact cert052 hδ hp

  · change 0 < admissionGuard branchPcap δ p (8 : Fin 15)
    rw [eq008]
    exact cert053 hδ hp

  · change 0 < admissionGuard branchPcap δ p (9 : Fin 15)
    rw [eq009]
    exact cert054 hδ hp

  · change 0 < admissionGuard branchPcap δ p (10 : Fin 15)
    rw [eq010]
    exact cert055 hδ hp

  · change 0 < admissionGuard branchPcap δ p (11 : Fin 15)
    rw [eq011]
    exact cert056 hδ hp

  · change 0 < admissionGuard branchPcap δ p (12 : Fin 15)
    rw [eq012]
    exact cert057 hδ hp

  · change 0 < admissionGuard branchPcap δ p (13 : Fin 15)
    rw [eq013]
    exact cert058 hδ hp

  · change 0 < admissionGuard branchPcap δ p (14 : Fin 15)
    rw [eq014]
    exact cert059 hδ hp

private theorem admission004 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert060 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert061 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert062 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert063 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert064 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert065 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert066 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert067 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert068 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert069 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert070 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert071 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert072 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert073 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert074 hδ hp

private theorem admission005 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert075 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert076 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert077 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert078 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert079 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert080 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert081 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert082 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert083 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert084 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert085 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert086 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert087 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert088 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert089 hδ hp

private theorem admission006 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert090 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert091 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert092 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert093 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert094 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert095 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert096 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert097 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert098 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert099 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert100 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert101 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert102 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert103 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert104 hδ hp

private theorem admission007 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert105 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert106 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert107 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert108 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert109 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert110 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert111 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert112 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert113 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert114 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert115 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert116 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert117 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert118 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert119 hδ hp

private theorem admission008 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert120 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert121 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert122 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert123 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert124 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert125 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert126 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert127 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert128 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert129 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert130 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert131 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert132 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert133 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert134 hδ hp

private theorem admission009 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert135 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert136 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert137 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert138 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert139 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert140 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert141 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert142 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert143 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert144 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert145 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert146 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert147 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert148 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert149 hδ hp

private theorem admission010 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert150 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert151 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert152 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert153 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert154 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert155 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert156 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert157 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert158 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert159 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert160 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert161 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert162 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert163 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert164 hδ hp

private theorem admission011 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert165 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert166 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert167 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert168 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert169 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert170 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert171 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert172 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert173 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert174 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert175 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert176 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert177 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert178 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert179 hδ hp

private theorem admission012 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Admitted branchC δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [eq015]
    exact cert180 hδ hp

  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [eq016]
    exact cert181 hδ hp

  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [eq017]
    exact cert182 hδ hp

  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [eq018]
    exact cert183 hδ hp

  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [eq019]
    exact cert184 hδ hp

  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [eq020]
    exact cert185 hδ hp

  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [eq021]
    exact cert186 hδ hp

  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [eq022]
    exact cert187 hδ hp

  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [eq023]
    exact cert188 hδ hp

  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [eq024]
    exact cert189 hδ hp

  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [eq025]
    exact cert190 hδ hp

  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [eq026]
    exact cert191 hδ hp

  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [eq027]
    exact cert192 hδ hp

  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [eq028]
    exact cert193 hδ hp

  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [eq029]
    exact cert194 hδ hp

private theorem admission013 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Admitted branchP δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchP δ p (0 : Fin 15)
    rw [eq030]
    exact cert195 hδ hp

  · change 0 < admissionGuard branchP δ p (1 : Fin 15)
    rw [eq031]
    exact cert196 hδ hp

  · change 0 < admissionGuard branchP δ p (2 : Fin 15)
    rw [eq032]
    exact cert197 hδ hp

  · change 0 < admissionGuard branchP δ p (3 : Fin 15)
    rw [eq033]
    exact cert198 hδ hp

  · change 0 < admissionGuard branchP δ p (4 : Fin 15)
    rw [eq034]
    exact cert199 hδ hp

  · change 0 < admissionGuard branchP δ p (5 : Fin 15)
    rw [eq035]
    exact cert200 hδ hp

  · change 0 < admissionGuard branchP δ p (6 : Fin 15)
    rw [eq036]
    exact cert201 hδ hp

  · change 0 < admissionGuard branchP δ p (7 : Fin 15)
    rw [eq037]
    exact cert202 hδ hp

  · change 0 < admissionGuard branchP δ p (8 : Fin 15)
    rw [eq038]
    exact cert203 hδ hp

  · change 0 < admissionGuard branchP δ p (9 : Fin 15)
    rw [eq039]
    exact cert204 hδ hp

  · change 0 < admissionGuard branchP δ p (10 : Fin 15)
    rw [eq040]
    exact cert205 hδ hp

  · change 0 < admissionGuard branchP δ p (11 : Fin 15)
    rw [eq041]
    exact cert206 hδ hp

  · change 0 < admissionGuard branchP δ p (12 : Fin 15)
    rw [eq042]
    exact cert207 hδ hp

  · change 0 < admissionGuard branchP δ p (13 : Fin 15)
    rw [eq043]
    exact cert208 hδ hp

  · change 0 < admissionGuard branchP δ p (14 : Fin 15)
    rw [eq044]
    exact cert209 hδ hp

private theorem admission014 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Admitted branchY δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchY δ p (0 : Fin 15)
    rw [eq045]
    exact cert210 hδ hp

  · change 0 < admissionGuard branchY δ p (1 : Fin 15)
    rw [eq046]
    exact cert211 hδ hp

  · change 0 < admissionGuard branchY δ p (2 : Fin 15)
    rw [eq047]
    exact cert212 hδ hp

  · change 0 < admissionGuard branchY δ p (3 : Fin 15)
    rw [eq048]
    exact cert213 hδ hp

  · change 0 < admissionGuard branchY δ p (4 : Fin 15)
    rw [eq049]
    exact cert214 hδ hp

  · change 0 < admissionGuard branchY δ p (5 : Fin 15)
    rw [eq050]
    exact cert215 hδ hp

  · change 0 < admissionGuard branchY δ p (6 : Fin 15)
    rw [eq051]
    exact cert216 hδ hp

  · change 0 < admissionGuard branchY δ p (7 : Fin 15)
    rw [eq052]
    exact cert217 hδ hp

  · change 0 < admissionGuard branchY δ p (8 : Fin 15)
    rw [eq053]
    exact cert218 hδ hp

  · change 0 < admissionGuard branchY δ p (9 : Fin 15)
    rw [eq054]
    exact cert219 hδ hp

  · change 0 < admissionGuard branchY δ p (10 : Fin 15)
    rw [eq055]
    exact cert220 hδ hp

  · change 0 < admissionGuard branchY δ p (11 : Fin 15)
    rw [eq056]
    exact cert221 hδ hp

  · change 0 < admissionGuard branchY δ p (12 : Fin 15)
    rw [eq057]
    exact cert222 hδ hp

  · change 0 < admissionGuard branchY δ p (13 : Fin 15)
    rw [eq058]
    exact cert223 hδ hp

  · change 0 < admissionGuard branchY δ p (14 : Fin 15)
    rw [eq059]
    exact cert224 hδ hp

private theorem admission015 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Admitted branchY3 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchY3 δ p (0 : Fin 15)
    rw [eq060]
    exact cert225 hδ hp

  · change 0 < admissionGuard branchY3 δ p (1 : Fin 15)
    rw [eq061]
    exact cert226 hδ hp

  · change 0 < admissionGuard branchY3 δ p (2 : Fin 15)
    rw [eq062]
    exact cert227 hδ hp

  · change 0 < admissionGuard branchY3 δ p (3 : Fin 15)
    rw [eq063]
    exact cert228 hδ hp

  · change 0 < admissionGuard branchY3 δ p (4 : Fin 15)
    rw [eq064]
    exact cert229 hδ hp

  · change 0 < admissionGuard branchY3 δ p (5 : Fin 15)
    rw [eq065]
    exact cert230 hδ hp

  · change 0 < admissionGuard branchY3 δ p (6 : Fin 15)
    rw [eq066]
    exact cert231 hδ hp

  · change 0 < admissionGuard branchY3 δ p (7 : Fin 15)
    rw [eq067]
    exact cert232 hδ hp

  · change 0 < admissionGuard branchY3 δ p (8 : Fin 15)
    rw [eq068]
    exact cert233 hδ hp

  · change 0 < admissionGuard branchY3 δ p (9 : Fin 15)
    rw [eq069]
    exact cert234 hδ hp

  · change 0 < admissionGuard branchY3 δ p (10 : Fin 15)
    rw [eq070]
    exact cert235 hδ hp

  · change 0 < admissionGuard branchY3 δ p (11 : Fin 15)
    rw [eq071]
    exact cert236 hδ hp

  · change 0 < admissionGuard branchY3 δ p (12 : Fin 15)
    rw [eq072]
    exact cert237 hδ hp

  · change 0 < admissionGuard branchY3 δ p (13 : Fin 15)
    rw [eq073]
    exact cert238 hδ hp

  · change 0 < admissionGuard branchY3 δ p (14 : Fin 15)
    rw [eq074]
    exact cert239 hδ hp

private theorem admission016 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : Admitted branchX8 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [eq075]
    exact cert240 hδ hp

  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [eq076]
    exact cert241 hδ hp

  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [eq077]
    exact cert242 hδ hp

  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [eq078]
    exact cert243 hδ hp

  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [eq079]
    exact cert244 hδ hp

  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [eq080]
    exact cert245 hδ hp

  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [eq081]
    exact cert246 hδ hp

  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [eq082]
    exact cert247 hδ hp

  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [eq083]
    exact cert248 hδ hp

  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [eq084]
    exact cert249 hδ hp

  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [eq085]
    exact cert250 hδ hp

  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [eq086]
    exact cert251 hδ hp

  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [eq087]
    exact cert252 hδ hp

  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [eq088]
    exact cert253 hδ hp

  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [eq089]
    exact cert254 hδ hp

private theorem admission017 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : Admitted branchX8 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [eq075]
    exact cert255 hδ hp

  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [eq076]
    exact cert256 hδ hp

  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [eq077]
    exact cert257 hδ hp

  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [eq078]
    exact cert258 hδ hp

  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [eq079]
    exact cert259 hδ hp

  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [eq080]
    exact cert260 hδ hp

  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [eq081]
    exact cert261 hδ hp

  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [eq082]
    exact cert262 hδ hp

  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [eq083]
    exact cert263 hδ hp

  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [eq084]
    exact cert264 hδ hp

  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [eq085]
    exact cert265 hδ hp

  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [eq086]
    exact cert266 hδ hp

  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [eq087]
    exact cert267 hδ hp

  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [eq088]
    exact cert268 hδ hp

  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [eq089]
    exact cert269 hδ hp

private theorem admission018 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : Admitted branchX8 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [eq075]
    exact cert270 hδ hp

  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [eq076]
    exact cert271 hδ hp

  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [eq077]
    exact cert272 hδ hp

  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [eq078]
    exact cert273 hδ hp

  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [eq079]
    exact cert274 hδ hp

  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [eq080]
    exact cert275 hδ hp

  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [eq081]
    exact cert276 hδ hp

  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [eq082]
    exact cert277 hδ hp

  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [eq083]
    exact cert278 hδ hp

  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [eq084]
    exact cert279 hδ hp

  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [eq085]
    exact cert280 hδ hp

  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [eq086]
    exact cert281 hδ hp

  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [eq087]
    exact cert282 hδ hp

  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [eq088]
    exact cert283 hδ hp

  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [eq089]
    exact cert284 hδ hp

private theorem admission019 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : Admitted branchX8 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [eq075]
    exact cert285 hδ hp

  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [eq076]
    exact cert286 hδ hp

  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [eq077]
    exact cert287 hδ hp

  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [eq078]
    exact cert288 hδ hp

  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [eq079]
    exact cert289 hδ hp

  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [eq080]
    exact cert290 hδ hp

  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [eq081]
    exact cert291 hδ hp

  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [eq082]
    exact cert292 hδ hp

  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [eq083]
    exact cert293 hδ hp

  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [eq084]
    exact cert294 hδ hp

  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [eq085]
    exact cert295 hδ hp

  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [eq086]
    exact cert296 hδ hp

  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [eq087]
    exact cert297 hδ hp

  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [eq088]
    exact cert298 hδ hp

  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [eq089]
    exact cert299 hδ hp

private theorem admission020 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : Admitted branchX8 δ p := by
  intro i
  fin_cases i

  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [eq075]
    exact cert300 hδ hp

  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [eq076]
    exact cert301 hδ hp

  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [eq077]
    exact cert302 hδ hp

  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [eq078]
    exact cert303 hδ hp

  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [eq079]
    exact cert304 hδ hp

  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [eq080]
    exact cert305 hδ hp

  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [eq081]
    exact cert306 hδ hp

  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [eq082]
    exact cert307 hδ hp

  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [eq083]
    exact cert308 hδ hp

  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [eq084]
    exact cert309 hδ hp

  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [eq085]
    exact cert310 hδ hp

  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [eq086]
    exact cert311 hδ hp

  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [eq087]
    exact cert312 hδ hp

  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [eq088]
    exact cert313 hδ hp

  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [eq089]
    exact cert314 hδ hp

theorem window_admitted (i : Fin 21) {δ p : ℝ}
    (hi : (window i).Contains δ p) : Admitted (window i).branch δ p := by
  fin_cases i

  · change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2) at hi
    change Admitted branchPcap δ p
    exact admission000 hi.1 hi.2

  · change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2) at hi
    change Admitted branchC δ p
    exact admission001 hi.1 hi.2

  · change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchC δ p
    exact admission002 hi.1 hi.2

  · change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchPcap δ p
    exact admission003 hi.1 hi.2

  · change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2) at hi
    change Admitted branchC δ p
    exact admission004 hi.1 hi.2

  · change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2) at hi
    change Admitted branchC δ p
    exact admission005 hi.1 hi.2

  · change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2) at hi
    change Admitted branchC δ p
    exact admission006 hi.1 hi.2

  · change δ ∈ Set.Icc (237/512) (951/2048) ∧ p ∈ Set.Icc (255/512) (1/2) at hi
    change Admitted branchC δ p
    exact admission007 hi.1 hi.2

  · change δ ∈ Set.Icc (237/512) (1899/4096) ∧ p ∈ Set.Icc (511/1024) (1/2) at hi
    change Admitted branchC δ p
    exact admission008 hi.1 hi.2

  · change δ ∈ Set.Icc (1899/4096) (951/2048) ∧ p ∈ Set.Icc (511/1024) (1/2) at hi
    change Admitted branchC δ p
    exact admission009 hi.1 hi.2

  · change δ ∈ Set.Icc (951/2048) (477/1024) ∧ p ∈ Set.Icc (255/512) (1/2) at hi
    change Admitted branchC δ p
    exact admission010 hi.1 hi.2

  · change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2) at hi
    change Admitted branchC δ p
    exact admission011 hi.1 hi.2

  · change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2) at hi
    change Admitted branchC δ p
    exact admission012 hi.1 hi.2

  · change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchP δ p
    exact admission013 hi.1 hi.2

  · change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2) at hi
    change Admitted branchY δ p
    exact admission014 hi.1 hi.2

  · change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2) at hi
    change Admitted branchY3 δ p
    exact admission015 hi.1 hi.2

  · change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission016 hi.1 hi.2

  · change δ ∈ Set.Icc (4149/8192) (8301/16384) ∧ p ∈ Set.Icc (2047/4096) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission017 hi.1 hi.2

  · change δ ∈ Set.Icc (8301/16384) (66411/131072) ∧ p ∈ Set.Icc (16383/32768) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission018 hi.1 hi.2

  · change δ ∈ Set.Icc (66411/131072) (265647/524288) ∧ p ∈ Set.Icc (65535/131072) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission019 hi.1 hi.2

  · change δ ∈ Set.Icc (265647/524288) (1062591/2097152) ∧ p ∈ Set.Icc (262143/524288) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission020 hi.1 hi.2

def Available (b : Branch) (δ p : ℝ) : Prop :=
  b = .old ∨ ∃ i : Fin 21, b = .improved (window i).branch ∧ (window i).Contains δ p
theorem available_used {b : Branch} {δ p : ℝ} (ha : Available b δ p) :
    b ∈ usedBranches := by
  rcases ha with rfl | ⟨i, rfl, _⟩
  · simp [usedBranches]
  · fin_cases i <;> norm_num [window, usedBranches, branchC, branchPcap, branchX8, branchP, branchY, branchY3]
theorem available_denominator {b : Branch} {δ p : ℝ}
    (ha : Available b δ p) (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < countJ b kappa δ p := by
  rcases ha with rfl | ⟨i, rfl, hi⟩
  · exact old_denominator_positive (by norm_num [kappa, theta]) hδ.1 hδ.2 hp.1 hp.2
  · exact (admitted_witness_ranges _ (window_admitted i hi)).2.1
def Certified (e : Edge) (δ p : ℝ) : Prop :=
  ∃ b : Branch, Available b δ p ∧ 0 < countJ b kappa δ p ∧ 0 < clearedEdge e b δ p

private theorem row000 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldsmall δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq090]
    exact cert315 hδ hp

private theorem row001 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldpeak δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq091]
    exact cert316 hδ hp

private theorem row002 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq092]
    exact cert317 hδ hp

private theorem row003 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : Certified .oldswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq092]
    exact cert318 hδ hp

private theorem row004 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .oldswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq092]
    exact cert319 hδ hp

private theorem row005 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .oldswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq092]
    exact cert320 hδ hp

private theorem row006 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq093]
    exact cert321 hδ hp

private theorem row007 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : Certified .newswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq093]
    exact cert322 hδ hp

private theorem row008 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .newswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq093]
    exact cert323 hδ hp

private theorem row009 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .newswitch δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq093]
    exact cert324 hδ hp

private theorem row010 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert325 hδ hp

private theorem row011 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert326 hδ hp

private theorem row012 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert327 hδ hp

private theorem row013 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert328 hδ hp

private theorem row014 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchPcap) δ p := by

    refine Or.inr ⟨0, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq095]
    exact cert329 hδ hp

private theorem row015 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert330 hδ hp

private theorem row016 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨1, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert331 hδ hp

private theorem row017 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert332 hδ hp

private theorem row018 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨2, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert333 hδ hp

private theorem row019 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) : Certified .newtop δ p := by
  have ha : Available (.improved branchPcap) δ p := by

    refine Or.inr ⟨3, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq095]
    exact cert334 hδ hp

private theorem row020 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨4, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert335 hδ hp

private theorem row021 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨5, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert336 hδ hp

private theorem row022 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨6, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert337 hδ hp

private theorem row023 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨7, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (951/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert338 hδ hp

private theorem row024 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (1899/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨8, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (1899/4096) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert339 hδ hp

private theorem row025 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1899/4096) (951/2048)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨9, rfl, ?_⟩
    change δ ∈ Set.Icc (1899/4096) (951/2048) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert340 hδ hp

private theorem row026 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨10, rfl, ?_⟩
    change δ ∈ Set.Icc (951/2048) (477/1024) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert341 hδ hp

private theorem row027 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨11, rfl, ?_⟩
    change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert342 hδ hp

private theorem row028 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert343 hδ hp

private theorem row029 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert344 hδ hp

private theorem row030 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨12, rfl, ?_⟩
    change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq096]
    exact cert345 hδ hp

private theorem row031 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert346 hδ hp

private theorem row032 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchP) δ p := by

    refine Or.inr ⟨13, rfl, ?_⟩
    change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchP), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq097]
    exact cert347 hδ hp

private theorem row033 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert348 hδ hp

private theorem row034 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert349 hδ hp

private theorem row035 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert350 hδ hp

private theorem row036 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchY) δ p := by

    refine Or.inr ⟨14, rfl, ?_⟩
    change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchY), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq098]
    exact cert351 hδ hp

private theorem row037 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert352 hδ hp

private theorem row038 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchY3) δ p := by

    refine Or.inr ⟨15, rfl, ?_⟩
    change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchY3), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq099]
    exact cert353 hδ hp

private theorem row039 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert354 hδ hp

private theorem row040 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨16, rfl, ?_⟩
    change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq100]
    exact cert355 hδ hp

private theorem row041 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert356 hδ hp

private theorem row042 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨17, rfl, ?_⟩
    change δ ∈ Set.Icc (4149/8192) (8301/16384) ∧ p ∈ Set.Icc (2047/4096) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq100]
    exact cert357 hδ hp

private theorem row043 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert358 hδ hp

private theorem row044 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (16605/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert359 hδ hp

private theorem row045 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (33207/65536)) (hp : p ∈ Set.Icc (8191/16384) (16383/32768)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert360 hδ hp

private theorem row046 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨18, rfl, ?_⟩
    change δ ∈ Set.Icc (8301/16384) (66411/131072) ∧ p ∈ Set.Icc (16383/32768) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq100]
    exact cert361 hδ hp

private theorem row047 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (33207/65536)) (hp : p ∈ Set.Icc (16383/32768) (32767/65536)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert362 hδ hp

private theorem row048 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (132825/262144)) (hp : p ∈ Set.Icc (32767/65536) (65535/131072)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert363 hδ hp

private theorem row049 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨19, rfl, ?_⟩
    change δ ∈ Set.Icc (66411/131072) (265647/524288) ∧ p ∈ Set.Icc (65535/131072) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq100]
    exact cert364 hδ hp

private theorem row050 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (132825/262144)) (hp : p ∈ Set.Icc (65535/131072) (131071/262144)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert365 hδ hp

private theorem row051 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (531297/1048576)) (hp : p ∈ Set.Icc (131071/262144) (262143/524288)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert366 hδ hp

private theorem row052 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (1062591/2097152)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨20, rfl, ?_⟩
    change δ ∈ Set.Icc (265647/524288) (1062591/2097152) ∧ p ∈ Set.Icc (262143/524288) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq100]
    exact cert367 hδ hp

private theorem row053 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1062591/2097152) (531297/1048576)) (hp : p ∈ Set.Icc (262143/524288) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert368 hδ hp

private theorem row054 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (531297/1048576) (132825/262144)) (hp : p ∈ Set.Icc (131071/262144) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert369 hδ hp

private theorem row055 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (132825/262144) (33207/65536)) (hp : p ∈ Set.Icc (32767/65536) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert370 hδ hp

private theorem row056 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33207/65536) (16605/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert371 hδ hp

private theorem row057 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16605/32768) (519/1024)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert372 hδ hp

private theorem row058 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert373 hδ hp

private theorem row059 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert374 hδ hp

private theorem row060 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert375 hδ hp

private theorem row061 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .newtop δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq094]
    exact cert376 hδ hp

private theorem row062 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert377 hδ hp

private theorem row063 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert378 hδ hp

private theorem row064 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert379 hδ hp

private theorem row065 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert380 hδ hp

private theorem row066 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchPcap) δ p := by

    refine Or.inr ⟨0, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq102]
    exact cert381 hδ hp

private theorem row067 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert382 hδ hp

private theorem row068 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨1, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert383 hδ hp

private theorem row069 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert384 hδ hp

private theorem row070 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨2, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert385 hδ hp

private theorem row071 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) : Certified .newkink δ p := by
  have ha : Available (.improved branchPcap) δ p := by

    refine Or.inr ⟨3, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq102]
    exact cert386 hδ hp

private theorem row072 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨4, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert387 hδ hp

private theorem row073 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨5, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert388 hδ hp

private theorem row074 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨6, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert389 hδ hp

private theorem row075 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (951/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨7, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (951/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert390 hδ hp

private theorem row076 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (951/2048) (477/1024)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨10, rfl, ?_⟩
    change δ ∈ Set.Icc (951/2048) (477/1024) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert391 hδ hp

private theorem row077 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨11, rfl, ?_⟩
    change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert392 hδ hp

private theorem row078 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert393 hδ hp

private theorem row079 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert394 hδ hp

private theorem row080 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by

    refine Or.inr ⟨12, rfl, ?_⟩
    change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq103]
    exact cert395 hδ hp

private theorem row081 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert396 hδ hp

private theorem row082 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchP) δ p := by

    refine Or.inr ⟨13, rfl, ?_⟩
    change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchP), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq104]
    exact cert397 hδ hp

private theorem row083 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert398 hδ hp

private theorem row084 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert399 hδ hp

private theorem row085 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert400 hδ hp

private theorem row086 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchY) δ p := by

    refine Or.inr ⟨14, rfl, ?_⟩
    change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchY), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq105]
    exact cert401 hδ hp

private theorem row087 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert402 hδ hp

private theorem row088 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchY3) δ p := by

    refine Or.inr ⟨15, rfl, ?_⟩
    change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchY3), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq106]
    exact cert403 hδ hp

private theorem row089 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert404 hδ hp

private theorem row090 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨16, rfl, ?_⟩
    change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq107]
    exact cert405 hδ hp

private theorem row091 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert406 hδ hp

private theorem row092 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨17, rfl, ?_⟩
    change δ ∈ Set.Icc (4149/8192) (8301/16384) ∧ p ∈ Set.Icc (2047/4096) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq107]
    exact cert407 hδ hp

private theorem row093 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert408 hδ hp

private theorem row094 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (16605/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert409 hδ hp

private theorem row095 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (33207/65536)) (hp : p ∈ Set.Icc (8191/16384) (16383/32768)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert410 hδ hp

private theorem row096 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (66411/131072)) (hp : p ∈ Set.Icc (16383/32768) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨18, rfl, ?_⟩
    change δ ∈ Set.Icc (8301/16384) (66411/131072) ∧ p ∈ Set.Icc (16383/32768) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq107]
    exact cert411 hδ hp

private theorem row097 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (33207/65536)) (hp : p ∈ Set.Icc (16383/32768) (32767/65536)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert412 hδ hp

private theorem row098 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (132825/262144)) (hp : p ∈ Set.Icc (32767/65536) (65535/131072)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert413 hδ hp

private theorem row099 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (66411/131072) (265647/524288)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by

    refine Or.inr ⟨19, rfl, ?_⟩
    change δ ∈ Set.Icc (66411/131072) (265647/524288) ∧ p ∈ Set.Icc (65535/131072) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩

  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq107]
    exact cert414 hδ hp

private theorem row100 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (265647/524288) (132825/262144)) (hp : p ∈ Set.Icc (65535/131072) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert415 hδ hp

private theorem row101 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (132825/262144) (33207/65536)) (hp : p ∈ Set.Icc (32767/65536) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert416 hδ hp

private theorem row102 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33207/65536) (16605/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert417 hδ hp

private theorem row103 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16605/32768) (519/1024)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert418 hδ hp

private theorem row104 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert419 hδ hp

private theorem row105 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert420 hδ hp

private theorem row106 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert421 hδ hp

private theorem row107 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) : Certified .newkink δ p := by
  have ha : Available .old δ p := by

    exact Or.inl rfl

  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [eq101]
    exact cert422 hδ hp

theorem cover_oldsmall {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldsmall δ p := by
  exact row000 hδ hp

theorem cover_oldpeak {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldpeak δ p := by
  exact row001 hδ hp

theorem cover_oldswitch {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .oldswitch δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row002 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row003 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        exact row004 hδ hp
      · intro δ p hδ hp
        exact row005 hδ hp

theorem cover_newswitch {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newswitch δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row006 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row007 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        exact row008 hδ hp
      · intro δ p hδ hp
        exact row009 hδ hp

theorem cover_newtop {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newtop δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row010 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row011 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        refine split_p (m := (3/8)) ?_ ?_ hδ hp
        · intro δ p hδ hp
          exact row012 hδ hp
        · intro δ p hδ hp
          refine split_delta (m := (15/32)) ?_ ?_ hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row013 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (27/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                exact row014 hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row015 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (57/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row016 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row017 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (117/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row018 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row019 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (237/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            exact row020 hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row021 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (477/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row022 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (951/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    refine split_p (m := (511/1024)) ?_ ?_ hδ hp
                                    · intro δ p hδ hp
                                      exact row023 hδ hp
                                    · intro δ p hδ hp
                                      refine split_delta (m := (1899/4096)) ?_ ?_ hδ hp
                                      · intro δ p hδ hp
                                        exact row024 hδ hp
                                      · intro δ p hδ hp
                                        exact row025 hδ hp
                                  · intro δ p hδ hp
                                    exact row026 hδ hp
                              · intro δ p hδ hp
                                exact row027 hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row028 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (33/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row029 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (63/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row030 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row031 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (129/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row032 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row033 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (261/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row034 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (519/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row035 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (1035/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    exact row036 hδ hp
                                  · intro δ p hδ hp
                                    refine split_p (m := (511/1024)) ?_ ?_ hδ hp
                                    · intro δ p hδ hp
                                      exact row037 hδ hp
                                    · intro δ p hδ hp
                                      refine split_delta (m := (2073/4096)) ?_ ?_ hδ hp
                                      · intro δ p hδ hp
                                        exact row038 hδ hp
                                      · intro δ p hδ hp
                                        refine split_p (m := (1023/2048)) ?_ ?_ hδ hp
                                        · intro δ p hδ hp
                                          exact row039 hδ hp
                                        · intro δ p hδ hp
                                          refine split_delta (m := (4149/8192)) ?_ ?_ hδ hp
                                          · intro δ p hδ hp
                                            exact row040 hδ hp
                                          · intro δ p hδ hp
                                            refine split_p (m := (2047/4096)) ?_ ?_ hδ hp
                                            · intro δ p hδ hp
                                              exact row041 hδ hp
                                            · intro δ p hδ hp
                                              refine split_delta (m := (8301/16384)) ?_ ?_ hδ hp
                                              · intro δ p hδ hp
                                                exact row042 hδ hp
                                              · intro δ p hδ hp
                                                refine split_p (m := (4095/8192)) ?_ ?_ hδ hp
                                                · intro δ p hδ hp
                                                  exact row043 hδ hp
                                                · intro δ p hδ hp
                                                  refine split_delta (m := (16605/32768)) ?_ ?_ hδ hp
                                                  · intro δ p hδ hp
                                                    refine split_p (m := (8191/16384)) ?_ ?_ hδ hp
                                                    · intro δ p hδ hp
                                                      exact row044 hδ hp
                                                    · intro δ p hδ hp
                                                      refine split_delta (m := (33207/65536)) ?_ ?_ hδ hp
                                                      · intro δ p hδ hp
                                                        refine split_p (m := (16383/32768)) ?_ ?_ hδ hp
                                                        · intro δ p hδ hp
                                                          exact row045 hδ hp
                                                        · intro δ p hδ hp
                                                          refine split_delta (m := (66411/131072)) ?_ ?_ hδ hp
                                                          · intro δ p hδ hp
                                                            exact row046 hδ hp
                                                          · intro δ p hδ hp
                                                            refine split_p (m := (32767/65536)) ?_ ?_ hδ hp
                                                            · intro δ p hδ hp
                                                              exact row047 hδ hp
                                                            · intro δ p hδ hp
                                                              refine split_delta (m := (132825/262144)) ?_ ?_ hδ hp
                                                              · intro δ p hδ hp
                                                                refine split_p (m := (65535/131072)) ?_ ?_ hδ hp
                                                                · intro δ p hδ hp
                                                                  exact row048 hδ hp
                                                                · intro δ p hδ hp
                                                                  refine split_delta (m := (265647/524288)) ?_ ?_ hδ hp
                                                                  · intro δ p hδ hp
                                                                    exact row049 hδ hp
                                                                  · intro δ p hδ hp
                                                                    refine split_p (m := (131071/262144)) ?_ ?_ hδ hp
                                                                    · intro δ p hδ hp
                                                                      exact row050 hδ hp
                                                                    · intro δ p hδ hp
                                                                      refine split_delta (m := (531297/1048576)) ?_ ?_ hδ hp
                                                                      · intro δ p hδ hp
                                                                        refine split_p (m := (262143/524288)) ?_ ?_ hδ hp
                                                                        · intro δ p hδ hp
                                                                          exact row051 hδ hp
                                                                        · intro δ p hδ hp
                                                                          refine split_delta (m := (1062591/2097152)) ?_ ?_ hδ hp
                                                                          · intro δ p hδ hp
                                                                            exact row052 hδ hp
                                                                          · intro δ p hδ hp
                                                                            exact row053 hδ hp
                                                                      · intro δ p hδ hp
                                                                        exact row054 hδ hp
                                                              · intro δ p hδ hp
                                                                exact row055 hδ hp
                                                      · intro δ p hδ hp
                                                        exact row056 hδ hp
                                                  · intro δ p hδ hp
                                                    exact row057 hδ hp
                              · intro δ p hδ hp
                                exact row058 hδ hp
                          · intro δ p hδ hp
                            exact row059 hδ hp
              · intro δ p hδ hp
                exact row060 hδ hp
      · intro δ p hδ hp
        exact row061 hδ hp

theorem cover_newkink {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified .newkink δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row062 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row063 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        refine split_p (m := (3/8)) ?_ ?_ hδ hp
        · intro δ p hδ hp
          exact row064 hδ hp
        · intro δ p hδ hp
          refine split_delta (m := (15/32)) ?_ ?_ hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row065 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (27/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                exact row066 hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row067 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (57/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row068 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row069 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (117/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row070 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row071 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (237/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            exact row072 hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row073 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (477/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row074 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (951/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    exact row075 hδ hp
                                  · intro δ p hδ hp
                                    exact row076 hδ hp
                              · intro δ p hδ hp
                                exact row077 hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row078 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (33/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row079 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (63/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row080 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row081 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (129/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row082 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row083 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (261/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row084 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (519/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row085 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (1035/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    exact row086 hδ hp
                                  · intro δ p hδ hp
                                    refine split_p (m := (511/1024)) ?_ ?_ hδ hp
                                    · intro δ p hδ hp
                                      exact row087 hδ hp
                                    · intro δ p hδ hp
                                      refine split_delta (m := (2073/4096)) ?_ ?_ hδ hp
                                      · intro δ p hδ hp
                                        exact row088 hδ hp
                                      · intro δ p hδ hp
                                        refine split_p (m := (1023/2048)) ?_ ?_ hδ hp
                                        · intro δ p hδ hp
                                          exact row089 hδ hp
                                        · intro δ p hδ hp
                                          refine split_delta (m := (4149/8192)) ?_ ?_ hδ hp
                                          · intro δ p hδ hp
                                            exact row090 hδ hp
                                          · intro δ p hδ hp
                                            refine split_p (m := (2047/4096)) ?_ ?_ hδ hp
                                            · intro δ p hδ hp
                                              exact row091 hδ hp
                                            · intro δ p hδ hp
                                              refine split_delta (m := (8301/16384)) ?_ ?_ hδ hp
                                              · intro δ p hδ hp
                                                exact row092 hδ hp
                                              · intro δ p hδ hp
                                                refine split_p (m := (4095/8192)) ?_ ?_ hδ hp
                                                · intro δ p hδ hp
                                                  exact row093 hδ hp
                                                · intro δ p hδ hp
                                                  refine split_delta (m := (16605/32768)) ?_ ?_ hδ hp
                                                  · intro δ p hδ hp
                                                    refine split_p (m := (8191/16384)) ?_ ?_ hδ hp
                                                    · intro δ p hδ hp
                                                      exact row094 hδ hp
                                                    · intro δ p hδ hp
                                                      refine split_delta (m := (33207/65536)) ?_ ?_ hδ hp
                                                      · intro δ p hδ hp
                                                        refine split_p (m := (16383/32768)) ?_ ?_ hδ hp
                                                        · intro δ p hδ hp
                                                          exact row095 hδ hp
                                                        · intro δ p hδ hp
                                                          refine split_delta (m := (66411/131072)) ?_ ?_ hδ hp
                                                          · intro δ p hδ hp
                                                            exact row096 hδ hp
                                                          · intro δ p hδ hp
                                                            refine split_p (m := (32767/65536)) ?_ ?_ hδ hp
                                                            · intro δ p hδ hp
                                                              exact row097 hδ hp
                                                            · intro δ p hδ hp
                                                              refine split_delta (m := (132825/262144)) ?_ ?_ hδ hp
                                                              · intro δ p hδ hp
                                                                refine split_p (m := (65535/131072)) ?_ ?_ hδ hp
                                                                · intro δ p hδ hp
                                                                  exact row098 hδ hp
                                                                · intro δ p hδ hp
                                                                  refine split_delta (m := (265647/524288)) ?_ ?_ hδ hp
                                                                  · intro δ p hδ hp
                                                                    exact row099 hδ hp
                                                                  · intro δ p hδ hp
                                                                    exact row100 hδ hp
                                                              · intro δ p hδ hp
                                                                exact row101 hδ hp
                                                      · intro δ p hδ hp
                                                        exact row102 hδ hp
                                                  · intro δ p hδ hp
                                                    exact row103 hδ hp
                              · intro δ p hδ hp
                                exact row104 hδ hp
                          · intro δ p hδ hp
                            exact row105 hδ hp
              · intro δ p hδ hp
                exact row106 hδ hp
      · intro δ p hδ hp
        exact row107 hδ hp

theorem complete_edge_certificate (e : Edge) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : Certified e δ p := by
  cases e
  · exact cover_oldsmall hδ hp
  · exact cover_oldpeak hδ hp
  · exact cover_oldswitch hδ hp
  · exact cover_newswitch hδ hp
  · exact cover_newtop hδ hp
  · exact cover_newkink hδ hp

#check complete_edge_certificate


/-- Admitted branches never disappear as p increases within the domain. -/
theorem available_upward {b : Branch} {δ p p' : ℝ}
    (ha : Available b δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) : Available b δ p' := by
  rcases ha with h | ⟨i, hb, hi⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hb, hi.1, hi.2.1.trans hpp, hp'⟩

/-- A concrete finite scalar envelope; its analytic counting interpretation
is a later theorem, not a premise of the finite certificate. -/
def windowValue (δ p : ℝ) (i : Option (Fin 21)) : ℝ := by
  classical
  exact match i with
    | none => countN .old kappa δ p/countJ .old kappa δ p
    | some j => if (window j).Contains δ p then
        countN (.improved (window j).branch) kappa δ p/
          countJ (.improved (window j).branch) kappa δ p
      else countN .old kappa δ p/countJ .old kappa δ p

def envelope (δ p : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (windowValue δ p)

theorem envelope_le_available {b : Branch} {δ p : ℝ}
    (ha : Available b δ p) : envelope δ p ≤ countN b kappa δ p/countJ b kappa δ p := by
  classical
  rcases ha with rfl | ⟨i, rfl, hi⟩
  · simpa only [envelope, windowValue] using
      (Finset.inf'_le (windowValue δ p) (Finset.mem_univ (none : Option (Fin 21))))
  · simpa only [envelope, windowValue, if_pos hi] using
      (Finset.inf'_le (windowValue δ p) (Finset.mem_univ (some i)))

/-- All six actual conductor edges, for every point of the complete rectangle,
with the SAME concrete count envelope and the original 10^-9 reserve. -/
theorem edge_return_bound (e : Edge) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    returnValue (edgeD e) (edgeC e) δ p (envelope δ p) ≤ theta-reserve := by
  obtain ⟨b, ha, hJ, hpoly⟩ := complete_edge_certificate e hδ hp
  exact cleared_return_sound b (edgeD_positive e).le hJ
    (envelope_le_available ha) hpoly.le

end
end Candidate.Feedback.FourthPower.ReturnFinite
