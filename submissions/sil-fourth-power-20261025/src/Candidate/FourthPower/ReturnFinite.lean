/- Copyright (c) 2026 Sil. Apache-2.0.
Generated exact certificate for the independently audited 86-box return.
The generator is untrusted: identities and inequalities below are Lean proofs. -/
import Candidate.FourthPower.ReturnCountData
import Candidate.FourthPower.ReturnBernstein

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Candidate.FourthPower.ReturnFinite
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
  ![![3, (-193/93), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly001 : Coeff :=
  ![![2, (-100/93), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly002 : Coeff :=
  ![![1, (-33333/62000), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly003 : Coeff :=
  ![![(5/2), (-965/558), 0, 0],
    ![-1, -1, (100/93), 0],
    ![0, 0, 0, 0]]

private def poly004 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-95333/62000), (33333/62000), 0],
    ![0, 0, 0, 0]]

private def poly005 : Coeff :=
  ![![(2499/4000), (-160769/372000), 0, 0],
    ![(-12499/10000), (99799/77500), (-16673/62000), 0],
    ![0, 0, 0, 0]]

private def poly006 : Coeff :=
  ![![(25/74), (-7042111/8258400), (328879141/768031200), 0],
    ![(69/37), (-27789889/6882000), (665954953/213342000), (-270200/320013)],
    ![0, 0, 0, 0]]

private def poly007 : Coeff :=
  ![![(5/2), (-685997/223200), (2144423/2306400), 0],
    ![-3, (685997/186000), (-2144423/1922000), 0],
    ![0, 0, 0, 0]]

private def poly008 : Coeff :=
  ![![(-2000003/4000000), (601008079/558000000), (-52497002249/103788000000), 0],
    ![(12000003/10000000), (-1222999957/465000000), (1457984507/930000000), (-192990157/864900000)],
    ![0, 0, 0, 0]]

private def poly009 : Coeff :=
  ![![(676592123/1000000000), (-184334154739/139500000000), (15316867913209/25947000000000), 0],
    ![(-3176592123/2500000000), (303218846237/116250000000), (-111825425929/77500000000), (36886827587/216225000000)],
    ![0, 0, 0, 0]]

private def poly010 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-39381727721/46500000000), (73751/223200), 0],
    ![(-1058864291/1250000000), (62873331979/38750000000), (-298393153/387500000), (34/465)]]

private def poly011 : Coeff :=
  ![![(471997/223200), (-33333/12400), (2144423/2306400), 0],
    ![(-157333/62000), (299999/93000), (-6433331/5766000), 0],
    ![0, 0, 0, 0]]

private def poly012 : Coeff :=
  ![![(41135459/2500000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly013 : Coeff :=
  ![![(16511247/625000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly014 : Coeff :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly015 : Coeff :=
  ![![3, -1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly016 : Coeff :=
  ![![2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly017 : Coeff :=
  ![![1, (-429999/5000000), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly018 : Coeff :=
  ![![(5/2), (-5/6), 0, 0],
    ![-1, -1, 0, 0],
    ![0, 0, 0, 0]]

private def poly019 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-5429999/5000000), (429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly020 : Coeff :=
  ![![(2499/4000), (-833/4000), 0, 0],
    ![(-12499/10000), (4180499/5000000), (-429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly021 : Coeff :=
  ![![(25/74), (-187270111/222000000), (54090037/222000000), 0],
    ![(69/37), (-372729889/185000000), (85909963/185000000), 0],
    ![0, 0, 0, 0]]

private def poly022 : Coeff :=
  ![![(5/2), (-6289997/6000000), (143333/2000000), 0],
    ![-3, (6289997/5000000), (-429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly023 : Coeff :=
  ![![(-2000003/4000000), (2855003/3000000), (-3140003/12000000), 0],
    ![(12000003/10000000), (-10999999/5000000), (8579993/10000000), (-429999/5000000)],
    ![0, 0, 0, 0]]

private def poly024 : Coeff :=
  ![![(159708626453968301/254867232000000000), (-396098175284392301/382300848000000000), (632487724114816301/2293805088000000000), 0],
    ![(-796876706453968301/637168080000000000), (2070379653546031699/955752120000000000), (-1607794480563487699/1911504240000000000), (429999/5000000)],
    ![0, 0, 0, 0]]

private def poly025 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-911364041/1500000000), (89999/6000000), 0],
    ![(-1058864291/1250000000), (1463635459/1250000000), (-769999/5000000), 0]]

private def poly026 : Coeff :=
  ![![(11289997/6000000), (-429999/1000000), (143333/2000000), 0],
    ![(-10429999/5000000), (429999/2500000), (429999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly027 : Coeff :=
  ![![(14291281181776163/955752120000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly028 : Coeff :=
  ![![(134997/2000000), (-44999/1000000), (44999/6000000), 0],
    ![(-134997/5000000), (-44999/2500000), (44999/5000000), 0],
    ![0, 0, 0, 0]]

private def poly029 : Coeff :=
  ![![3, (-357406588190789/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly030 : Coeff :=
  ![![2, (-200000000000000/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly031 : Coeff :=
  ![![1, (-96026151753982/157406588190789), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly032 : Coeff :=
  ![![(5/2), (-1787032940953945/944439529144734), 0, 0],
    ![-1, -1, (200000000000000/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly033 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-253432739944771/157406588190789), (96026151753982/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly034 : Coeff :=
  ![![(2499/4000), (-42531383994703891/89946621823308000), 0, 0],
    ![(-12499/10000), (2140968335558928289/1574065881907890000), (-46046151753982/157406588190789), 0],
    ![0, 0, 0, 0]]

private def poly035 : Coeff :=
  ![![(25/74), (-30696034001375405/34944262578355158), (432082113964751697913885615640/916742858216991497673784373277), 0],
    ![(69/37), (-25490331077093287/5824043763059193), (3379683497011762944526741651820/916742858216991497673784373277), (-142962635276315600000000000000/130963265459570213953397767611)],
    ![0, 0, 0, 0]]

private def poly036 : Coeff :=
  ![![(5/2), (-3227425217263675/944439529144734), (85800948188704138751016179495/74330502017593905216793327563), 0],
    ![-3, (645485043452735/157406588190789), (-34320379275481655500406471798/24776834005864635072264442521), 0],
    ![0, 0, 0, 0]]

private def poly037 : Coeff :=
  ![![(-2000003/4000000), (1061454913245557572367/944439529144734000000), (-7988295814922555593582291636592501/14158190860494077184151110012000000), 0],
    ![(12000003/10000000), (-2131472412692090809211/787032940953945000000), (2625223124357605809211/1574065881907890000000), (-90918175747409074359150346/393283079458168810670864167)],
    ![0, 0, 0, 0]]

private def poly038 : Coeff :=
  ![![(676592123/1000000000), (-328478648439246408555047/236109882286183500000000), (7065397492945799178275953590485469623/10618643145370557888113332509000000000), 0],
    ![(-3176592123/2500000000), (529488933763737030481651/196758235238486250000000), (-199983066593371926827217/131172156825657500000000), (577825790763416848419793114/3539547715123519296037777503)],
    ![0, 0, 0, 0]]

private def poly039 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-29762726186742153173657/33729983183740500000000), (5976875313084029/15740658819078900), 0],
    ![(-1058864291/1250000000), (333497384769864167784401/196758235238486250000000), (-34327878297738913/39351647047697250), (13600000000000/157406588190789)]]

private def poly040 : Coeff :=
  ![![(1007229079108810/472219764572367), (-480130758769910/157406588190789), (85800948188704138751016179495/74330502017593905216793327563), 0],
    ![(-410839328135560/157406588190789), (197350767835988/52468862730263), (-35571399064268944499593528202/24776834005864635072264442521), 0],
    ![0, 0, 0, 0]]

private def poly041 : Coeff :=
  ![![(3066544978453549211/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly042 : Coeff :=
  ![![3, (-28567/12567), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly043 : Coeff :=
  ![![2, (-16000/12567), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly044 : Coeff :=
  ![![1, (-4629970844602/7506835557525), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly045 : Coeff :=
  ![![(5/2), (-142835/75402), 0, 0],
    ![-1, -1, (16000/12567), 0],
    ![0, 0, 0, 0]]

private def poly046 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-12136806402127/7506835557525), (4629970844602/7506835557525), 0],
    ![0, 0, 0, 0]]

private def poly047 : Coeff :=
  ![![(2499/4000), (-23796311/50268000), 0, 0],
    ![(-12499/10000), (4104339278520601/3002734223010000), (-2241546296722/7506835557525), 0],
    ![0, 0, 0, 0]]

private def poly048 : Coeff :=
  ![![(25/74), (-96032667950951/111101166251370), (965451379767228046/2094312534421450185), 0],
    ![(69/37), (-407231354196649/92584305209475), (12940644247218810808/3490520890702416975), (-6399008000/5843391093)],
    ![0, 0, 0, 0]]

private def poly049 : Coeff :=
  ![![(5/2), (-10318089763777/3002734223010), (66132188558872667/56603041470850005), 0],
    ![-3, (10318089763777/2502278519175), (-132264377117745334/94338402451416675), 0],
    ![0, 0, 0, 0]]

private def poly050 : Coeff :=
  ![![(-159709008754816301/254867232000000000), (6255444172415637270667/4804374756816000000000), (-75688086449173511837048063/120753155137813344000000000), 0],
    ![(796877088754816301/637168080000000000), (-32393473011776753953333/12010936892040000000000), (38039173677569180281333/24021873784080000000000), (-154370052732511/789647445000000)],
    ![0, 0, 0, 0]]

private def poly051 : Coeff :=
  ![![(676592123/1000000000), (-206848861944693146341/150136711150500000000), (125770461720176163754633/191874716850339000000000), 0],
    ![(-3176592123/2500000000), (42290417924753/15708750000000), (-386086572208845516553/250227851917500000000), (29847459595623439/169380929422968750)],
    ![0, 0, 0, 0]]

private def poly052 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-399806280320455721591/450410133451500000000), (34695945850903/90082026690300), 0],
    ![(-1058864291/1250000000), (638710052676123046409/375341777876250000000), (-41261640844933279/46917722234531250), (1088/12567)]]

private def poly053 : Coeff :=
  ![![(3224343741476/1501367111505), (-4629970844602/1501367111505), (66132188558872667/56603041470850005), 0],
    ![(-19643641959652/7506835557525), (28374984089204/7506835557525), (-136004058829918666/94338402451416675), 0],
    ![0, 0, 0, 0]]

private def poly054 : Coeff :=
  ![![3, (-363653997694883/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly055 : Coeff :=
  ![![2, (-200000000000000/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly056 : Coeff :=
  ![![1, (-96739031091242/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly057 : Coeff :=
  ![![(5/2), (-1818269988474415/981923986169298), 0, 0],
    ![-1, -1, (200000000000000/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly058 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-260393028786125/163653997694883), (96739031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly059 : Coeff :=
  ![![(2499/4000), (-302923780079837539/654615990779532000), 0, 0],
    ![(-12499/10000), (2194958947621737383/1636539976948830000), (-46759031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly060 : Coeff :=
  ![![(25/74), (-31768527202658195/36331187488264026), (1374441027856423644630173320660/2972872036728361500809646589479), 0],
    ![(69/37), (-25975542301295257/6055197914710671), (3509524417053934509919733415028/990957345576120500269882196493), (-1018231193545672400000000000000/990957345576120500269882196493)],
    ![0, 0, 0, 0]]

private def poly061 : Coeff :=
  ![![(5/2), (-3269355454843045/981923986169298), (87948838473649332840123786715/80347892884550310832693151067), 0],
    ![-3, (653871090968609/163653997694883), (-35179535389459733136049514686/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly062 : Coeff :=
  ![![(-2000003/4000000), (1094493608457544084649/981923986169298000000), (-177181698507512589219732665460383689/321391571538201243330772604268000000), 0],
    ![(12000003/10000000), (-2200193910989715305117/818269988474415000000), (2684093955252560305117/1636539976948830000000), (-6087208300789139238389514686/26782630961516770277564383689)],
    ![0, 0, 0, 0]]

private def poly063 : Coeff :=
  ![![(676592123/1000000000), (-337841560864264245206609/245480996542324500000000), (17359940448292476462042642745203009083/26782630961516770277564383689000000000), 0],
    ![(-3176592123/2500000000), (546301562130802751597797/204567497118603750000000), (-204766387098838000532599/136378331412402500000000), (1458241355819684421291091562/8927543653838923425854794563)],
    ![0, 0, 0, 0]]

private def poly064 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-214252251890365257122953/245480996542324500000000), (18002639811997489/49096199308464900), 0],
    ![(-1058864291/1250000000), (342860819058687022877047/204567497118603750000000), (-34612304093623511/40913499423720750), (13600000000000/163653997694883)]]

private def poly065 : Coeff :=
  ![![(1043812721658730/490961993084649), (-483695155456210/163653997694883), (87948838473649332840123786715/80347892884550310832693151067), 0],
    ![(-424047026481008/163653997694883), (593478062182484/163653997694883), (-36246876586013666863950485314/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly066 : Coeff :=
  ![![(4506816185952085117/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly067 : Coeff :=
  ![![1, (-96664031091242/163653997694883), 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly068 : Coeff :=
  ![![0, 0, 0, 0],
    ![1, (-260318028786125/163653997694883), (96664031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly069 : Coeff :=
  ![![(2499/4000), (-302923780079837539/654615990779532000), 0, 0],
    ![(-12499/10000), (2194208947621737383/1636539976948830000), (-46684031091242/163653997694883), 0],
    ![0, 0, 0, 0]]

private def poly070 : Coeff :=
  ![![(25/74), (-31810152202658195/36331187488264026), (1376963877465431895442673320660/2972872036728361500809646589479), 0],
    ![(69/37), (-25967217301295257/6055197914710671), (3508515277210331209594733415028/990957345576120500269882196493), (-1018231193545672400000000000000/990957345576120500269882196493)],
    ![0, 0, 0, 0]]

private def poly071 : Coeff :=
  ![![(5/2), (-3268230454843045/981923986169298), (87880653349081542277623786715/80347892884550310832693151067), 0],
    ![-3, (653646090968609/163653997694883), (-35152261339632616911049514686/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly072 : Coeff :=
  ![![(-2000003/4000000), (1095618608457544084649/981923986169298000000), (-177454439005783751469732665460383689/321391571538201243330772604268000000), 0],
    ![(12000003/10000000), (-2200193910989715305117/818269988474415000000), (2681843955252560305117/1636539976948830000000), (-6059934250962023013389514686/26782630961516770277564383689)],
    ![0, 0, 0, 0]]

private def poly073 : Coeff :=
  ![![(676592123/1000000000), (-338122810864264245206609/245480996542324500000000), (17382668823148406649542642745203009083/26782630961516770277564383689000000000), 0],
    ![(-3176592123/2500000000), (546301562130802751597797/204567497118603750000000), (-204578887098838000532599/136378331412402500000000), (483050001959104115430363854/2975847884612974475284931521)],
    ![0, 0, 0, 0]]

private def poly074 : Coeff :=
  ![![0, 0, 0, 0],
    ![(676592873/1500000000), (-214158501890365257122953/245480996542324500000000), (17983889811997489/49096199308464900), 0],
    ![(-1058864291/1250000000), (342767069058687022877047/204567497118603750000000), (-34593554093623511/40913499423720750), (13600000000000/163653997694883)]]

private def poly075 : Coeff :=
  ![![(1043250221658730/490961993084649), (-483320155456210/163653997694883), (87880653349081542277623786715/80347892884550310832693151067), 0],
    ![(-423972026481008/163653997694883), (593328062182484/163653997694883), (-36244150635840783088950485314/26782630961516770277564383689), 0],
    ![0, 0, 0, 0]]

private def poly076 : Coeff :=
  ![![(4131816185952085117/500000000000000000000), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

private def poly077 : Coeff :=
  ![![(547624099/400000000), (-2326395340031939/2697793200000000), 0, 0],
    ![(-1791374099/1000000000), (-1214113266490817/6744483000000000), (2272239811842694373/3032536729152600000), 0],
    ![(1/2), (739834518943/1124080500000), (-306275127307/1124080500000), (-752399490772/5054227881921)]]

private def poly078 : Coeff :=
  ![![(246878819/400000000), (-1048780970601859/2697793200000000), 0, 0],
    ![(-2763106457/3000000000), (814258161799423/6744483000000000), (2504272700147795119/9097610187457800000), 0],
    ![(1/2), (-768975975319/3372241500000), (448198618079/3372241500000), (-1573686472316/15162683645763)]]

private def poly079 : Coeff :=
  ![![(523985310831939/5899264400000000), (-741991320683040271393/13262496152768400000000), 0, 0],
    ![(-13689309682495817/44244483000000000), (268792305629166806359/1745065283259000000000), (1080155220743194373/19893744229152600000), 0],
    ![(1/2), (-12924165663810882427/16578120190960500000), (8106821602358867573/16578120190960500000), (-1497180496924/11052080127307)]]

private def poly080 : Coeff :=
  ![![(12630249467/200000000000), (-53655333205980187/1348896600000000000), 0, 0],
    ![(-279685498809/1000000000000), (12057445616898327499350976859/75006999705959829000000000000), (201749499276692756185860019/5000466647063988600000000000), 0],
    ![(1/2), (-842193547582790681279234639/1041763884804997625000000000), (6303925601219548098083180057/12501166617659971500000000000), (-281670334784416587379/2083527769609995250000)]]

private def poly081 : Coeff :=
  ![![(12630249467/200000000000), (-12630249467/600000000000), 0, 0],
    ![(-279685498809/1000000000000), (144950903535784374835676411/2669097087120000000000000000), (74580451719226183441547863/889699029040000000000000000), 0],
    ![(1/2), (-1321421191385452585565356411/2224247572600000000000000000), (452267448324921259384956411/2224247572600000000000000000), 0]]

private def poly082 : Coeff :=
  ![![(12630249467/200000000000), (-2437638147131/55800000000000), 0, 0],
    ![(-279685498809/1000000000000), (3810682134711173736670351/19858082328172800000000000), (739417059862605404735783/33096803880288000000000000), 0],
    ![(1/2), (-23826293528808716280098617/27580669900240000000000000), (47807136549437006224184971/82742009700720000000000000), (-281670334784416587379/1723791868765000000000)]]

private def poly083 : Coeff :=
  ![![(12630249467/200000000000), (-360808336523789/7540200000000000), 0, 0],
    ![(-279685498809/1000000000000), (25285401014590057471/117477864750000000000), (272709506197167701424479/20964089433648150000000000), 0],
    ![(1/2), (-15199663718271577573531/16681856794500000000000), (5374257435915256413589/8340928397250000000000), (-281670334784416587379/1455839544003343750000)]]

private def poly084 : Coeff :=
  ![![(12630249467/200000000000), (-4593040710558215239377361/98192398616929800000000000), 0, 0],
    ![(-279685498809/1000000000000), (564062293951369518241755325298989651/2730052553393471311432543500000000000), (3278976737856827400326241489741791/182003503559564754095502900000000000), 0],
    ![(1/2), (-271739924026983481124393554879392143/303339172599274590159171500000000000), (141969562620853853766254920791409799/227504379449455942619378625000000000), (-112668133913766634951600/606678345198549180318343)]]

private def poly085 : Coeff :=
  ![![(12630249467/200000000000), (-4593040710558215239377361/98192398616929800000000000), 0, 0],
    ![(-279685498809/1000000000000), (563439492467109409381781106548989651/2730052553393471311432543500000000000), (3320496836807501324324522739741791/182003503559564754095502900000000000), 0],
    ![(1/2), (-271656883829082133276396992379392143/303339172599274590159171500000000000), (141907282472427842880257498916409799/227504379449455942619378625000000000), (-112668133913766634951600/606678345198549180318343)]]

private def poly086 : Coeff :=
  ![![(12630249467/200000000000), (-4514134369999001261559463/94443952914473400000000000), 0, 0],
    ![(-279685498809/1000000000000), (556944282269389181161656443700855283/2625834162709576941965860500000000000), (2793772716219089883318079676848103/175055610847305129464390700000000000), 0],
    ![(1/2), (-264665946088055918588699415317401469/291759351412175215773984500000000000), (5002064420124293055569012292746639/7814982627111836136803156250000000), (-112668133913766634951600/583518702824350431547969)]]

private def poly087 : Coeff :=
  ![![(349106899336217/5528097200000000), (-1483062314591042946937/37284157587747600000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (14983658525770468013789/93210393969369000000000), (56410248121460805727/1398155909540535000000), 0],
    ![(1/2), (-313975419002328513041/388376641539037500000), (65281828370409697303/129458880513012500000), (-315025808490428/2330259849234225)]]

private def poly088 : Coeff :=
  ![![(349106899336217/5528097200000000), (-349106899336217/16584291600000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (17454346853466429/321401000000000000), (10426536074639738977/124382187000000000000), 0],
    ![(1/2), (-61579337165130261023/103651822500000000000), (21076044774403061023/103651822500000000000), 0]]

private def poly089 : Coeff :=
  ![![(349106899336217/5528097200000000), (-67377631571889881/1542339118800000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (1479841865249162219/7711695594000000000), (103372642814839177/4627017356400000000), 0],
    ![(1/2), (-1110325314148832981/1285282599000000000), (247539189478538567/428427533000000000), (-78756452122607/481980974625000)]]

private def poly090 : Coeff :=
  ![![(349106899336217/5528097200000000), (-9972936793337711039/208414792537200000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (12460626104466745587/57892997927000000000), (101668475356002491/7815554720145000000), 0],
    ![(1/2), (-1978093590382911233/2170987422262500000), (1398818291122730029/2170987422262500000), (-315025808490428/1628240566696875)]]

private def poly091 : Coeff :=
  ![![(349106899336217/5528097200000000), (-126954119566480408440797477611/2714085619277667499882800000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (1401908396138107903171285960967/6785214048194168749707000000000), (1833643628078045097278534131/101778210722912531245605000000), 0],
    ![(1/2), (-25326617985488697759508983473/28271725200809036457112500000), (5880800705957209618189611759/9423908400269678819037500000), (-1260103233961712000000/6785214048194168749707)]]

private def poly092 : Coeff :=
  ![![(349106899336217/5528097200000000), (-126954119566480408440797477611/2714085619277667499882800000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (1400360498831985778171285960967/6785214048194168749707000000000), (1856862087669876972278534131/101778210722912531245605000000), 0],
    ![(1/2), (-25318878498958087134508983473/28271725200809036457112500000), (5878220877113672743189611759/9423908400269678819037500000), (-1260103233961712000000/6785214048194168749707)]]

private def poly093 : Coeff :=
  ![![(349106899336217/5528097200000000), (-124773105805622539015053505213/2610476758317161210072400000000), 0, 0],
    ![(-3865323483806217/13820243000000000), (1384217448676922205732336789761/6526191895792903025181000000000), (1562312621725522007846656573/97892878436893545377715000000), 0],
    ![(1/2), (-3523901622794046750650749337/3884638033210061324512500000), (5801609971663156838891719697/9064155410823476423862500000), (-180014747708816000000/932313127970414717883)]]

#check poly093

private theorem guard_C_00_eq (δ p : ℝ) :
    admissionGuard branchC δ p (0 : Fin 15) = eval poly000 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly000, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_01_eq (δ p : ℝ) :
    admissionGuard branchC δ p (1 : Fin 15) = eval poly001 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly001, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_02_eq (δ p : ℝ) :
    admissionGuard branchC δ p (2 : Fin 15) = eval poly002 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly002, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_03_eq (δ p : ℝ) :
    admissionGuard branchC δ p (3 : Fin 15) = eval poly003 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly003, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_04_eq (δ p : ℝ) :
    admissionGuard branchC δ p (4 : Fin 15) = eval poly004 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly004, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_05_eq (δ p : ℝ) :
    admissionGuard branchC δ p (5 : Fin 15) = eval poly005 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly005, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_06_eq (δ p : ℝ) :
    admissionGuard branchC δ p (6 : Fin 15) = eval poly006 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly006, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_07_eq (δ p : ℝ) :
    admissionGuard branchC δ p (7 : Fin 15) = eval poly007 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly007, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_08_eq (δ p : ℝ) :
    admissionGuard branchC δ p (8 : Fin 15) = eval poly008 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly008, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_09_eq (δ p : ℝ) :
    admissionGuard branchC δ p (9 : Fin 15) = eval poly009 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly009, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_10_eq (δ p : ℝ) :
    admissionGuard branchC δ p (10 : Fin 15) = eval poly010 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly010, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_11_eq (δ p : ℝ) :
    admissionGuard branchC δ p (11 : Fin 15) = eval poly011 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly011, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_12_eq (δ p : ℝ) :
    admissionGuard branchC δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_13_eq (δ p : ℝ) :
    admissionGuard branchC δ p (13 : Fin 15) = eval poly013 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly013, Fin.sum_univ_succ]
  <;> ring

private theorem guard_C_14_eq (δ p : ℝ) :
    admissionGuard branchC δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

#check guard_C_14_eq

private theorem guard_Pcap_00_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (0 : Fin 15) = eval poly015 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly015, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_01_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (1 : Fin 15) = eval poly016 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly016, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_02_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (2 : Fin 15) = eval poly017 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly017, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_03_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (3 : Fin 15) = eval poly018 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly018, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_04_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (4 : Fin 15) = eval poly019 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly019, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_05_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (5 : Fin 15) = eval poly020 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly020, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_06_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (6 : Fin 15) = eval poly021 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly021, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_07_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (7 : Fin 15) = eval poly022 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly022, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_08_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (8 : Fin 15) = eval poly023 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly023, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_09_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (9 : Fin 15) = eval poly024 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly024, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_10_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (10 : Fin 15) = eval poly025 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly025, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_11_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (11 : Fin 15) = eval poly026 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly026, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_12_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_13_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (13 : Fin 15) = eval poly027 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly027, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Pcap_14_eq (δ p : ℝ) :
    admissionGuard branchPcap δ p (14 : Fin 15) = eval poly028 δ p := by
  norm_num [admissionGuard, branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly028, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_00_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (0 : Fin 15) = eval poly029 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly029, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_01_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (1 : Fin 15) = eval poly030 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly030, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_02_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (2 : Fin 15) = eval poly031 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly031, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_03_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (3 : Fin 15) = eval poly032 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly032, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_04_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (4 : Fin 15) = eval poly033 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly033, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_05_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (5 : Fin 15) = eval poly034 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly034, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_06_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (6 : Fin 15) = eval poly035 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly035, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_07_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (7 : Fin 15) = eval poly036 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly036, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_08_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (8 : Fin 15) = eval poly037 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly037, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_09_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (9 : Fin 15) = eval poly038 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly038, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_10_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (10 : Fin 15) = eval poly039 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly039, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_11_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (11 : Fin 15) = eval poly040 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly040, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_12_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_13_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (13 : Fin 15) = eval poly041 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly041, Fin.sum_univ_succ]
  <;> ring

private theorem guard_X8_14_eq (δ p : ℝ) :
    admissionGuard branchX8 δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_00_eq (δ p : ℝ) :
    admissionGuard branchP δ p (0 : Fin 15) = eval poly042 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly042, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_01_eq (δ p : ℝ) :
    admissionGuard branchP δ p (1 : Fin 15) = eval poly043 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly043, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_02_eq (δ p : ℝ) :
    admissionGuard branchP δ p (2 : Fin 15) = eval poly044 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly044, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_03_eq (δ p : ℝ) :
    admissionGuard branchP δ p (3 : Fin 15) = eval poly045 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly045, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_04_eq (δ p : ℝ) :
    admissionGuard branchP δ p (4 : Fin 15) = eval poly046 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly046, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_05_eq (δ p : ℝ) :
    admissionGuard branchP δ p (5 : Fin 15) = eval poly047 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly047, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_06_eq (δ p : ℝ) :
    admissionGuard branchP δ p (6 : Fin 15) = eval poly048 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly048, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_07_eq (δ p : ℝ) :
    admissionGuard branchP δ p (7 : Fin 15) = eval poly049 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly049, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_08_eq (δ p : ℝ) :
    admissionGuard branchP δ p (8 : Fin 15) = eval poly050 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly050, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_09_eq (δ p : ℝ) :
    admissionGuard branchP δ p (9 : Fin 15) = eval poly051 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly051, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_10_eq (δ p : ℝ) :
    admissionGuard branchP δ p (10 : Fin 15) = eval poly052 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly052, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_11_eq (δ p : ℝ) :
    admissionGuard branchP δ p (11 : Fin 15) = eval poly053 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly053, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_12_eq (δ p : ℝ) :
    admissionGuard branchP δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_13_eq (δ p : ℝ) :
    admissionGuard branchP δ p (13 : Fin 15) = eval poly027 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly027, Fin.sum_univ_succ]
  <;> ring

private theorem guard_P_14_eq (δ p : ℝ) :
    admissionGuard branchP δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_00_eq (δ p : ℝ) :
    admissionGuard branchY δ p (0 : Fin 15) = eval poly054 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly054, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_01_eq (δ p : ℝ) :
    admissionGuard branchY δ p (1 : Fin 15) = eval poly055 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly055, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_02_eq (δ p : ℝ) :
    admissionGuard branchY δ p (2 : Fin 15) = eval poly056 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly056, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_03_eq (δ p : ℝ) :
    admissionGuard branchY δ p (3 : Fin 15) = eval poly057 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly057, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_04_eq (δ p : ℝ) :
    admissionGuard branchY δ p (4 : Fin 15) = eval poly058 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly058, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_05_eq (δ p : ℝ) :
    admissionGuard branchY δ p (5 : Fin 15) = eval poly059 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly059, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_06_eq (δ p : ℝ) :
    admissionGuard branchY δ p (6 : Fin 15) = eval poly060 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly060, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_07_eq (δ p : ℝ) :
    admissionGuard branchY δ p (7 : Fin 15) = eval poly061 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly061, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_08_eq (δ p : ℝ) :
    admissionGuard branchY δ p (8 : Fin 15) = eval poly062 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly062, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_09_eq (δ p : ℝ) :
    admissionGuard branchY δ p (9 : Fin 15) = eval poly063 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly063, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_10_eq (δ p : ℝ) :
    admissionGuard branchY δ p (10 : Fin 15) = eval poly064 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly064, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_11_eq (δ p : ℝ) :
    admissionGuard branchY δ p (11 : Fin 15) = eval poly065 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly065, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_12_eq (δ p : ℝ) :
    admissionGuard branchY δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_13_eq (δ p : ℝ) :
    admissionGuard branchY δ p (13 : Fin 15) = eval poly066 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly066, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y_14_eq (δ p : ℝ) :
    admissionGuard branchY δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_00_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (0 : Fin 15) = eval poly054 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly054, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_01_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (1 : Fin 15) = eval poly055 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly055, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_02_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (2 : Fin 15) = eval poly067 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly067, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_03_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (3 : Fin 15) = eval poly057 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly057, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_04_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (4 : Fin 15) = eval poly068 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly068, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_05_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (5 : Fin 15) = eval poly069 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly069, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_06_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (6 : Fin 15) = eval poly070 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly070, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_07_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (7 : Fin 15) = eval poly071 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly071, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_08_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (8 : Fin 15) = eval poly072 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly072, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_09_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (9 : Fin 15) = eval poly073 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly073, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_10_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (10 : Fin 15) = eval poly074 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly074, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_11_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (11 : Fin 15) = eval poly075 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly075, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_12_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (12 : Fin 15) = eval poly012 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly012, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_13_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (13 : Fin 15) = eval poly076 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly076, Fin.sum_univ_succ]
  <;> ring

private theorem guard_Y3_14_eq (δ p : ℝ) :
    admissionGuard branchY3 δ p (14 : Fin 15) = eval poly014 δ p := by
  norm_num [admissionGuard, branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    eval, poly014, Fin.sum_univ_succ]
  <;> ring

#check guard_Y3_14_eq

private theorem return_oldsmall_old_eq (δ p : ℝ) :
    clearedEdge .oldsmall .old δ p = eval poly077 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly077, Fin.sum_univ_succ]
  <;> ring

private theorem return_oldpeak_old_eq (δ p : ℝ) :
    clearedEdge .oldpeak .old δ p = eval poly078 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly078, Fin.sum_univ_succ]
  <;> ring

private theorem return_oldswitch_old_eq (δ p : ℝ) :
    clearedEdge .oldswitch .old δ p = eval poly079 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly079, Fin.sum_univ_succ]
  <;> ring

private theorem return_newswitch_old_eq (δ p : ℝ) :
    clearedEdge .newswitch .old δ p = eval poly079 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly079, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_old_eq (δ p : ℝ) :
    clearedEdge .newtop .old δ p = eval poly080 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly080, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_Pcap_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchPcap) δ p = eval poly081 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly081, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_C_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchC) δ p = eval poly082 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly082, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_P_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchP) δ p = eval poly083 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly083, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_Y_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchY) δ p = eval poly084 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly084, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_Y3_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchY3) δ p = eval poly085 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly085, Fin.sum_univ_succ]
  <;> ring

private theorem return_newtop_X8_eq (δ p : ℝ) :
    clearedEdge .newtop (.improved branchX8) δ p = eval poly086 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly086, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_old_eq (δ p : ℝ) :
    clearedEdge .newkink .old δ p = eval poly087 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly087, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_Pcap_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchPcap) δ p = eval poly088 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchPcap, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly088, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_C_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchC) δ p = eval poly089 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchC, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly089, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_P_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchP) δ p = eval poly090 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchP, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly090, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_Y_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchY) δ p = eval poly091 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchY, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly091, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_Y3_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchY3) δ p = eval poly092 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchY3, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly092, Fin.sum_univ_succ]
  <;> ring

private theorem return_newkink_X8_eq (δ p : ℝ) :
    clearedEdge .newkink (.improved branchX8) δ p = eval poly093 δ p := by
  norm_num [clearedEdge, clearedReturn, edgeD, edgeC, oldCapacity, newCapacity,
    countJ, countN, oldJ, oldN, oldD, oldC, returnValue,
    branchX8, V, A, D, Z, C0, U, J, N, T, RN, MN, DJ, APrime, DPrime, CPrime, UPrime, JPrime, lowerM, upperM, capWidth, ImprovedBranch.face, roleFace, countFace, physicalFace, xFace, yFace, sourceB, sourceSlope, physical_intercept_exact, physicalSlope, eta, mMinus, mPlus, mHigh, sMinus, incumbentCost, incumbent,
    reserve, sPhysical, d0, ds, dk, dplus, x, y, ell, kappa, theta, h,
    eval, poly093, Fin.sum_univ_succ]
  <;> ring

#check return_newkink_X8_eq

private def bern000 : Coeff :=
  ![![3, (17/6), (8/3), (5/2)],
    ![3, (17/6), (8/3), (5/2)],
    ![3, (17/6), (8/3), (5/2)]]

private theorem tensor000 (u v : ℝ) :
    eval poly015 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern000 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly015, bern000, Fin.sum_univ_succ]
  <;> ring

private theorem cert000 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly015 δ p := by
  apply positive_on_box_from_tensor (β := bern000) (m := (1/1000000000000000))
    tensor000 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern000]

#check cert000

private def bern001 : Coeff :=
  ![![2, 2, 2, 2],
    ![2, 2, 2, 2],
    ![2, 2, 2, 2]]

private theorem tensor001 (u v : ℝ) :
    eval poly016 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern001 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly016, bern001, Fin.sum_univ_succ]
  <;> ring

private theorem cert001 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly016 δ p := by
  apply positive_on_box_from_tensor (β := bern001) (m := (1/1000000000000000))
    tensor001 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern001]

private def bern002 : Coeff :=
  ![![1, (9856667/10000000), (4856667/5000000), (9570001/10000000)],
    ![1, (9856667/10000000), (4856667/5000000), (9570001/10000000)],
    ![1, (9856667/10000000), (4856667/5000000), (9570001/10000000)]]

private theorem tensor002 (u v : ℝ) :
    eval poly017 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern002 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly017, bern002, Fin.sum_univ_succ]
  <;> ring

private theorem cert002 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly017 δ p := by
  apply positive_on_box_from_tensor (β := bern002) (m := (1/1000000000000000))
    tensor002 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern002]

private def bern003 : Coeff :=
  ![![(5/2), (85/36), (20/9), (25/12)],
    ![(17/8), (277/144), (31/18), (73/48)],
    ![(7/4), (107/72), (11/9), (23/24)]]

private theorem tensor003 (u v : ℝ) :
    eval poly018 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern003 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly018, bern003, Fin.sum_univ_succ]
  <;> ring

private theorem cert003 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly018 δ p := by
  apply positive_on_box_from_tensor (β := bern003) (m := (1/1000000000000000))
    tensor003 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern003]

private def bern004 : Coeff :=
  ![![(116130009/512000000), (539790047/2560000000), (31210003/160000000), (28710003/160000000)],
    ![(1045170081/4096000000), (4858110423/20480000000), (280890027/1280000000), (258390027/1280000000)],
    ![(116130009/409600000), (539790047/2048000000), (31210003/128000000), (28710003/128000000)]]

private theorem tensor004 (u v : ℝ) :
    eval poly019 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern004 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern004, Fin.sum_univ_succ]
  <;> ring

private theorem cert004 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern004) (m := (1/1000000000000000))
    tensor004 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern004]

private def bern005 : Coeff :=
  ![![(97784391/512000000), (1492717859/7680000000), (94836241/480000000), (32098997/160000000)],
    ![(600171519/4096000000), (9302780731/61440000000), (599461169/3840000000), (205590973/1280000000)],
    ![(41806791/409600000), (666381859/6144000000), (44023241/384000000), (15438997/128000000)]]

private theorem tensor005 (u v : ℝ) :
    eval poly020 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern005 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern005, Fin.sum_univ_succ]
  <;> ring

private theorem cert005 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern005) (m := (1/1000000000000000))
    tensor005 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern005]

private def bern006 : Coeff :=
  ![![(47005201453/94720000000), (377376985751/852480000000), (3474605717/8880000000), (1215009593/3552000000)],
    ![(417764628617/757760000000), (3372325624939/6819840000000), (31253986513/71040000000), (11016887077/28416000000)],
    ![(45948764561/75776000000), (372563536387/681984000000), (3471112729/7104000000), (1231369741/2841600000)]]

private theorem tensor006 (u v : ℝ) :
    eval poly021 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern006 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern006, Fin.sum_univ_succ]
  <;> ring

private theorem cert006 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern006) (m := (1/1000000000000000))
    tensor006 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern006]

private def bern007 : Coeff :=
  ![![(5/2), (83710003/36000000), (155270011/72000000), (9570001/4800000)],
    ![(11/8), (920810033/720000000), (1707970121/1440000000), (105270011/96000000)],
    ![(1/4), (83710003/360000000), (155270011/720000000), (9570001/48000000)]]

private theorem tensor007 (u v : ℝ) :
    eval poly022 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern007 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly022, bern007, Fin.sum_univ_succ]
  <;> ring

private theorem cert007 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly022 δ p := by
  apply positive_on_box_from_tensor (β := bern007) (m := (1/1000000000000000))
    tensor007 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern007]

private def bern008 : Coeff :=
  ![![(17400761/4096000000), (62419681/5760000000), (67389061/3840000000), (2334979/96000000)],
    ![(893568529/32768000000), (2833658593/92160000000), (1060902869/30720000000), (29614841/768000000)],
    ![(164793097/3276800000), (466860229/9216000000), (6330773/122880000), (810997/15360000)]]

private theorem tensor008 (u v : ℝ) :
    eval poly023 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern008 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern008, Fin.sum_univ_succ]
  <;> ring

private theorem cert008 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern008) (m := (1/1000000000000000))
    tensor008 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern008]

private def bern009 : Coeff :=
  ![![(22787938473741071449/326230056960000000000), (175741900303507415731/2936070512640000000000), (54877638204180551999/1101026442240000000000), (1463397357396541973/36700881408000000000)],
    ![(114766066011299428061/2609840455680000000000), (870200587586647691039/23488564101120000000000), (263558296520398114891/8808211537920000000000), (6655295524389007657/293607051264000000000)],
    ![(4722862423267028453/260984045568000000000), (33446597274523605623/2348856410112000000000), (383023858292833973/38296571904000000000), (160341218960567953/29360705126400000000)]]

private theorem tensor009 (u v : ℝ) :
    eval poly024 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern009 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern009, Fin.sum_univ_succ]
  <;> ring

private theorem cert009 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern009) (m := (1/1000000000000000))
    tensor009 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern009]

private def bern010 : Coeff :=
  ![![(61640520269/2560000000000), (160855805801/7680000000000), (2269146657/128000000000), (1154172309/80000000000)],
    ![(40008815631/2048000000000), (6874440381/409600000000), (7128584451/512000000000), (701100729/64000000000)],
    ![(18377110993/1638400000000), (45377405629/4915200000000), (2911435617/409600000000), (248029149/51200000000)]]

private theorem tensor010 (u v : ℝ) :
    eval poly025 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((1/2)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern010 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern010, Fin.sum_univ_succ]
  <;> ring

private theorem cert010 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern010) (m := (1/1000000000000000))
    tensor010 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern010]

private def bern011 : Coeff :=
  ![![(11289997/6000000), (5429999/3000000), (13954443/8000000), (40429999/24000000)],
    ![(131929949/120000000), (62309983/60000000), (157798863/160000000), (452469971/480000000)],
    ![(19029979/60000000), (8009993/30000000), (18254433/80000000), (48169981/240000000)]]

private theorem tensor011 (u v : ℝ) :
    eval poly026 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern011 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly026, bern011, Fin.sum_univ_succ]
  <;> ring

private theorem cert011 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly026 δ p := by
  apply positive_on_box_from_tensor (β := bern011) (m := (1/1000000000000000))
    tensor011 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern011]

private def bern012 : Coeff :=
  ![![(41135459/2500000000), (41135459/2500000000), (41135459/2500000000), (41135459/2500000000)],
    ![(41135459/2500000000), (41135459/2500000000), (41135459/2500000000), (41135459/2500000000)],
    ![(41135459/2500000000), (41135459/2500000000), (41135459/2500000000), (41135459/2500000000)]]

private theorem tensor012 (u v : ℝ) :
    eval poly012 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern012 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly012, bern012, Fin.sum_univ_succ]
  <;> ring

private theorem cert012 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly012 δ p := by
  apply positive_on_box_from_tensor (β := bern012) (m := (1/1000000000000000))
    tensor012 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern012]

private def bern013 : Coeff :=
  ![![(14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000)],
    ![(14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000)],
    ![(14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000), (14291281181776163/955752120000000000)]]

private theorem tensor013 (u v : ℝ) :
    eval poly027 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern013 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly027, bern013, Fin.sum_univ_succ]
  <;> ring

private theorem cert013 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly027 δ p := by
  apply positive_on_box_from_tensor (β := bern013) (m := (1/1000000000000000))
    tensor013 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern013]

private def bern014 : Coeff :=
  ![![(134997/2000000), (44999/750000), (764983/14400000), (44999/960000)],
    ![(2294949/40000000), (584987/12000000), (59083687/1440000000), (3284927/96000000)],
    ![(944979/20000000), (44999/1200000), (20834537/720000000), (1034977/48000000)]]

private theorem tensor014 (u v : ℝ) :
    eval poly028 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern014 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly028, bern014, Fin.sum_univ_succ]
  <;> ring

private theorem cert014 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly028 δ p := by
  apply positive_on_box_from_tensor (β := bern014) (m := (1/1000000000000000))
    tensor014 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern014]

private def bern015 : Coeff :=
  ![![(2078730189/10240000000), (1997870191/10240000000), (29960003/160000000), (28710003/160000000)],
    ![(35338413213/163840000000), (33963793247/163840000000), (509320051/2560000000), (488070051/2560000000)],
    ![(18708571701/81920000000), (17980831719/81920000000), (269640027/1280000000), (258390027/1280000000)]]

private theorem tensor015 (u v : ℝ) :
    eval poly019 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern015 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern015, Fin.sum_univ_succ]
  <;> ring

private theorem cert015 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern015) (m := (1/1000000000000000))
    tensor015 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern015]

private def bern016 : Coeff :=
  ![![(2006301811/10240000000), (6068229427/30720000000), (11945827/60000000), (32098997/160000000)],
    ![(28642650787/163840000000), (86899740259/491520000000), (343162493/1920000000), (462382949/2560000000)],
    ![(12592236299/81920000000), (38353904843/245760000000), (152029261/960000000), (205590973/1280000000)]]

private theorem tensor016 (u v : ℝ) :
    eval poly020 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern016 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern016, Fin.sum_univ_succ]
  <;> ring

private theorem cert016 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern016) (m := (1/1000000000000000))
    tensor016 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern016]

private def bern017 : Coeff :=
  ![![(158192584397/378880000000), (267220717147/681984000000), (13024259399/35520000000), (1215009593/3552000000)],
    ![(2683432872209/6062080000000), (4541194523959/10911744000000), (221786483603/568320000000), (20736963821/56832000000)],
    ![(1417892197033/3031040000000), (2403428786783/5455872000000), (117592408411/284160000000), (11016887077/28416000000)]]

private theorem tensor017 (u v : ℝ) :
    eval poly021 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern017 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern017, Fin.sum_univ_succ]
  <;> ring

private theorem cert017 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern017) (m := (1/1000000000000000))
    tensor017 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern017]

private def bern018 : Coeff :=
  ![![(465833513/32768000000), (101171401/5760000000), (160788221/7680000000), (2334979/96000000)],
    ![(12301261529/524288000000), (19227826391/737280000000), (3531802277/122880000000), (48294673/1536000000)],
    ![(342983737/10485760000), (12752856727/368640000000), (2245496509/61440000000), (29614841/768000000)]]

private theorem tensor018 (u v : ℝ) :
    eval poly023 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern018 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern018, Fin.sum_univ_succ]
  <;> ring

private theorem cert018 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern018) (m := (1/1000000000000000))
    tensor018 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern018]

private def bern019 : Coeff :=
  ![![(644205020699679832033/11744282050560000000000), (1756483277952581152697/35232846151680000000000), (98779558926076811189/2202052884480000000000), (1463397357396541973/36700881408000000000)],
    ![(8295833351085410384941/187908512808960000000000), (22476671656560323970629/563725538426880000000000), (1253453633660682834113/35232846151680000000000), (18362474383561343441/587214102528000000000)],
    ![(3142193185487971728677/93954256404480000000000), (8424805432939674749053/281862769213440000000000), (463217162252068344601/17616423075840000000000), (6655295524389007657/293607051264000000000)]]

private theorem tensor019 (u v : ℝ) :
    eval poly024 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern019 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern019, Fin.sum_univ_succ]
  <;> ring

private theorem cert019 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern019) (m := (1/1000000000000000))
    tensor019 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern019]

private def bern020 : Coeff :=
  ![![(197789319689/10240000000000), (108790789261/6144000000000), (20579111757/1280000000000), (1154172309/80000000000)],
    ![(1418916423971/81920000000000), (776671459567/49152000000000), (146003398443/10240000000000), (8122192881/640000000000)],
    ![(9519560736669/655360000000000), (344535489471/26214400000000), (961153119657/81920000000000), (52711514829/5120000000000)]]

private theorem tensor020 (u v : ℝ) :
    eval poly025 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern020 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern020, Fin.sum_univ_succ]
  <;> ring

private theorem cert020 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern020) (m := (1/1000000000000000))
    tensor020 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern020]

private def bern021 : Coeff :=
  ![![(18708571701/81920000000), (17980831719/81920000000), (269640027/1280000000), (258390027/1280000000)],
    ![(39495873591/163840000000), (37959533629/163840000000), (569240057/2560000000), (545490057/2560000000)],
    ![(2078730189/8192000000), (1997870191/8192000000), (29960003/128000000), (28710003/128000000)]]

private theorem tensor021 (u v : ℝ) :
    eval poly019 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern021 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly019, bern021, Fin.sum_univ_succ]
  <;> ring

private theorem cert021 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly019 δ p := by
  apply positive_on_box_from_tensor (β := bern021) (m := (1/1000000000000000))
    tensor021 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern021]

private def bern022 : Coeff :=
  ![![(12592236299/81920000000), (38353904843/245760000000), (152029261/960000000), (205590973/1280000000)],
    ![(21726294409/163840000000), (66515879113/491520000000), (264954551/1920000000), (359980943/2560000000)],
    ![(913405811/8192000000), (2816197427/24576000000), (11292529/96000000), (15438997/128000000)]]

private theorem tensor022 (u v : ℝ) :
    eval poly020 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern022 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly020, bern022, Fin.sum_univ_succ]
  <;> ring

private theorem cert022 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly020 δ p := by
  apply positive_on_box_from_tensor (β := bern022) (m := (1/1000000000000000))
    tensor022 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern022]

private def bern023 : Coeff :=
  ![![(1417892197033/3031040000000), (2403428786783/5455872000000), (117592408411/284160000000), (11016887077/28416000000)],
    ![(2988135915923/6062080000000), (5072520623173/10911744000000), (248583150041/568320000000), (23330584487/56832000000)],
    ![(157024371889/303104000000), (266909183639/545587200000), (13099074163/28416000000), (1231369741/2841600000)]]

private theorem tensor023 (u v : ℝ) :
    eval poly021 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern023 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly021, bern023, Fin.sum_univ_succ]
  <;> ring

private theorem cert023 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly021 δ p := by
  apply positive_on_box_from_tensor (β := bern023) (m := (1/1000000000000000))
    tensor023 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern023]

private def bern024 : Coeff :=
  ![![(342983737/10485760000), (12752856727/368640000000), (2245496509/61440000000), (29614841/768000000)],
    ![(21997112171/524288000000), (31783600517/737280000000), (5450183759/122880000000), (70164691/1536000000)],
    ![(6711259373/131072000000), (1903074379/36864000000), (12818749/245760000), (810997/15360000)]]

private theorem tensor024 (u v : ℝ) :
    eval poly023 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern024 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly023, bern024, Fin.sum_univ_succ]
  <;> ring

private theorem cert024 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly023 δ p := by
  apply positive_on_box_from_tensor (β := bern024) (m := (1/1000000000000000))
    tensor024 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern024]

private def bern025 : Coeff :=
  ![![(3142193185487971728677/93954256404480000000000), (8424805432939674749053/281862769213440000000000), (463217162252068344601/17616423075840000000000), (6655295524389007657/293607051264000000000)],
    ![(4272939390866476529767/187908512808960000000000), (11222550075198375025583/563725538426880000000000), (599415015347590544291/35232846151680000000000), (8258707713994687187/587214102528000000000)],
    ![(113074620537850480109/9395425640448000000000), (279774464225870027653/28186276921344000000000), (13619785309552219969/1761642307584000000000), (160341218960567953/29360705126400000000)]]

private theorem tensor025 (u v : ℝ) :
    eval poly024 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern025 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly024, bern025, Fin.sum_univ_succ]
  <;> ring

private theorem cert025 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly024 δ p := by
  apply positive_on_box_from_tensor (β := bern025) (m := (1/1000000000000000))
    tensor025 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern025]

private def bern026 : Coeff :=
  ![![(9519560736669/655360000000000), (344535489471/26214400000000), (961153119657/81920000000000), (52711514829/5120000000000)],
    ![(768779008157/65536000000000), (2061346503797/196608000000000), (75427905177/8192000000000), (4044548661/512000000000)],
    ![(53314338397/6553600000000), (139062658741/19660800000000), (4895668809/819200000000), (248029149/51200000000)]]

private theorem tensor026 (u v : ℝ) :
    eval poly025 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern026 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly025, bern026, Fin.sum_univ_succ]
  <;> ring

private theorem cert026 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly025 δ p := by
  apply positive_on_box_from_tensor (β := bern026) (m := (1/1000000000000000))
    tensor026 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern026]

private def bern027 : Coeff :=
  ![![3, (1481/558), (644/279), (365/186)],
    ![3, (1481/558), (644/279), (365/186)],
    ![3, (1481/558), (644/279), (365/186)]]

private theorem tensor027 (u v : ℝ) :
    eval poly000 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern027 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly000, bern027, Fin.sum_univ_succ]
  <;> ring

private theorem cert027 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly000 δ p := by
  apply positive_on_box_from_tensor (β := bern027) (m := (1/1000000000000000))
    tensor027 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern027]

private def bern028 : Coeff :=
  ![![2, (508/279), (458/279), (136/93)],
    ![2, (508/279), (458/279), (136/93)],
    ![2, (508/279), (458/279), (136/93)]]

private theorem tensor028 (u v : ℝ) :
    eval poly001 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern028 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly001, bern028, Fin.sum_univ_succ]
  <;> ring

private theorem cert028 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly001 δ p := by
  apply positive_on_box_from_tensor (β := bern028) (m := (1/1000000000000000))
    tensor028 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern028]

private def bern029 : Coeff :=
  ![![1, (112889/124000), (50889/62000), (90667/124000)],
    ![1, (112889/124000), (50889/62000), (90667/124000)],
    ![1, (112889/124000), (50889/62000), (90667/124000)]]

private theorem tensor029 (u v : ℝ) :
    eval poly002 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern029 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly002, bern029, Fin.sum_univ_succ]
  <;> ring

private theorem cert029 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly002 δ p := by
  apply positive_on_box_from_tensor (β := bern029) (m := (1/1000000000000000))
    tensor029 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern029]

private def bern030 : Coeff :=
  ![![(5/2), (7405/3348), (1610/837), (1825/1116)],
    ![(17/8), (23761/13392), (9757/6696), (169/144)],
    ![(7/4), (8951/6696), (107/108), (1589/2232)]]

private theorem tensor030 (u v : ℝ) :
    eval poly003 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern030 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly003, bern030, Fin.sum_univ_succ]
  <;> ring

private theorem cert030 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly003 δ p := by
  apply positive_on_box_from_tensor (β := bern030) (m := (1/1000000000000000))
    tensor030 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern030]

private def bern031 : Coeff :=
  ![![(136231659/812646400), (662702301/4063232000), (2517759/15872000), (2448009/15872000)],
    ![(560063487/3250585600), (2724442793/16252928000), (10350787/63488000), (10064037/63488000)],
    ![(287600169/1625292800), (1399038191/8126464000), (5315269/31744000), (5168019/31744000)]]

private theorem tensor031 (u v : ℝ) :
    eval poly004 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern031 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern031, Fin.sum_univ_succ]
  <;> ring

private theorem cert031 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern031) (m := (1/1000000000000000))
    tensor031 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern031]

private def bern032 : Coeff :=
  ![![(2531229433/20316160000), (22790066699/182845440000), (712259873/5713920000), (29671631/238080000)],
    ![(9453183829/81264640000), (85207121567/731381760000), (2665869629/22855680000), (111172883/952320000)],
    ![(4390724963/40632320000), (39626988169/365690880000), (1241349883/11427840000), (51829621/476160000)]]

private theorem tensor032 (u v : ℝ) :
    eval poly005 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern032 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern032, Fin.sum_univ_succ]
  <;> ring

private theorem cert032 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern032) (m := (1/1000000000000000))
    tensor032 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern032]

private def bern033 : Coeff :=
  ![![(25/74), (9697889/49550400), (822853849/9216374400), (11385299/614424960)],
    ![(307/296), (636884779/991008000), (70302008339/184327488000), (2627094289/12288499200)],
    ![(257/148), (17416319/15984000), (62073469849/92163744000), (2513241299/6144249600)]]

private theorem tensor033 (u v : ℝ) :
    eval poly006 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern033 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly006, bern033, Fin.sum_univ_succ]
  <;> ring

private theorem cert033 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly006 δ p := by
  apply positive_on_box_from_tensor (β := bern033) (m := (1/1000000000000000))
    tensor033 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern033]

private def bern034 : Coeff :=
  ![![(5/2), (2662003/1339200), (128945641/83030400), (6618691/5535360)],
    ![(11/8), (29282033/26784000), (1418402051/1660608000), (72805601/110707200)],
    ![(1/4), (2662003/13392000), (128945641/830304000), (6618691/55353600)]]

private theorem tensor034 (u v : ℝ) :
    eval poly007 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern034 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly007, bern034, Fin.sum_univ_succ]
  <;> ring

private theorem cert034 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly007 δ p := by
  apply positive_on_box_from_tensor (β := bern034) (m := (1/1000000000000000))
    tensor034 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern034]

private def bern035 : Coeff :=
  ![![(78108328910247/5038407680000000), (54540401271727/3400925184000000), (13214850099373/797091840000000), (227508708377/13284864000000)],
    ![(380599676056011/20153630720000000), (2096021870543/108829605888000), (62641049500489/3188367360000000), (1065085341461/53139456000000)],
    ![(224383018235517/10076815360000000), (152921931274421/6801850368000000), (36211349301743/1594183680000000), (610067924707/26569728000000)]]

private theorem tensor035 (u v : ℝ) :
    eval poly008 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern035 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern035, Fin.sum_univ_succ]
  <;> ring

private theorem cert035 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern035) (m := (1/1000000000000000))
    tensor035 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern035]

private def bern036 : Coeff :=
  ![![(152341726582346869/3778805760000000000), (10862284703221231/283410432000000000), (3623406376254041/99636480000000000), (114364831171043/3321216000000000)],
    ![(547821695775004897/15115223040000000000), (312180524825999/9069133824000000), (13002136348770413/398545920000000000), (409840463748599/13284864000000000)],
    ![(243138242610311159/7557611520000000000), (17297996196807413/566820864000000000), (5755323596262331/199272960000000000), (181110801406513/6642432000000000)]]

private theorem tensor036 (u v : ℝ) :
    eval poly009 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern036 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern036, Fin.sum_univ_succ]
  <;> ring

private theorem cert036 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern036) (m := (1/1000000000000000))
    tensor036 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern036]

private def bern037 : Coeff :=
  ![![(376508584127961/40632320000000000), (352070366630997/40632320000000000), (40988154563851/5079040000000000), (2375229144423/317440000000000)],
    ![(674219195792611/81264640000000000), (1883867640638501/243793920000000000), (21127015541759/2949120000000000), (12583255617479/1904640000000000)],
    ![(1168683531986161/162529280000000000), (3246796617740711/487587840000000000), (1121211167849099/182845440000000000), (21371608120589/3809280000000000)]]

private theorem tensor037 (u v : ℝ) :
    eval poly010 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern037 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern037, Fin.sum_univ_succ]
  <;> ring

private theorem cert037 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern037) (m := (1/1000000000000000))
    tensor037 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern037]

private def bern038 : Coeff :=
  ![![(471997/223200), (185999/111600), (3985811/3075200), (27761269/27676800)],
    ![(5191949/4464000), (2045983/2232000), (131531453/184512000), (305373401/553536000)],
    ![(471979/2232000), (185993/1116000), (11957123/92256000), (27760711/276768000)]]

private theorem tensor038 (u v : ℝ) :
    eval poly011 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern038 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly011, bern038, Fin.sum_univ_succ]
  <;> ring

private theorem cert038 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly011 δ p := by
  apply positive_on_box_from_tensor (β := bern038) (m := (1/1000000000000000))
    tensor038 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern038]

private def bern039 : Coeff :=
  ![![(16511247/625000000), (16511247/625000000), (16511247/625000000), (16511247/625000000)],
    ![(16511247/625000000), (16511247/625000000), (16511247/625000000), (16511247/625000000)],
    ![(16511247/625000000), (16511247/625000000), (16511247/625000000), (16511247/625000000)]]

private theorem tensor039 (u v : ℝ) :
    eval poly013 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern039 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly013, bern039, Fin.sum_univ_succ]
  <;> ring

private theorem cert039 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly013 δ p := by
  apply positive_on_box_from_tensor (β := bern039) (m := (1/1000000000000000))
    tensor039 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern039]

private def bern040 : Coeff :=
  ![![1, 1, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

private theorem tensor040 (u v : ℝ) :
    eval poly014 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern040 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly014, bern040, Fin.sum_univ_succ]
  <;> ring

private theorem cert040 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly014 δ p := by
  apply positive_on_box_from_tensor (β := bern040) (m := (1/1000000000000000))
    tensor040 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern040]

private def bern041 : Coeff :=
  ![![(287600169/1625292800), (1399038191/8126464000), (5315269/31744000), (5168019/31744000)],
    ![(590337189/3250585600), (2871709971/16252928000), (10910289/63488000), (10608039/63488000)],
    ![(15136851/81264640), (73633589/406323200), (279751/1587200), (272001/1587200)]]

private theorem tensor041 (u v : ℝ) :
    eval poly004 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern041 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern041, Fin.sum_univ_succ]
  <;> ring

private theorem cert041 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern041) (m := (1/1000000000000000))
    tensor041 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern041]

private def bern042 : Coeff :=
  ![![(4390724963/40632320000), (39626988169/365690880000), (1241349883/11427840000), (51829621/476160000)],
    ![(8109716023/81264640000), (2364542939/23592960000), (2299529903/22855680000), (3101471/30720000)],
    ![(185949553/2031616000), (1683692147/18284544000), (52909001/571392000), (2215799/23808000)]]

private theorem tensor042 (u v : ℝ) :
    eval poly005 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern042 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern042, Fin.sum_univ_succ]
  <;> ring

private theorem cert042 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern042) (m := (1/1000000000000000))
    tensor042 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern042]

private def bern043 : Coeff :=
  ![![(224383018235517/10076815360000000), (152921931274421/6801850368000000), (36211349301743/1594183680000000), (610067924707/26569728000000)],
    ![(516932396886057/20153630720000000), (349684991279809/13603700736000000), (82204347706483/3188367360000000), (1375186357367/53139456000000)],
    ![(14627468932527/503840768000000), (49190765001347/1700462592000000), (2299649920237/79709184000000), (38255921633/1328486400000)]]

private theorem tensor043 (u v : ℝ) :
    eval poly008 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern043 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern043, Fin.sum_univ_succ]
  <;> ring

private theorem cert043 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern043) (m := (1/1000000000000000))
    tensor043 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern043]

private def bern044 : Coeff :=
  ![![(243138242610311159/7557611520000000000), (17297996196807413/566820864000000000), (5755323596262331/199272960000000000), (181110801406513/6642432000000000)],
    ![(424731274666239739/15115223040000000000), (30169419183979777/1133641728000000000), (10019158036278911/398545920000000000), (314602741877453/13284864000000000)],
    ![(9079651602796429/377880576000000000), (3217855746793091/141705216000000000), (213191722000829/9963648000000000), (6674597023547/332121600000000)]]

private theorem tensor044 (u v : ℝ) :
    eval poly009 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern044 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern044, Fin.sum_univ_succ]
  <;> ring

private theorem cert044 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern044) (m := (1/1000000000000000))
    tensor044 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern044]

private def bern045 : Coeff :=
  ![![(1168683531986161/162529280000000000), (3246796617740711/487587840000000000), (1121211167849099/182845440000000000), (21371608120589/3809280000000000)],
    ![(9889286723871/1625292800000000), (45430965903407/8126464000000000), (15542456201819/3047424000000000), (292945083437/63488000000000)],
    ![(1967537245289/406323200000000), (172668527857/39321600000000), (1802295953347/457113600000000), (33307843189/9523200000000)]]

private theorem tensor045 (u v : ℝ) :
    eval poly010 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern045 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern045, Fin.sum_univ_succ]
  <;> ring

private theorem cert045 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern045) (m := (1/1000000000000000))
    tensor045 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern045]

private def bern046 : Coeff :=
  ![![(178068627/1048576000), (5443468783/32505856000), (1310411/7936000), (5168019/31744000)],
    ![(721646541/4194304000), (22060373489/130023424000), (5310613/31744000), (20944077/126976000)],
    ![(365509287/2097152000), (11173435923/65011712000), (2689791/15872000), (10608039/63488000)]]

private theorem tensor046 (u v : ℝ) :
    eval poly004 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern046 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern046, Fin.sum_univ_succ]
  <;> ring

private theorem cert046 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern046) (m := (1/1000000000000000))
    tensor046 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern046]

private def bern047 : Coeff :=
  ![![(341260459/3145728000), (158878529609/1462763520000), (2485260787/22855680000), (51829621/476160000)],
    ![(1314224821/12582912000), (612067625687/5851054080000), (9577545901/91422720000), (199804843/1904640000)],
    ![(631703903/6291456000), (294310566469/2925527040000), (4607024327/45711360000), (3101471/30720000)]]

private theorem tensor047 (u v : ℝ) :
    eval poly005 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern047 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern047, Fin.sum_univ_succ]
  <;> ring

private theorem cert047 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern047) (m := (1/1000000000000000))
    tensor047 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern047]

private def bern048 : Coeff :=
  ![![(2047711951583/90596966400000), (299082016471429/13164871680000000), (72815424784163/3188367360000000), (610067924707/26569728000000)],
    ![(43804883926789/1811939328000000), (1277136516424027/52659486720000000), (310346378716829/12753469440000000), (2595322206781/106278912000000)],
    ![(23327764410959/905969664000000), (678972483481169/26329743360000000), (164715529148503/6376734720000000), (1375186357367/53139456000000)]]

private theorem tensor048 (u v : ℝ) :
    eval poly008 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern048 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern048, Fin.sum_univ_succ]
  <;> ring

private theorem cert048 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern048) (m := (1/1000000000000000))
    tensor048 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern048]

private def bern049 : Coeff :=
  ![![(672780386402447/22649241600000000), (95072198287112911/3291217920000000000), (11188647638457721/398545920000000000), (181110801406513/6642432000000000)],
    ![(12589348564170901/452984832000000000), (355647714296029393/13164871680000000000), (41834535569517943/1594183680000000000), (676824344690479/26569728000000000)],
    ![(5861544700146431/226492416000000000), (5338816700703341/212336640000000000), (19457240292602501/797091840000000000), (314602741877453/13284864000000000)]]

private theorem tensor049 (u v : ℝ) :
    eval poly009 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern049 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern049, Fin.sum_univ_succ]
  <;> ring

private theorem cert049 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern049) (m := (1/1000000000000000))
    tensor049 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern049]

#check cert049

private def bern050 : Coeff :=
  ![![(1006116759331/157286400000000), (35886466057113893/5851054080000000000), (2147048357637371/365690880000000000), (21371608120589/3809280000000000)],
    ![(9235131598559/1572864000000000), (65734252595861873/11702108160000000000), (3923277570045071/731381760000000000), (1256397197639/245760000000000)],
    ![(5572434971701/1048576000000000), (39552029062047151/7801405440000000000), (2353311917673457/487587840000000000), (23282718469543/5079040000000000)]]

private theorem tensor050 (u v : ℝ) :
    eval poly010 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern050 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern050, Fin.sum_univ_succ]
  <;> ring

private theorem cert050 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern050) (m := (1/1000000000000000))
    tensor050 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern050]

private def bern051 : Coeff :=
  ![![(365509287/2097152000), (11173435923/65011712000), (2689791/15872000), (10608039/63488000)],
    ![(740390607/4194304000), (22633370203/130023424000), (5448551/31744000), (21488079/126976000)],
    ![(9372033/52428800), (286498357/1625292800), (68969/396800), (272001/1587200)]]

private theorem tensor051 (u v : ℝ) :
    eval poly004 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern051 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern051, Fin.sum_univ_succ]
  <;> ring

private theorem cert051 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern051) (m := (1/1000000000000000))
    tensor051 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern051]

private def bern052 : Coeff :=
  ![![(631703903/6291456000), (294310566469/2925527040000), (4607024327/45711360000), (3101471/30720000)],
    ![(1212590791/12582912000), (565174640189/5851054080000), (8850551407/91422720000), (184777561/1904640000)],
    ![(72610861/786432000), (6771601843/73138176000), (106088177/1142784000), (2215799/23808000)]]

private theorem tensor052 (u v : ℝ) :
    eval poly005 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern052 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern052, Fin.sum_univ_succ]
  <;> ring

private theorem cert052 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern052) (m := (1/1000000000000000))
    tensor052 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern052]

private def bern053 : Coeff :=
  ![![(23327764410959/905969664000000), (678972483481169/26329743360000000), (164715529148503/6376734720000000), (1375186357367/53139456000000)],
    ![(49506173717047/1811939328000000), (1438753417500649/52659486720000000), (348515737877183/12753469440000000), (2905423222687/106278912000000)],
    ![(3272301163261/113246208000000), (18994523350487/658243584000000), (4595005218217/159418368000000), (38255921633/1328486400000)]]

private theorem tensor053 (u v : ℝ) :
    eval poly008 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern053 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern053, Fin.sum_univ_succ]
  <;> ring

private theorem cert053 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern053) (m := (1/1000000000000000))
    tensor053 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern053]

private def bern054 : Coeff :=
  ![![(5861544700146431/226492416000000000), (5338816700703341/212336640000000000), (19457240292602501/797091840000000000), (314602741877453/13284864000000000)],
    ![(10856830236414823/452984832000000000), (306365556591184891/13164871680000000000), (35994425600892061/1594183680000000000), (581586622819333/26569728000000000)],
    ![(624410692033549/28311552000000000), (3521555971734533/164560896000000000), (413429632707239/19927296000000000), (6674597023547/332121600000000)]]

private theorem tensor054 (u v : ℝ) :
    eval poly009 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern054 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern054, Fin.sum_univ_succ]
  <;> ring

private theorem cert054 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern054) (m := (1/1000000000000000))
    tensor054 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern054]

private def bern055 : Coeff :=
  ![![(5572434971701/1048576000000000), (39552029062047151/7801405440000000000), (2353311917673457/487587840000000000), (23282718469543/5079040000000000)],
    ![(116908958071/24576000000000), (2646091729513979/585105408000000000), (31366581829753/7313817600000000), (1544992114091/380928000000000)],
    ![(40970318933/9830400000000), (57685120128829/14627635200000000), (3401072426419/914227200000000), (33307843189/9523200000000)]]

private theorem tensor055 (u v : ℝ) :
    eval poly010 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern055 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern055, Fin.sum_univ_succ]
  <;> ring

private theorem cert055 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern055) (m := (1/1000000000000000))
    tensor055 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern055]

private def bern056 : Coeff :=
  ![![(8876587941/52009369600), (44070835731/260046848000), (21367203/126976000), (10608039/63488000)],
    ![(35733956583/208037478400), (177413364353/1040187392000), (86016689/507904000), (42704157/253952000)],
    ![(17980780701/104018739200), (89271692891/520093696000), (43282283/253952000), (21488079/126976000)]]

private theorem tensor056 (u v : ℝ) :
    eval poly004 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern056 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern056, Fin.sum_univ_succ]
  <;> ring

private theorem cert056 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern056) (m := (1/1000000000000000))
    tensor056 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern056]

private def bern057 : Coeff :=
  ![![(130921220631/1300234240000), (1179368966597/11702108160000), (368880527/3656908800), (3101471/30720000)],
    ![(513304728813/5200936960000), (4624419820871/46808432640000), (7232780137/73138176000), (377068763/3809280000)],
    ![(251462287551/2600468480000), (2265681887677/23404216320000), (3543974867/36569088000), (184777561/1904640000)]]

private theorem tensor057 (u v : ℝ) :
    eval poly005 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern057 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern057, Fin.sum_univ_succ]
  <;> ring

private theorem cert057 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern057) (m := (1/1000000000000000))
    tensor057 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern057]

private def bern058 : Coeff :=
  ![![(33290849255294689/1289832366080000000), (28112728299696709/1088296058880000000), (329737892032543/12753469440000000), (1375186357367/53139456000000)],
    ![(137073230413023547/5159329464320000000), (115708351779243847/4353184235520000000), (1356642308664709/51013877760000000), (5655795937421/212557824000000)],
    ![(70491531902434169/2579664732160000000), (59482895179850429/2176592117760000000), (697166524599623/25506938880000000), (2905423222687/106278912000000)]]

private theorem tensor058 (u v : ℝ) :
    eval poly008 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern058 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern058, Fin.sum_univ_succ]
  <;> ring

private theorem cert058 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern058) (m := (1/1000000000000000))
    tensor058 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern058]

private def bern059 : Coeff :=
  ![![(7989758545456258001/322458091520000000000), (6641669331475356431/272074014720000000000), (38333404805249681/1594183680000000000), (314602741877453/13284864000000000)],
    ![(30764744081942685323/1289832366080000000000), (25569888225780186773/1088296058880000000000), (147556432580551403/6376734720000000000), (1210792106574239/53139456000000000)],
    ![(14785226991030169321/644916183040000000000), (12286549562829473911/544148029440000000000), (70889622970052041/3188367360000000000), (581586622819333/26569728000000000)]]

private theorem tensor059 (u v : ℝ) :
    eval poly009 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern059 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern059, Fin.sum_univ_succ]
  <;> ring

private theorem cert059 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern059) (m := (1/1000000000000000))
    tensor059 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern059]

private def bern060 : Coeff :=
  ![![(3320819688098289/671088640000000000), (50206755332271941/10401873920000000000), (917690578149917/195035136000000000), (23282718469543/5079040000000000)],
    ![(194601993391850519/41607495680000000000), (284458302123725623/62411243520000000000), (5194288951261759/1170210816000000000), (131647839972269/30474240000000000)],
    ![(365979735308690879/83214991360000000000), (534392490203990623/124822487040000000000), (9747066287293927/2340421632000000000), (7959357214139/1966080000000000)]]

private theorem tensor060 (u v : ℝ) :
    eval poly010 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern060 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern060, Fin.sum_univ_succ]
  <;> ring

private theorem cert060 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern060) (m := (1/1000000000000000))
    tensor060 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern060]

private def bern061 : Coeff :=
  ![![(17980780701/104018739200), (89271692891/520093696000), (43282283/253952000), (21488079/126976000)],
    ![(36189166221/208037478400), (179673407211/1040187392000), (87112443/507904000), (43248159/253952000)],
    ![(227604819/1300234240), (1130021429/6501171200), (547877/3174400), (272001/1587200)]]

private theorem tensor061 (u v : ℝ) :
    eval poly004 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern061 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern061, Fin.sum_univ_succ]
  <;> ring

private theorem cert061 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern061) (m := (1/1000000000000000))
    tensor061 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern061]

private def bern062 : Coeff :=
  ![![(251462287551/2600468480000), (2265681887677/23404216320000), (3543974867/36569088000), (184777561/1904640000)],
    ![(492544421391/5200936960000), (4438307729837/46808432640000), (6943119331/73138176000), (362041481/3809280000)],
    ![(3013526673/32505856000), (27157823027/292552704000), (212446529/2285568000), (2215799/23808000)]]

private theorem tensor062 (u v : ℝ) :
    eval poly005 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern062 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern062, Fin.sum_univ_succ]
  <;> ring

private theorem cert062 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern062) (m := (1/1000000000000000))
    tensor062 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern062]

private def bern063 : Coeff :=
  ![![(70491531902434169/2579664732160000000), (59482895179850429/2176592117760000000), (697166524599623/25506938880000000), (2905423222687/106278912000000)],
    ![(144892897196713129/5159329464320000000), (122223228940157869/4353184235520000000), (1432023789733783/51013877760000000), (192448288817/6856704000000)],
    ![(930017066178487/32245809152000000), (784254172003843/27207401472000000), (9185715814177/318836736000000), (38255921633/1328486400000)]]

private theorem tensor063 (u v : ℝ) :
    eval poly008 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern063 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern063, Fin.sum_univ_succ]
  <;> ring

private theorem cert063 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern063) (m := (1/1000000000000000))
    tensor063 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern063]

private def bern064 : Coeff :=
  ![![(14785226991030169321/644916183040000000000), (12286549562829473911/544148029440000000000), (70889622970052041/3188367360000000000), (581586622819333/26569728000000000)],
    ![(28376163882177991961/1289832366080000000000), (23576310025537708871/1088296058880000000000), (136002059299656761/6376734720000000000), (35985625313003/1714176000000000)],
    ![(169886711139347783/8061452288000000000), (141122005783852937/6801850368000000000), (813905454120059/39854592000000000), (6674597023547/332121600000000)]]

private theorem tensor064 (u v : ℝ) :
    eval poly009 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern064 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern064, Fin.sum_univ_succ]
  <;> ring

private theorem cert064 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern064) (m := (1/1000000000000000))
    tensor064 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern064]

private def bern065 : Coeff :=
  ![![(365979735308690879/83214991360000000000), (534392490203990623/124822487040000000000), (9747066287293927/2340421632000000000), (7959357214139/1966080000000000)],
    ![(4284443547921009/1040187392000000000), (16662279205351/4160749568000000), (189699055668007/48758784000000000), (959101947217/253952000000000)],
    ![(49825724285023/13002342400000000), (72560094970847/19503513600000000), (6598625372563/1828454400000000), (33307843189/9523200000000)]]

private theorem tensor065 (u v : ℝ) :
    eval poly010 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern065 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern065, Fin.sum_univ_succ]
  <;> ring

private theorem cert065 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern065) (m := (1/1000000000000000))
    tensor065 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern065]

private def bern066 : Coeff :=
  ![![(355830250257/2080374784000), (354571095643/2080374784000), (86258441/507904000), (21488079/126976000)],
    ![(1427825181411/8321499136000), (1422772624289/8321499136000), (346125643/2031616000), (86224317/507904000)],
    ![(716164680897/4160749568000), (713630433003/4160749568000), (173608761/1015808000), (43248159/253952000)]]

private theorem tensor066 (u v : ℝ) :
    eval poly004 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern066 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern066, Fin.sum_univ_succ]
  <;> ring

private theorem cert066 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern066) (m := (1/1000000000000000))
    tensor066 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern066]

private def bern067 : Coeff :=
  ![![(3022530777533/31205621760000), (1814503277401/18723373056000), (35458520191/365690880000), (184777561/1904640000)],
    ![(11966291191079/124822487040000), (7183859793211/74893492224000), (140388619213/1462763520000), (731596603/7618560000)],
    ![(5921229636013/62411243520000), (3554853238409/37446746112000), (69471578831/731381760000), (362041481/3809280000)]]

private theorem tensor067 (u v : ℝ) :
    eval poly005 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern067 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern067, Fin.sum_univ_succ]
  <;> ring

private theorem cert067 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern067) (m := (1/1000000000000000))
    tensor067 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern067]

private def bern068 : Coeff :=
  ![![(15228915631371627683/557207582146560000000), (713907148936447543/26119105413120000000), (1394468098044503/51013877760000000), (2905423222687/106278912000000)],
    ![(61744318578141198329/2228830328586240000000), (2894224873849476469/104476421652480000000), (5652775254621269/204055511040000000), (11776743398701/425115648000000)],
    ![(31286487315397942963/1114415164293120000000), (1466410575976581383/52238210826240000000), (2863839058532263/102027755520000000), (192448288817/6856704000000)]]

private theorem tensor068 (u v : ℝ) :
    eval poly008 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern068 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern068, Fin.sum_univ_succ]
  <;> ring

private theorem cert068 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern068) (m := (1/1000000000000000))
    tensor068 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern068]

private def bern069 : Coeff :=
  ![![(3121314078661654781747/139301895536640000000000), (145183304715841531237/6529776353280000000000), (140680017708372001/6376734720000000000), (581586622819333/26569728000000000)],
    ![(12231457805718330798761/557207582146560000000000), (568901309627302746271/26119105413120000000000), (551228620880771923/25506938880000000000), (2278727630341759/106278912000000000)],
    ![(5988829648395021235267/278603791073280000000000), (278534700195619683797/13059552706560000000000), (269868585464027921/12753469440000000000), (35985625313003/1714176000000000)]]

private theorem tensor069 (u v : ℝ) :
    eval poly009 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern069 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern069, Fin.sum_univ_succ]
  <;> ring

private theorem cert069 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern069) (m := (1/1000000000000000))
    tensor069 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern069]

private def bern070 : Coeff :=
  ![![(8434002700706586679/1997159792640000000000), (1247641938995959801/299573968896000000000), (96109425575024963/23404216320000000000), (7959357214139/1966080000000000)],
    ![(16318092482423596039/3994319585280000000000), (2413169137162055209/599147937792000000000), (185832616663106003/46808432640000000000), (476924540970389/121896960000000000)],
    ![(338936407466549443/85899345920000000000), (1553276675961560179/399431958528000000000), (119571895948744481/31205621760000000000), (306759734904023/81264640000000000)]]

private theorem tensor070 (u v : ℝ) :
    eval poly010 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern070 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern070, Fin.sum_univ_succ]
  <;> ring

private theorem cert070 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern070) (m := (1/1000000000000000))
    tensor070 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern070]

private def bern071 : Coeff :=
  ![![(716164680897/4160749568000), (713630433003/4160749568000), (173608761/1015808000), (43248159/253952000)],
    ![(1436833542177/8321499136000), (1431749107723/8321499136000), (348309401/2031616000), (86768319/507904000)],
    ![(4504180383/26004684800), (4488241717/26004684800), (1091879/6348800), (272001/1587200)]]

private theorem tensor071 (u v : ℝ) :
    eval poly004 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern071 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern071, Fin.sum_univ_succ]
  <;> ring

private theorem cert071 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern071) (m := (1/1000000000000000))
    tensor071 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern071]

private def bern072 : Coeff :=
  ![![(5921229636013/62411243520000), (3554853238409/37446746112000), (69471578831/731381760000), (362041481/3809280000)],
    ![(11718627352973/124822487040000), (281422126417/2995739688960), (137497696111/1462763520000), (716569321/7618560000)],
    ![(36233735731/390070272000), (108771872563/1170210816000), (13714943/147456000), (2215799/23808000)]]

private theorem tensor072 (u v : ℝ) :
    eval poly005 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern072 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern072, Fin.sum_univ_succ]
  <;> ring

private theorem cert072 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern072) (m := (1/1000000000000000))
    tensor072 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern072]

private def bern073 : Coeff :=
  ![![(31286487315397942963/1114415164293120000000), (1466410575976581383/52238210826240000000), (2863839058532263/102027755520000000), (192448288817/6856704000000)],
    ![(63401630683450573523/2228830328586240000000), (2971417430056849063/104476421652480000000), (5802580979507783/204055511040000000), (12086844414607/425115648000000)],
    ![(200719646050328941/6965094776832000000), (9406292838001673/326488817664000000), (18367137006097/637673472000000), (38255921633/1328486400000)]]

private theorem tensor073 (u v : ℝ) :
    eval poly008 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern073 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern073, Fin.sum_univ_succ]
  <;> ring

private theorem cert073 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern073) (m := (1/1000000000000000))
    tensor073 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern073]

private def bern074 : Coeff :=
  ![![(5988829648395021235267/278603791073280000000000), (278534700195619683797/13059552706560000000000), (269868585464027921/12753469440000000000), (35985625313003/1714176000000000)],
    ![(11723860787861754142307/557207582146560000000000), (545237491155175988917/26119105413120000000000), (528245720975339761/25506938880000000000), (2183489908470613/106278912000000000)],
    ![(35843944621667080669/1741273694208000000000), (1666892443497226907/81622204416000000000), (1614857096945699/79709184000000000), (6674597023547/332121600000000)]]

private theorem tensor074 (u v : ℝ) :
    eval poly009 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern074 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern074, Fin.sum_univ_succ]
  <;> ring

private theorem cert074 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern074) (m := (1/1000000000000000))
    tensor074 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern074]

private def bern075 : Coeff :=
  ![![(338936407466549443/85899345920000000000), (1553276675961560179/399431958528000000000), (119571895948744481/31205621760000000000), (306759734904023/81264640000000000)],
    ![(190037417649568777/49928994816000000000), (140416305670164083/37446746112000000000), (2161038389789093/585105408000000000), (5541933296771/1523712000000000)],
    ![(1143578692226327/312056217600000000), (844635697309789/234042163200000000), (12993731264851/3656908800000000), (33307843189/9523200000000)]]

private theorem tensor075 (u v : ℝ) :
    eval poly010 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern075 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern075, Fin.sum_univ_succ]
  <;> ring

private theorem cert075 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern075) (m := (1/1000000000000000))
    tensor075 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern075]

private def bern076 : Coeff :=
  ![![(15136851/81264640), (73633589/406323200), (279751/1587200), (272001/1587200)],
    ![(620610891/3250585600), (3018977149/16252928000), (11469791/63488000), (11152041/63488000)],
    ![(317873871/1625292800), (1546305369/8126464000), (5874771/31744000), (5712021/31744000)]]

private theorem tensor076 (u v : ℝ) :
    eval poly004 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern076 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly004, bern076, Fin.sum_univ_succ]
  <;> ring

private theorem cert076 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly004 δ p := by
  apply positive_on_box_from_tensor (β := bern076) (m := (1/1000000000000000))
    tensor076 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern076]

private def bern077 : Coeff :=
  ![![(185949553/2031616000), (1683692147/18284544000), (52909001/571392000), (2215799/23808000)],
    ![(6766248217/81264640000), (61394540651/731381760000), (1933190177/22855680000), (81118319/952320000)],
    ![(3047257157/40632320000), (27720697711/365690880000), (875010157/11427840000), (36802339/476160000)]]

private theorem tensor077 (u v : ℝ) :
    eval poly005 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern077 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly005, bern077, Fin.sum_univ_succ]
  <;> ring

private theorem cert077 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly005 δ p := by
  apply positive_on_box_from_tensor (β := bern077) (m := (1/1000000000000000))
    tensor077 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern077]

private def bern078 : Coeff :=
  ![![(14627468932527/503840768000000), (49190765001347/1700462592000000), (2299649920237/79709184000000), (38255921633/1328486400000)],
    ![(653265117716103/20153630720000000), (14108620927153/438829056000000), (101767645912477/3188367360000000), (1685287373273/53139456000000)],
    ![(360715739065563/10076815360000000), (48120837747271/1360370073600000), (55774647507737/1594183680000000), (920168940613/26569728000000)]]

private theorem tensor078 (u v : ℝ) :
    eval poly008 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern078 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly008, bern078, Fin.sum_univ_succ]
  <;> ring

private theorem cert078 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly008 δ p := by
  apply positive_on_box_from_tensor (β := bern078) (m := (1/1000000000000000))
    tensor078 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern078]

private def bern079 : Coeff :=
  ![![(9079651602796429/377880576000000000), (3217855746793091/141705216000000000), (213191722000829/9963648000000000), (6674597023547/332121600000000)],
    ![(301640853557474581/15115223040000000000), (687621702087409/36569088000000000), (7036179723787409/398545920000000000), (219365020006307/13284864000000000)],
    ![(120047821501546001/7557611520000000000), (1688969955507463/113364172800000000), (2772345283770829/199272960000000000), (85873079535367/6642432000000000)]]

private theorem tensor079 (u v : ℝ) :
    eval poly009 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern079 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly009, bern079, Fin.sum_univ_succ]
  <;> ring

private theorem cert079 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly009 δ p := by
  apply positive_on_box_from_tensor (β := bern079) (m := (1/1000000000000000))
    tensor079 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern079]

private def bern080 : Coeff :=
  ![![(1967537245289/406323200000000), (172668527857/39321600000000), (1802295953347/457113600000000), (33307843189/9523200000000)],
    ![(5851011238441/1625292800000000), (77816076832459/24379392000000000), (25464469528423/9142272000000000), (453478477249/190464000000000)],
    ![(361028434900161/162529280000000000), (302574594210077/162529280000000000), (2953711879223/1966080000000000), (1452445732703/1269760000000000)]]

private theorem tensor080 (u v : ℝ) :
    eval poly010 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern080 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly010, bern080, Fin.sum_univ_succ]
  <;> ring

private theorem cert080 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly010 δ p := by
  apply positive_on_box_from_tensor (β := bern080) (m := (1/1000000000000000))
    tensor080 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern080]

private def bern081 : Coeff :=
  ![![3, (197639/75402), (84536/37701), (46835/25134)],
    ![3, (197639/75402), (84536/37701), (46835/25134)],
    ![3, (197639/75402), (84536/37701), (46835/25134)]]

private theorem tensor081 (u v : ℝ) :
    eval poly042 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern081 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly042, bern081, Fin.sum_univ_succ]
  <;> ring

private theorem cert081 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly042 δ p := by
  apply positive_on_box_from_tensor (β := bern081) (m := (1/1000000000000000))
    tensor081 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern081]

private def bern082 : Coeff :=
  ![![2, (67402/37701), (59402/37701), (17134/12567)],
    ![2, (67402/37701), (59402/37701), (17134/12567)],
    ![2, (67402/37701), (59402/37701), (17134/12567)]]

private theorem tensor082 (u v : ℝ) :
    eval poly043 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern082 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly043, bern082, Fin.sum_univ_succ]
  <;> ring

private theorem cert082 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly043 δ p := by
  apply positive_on_box_from_tensor (β := bern082) (m := (1/1000000000000000))
    tensor082 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern082]

private def bern083 : Coeff :=
  ![![1, (20205521250274/22520506672575), (17890535827973/22520506672575), (5191850135224/7506835557525)],
    ![1, (20205521250274/22520506672575), (17890535827973/22520506672575), (5191850135224/7506835557525)],
    ![1, (20205521250274/22520506672575), (17890535827973/22520506672575), (5191850135224/7506835557525)]]

private theorem tensor083 (u v : ℝ) :
    eval poly044 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern083 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly044, bern083, Fin.sum_univ_succ]
  <;> ring

private theorem cert083 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly044 δ p := by
  apply positive_on_box_from_tensor (β := bern083) (m := (1/1000000000000000))
    tensor083 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern083]

private def bern084 : Coeff :=
  ![![(5/2), (988195/452412), (211340/113103), (234175/150804)],
    ![(17/8), (3161059/1809648), (4487/3186), (669391/603216)],
    ![(7/4), (1184669/904824), (107237/113103), (201041/301608)]]

private theorem tensor084 (u v : ℝ) :
    eval poly045 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern084 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly045, bern084, Fin.sum_univ_succ]
  <;> ring

private theorem cert084 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly045 δ p := by
  apply positive_on_box_from_tensor (β := bern084) (m := (1/1000000000000000))
    tensor084 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern084]

private def bern085 : Coeff :=
  ![![(12970972610709113/72884144458956800), (115024812535584203/655957300130611200), (1180490379924401/6832888543027200), (4542868868321/26690970871200)],
    ![(31500933483150703/174921946701496320), (279345973300704493/1574297520313466880), (2866905208387831/16398932503265280), (11032681537351/64058330090880)],
    ![(79678831751498837/437304866753740800), (706580991290017247/3935743800783667200), (7251583762392749/40997331258163200), (27906194476829/160145825227200)]]

private theorem tensor085 (u v : ℝ) :
    eval poly046 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern085 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly046, bern085, Fin.sum_univ_succ]
  <;> ring

private theorem cert085 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly046 δ p := by
  apply positive_on_box_from_tensor (β := bern085) (m := (1/1000000000000000))
    tensor085 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern085]

private def bern086 : Coeff :=
  ![![(78333796457413567/1093262166884352000), (393291547330522463/5466310834421760000), (592273100910484049/8199466251632640000), (2064273656856607/28470368929280000)],
    ![(98826026825337173/1457682889179136000), (2681279488632393323/39357438007836672000), (1995392536587133/29153657783582720), (14092729331066731/204986656290816000)],
    ![(27962097512236877/437304866753740800), (6327149591212562281/98393595019591680000), (1060270401839556527/16398932503265280000), (33306720831914729/512466640727040000)]]

private theorem tensor086 (u v : ℝ) :
    eval poly047 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern086 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly047, bern086, Fin.sum_univ_succ]
  <;> ring

private theorem cert086 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly047 δ p := by
  apply positive_on_box_from_tensor (β := bern086) (m := (1/1000000000000000))
    tensor086 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern086]

private def bern087 : Coeff :=
  ![![(25/74), (129172398774799/666606997508220), (1107426185778560747/12565875206528701110), (35015167778184929/1675450027537160148)],
    ![(307/296), (139692466952071/225968473731600), (44420076738846014621/125658752065287011100), (6425002473611855269/33509000550743202960)],
    ![(257/148), (6950131562424199/6666069975082200), (19441472904976605443/31414688016321752775), (6074850795830005979/16754500275371601480)]]

private theorem tensor087 (u v : ℝ) :
    eval poly048 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern087 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly048, bern087, Fin.sum_univ_succ]
  <;> ring

private theorem cert087 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly048 δ p := by
  apply positive_on_box_from_tensor (β := bern087) (m := (1/1000000000000000))
    tensor087 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern087]

private def bern088 : Coeff :=
  ![![(5/2), (34722923581373/18016405338060), (986218828316059463/679236497650200060), (12158015054160802/11320608294170001)],
    ![(11/8), (381952159395103/360328106761200), (10848407111476654093/13584729953004001200), (66869082797884411/113206082941700010)],
    ![(1/4), (34722923581373/180164053380600), (986218828316059463/6792364976502000600), (6079007527080401/56603041470850005)]]

private theorem tensor088 (u v : ℝ) :
    eval poly049 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern088 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly049, bern088, Fin.sum_univ_succ]
  <;> ring

private theorem cert088 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly049 δ p := by
  apply positive_on_box_from_tensor (β := bern088) (m := (1/1000000000000000))
    tensor088 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern088]

private def bern089 : Coeff :=
  ![![(46979408740730336361483900991/31654715100446941249536000000000), (839963471194794009553724295997/474820726506704118743040000000000), (15245770687240098205871272333/7419073851667251855360000000000), (72383750549231598889525321/30912807715280216064000000000)],
    ![(405744765520957325632176978367/126618860401787764998144000000000), (1310375688805251638437154593241/379856581205363294994432000000000), (21939800934161808556272788201/5935259081333801484288000000000), (97552599274373151244137077/24730246172224172851200000000)],
    ![(62357189607899330581841835277/12661886040178776499814400000000), (1399583884411568564515462331/272807082164150599680000000000), (79207463296328846369621396339/14838147703334503710720000000000), (342995495273402558441634743/61825615430560432128000000000)]]

private theorem tensor089 (u v : ℝ) :
    eval poly050 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern089 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly050, bern089, Fin.sum_univ_succ]
  <;> ring

private theorem cert089 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly050 δ p := by
  apply positive_on_box_from_tensor (β := bern089) (m := (1/1000000000000000))
    tensor089 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern089]

private def bern090 : Coeff :=
  ![![(9505647135180467064222941/852522131762970624000000000), (8049676865545558926511787173/754482086610229002240000000000), (120128324649296600331575797/11788782603284828160000000000), (477106450027958784745489/49119927513686784000000000)],
    ![(1879529763847070386852475503/201195223096061067264000000000), (5372673940532366285725108769/603585669288183201792000000000), (79804275304404526037839409/9431026082627862528000000000), (315311875205280506004893/39295942010949427200000000)],
    ![(151572680379155054654833693/20119522309606106726400000000), (10764015971570713575601969499/1508964173220458004480000000000), (158764727223429429526045451/23577565206569656320000000000), (622346475970484960533487/98239855027373568000000000)]]

private theorem tensor090 (u v : ℝ) :
    eval poly051 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern090 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly051, bern090, Fin.sum_univ_succ]
  <;> ring

private theorem cert090 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly051 δ p := by
  apply positive_on_box_from_tensor (β := bern090) (m := (1/1000000000000000))
    tensor090 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern090]

private def bern091 : Coeff :=
  ![![(7569627980326462007251/4373048667537408000000000), (614358929694104989124857/393574380078366720000000000), (182558538805066893079583/131191460026122240000000000), (5013000691787608628521/4099733125816320000000000)],
    ![(29361357983002604429927/26238292005224448000000000), (2268598107141786998334773/2361446280470200320000000000), (631872662450258632567747/787148760156733440000000000), (15872659223950750153829/24598398754897920000000000)],
    ![(217645393087485336611/456318121829990400000000), (67952203340714477404813/205343154823495680000000000), (12669803177902103372267/68447718274498560000000000), (84679850252310925309/2138991196078080000000000)]]

private theorem tensor091 (u v : ℝ) :
    eval poly052 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern091 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly052, bern091, Fin.sum_univ_succ]
  <;> ring

private theorem cert091 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly052 δ p := by
  apply positive_on_box_from_tensor (β := bern091) (m := (1/1000000000000000))
    tensor091 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern091]

private def bern092 : Coeff :=
  ![![(3224343741476/1501367111505), (7358045802127/4504101334515), (826645866078152771/679236497650200060), (203267060523739367/226412165883400020)],
    ![(17510705945021/15013671115050), (80045765291009/90082026690300), (9008961688335780511/13584729953004001200), (2219109098056353043/4528243317668000400)],
    ![(1388987237641/7506835557525), (6465307269739/45041013345150), (742503027554252801/6792364976502000600), (186438492818959373/2264121658834000200)]]

private theorem tensor092 (u v : ℝ) :
    eval poly053 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern092 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly053, bern092, Fin.sum_univ_succ]
  <;> ring

private theorem cert092 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly053 δ p := by
  apply positive_on_box_from_tensor (β := bern092) (m := (1/1000000000000000))
    tensor092 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern092]

private def bern093 : Coeff :=
  ![![3, (2582117960813011/981923986169298), (1109231981559064/490961993084649), (618269988474415/327307995389766)],
    ![3, (2582117960813011/981923986169298), (1109231981559064/490961993084649), (618269988474415/327307995389766)],
    ![3, (2582117960813011/981923986169298), (1109231981559064/490961993084649), (618269988474415/327307995389766)]]

private theorem tensor093 (u v : ℝ) :
    eval poly054 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern093 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly054, bern093, Fin.sum_univ_succ]
  <;> ring

private theorem cert093 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly054 δ p := by
  apply positive_on_box_from_tensor (β := bern093) (m := (1/1000000000000000))
    tensor093 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern093]

private def bern094 : Coeff :=
  ![![2, (881923986169298/490961993084649), (781923986169298/490961993084649), (227307995389766/163653997694883)],
    ![2, (881923986169298/490961993084649), (781923986169298/490961993084649), (227307995389766/163653997694883)],
    ![2, (881923986169298/490961993084649), (781923986169298/490961993084649), (227307995389766/163653997694883)]]

private theorem tensor094 (u v : ℝ) :
    eval poly055 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern094 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly055, bern094, Fin.sum_univ_succ]
  <;> ring

private theorem cert094 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly055 δ p := by
  apply positive_on_box_from_tensor (β := bern094) (m := (1/1000000000000000))
    tensor094 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern094]

private def bern095 : Coeff :=
  ![![1, (442592477539028/490961993084649), (394222961993407/490961993084649), (115284482149262/163653997694883)],
    ![1, (442592477539028/490961993084649), (394222961993407/490961993084649), (115284482149262/163653997694883)],
    ![1, (442592477539028/490961993084649), (394222961993407/490961993084649), (115284482149262/163653997694883)]]

private theorem tensor095 (u v : ℝ) :
    eval poly056 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern095 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly056, bern095, Fin.sum_univ_succ]
  <;> ring

private theorem cert095 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly056 δ p := by
  apply positive_on_box_from_tensor (β := bern095) (m := (1/1000000000000000))
    tensor095 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern095]

private def bern096 : Coeff :=
  ![![(5/2), (12910589804065055/5891543917015788), (2773079953897660/1472885979253947), (3091349942372075/1963847972338596)],
    ![(17/8), (41332157361482591/23566175668063152), (4185773928541373/2945771958507894), (8846741831726459/7855391889354384)],
    ![(7/4), (15510977753352481/11783087834031576), (1412693974643713/1472885979253947), (2664041946982309/3927695944677192)]]

private theorem tensor096 (u v : ℝ) :
    eval poly057 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern096 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly057, bern096, Fin.sum_univ_succ]
  <;> ring

private theorem cert096 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly057 δ p := by
  apply positive_on_box_from_tensor (β := bern096) (m := (1/1000000000000000))
    tensor096 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern096]

private def bern097 : Coeff :=
  ![![(326680787447557214343/1830438979060369457152), (978236699357709447559/5491316937181108371456), (1271397286799369419/7150152261954568192), (2478616366209133/13965141136630016)],
    ![(5234489826775974899589/29287023664965911314432), (15674536880406088589957/87861070994897733943296), (20371923967552686737/114402436191273091072), (39715504100420759/223442258186080256)],
    ![(2621043527195517184845/14643511832482955657216), (2616214428514804336495/14643511832482955657216), (10200745673157731385/57201218095636545536), (19886573170747695/111721129093040128)]]

private theorem tensor097 (u v : ℝ) :
    eval poly058 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern097 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly058, bern097, Fin.sum_univ_succ]
  <;> ring

private theorem cert097 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly058 δ p := by
  apply positive_on_box_from_tensor (β := bern097) (m := (1/1000000000000000))
    tensor097 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern097]

private def bern098 : Coeff :=
  ![![(74747525815984933621913/1144024361912730910720000), (673194851648896628662619/10296219257214578196480000), (42103755373780499314681/643513703575911137280000), (54860305610240762021/837908468197800960000)],
    ![(1187208858727677470301659/18304389790603694571520000), (10692436638797358193074497/164739508115433251143680000), (668747709102123353394043/10296219257214578196480000), (871375313237218718783/13406535491164815360000)],
    ![(117845730439959600265271/1830438979060369457152000), (1061375565121237032754709/16473950811543325114368000), (66383533222375871775319/1029621925721457819648000), (86498573671058524523/1340653549116481536000)]]

private theorem tensor098 (u v : ℝ) :
    eval poly059 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern098 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly059, bern098, Fin.sum_univ_succ]
  <;> ring

private theorem cert098 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly059 δ p := by
  apply positive_on_box_from_tensor (β := bern098) (m := (1/1000000000000000))
    tensor098 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern098]

private def bern099 : Coeff :=
  ![![(25/74), (41875771760039155/217987124929584156), (757133001337916505023461737085/8918616110185084502428939768437), (192789194490287061544681357825/11891488146913446003238586357916)],
    ![(307/296), (543498001739633365/871948499718336624), (25590523371284839099320911263721/71348928881480676019431518147496), (9278012064334330710263860711285/47565952587653784012954345431664)],
    ![(257/148), (459746458219555055/435974249859168312), (22561991365933173079227064315381/35674464440740338009715759073748), (8892433675353756587174497995635/23782976293826892006477172715832)]]

private theorem tensor099 (u v : ℝ) :
    eval poly060 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern099 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly060, bern099, Fin.sum_univ_succ]
  <;> ring

private theorem cert099 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly060 δ p := by
  apply positive_on_box_from_tensor (β := bern099) (m := (1/1000000000000000))
    tensor099 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern099]

#check cert099

private def bern100 : Coeff :=
  ![![(5/2), (11459504337696425/5891543917015788), (1428299444868884960963789041255/964174714614603729992317812804), (178192338624257796369245329325/160695785769100621665386302134)],
    ![(11/8), (25210909542932135/23566175668063152), (3142258778711546914120335890761/3856698858458414919969271251216), (392023144973367152012339724515/642783143076402486661545208536)],
    ![(1/4), (2291900867539285/11783087834031576), (285659888973776992192757808251/1928349429229207459984635625608), (35638467724851559273849065865/321391571538201243330772604268)]]

private theorem tensor100 (u v : ℝ) :
    eval poly061 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern100 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly061, bern100, Fin.sum_univ_succ]
  <;> ring

private theorem cert100 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly061 δ p := by
  apply positive_on_box_from_tensor (β := bern100) (m := (1/1000000000000000))
    tensor100 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern100]

private def bern101 : Coeff :=
  ![![(156256922699672360158409318584984277856601/3994115419463595933947356613842042880000000), (84306537447034000947568517110333121994959/2156822326510341804331572571474703155200000), (12339055952903420438618546292575602315237/315940770484913350243882700899614720000000), (6421126555767344477388533948517658129/164552484627559036585355573385216000000)],
    ![(2511324737413170040107427158733936348047643/63905846711417534943157705821472686080000000), (6774699997635116261994280453412901126570193/172545786120827344346525805717976252416000000), (198306042190063072099078325501338749028351/5055052327758613603902123214393835520000000), (103195424971379313859419387737792889667/2632839754040944585365689174163456000000)],
    ![(252253871163158231768030522010812425038967/6390584671141753494315770582147268608000000), (3402438499753756224091539768999576246771833/86272893060413672173262902858988126208000000), (19918718913367141718025991032146786101291/505505232775861360390212321439383552000000), (10365282505048111608062223229930324927/263283975404094458536568917416345600000)]]

private theorem tensor101 (u v : ℝ) :
    eval poly062 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern101 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly062, bern101, Fin.sum_univ_succ]
  <;> ring

private theorem cert101 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly062 δ p := by
  apply positive_on_box_from_tensor (β := bern101) (m := (1/1000000000000000))
    tensor101 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern101]

private def bern102 : Coeff :=
  ![![(3272832182371261191815815213874697845363863/748896641149424237615129365095383040000000000), (2329305860732974397243135421170914701230681/539205581627585451082893142868675788800000000), (37470418898232490011654105218886047478587/8776132513469815284552297247211520000000000), (57858010129247471314286528948935520237/13712707052296586382112964448768000000000)],
    ![(49795214209028114736776731858431408141515509/11982346258390787801842069841526128640000000000), (177118773635281489479701199298540134985870087/43136446530206836086631451429494063104000000000), (569581785674264825399538225614083121730401/140418120215517044552836755955384320000000000), (879074353108309562007251006222487078551/219403312836745382113807431180288000000000)],
    ![(4722511350011605040450042029486765075720921/1198234625839078780184206984152612864000000000), (83946539205962513589975782451703546936642847/21568223265103418043315725714747031552000000000), (53963686897680981061261076772598948380341/14041812021551704455283675595538432000000000), (83242054414865958298591754926200583331/21940331283674538211380743118028800000000)]]

private theorem tensor102 (u v : ℝ) :
    eval poly063 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern102 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly063, bern102, Fin.sum_univ_succ]
  <;> ring

private theorem cert102 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly063 δ p := by
  apply positive_on_box_from_tensor (β := bern102) (m := (1/1000000000000000))
    tensor102 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern102]

private def bern103 : Coeff :=
  ![![(4937461206774845357247197759/18304389790603694571520000000000), (41386455163346204256719554117/164739508115433251143680000000000), (4792008867543778817069066441/20592438514429156392960000000000), (1914389327906878447216727/8937690327443210240000000000)],
    ![(224825626268884212448899673/1171480946598636452577280000000), (45754253933427828817167737099/263583212984693201829888000000000), (5115393968910894272728261831/32947901623086650228736000000000), (1958143496339640091178521/14300304523909136384000000000)],
    ![(5324839833171408421276559199/46859237863945458103091200000000), (13424342853482866005918794807/140577713591836374309273600000000), (1359292156686734390896643299/17572214198979546788659200000000), (1354903146086952955032183/22880487238254618214400000000)]]

private theorem tensor103 (u v : ℝ) :
    eval poly064 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern103 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly064, bern103, Fin.sum_univ_succ]
  <;> ring

private theorem cert103 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly064 δ p := by
  apply positive_on_box_from_tensor (β := bern103) (m := (1/1000000000000000))
    tensor103 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern103]

private def bern104 : Coeff :=
  ![![(1043812721658730/490961993084649), (801965143930625/490961993084649), (1187934585131697543575472248635/964174714614603729992317812804), (296293462314218738391411460495/321391571538201243330772604268)],
    ![(566759816867596/490961993084649), (1744757503194827/1963847972338596), (2589440910367271086988267107867/3856698858458414919969271251216), (647042581706788522685550845263/1285566286152804973323090417072)],
    ![(89706912076462/490961993084649), (140827215333577/981923986169298), (213571740103875999837322610597/1928349429229207459984635625608), (54455657078351045902727924273/642783143076402486661545208536)]]

private theorem tensor104 (u v : ℝ) :
    eval poly065 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern104 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly065, bern104, Fin.sum_univ_succ]
  <;> ring

private theorem cert104 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly065 δ p := by
  apply positive_on_box_from_tensor (β := bern104) (m := (1/1000000000000000))
    tensor104 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern104]

private def bern105 : Coeff :=
  ![![(4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000)],
    ![(4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000)],
    ![(4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000), (4506816185952085117/500000000000000000000)]]

private theorem tensor105 (u v : ℝ) :
    eval poly066 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern105 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly066, bern105, Fin.sum_univ_succ]
  <;> ring

private theorem cert105 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly066 δ p := by
  apply positive_on_box_from_tensor (β := bern105) (m := (1/1000000000000000))
    tensor105 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern105]

private def bern106 : Coeff :=
  ![![1, (442629977539028/490961993084649), (394297961993407/490961993084649), (115321982149262/163653997694883)],
    ![1, (442629977539028/490961993084649), (394297961993407/490961993084649), (115321982149262/163653997694883)],
    ![1, (442629977539028/490961993084649), (394297961993407/490961993084649), (115321982149262/163653997694883)]]

private theorem tensor106 (u v : ℝ) :
    eval poly067 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern106 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly067, bern106, Fin.sum_univ_succ]
  <;> ring

private theorem cert106 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly067 δ p := by
  apply positive_on_box_from_tensor (β := bern106) (m := (1/1000000000000000))
    tensor106 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern106]

private def bern107 : Coeff :=
  ![![(10458607679243154888525/58574047329931822628864), (10448960615495304684655/58574047329931822628864), (20389295136580551225/114402436191273091072), (19893041920747695/111721129093040128)],
    ![(41864745521839991017545/234296189319727290515456), (125478387913034919734857/702888567959181871546368), (81616279952515192005/457609744765092364288), (79629828674065411/446884516372160512)],
    ![(20947530163353681240495/117148094659863645257728), (62784624220063091626927/351444283979590935773184), (40837689679354089555/228804872382546182144), (39843744832570021/223442258186080256)]]

private theorem tensor107 (u v : ℝ) :
    eval poly068 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern107 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly068, bern107, Fin.sum_univ_succ]
  <;> ring

private theorem cert107 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly068 δ p := by
  apply positive_on_box_from_tensor (β := bern107) (m := (1/1000000000000000))
    tensor107 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern107]

private def bern108 : Coeff :=
  ![![(1414401919729455249200917/21965267748724433485824000), (4244727682358794578903541/65895803246173300457472000), (132695205801748818608983/2059243851442915639296000), (86420948671058524523/1340653549116481536000)],
    ![(5636633453924267782163569/87861070994897733943296000), (84580106187194275749016853/1317916064923466009149440000), (2644082816384157228850103/41184877028858312785920000), (1722028271894537016907/26813070982329630720000)],
    ![(561565922893071456752347/8786107099489773394329600), (42132829363606329959981443/658958032461733004574720000), (1317130758366669042760273/20592438514429156392960000), (857818785183951771677/13406535491164815360000)]]

private theorem tensor108 (u v : ℝ) :
    eval poly069 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern108 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly069, bern108, Fin.sum_univ_succ]
  <;> ring

private theorem cert108 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly069 δ p := by
  apply positive_on_box_from_tensor (β := bern108) (m := (1/1000000000000000))
    tensor108 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern108]

private def bern109 : Coeff :=
  ![![(25/74), (41834146760039155/217987124929584156), (754357664913143815289086737085/8918616110185084502428939768437), (188499946445245807482181357825/11891488146913446003238586357916)],
    ![(307/296), (543406426739633365/871948499718336624), (25578311891015839264489661263721/71348928881480676019431518147496), (9268575718635239951326360711285/47565952587653784012954345431664)],
    ![(257/148), (459738133219555055/435974249859168312), (22560881231363264003333314315381/35674464440740338009715759073748), (8891575825744748336361997995635/23782976293826892006477172715832)]]

private theorem tensor109 (u v : ℝ) :
    eval poly070 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern109 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly070, bern109, Fin.sum_univ_succ]
  <;> ring

private theorem cert109 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly070 δ p := by
  apply positive_on_box_from_tensor (β := bern109) (m := (1/1000000000000000))
    tensor109 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern109]

private def bern110 : Coeff :=
  ![![(5/2), (11460629337696425/5891543917015788), (1428599481239130657151289041255/964174714614603729992317812804), (178250301435677272775495329325/160695785769100621665386302134)],
    ![(11/8), (25213384542932135/23566175668063152), (3142918858726087445732835890761/3856698858458414919969271251216), (392150663158490000106089724515/642783143076402486661545208536)],
    ![(1/4), (2292125867539285/11783087834031576), (285719896247826131430257808251/1928349429229207459984635625608), (35650060287135454555099065865/321391571538201243330772604268)]]

private theorem tensor110 (u v : ℝ) :
    eval poly071 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern110 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly071, bern110, Fin.sum_univ_succ]
  <;> ring

private theorem cert110 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly071 δ p := by
  apply positive_on_box_from_tensor (β := bern110) (m := (1/1000000000000000))
    tensor110 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern110]

private def bern111 : Coeff :=
  ![![(54762183222026311646215821839417027168563811/1380366288966618754772206445743810019328000000), (41053771025963028589109486172867744324275563/1035274716724964066079154834307857514496000000), (40074159313963527225711272133613009961131/1011010465551722720780424642878767104000000), (10431452850564585873437223229930324927/263283975404094458536568917416345600000)],
    ![(219530325199734914806928870600564647037065127/5521465155866475019088825782975240077312000000), (822878374591274074468574718524708011566434891/20705494334499281321583096686157150289920000000), (803240940291939314167472051550489201644939/20220209311034454415608492857575342080000000), (209086039758151299459822309160116858143/5265679508081889170731378348326912000000)],
    ![(22001191751136458302899445384346118539987501/552146515586647501908882578297524007731200000), (412340664331643788577479856796030568323679261/10352747167249640660791548343078575144960000000), (402499347152304041910359330214359102033629/10110104655517227207804246428787671040000000), (104771511252505440725450076860813608873/2632839754040944585365689174163456000000)]]

private theorem tensor111 (u v : ℝ) :
    eval poly072 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern111 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly072, bern111, Fin.sum_univ_succ]
  <;> ring

private theorem cert111 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly072 δ p := by
  apply positive_on_box_from_tensor (β := bern111) (m := (1/1000000000000000))
    tensor111 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern111]

private def bern112 : Coeff :=
  ![![(207990837092274303740910357378795716749074229/57515262040275781448841935239325417472000000000), (11476663607037742797177300196658508807361357/3195292335570876747157885291073634304000000000), (300540972594251314766595024776101965136543/84250872129310226731702053573230592000000000), (25909286318386589839113918308733527777/7313443761224846070460247706009600000000)],
    ![(807415133095073294202650688810618540063259153/230061048161103125795367740957301669888000000000), (668172558581847159844455852589697156819864647/191717540134252604829473117464418058240000000000), (5831542812158052932303861009493634398087167/1685017442586204534634041071464611840000000000), (502646049276799032389750547187843473793/146268875224496921409204954120192000000000)],
    ![(78286691782104937344165994810605421313022139/23006104816110312579536774095730166988800000000), (323872650370714875929136846689941892599023937/95858770067126302414736558732209029120000000000), (2826133086215539784637910761732614746721737/842508721293102267317020535732305920000000000), (243553186092933133998611364100508196023/73134437612248460704602477060096000000000)]]

private theorem tensor112 (u v : ℝ) :
    eval poly073 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern112 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly073, bern112, Fin.sum_univ_succ]
  <;> ring

private theorem cert112 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly073 δ p := by
  apply positive_on_box_from_tensor (β := bern112) (m := (1/1000000000000000))
    tensor112 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern112]

private def bern113 : Coeff :=
  ![![(19758463214030395853137205591/187436951455781832412364800000000), (18058472237464045488660939981/187436951455781832412364800000000), (3067225772881514260361359843/35144428397959093577318400000000), (1789387521086952955032183/22880487238254618214400000000)],
    ![(373419107270018372779725690611/5623108543673454972370944000000000), (107561733444176647137538610411/1874369514557818324123648000000000), (10198227820769748274766519843/210866570387754561463910400000000), (9001539845587173596054577/228804872382546182144000000000)],
    ![(61378928034942824318199237277/2249243417469381988948377600000000), (343267043762492504467568268957/18743695145578183241236480000000000), (98463968679078628076270031161/10543328519387728073195520000000000), (833920109091013621266663/2288048723825461821440000000000)]]

private theorem tensor113 (u v : ℝ) :
    eval poly074 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern113 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly074, bern113, Fin.sum_univ_succ]
  <;> ring

private theorem cert113 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly074 δ p := by
  apply positive_on_box_from_tensor (β := bern113) (m := (1/1000000000000000))
    tensor113 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern113]

private def bern114 : Coeff :=
  ![![(1043250221658730/490961993084649), (801590143930625/490961993084649), (1187498178512316266262972248635/964174714614603729992317812804), (296225277189650947828911460495/321391571538201243330772604268)],
    ![(566281691867596/490961993084649), (1743482503194827/1963847972338596), (2587928483562412046775767107867/3856698858458414919969271251216), (646782107984295337423050845263/1285566286152804973323090417072)],
    ![(89313162076462/490961993084649), (140302215333577/981923986169298), (212932126537779514249822610597/1928349429229207459984635625608), (54331553604993441765227924273/642783143076402486661545208536)]]

private theorem tensor114 (u v : ℝ) :
    eval poly075 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern114 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly075, bern114, Fin.sum_univ_succ]
  <;> ring

private theorem cert114 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly075 δ p := by
  apply positive_on_box_from_tensor (β := bern114) (m := (1/1000000000000000))
    tensor114 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern114]

private def bern115 : Coeff :=
  ![![(4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000)],
    ![(4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000)],
    ![(4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000), (4131816185952085117/500000000000000000000)]]

private theorem tensor115 (u v : ℝ) :
    eval poly076 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern115 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly076, bern115, Fin.sum_univ_succ]
  <;> ring

private theorem cert115 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly076 δ p := by
  apply positive_on_box_from_tensor (β := bern115) (m := (1/1000000000000000))
    tensor115 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern115]

private def bern116 : Coeff :=
  ![![3, (2475911999243413/944439529144734), (1059252705526312/472219764572367), (587032940953945/314813176381578)],
    ![3, (2475911999243413/944439529144734), (1059252705526312/472219764572367), (587032940953945/314813176381578)],
    ![3, (2475911999243413/944439529144734), (1059252705526312/472219764572367), (587032940953945/314813176381578)]]

private theorem tensor116 (u v : ℝ) :
    eval poly029 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern116 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly029, bern116, Fin.sum_univ_succ]
  <;> ring

private theorem cert116 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly029 δ p := by
  apply positive_on_box_from_tensor (β := bern116) (m := (1/1000000000000000))
    tensor116 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern116]

private def bern117 : Coeff :=
  ![![2, (844439529144734/472219764572367), (744439529144734/472219764572367), (214813176381578/157406588190789)],
    ![2, (844439529144734/472219764572367), (744439529144734/472219764572367), (214813176381578/157406588190789)],
    ![2, (844439529144734/472219764572367), (744439529144734/472219764572367), (214813176381578/157406588190789)]]

private theorem tensor117 (u v : ℝ) :
    eval poly030 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern117 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly030, bern117, Fin.sum_univ_succ]
  <;> ring

private theorem cert117 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly030 δ p := by
  apply positive_on_box_from_tensor (β := bern117) (m := (1/1000000000000000))
    tensor117 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern117]

private def bern118 : Coeff :=
  ![![1, (424206688695376/472219764572367), (376193612818385/472219764572367), (109393512313798/157406588190789)],
    ![1, (424206688695376/472219764572367), (376193612818385/472219764572367), (109393512313798/157406588190789)],
    ![1, (424206688695376/472219764572367), (376193612818385/472219764572367), (109393512313798/157406588190789)]]

private theorem tensor118 (u v : ℝ) :
    eval poly031 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern118 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly031, bern118, Fin.sum_univ_succ]
  <;> ring

private theorem cert118 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly031 δ p := by
  apply positive_on_box_from_tensor (β := bern118) (m := (1/1000000000000000))
    tensor118 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern118]

private def bern119 : Coeff :=
  ![![(5/2), (12379559996217065/5666637174868404), (2648131763815780/1416659293717101), (2935164704769725/1888879058289468)],
    ![(17/8), (39601624928848553/22666548699473616), (3992104233914459/2833318587434202), (8390680937927597/7555516233157872)],
    ![(7/4), (14842504936414423/11333274349736808), (1343972470098679/1416659293717101), (2520351528388147/3777758116578936)]]

private theorem tensor119 (u v : ℝ) :
    eval poly032 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern119 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly032, bern119, Fin.sum_univ_succ]
  <;> ring

private theorem cert119 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly032 δ p := by
  apply positive_on_box_from_tensor (β := bern119) (m := (1/1000000000000000))
    tensor119 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern119]

private def bern120 : Coeff :=
  ![![(79374232953789380933325/450704098969585708957696), (238011254123998889554637/1352112296908757126873088), (77441355001193055765/440140721649986043904), (37795458504417209/214912461743157248)],
    ![(45373114351297837147125/257545199411191833690112), (136055637306772158283765/772635598233575501070336), (44268213061463468925/251508983799992025088), (21605218681975105/122807120996089856)],
    ![(158863334551506098163225/901408197939171417915392), (158788984299802442959027/901408197939171417915392), (154994781427858170945/880281443299972087808), (75645613764991317/429824923486314496)]]

private theorem tensor120 (u v : ℝ) :
    eval poly033 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern120 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly033, bern120, Fin.sum_univ_succ]
  <;> ring

private theorem cert120 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly033 δ p := by
  apply positive_on_box_from_tensor (β := bern120) (m := (1/1000000000000000))
    tensor120 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern120]

private def bern121 : Coeff :=
  ![![(17715121251921276332210371/281690061855991068098560000), (159463993551693700383699977/2535210556703919612887040000), (498412081271322595784507/7922532989699748790272000), (811359195112508533691/12894747704589434880000)],
    ![(404158429806836076747859/6438629985279795842252800), (18190327395057750533160349/289738349337590812901376000), (284273781851793177083987/4527161708399856451584000), (92553269814446318839/1473685451953078272000)],
    ![(35297482712353760766454583/563380123711982136197120000), (317733471723633867893212261/5070421113407839225774080000), (198618462083981409603779/3169013195879899516108800), (1616646053280604091983/25789495409178869760000)]]

private theorem tensor121 (u v : ℝ) :
    eval poly034 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern121 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly034, bern121, Fin.sum_univ_succ]
  <;> ring

private theorem cert121 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly034 δ p := by
  apply positive_on_box_from_tensor (β := bern121) (m := (1/1000000000000000))
    tensor121 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern121]

private def bern122 : Coeff :=
  ![![(25/74), (40136930684479645/209665575470130948), (77286268840095277715209769230/916742858216991497673784373277), (60337819876331638441590360175/3666971432867965990695137493108)],
    ![(307/296), (517631690642958811/838662301880523792), (2579669617488788377569796035199/7333942865735931981390274986216), (2780893828153590869747031721795/14667885731471863962780549972432)],
    ![(257/148), (437357829273999521/419331150940261896), (252280504680934140745439662031/407441270318662887855015277012), (2660218188400927592863851001445/7333942865735931981390274986216)]]

private theorem tensor122 (u v : ℝ) :
    eval poly035 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern122 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly035, bern122, Fin.sum_univ_succ]
  <;> ring

private theorem cert122 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly035 δ p := by
  apply positive_on_box_from_tensor (β := bern122) (m := (1/1000000000000000))
    tensor122 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern122]

private def bern123 : Coeff :=
  ![![(5/2), (10939167719907335/5666637174868404), (1299680024535739279519977427235/891966024211126862601519930756), (160543988137126091525765082775/148661004035187810433586655126)],
    ![(11/8), (24066168983796137/22666548699473616), (2859296053978626414943950339917/3567864096844507450406079723024), (353196773901677401356683182105/594644016140751241734346620504)],
    ![(1/4), (2187833543981467/11333274349736808), (259936004907147855903995485447/1783932048422253725203039861512), (32108797627425218305153016555/297322008070375620867173310252)]]

private theorem tensor123 (u v : ℝ) :
    eval poly036 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern123 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly036, bern123, Fin.sum_univ_succ]
  <;> ring

private theorem cert123 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly036 δ p := by
  apply positive_on_box_from_tensor (β := bern123) (m := (1/1000000000000000))
    tensor123 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern123]

private def bern124 : Coeff :=
  ![![(63753541023377913344078005057695156716171779/1621572445769284264203434320630351134720000000), (71706480227093801653195292982693420239386297/1824269001490444797228863610709145026560000000), (555634935810602655652525964168167508807/14138989656888988073760413649469440000000), (4556911393435972477979642277050239957/115983899529167480292565893218304000000)],
    ![(10211708218309199817986587689585555228146437/259451591323085482272549491300856181555200000), (57427803138514969750884145584122093109065819/1459415201192355837783090888567316021248000000), (3114950070595420995766130076670605975427/79178342078578333213058316437028864000000), (3649503605919106528949446946853791471/92787119623333984234052714574643200000)],
    ![(127785623410974168761508682124248567271317367/3243144891538568528406868641260702269440000000), (143726055238387245448030141955223625066556501/3648538002980889594457727221418290053120000000), (7795861251628667799695286884998684753837/197945855196445833032645791092572160000000), (9133695242723587688787950180168477441/231967799058334960585131786436608000000)]]

private theorem tensor124 (u v : ℝ) :
    eval poly037 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern124 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly037, bern124, Fin.sum_univ_succ]
  <;> ring

private theorem cert124 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly037 δ p := by
  apply positive_on_box_from_tensor (β := bern124) (m := (1/1000000000000000))
    tensor124 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern124]

private def bern125 : Coeff :=
  ![![(182392568639222220648990452969975190626809031/67565518573720177675143096692931297280000000000), (1225691956607235624159596088620379145886553823/456067250372611199307215902677286256640000000000), (1787453192005563230709703695932763319382557/668067261288004686485179544937431040000000000), (231700536748319926311070300158637941289/86987924646875610219424419913728000000000)],
    ![(28615745978064802674939715590879215835224993/10810482971795228428022895470869007564800000000), (961429149991928893917627479802783607614685421/364853800298088959445772722141829005312000000000), (1401968813138710616310276566469065383146311/534453809030403749188143635949944832000000000), (181718084259514876740835819956288817067/69590339717500488175539535930982400000000)],
    ![(50086930310453660796501711976004287803858109/19304433878205765050040884769408942080000000000), (2355761836745173221268945221773159746300319459/912134500745222398614431805354572513280000000000), (3434937681682426620131975440479800276966441/1336134522576009372970359089874862080000000000), (63598478257276361583148357066309743251/24853692756250174348406977118208000000000)]]

private theorem tensor125 (u v : ℝ) :
    eval poly038 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern125 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly038, bern125, Fin.sum_univ_succ]
  <;> ring

private theorem cert125 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly038 δ p := by
  apply positive_on_box_from_tensor (β := bern125) (m := (1/1000000000000000))
    tensor125 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern125]

private def bern126 : Coeff :=
  ![![(4159613696078638276638380653361/72112655835133713433231360000000000), (34573771724553749769423642663107/649013902516203420899082240000000000), (198194487006265979043832277299/4056336890726271380619264000000000), (293462763734345520764135587/6602110824749790658560000000000)],
    ![(5551202654856215674855892020973/144225311670267426866462720000000000), (44250637753481655765805774057271/1298027805032406841798164480000000000), (240879000347842872531198219751/8112673781452542761238528000000000), (333972515328157897203675031/13204221649499581317120000000000)],
    ![(5558335474508220410740799951289/288450623340534853732925440000000000), (1839777676119052003404576569903/123621695717372080171253760000000000), (11352502470437748676177108613/1081689837527005701498470400000000), (53768751899739506638612201/8802814432999720878080000000000)]]

private theorem tensor126 (u v : ℝ) :
    eval poly039 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern126 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly039, bern126, Fin.sum_univ_succ]
  <;> ring

private theorem cert126 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly039 δ p := by
  apply positive_on_box_from_tensor (β := bern126) (m := (1/1000000000000000))
    tensor126 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern126]

private def bern127 : Coeff :=
  ![![(1007229079108810/472219764572367), (36531604748755/22486655455827), (1081425927136405908099076884695/891966024211126862601519930756), (266524451924418840196305029915/297322008070375620867173310252)],
    ![(545034834956305/472219764572367), (79234145234113/89946621823308), (2350989094452378995336260377239/3567864096844507450406079723024), (580724205184178647935529311995/1189288032281502483468693241008)],
    ![(82840590803800/472219764572367), (6170935736603/44973310911654), (188137240179567179138106607849/1783932048422253725203039861512), (47675301335340967542919252165/594644016140751241734346620504)]]

private theorem tensor127 (u v : ℝ) :
    eval poly040 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern127 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly040, bern127, Fin.sum_univ_succ]
  <;> ring

private theorem cert127 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly040 δ p := by
  apply positive_on_box_from_tensor (β := bern127) (m := (1/1000000000000000))
    tensor127 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern127]

private def bern128 : Coeff :=
  ![![(3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000)],
    ![(3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000)],
    ![(3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000), (3066544978453549211/500000000000000000000)]]

private theorem tensor128 (u v : ℝ) :
    eval poly041 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern128 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly041, bern128, Fin.sum_univ_succ]
  <;> ring

private theorem cert128 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly041 δ p := by
  apply positive_on_box_from_tensor (β := bern128) (m := (1/1000000000000000))
    tensor128 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern128]

private def bern129 : Coeff :=
  ![![(10154765822712289164190233/57690124668106970746585088), (10154171330575051632656563/57690124668106970746585088), (1239450300362773691457/7042251546399776702464), (75645613764991317/429824923486314496)],
    ![(162483595727259759157169679/923041994689711531945361408), (487422250269621079347195407/2769125984069134595836084224), (19832101009926116426791/112676024742396427239424), (1210384516996017971/6877198775781031936)],
    ![(81245469145561445843647815/461520997344855765972680704), (243722138335819840163437895/1384562992034567297918042112), (9916498607023926895135/56338012371198213619712), (605219606876087435/3438599387890515968)]]

private theorem tensor129 (u v : ℝ) :
    eval poly033 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern129 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly033, bern129, Fin.sum_univ_succ]
  <;> ring

private theorem cert129 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly033 δ p := by
  apply positive_on_box_from_tensor (β := bern129) (m := (1/1000000000000000))
    tensor129 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern129]

private def bern130 : Coeff :=
  ![![(1356051376977031040058799969/21633796750540114029969408000), (20341218837331074899530951397/324506951258101710449541120000), (39729818281845645634096907/633802639175979903221760000), (1616646053280604091983/25789495409178869760000)],
    ![(21691727669945108667943276039/346140748008641824479510528000), (325383088553331187809421418531/5192111220129627367192657920000), (635527853715263982804819821/10140842226815678451548160000), (25860264515545252496329/412631926546861916160000)],
    ![(10843316654128860347472876287/173070374004320912239755264000), (32530667570936517722634761471/519211122012962736719265792000), (63537861492099763546408913/1014084222681567845154816000), (2585419217860083952093/41263192654686191616000)]]

private theorem tensor130 (u v : ℝ) :
    eval poly034 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern130 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly034, bern130, Fin.sum_univ_succ]
  <;> ring

private theorem cert130 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly034 δ p := by
  apply positive_on_box_from_tensor (β := bern130) (m := (1/1000000000000000))
    tensor130 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern130]

private def bern131 : Coeff :=
  ![![(4359141364181211975895434759352895324970583569/110699345631183139102954449621698637463552000000), (9194802072281746296827307063423815158287588437/233506432190776934045294542170770563399680000000), (187063402504492694782165927883615170004231/4750700524714699992783498986221731840000000), (9133695242723587688787950180168477441/231967799058334960585131786436608000000)],
    ![(9965106905117267696159816943315762332596723377/253027075728418603663895884849596885630976000000), (147136841649223966058263434583174787152701117491/3736102915052430944724712674732329014394880000000), (2993421470931585246148624304316914254643153/76011208395435199884535983779547709440000000), (146158996339429045753435868508763636583/3711484784933359369362108582985728000000)],
    ![(34882617422371178065955240528387173728412395087/885594765049465112823635596973589099708416000000), (14715685014193999136728995615156853177280081999/373610291505243094472471267473232901439488000000), (299382850179128737578259376249598578921861/7601120839543519988453598377954770944000000), (14617886879528068848626453413483163411/371148478493335936936210858298572800000)]]

private theorem tensor131 (u v : ℝ) :
    eval poly037 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern131 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly037, bern131, Fin.sum_univ_succ]
  <;> ring

private theorem cert131 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly037 δ p := by
  apply positive_on_box_from_tensor (β := bern131) (m := (1/1000000000000000))
    tensor131 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern131]

private def bern132 : Coeff :=
  ![![(136814624765247974385636579625072108887062629303/53372898786463299210353038210461843062784000000000), (448662744905822909961182342681148946250063918249/175129824143082700533970906628077922549760000000000), (27368317019460667011102365171673482857182761/10689076180608074983762872718998896640000000000), (63598478257276361583148357066309743251/24853692756250174348406977118208000000000)],
    ![(15284117826395835656309421154136778057130860315751/5977764664083889511559540279571726423031808000000000), (7160268031445511754567536429251299842839263876607/2802077186289323208543534506049246760796160000000000), (436774041235640854250354521853526930485948543/171025218889729199740205963503982346240000000000), (7104817839119247175772513890573583564291/2783613588700019527021581437239296000000000)],
    ![(7622498839541949090713772695132739959455353074783/2988882332041944755779770139785863211515904000000000), (714193214439785694975615537560421654567750506123/280207718628932320854353450604924676079616000000000), (43565501015991103632307120096027813525697291/17102521888972919974020596350398234624000000000), (708660611342354185423241178972047588447/278361358870001952702158143723929600000000)]]

private theorem tensor132 (u v : ℝ) :
    eval poly038 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern132 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly038, bern132, Fin.sum_univ_succ]
  <;> ring

private theorem cert132 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly038 δ p := by
  apply positive_on_box_from_tensor (β := bern132) (m := (1/1000000000000000))
    tensor132 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern132]

private def bern133 : Coeff :=
  ![![(28626383474936983033647125202959/3692167978758846127781445632000000000), (57003565336083397109502887000431/7911788525911813130960240640000000000), (1440055802612942067661144485629/216337967505401140299694080000000000), (53768751899739506638612201/8802814432999720878080000000000)],
    ![(67783492409859119532279481719029/12658861641458901009536385024000000000), (1277722581013235549681415837246977/265836094470636921200264085504000000000), (884369069113503690344130527249/207684448805185094687706316800000000), (156762254127330176967035873/42253509278398660214784000000000)],
    ![(419035620868739838963961645463881/141779250384339691306807512268800000000), (1024016151844454206628806917986323/425337751153019073920422536806400000000), (3089556155665220884325006378063/1661475590441480757501650534400000000), (88665888590415915876280243/67605614845437856343654400000000)]]

private theorem tensor133 (u v : ℝ) :
    eval poly039 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern133 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly039, bern133, Fin.sum_univ_succ]
  <;> ring

private theorem cert133 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly039 δ p := by
  apply positive_on_box_from_tensor (β := bern133) (m := (1/1000000000000000))
    tensor133 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern133]

private def bern134 : Coeff :=
  ![![(547624099/400000000), (19834253216542963/16186759200000000), (1094241117281939/1011672450000000), (1012097502431939/1079117280000000)],
    ![(5578359683/8000000000), (175568665699162103/323735184000000000), (24913136155746792936991/60650734583052000000000), (8157423677031454283063/26955882036912000000000)],
    ![(1227118693/4000000000), (32739159789462973/161867592000000000), (2664520897715550961889/20216911527684000000000), (3433874960761878522289/40433823055368000000000)]]

private theorem tensor134 (u v : ℝ) :
    eval poly077 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern134 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly077, bern134, Fin.sum_univ_succ]
  <;> ring

private theorem cert134 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly077 δ p := by
  apply positive_on_box_from_tensor (β := bern134) (m := (1/1000000000000000))
    tensor134 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern134]

private def bern135 : Coeff :=
  ![![(246878819/400000000), (8941639016231603/16186759200000000), (493303627851859/1011672450000000), (456271805001859/1079117280000000)],
    ![(2174469923/8000000000), (69461207651469943/323735184000000000), (30188960155547086382413/181952203749156000000000), (30537461646603286777327/242602938332208000000000)],
    ![(830681733/4000000000), (22109685850218413/161867592000000000), (16183956827614611204281/181952203749156000000000), (6967310219424928714627/121301469166104000000000)]]

private theorem tensor135 (u v : ℝ) :
    eval poly078 (0+((3/4)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern135 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly078, bern135, Fin.sum_univ_succ]
  <;> ring

private theorem cert135 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly078 δ p := by
  apply positive_on_box_from_tensor (β := bern135) (m := (1/1000000000000000))
    tensor135 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern135]

private def bern136 : Coeff :=
  ![![(523985310831939/5899264400000000), (6326028721628416613681/79574976916610400000000), (349002337559086021393/4973436057288150000000), (322803072017489071393/5304998461107360000000)],
    ![(7270102750781743/235970576000000000), (83707677415342301854481/3182999076664416000000000), (6004131171728432074477/265249923055368000000000), (21030619585999351288489/1060999692221472000000000)],
    ![(5086237096642963/117985288000000000), (40010041528182859120111/1591499538332208000000000), (23232566146321788146089/1591499538332208000000000), (50298315924074840709/5526040063653500000000)]]

private theorem tensor136 (u v : ℝ) :
    eval poly079 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern136 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern136, Fin.sum_univ_succ]
  <;> ring

private theorem cert136 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern136) (m := (1/1000000000000000))
    tensor136 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern136]

private def bern137 : Coeff :=
  ![![(5086237096642963/117985288000000000), (108618120792738501166369/3182999076664416000000000), (19095636496360349825841/707333128147648000000000), (1818812115161354253127/84879975377717760000000)],
    ![(13074845635790109/235970576000000000), (252698636933810298063257/6365998153328832000000000), (87477954038936350094963/3182999076664416000000000), (7714291451479377216973/424399876888588800000000)],
    ![(8142224550823573/58992644000000000), (169402882987732030718069/1591499538332208000000000), (129615754043197884030977/1591499538332208000000000), (34168098736398270427/552604006365350000000)]]

private theorem tensor137 (u v : ℝ) :
    eval poly079 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern137 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern137, Fin.sum_univ_succ]
  <;> ring

private theorem cert137 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern137) (m := (1/1000000000000000))
    tensor137 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern137]

private def bern138 : Coeff :=
  ![![(1818812115161354253127/84879975377717760000000), (33653696268986663178827/2121999384442944000000000), (37718481132455342270281/3182999076664416000000000), (50298315924074840709/5526040063653500000000)],
    ![(350174000568461426721/17683328203691200000000), (31486784854693721171149/2546399261331532800000000), (2025987866133173663611/282933251259059200000000), (83591688276502704841/22336835625715200000000)],
    ![(50763743308319397387517/1697599507554355200000000), (482676738453801836689181/25463992613315328000000000), (17820462670004326552327/1591499538332208000000000), (12646193402151515646409/2121999384442944000000000)]]

private theorem tensor138 (u v : ℝ) :
    eval poly079 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern138 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern138, Fin.sum_univ_succ]
  <;> ring

private theorem cert138 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern138) (m := (1/1000000000000000))
    tensor138 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern138]

private def bern139 : Coeff :=
  ![![(50763743308319397387517/1697599507554355200000000), (482676738453801836689181/25463992613315328000000000), (17820462670004326552327/1591499538332208000000000), (12646193402151515646409/2121999384442944000000000)],
    ![(33955391281033248904909/848799753777177600000000), (9034522616120367523151/353666564073824000000000), (193957948744076409974737/12731996306657664000000000), (5783725472678424777641/707333128147648000000000)],
    ![(34168098736398270427/552604006365350000000), (3536447088339797559397/83763133596432000000000), (14852121419416189971067/530499846110736000000000), (4766810672297471697289/265249923055368000000000)]]

private theorem tensor139 (u v : ℝ) :
    eval poly079 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern139 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly079, bern139, Fin.sum_univ_succ]
  <;> ring

private theorem cert139 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < eval poly079 δ p := by
  apply positive_on_box_from_tensor (β := bern139) (m := (1/1000000000000000))
    tensor139 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern139]

private def bern140 : Coeff :=
  ![![(12630249467/200000000000), (457451683689663179/8093379600000000000), (25237271905230187/505836225000000000), (23342734485180187/539558640000000000)],
    ![(171363460933/16000000000000), (65555993377399477667328462839/7200671971772143584000000000000), (117061192211283608968371226727/14401343943544287168000000000000), (37363041711739812210149742877/4800447981181429056000000000000)],
    ![(228653482253/8000000000000), (23494890312552293919120299/1800167992943035896000000000), (135128030650767725201594325583/28802687887088574336000000000000), (86434202802181364602313419/76807167698902864896000000000)]]

private theorem tensor140 (u v : ℝ) :
    eval poly080 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern140 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern140, Fin.sum_univ_succ]
  <;> ring

private theorem cert140 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern140) (m := (1/1000000000000000))
    tensor140 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern140]

private def bern141 : Coeff :=
  ![![(228653482253/8000000000000), (74946725340904679854867543211/3600335985886071792000000000000), (74356255700264317634147817433/5009163110798012928000000000000), (3185041351279025960560507691/307228670795611459584000000000)],
    ![(743250468079/16000000000000), (456897054966955223306958720107/14401343943544287168000000000000), (1035798597376260836459866547/50708957547691152000000000000), (499250305311607559837514767/41743025923316774400000000000)],
    ![(538548492913/4000000000000), (372541587473084332081802813963/3600335985886071792000000000000), (454223561475682291003035173293/5760537577417714867200000000000), (22880578872848957129524719793/384035838494514324480000000000)]]

private theorem tensor141 (u v : ℝ) :
    eval poly080 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern141 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern141, Fin.sum_univ_succ]
  <;> ring

private theorem cert141 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern141) (m := (1/1000000000000000))
    tensor141 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern141]

private def bern142 : Coeff :=
  ![![(3185041351279025960560507691/307228670795611459584000000000), (234122204885353112505646418927/28802687887088574336000000000000), (2886646484839186538735076034123/460843006193417189376000000000000), (242502686011221761010187475597/51204778465935243264000000000000)],
    ![(171488089959311440024115409403/15361433539780572979200000000000), (891952088335954803482172077/112510499558939743500000000000), (964638805816394477786742367711/184337202477366875750400000000000), (309657615927302043868930707277/102409556931870486528000000000000)],
    ![(720961723593626373624712522391/30722867079561145958400000000000), (2117742953076966555824040831401/115210751548354297344000000000000), (25951807952073766195102560335743/1843372024773668757504000000000000), (2145273585400122950454111577049/204819113863740973056000000000000)]]

private theorem tensor142 (u v : ℝ) :
    eval poly080 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((3/8)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern142 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern142, Fin.sum_univ_succ]
  <;> ring

private theorem cert142 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern142) (m := (1/1000000000000000))
    tensor142 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern142]

private def bern143 : Coeff :=
  ![![(9906590214010514010317321563/1822103611473920000000000000000), (189409804426350027091512315949/40997331258163200000000000000000), (1273006334713941498629951612281/327978650065305600000000000000000), (352123312143772122516892378469/109326216688435200000000000000000)],
    ![(6683270794445381620421599097/1457682889179136000000000000000), (116727913067229349674846251231/32797865006530560000000000000000), (688951120358788418842576759139/262382920052244480000000000000000), (2646170567587737604561062629/1482389378826240000000000000000)],
    ![(7487335429216768534295988631/1166146311343308800000000000000), (133942987206691692431620186513/26238292005224448000000000000000), (818318224200390187151621745997/209906336041795584000000000000000), (196014452299862759756419571753/69968778680598528000000000000000)]]

private theorem tensor143 (u v : ℝ) :
    eval poly081 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern143 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern143, Fin.sum_univ_succ]
  <;> ring

private theorem cert143 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern143) (m := (1/1000000000000000))
    tensor143 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern143]

private def bern144 : Coeff :=
  ![![(352123312143772122516892378469/109326216688435200000000000000000), (839733538148691236471402658533/327978650065305600000000000000000), (10136450660629682693984384689/5124666407270400000000000000000), (2517540879302821538445161563/1708222135756800000000000000000)],
    ![(2189113566013471083413082989431/874609733507481600000000000000000), (4597900455431118411745807691767/2623829200522444800000000000000000), (44569832717112429686694985211/40997331258163200000000000000000), (6932537569961690181496161737/13665777086054400000000000000000)],
    ![(16779296841303983700944875153769/6996877868059852800000000000000000), (32291679273039546795096411110633/20990633604179558400000000000000000), (253142806030233072172430573989/327978650065305600000000000000000), (10761830534364898826312824663/109326216688435200000000000000000)]]

private theorem tensor144 (u v : ℝ) :
    eval poly081 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern144 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern144, Fin.sum_univ_succ]
  <;> ring

private theorem cert144 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern144) (m := (1/1000000000000000))
    tensor144 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern144]

private def bern145 : Coeff :=
  ![![(16779296841303983700944875153769/6996877868059852800000000000000000), (179629499558590212821589209939/91263624365998080000000000000000), (131122388655925961312063004417869/83962534416718233600000000000000000), (2198695761815926687998695459271/1865834098149294080000000000000000)],
    ![(1604568515450019873458508639209/699687786805985280000000000000000), (379686051830653712499908099317/209906336041795584000000000000000), (11331989008946915803469126159309/8396253441671823360000000000000000), (170854733168056453153789116231/186583409814929408000000000000000)],
    ![(196014452299862759756419571753/69968778680598528000000000000000), (47290592324918732532807719989/20990633604179558400000000000000), (1454024764547486929966559453453/839625344167182336000000000000000), (23097258716679244511995262727/18658340981492940800000000000000)]]

private theorem tensor145 (u v : ℝ) :
    eval poly081 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern145 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly081, bern145, Fin.sum_univ_succ]
  <;> ring

private theorem cert145 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    0 < eval poly081 δ p := by
  apply positive_on_box_from_tensor (β := bern145) (m := (1/1000000000000000))
    tensor145 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern145]

private def bern146 : Coeff :=
  ![![(84587909319202645795586202619/69409028451153739776000000000000), (2817098462015212886389979331481/3123406280301918289920000000000000), (7423035853121219816273013269/12200805782429368320000000000000), (1371458346244526542557844903/4066935260809789440000000000000)],
    ![(150138664253225070864389473673/138818056902307479552000000000000), (4663219364174082334180068322451/6246812560603836579840000000000000), (10636096098503126862369674599/24401611564858736640000000000000), (1209962863037284095611395373/8133870521619578880000000000000)],
    ![(293495472426400051045501244707/277636113804614959104000000000000), (8761909844700646369809423984721/12493625121207673159680000000000000), (18115793909527868702248846829/48803223129717473280000000000000), (1070497349237395394269628143/16267741043239157760000000000000)]]

private theorem tensor146 (u v : ℝ) :
    eval poly082 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern146 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern146, Fin.sum_univ_succ]
  <;> ring

private theorem cert146 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern146) (m := (1/1000000000000000))
    tensor146 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern146]

private def bern147 : Coeff :=
  ![![(293495472426400051045501244707/277636113804614959104000000000000), (2746150762986081083357122499567/3123406280301918289920000000000000), (35368759189428429424442108769481/49974500484830692638720000000000000), (291548911182912173293559229809/537360220266996695040000000000000)],
    ![(71678404086587490090555885517/69409028451153739776000000000000), (26374367120798595359448463397/31234062803019182899200000000000), (331264799369366721808356182239/499745004848306926387200000000000), (569995937672773572357055253/1168174391884775424000000000000)],
    ![(3890302661957627755615424999/3470451422557686988800000000000), (10087380740058835147077751/10951634923919769600000000000), (90986707693018198629407386321/124936251212076731596800000000000), (728638591278682448485002521/1343400550667491737600000000000)]]

private theorem tensor147 (u v : ℝ) :
    eval poly082 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern147 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern147, Fin.sum_univ_succ]
  <;> ring

private theorem cert147 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern147) (m := (1/1000000000000000))
    tensor147 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern147]

private def bern148 : Coeff :=
  ![![(291548911182912173293559229809/537360220266996695040000000000000), (18859338290593234808159907974993/49974500484830692638720000000000000), (10663642978620027442528865629/48803223129717473280000000000000), (1070497349237395394269628143/16267741043239157760000000000000)],
    ![(553747042512388016577804646189/1074720440533993390080000000000000), (34501710780939069478193937197773/99949000969661385277440000000000000), (17724944248245103178382736169/97606446259434946560000000000000), (34415927027722521373308421/1414586177672970240000000000000)],
    ![(1107400610353336839256051070969/2149440881067986780160000000000000), (67960111385211598863749199454553/199898001939322770554880000000000000), (33451700465599970975429722309/195212892518869893120000000000000), (600755171667255571321288423/65070964172956631040000000000000)]]

private theorem tensor148 (u v : ℝ) :
    eval poly082 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern148 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern148, Fin.sum_univ_succ]
  <;> ring

private theorem cert148 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern148) (m := (1/1000000000000000))
    tensor148 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern148]

private def bern149 : Coeff :=
  ![![(1107400610353336839256051070969/2149440881067986780160000000000000), (17094836814807192491456194905467/39979600387864554110976000000000000), (11876653078698169306832660180593/34764869902490916618240000000000000), (23812368902556715427874968341/92545371268204986368000000000000)],
    ![(27682678392047441133912321239/53736022026699669504000000000000), (2123704560337019247365804494033/4997450048483069263872000000000000), (6725539069216234195218177791273/19989800193932277055488000000000000), (23100857276508220970279810641/92545371268204986368000000000000)],
    ![(728638591278682448485002521/1343400550667491737600000000000), (56151729636867102248954158519/124936251212076731596800000000000), (179027094224739208963365775559/499745004848306926387200000000000), (310892424192275912234321123/1156817140852562329600000000000)]]

private theorem tensor149 (u v : ℝ) :
    eval poly082 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern149 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern149, Fin.sum_univ_succ]
  <;> ring

private theorem cert149 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern149) (m := (1/1000000000000000))
    tensor149 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern149]

#check cert149

private def bern150 : Coeff :=
  ![![(23812368902556715427874968341/92545371268204986368000000000000), (138314713826122148536528268778841/799592007757291082219520000000000000), (17626982990300868844696793789/195212892518869893120000000000000), (600755171667255571321288423/65070964172956631040000000000000)],
    ![(23456613089532468199077389491/92545371268204986368000000000000), (268475964795534839094236285004401/1599184015514582164439040000000000000), (32781305757744649380949364149/390425785037739786240000000000000), (219132871726530730791677903/130141928345913262080000000000000)],
    ![(94885477390955230347180279463/370181485072819945472000000000000), (541971552208767016383284580770761/3198368031029164328878080000000000000), (65795257686424503934100540909/780851570075479572480000000000000), (3220170886499420676898037/4411590791386890240000000000000)]]

private theorem tensor150 (u v : ℝ) :
    eval poly082 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern150 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern150, Fin.sum_univ_succ]
  <;> ring

private theorem cert150 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern150) (m := (1/1000000000000000))
    tensor150 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern150]

private def bern151 : Coeff :=
  ![![(94885477390955230347180279463/370181485072819945472000000000000), (1361782076866620206582922195331081/6396736062058328657756160000000000000), (1086625502279490995540141295832553/6396736062058328657756160000000000000), (1085517301955427843895701488401033/8528981416077771543674880000000000000)],
    ![(47972251211890293949025500481/185090742536409972736000000000000), (3439879189419821585043143099611/15991840155145821644390400000000000), (596030745867972379645317465053/3476486990249091661824000000000000), (13669036228446800855927203292087/106612267700972144295936000000000000)],
    ![(310892424192275912234321123/1156817140852562329600000000000), (223889487528450373292314399849/999490009696613852774400000000000), (179597049229300950991331253473/999490009696613852774400000000000), (180975467560764469472058135817/1332653346262151803699200000000000)]]

private theorem tensor151 (u v : ℝ) :
    eval poly082 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern151 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern151, Fin.sum_univ_succ]
  <;> ring

private theorem cert151 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern151) (m := (1/1000000000000000))
    tensor151 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern151]

private def bern152 : Coeff :=
  ![![(1085517301955427843895701488401033/8528981416077771543674880000000000000), (1083300901307301540606821873537993/12793472124116657315512320000000000000), (33182613966667450696955746729/780851570075479572480000000000000), (3220170886499420676898037/4411590791386890240000000000000)],
    ![(2179040200231171912369877751767993/17057962832155543087349760000000000000), (2170476451340395388934582392243833/25586944248233314631024640000000000000), (66109137527078110517542842329/1561703140150959144960000000000000), (131704503457335998227596743/520567713383653048320000000000000)],
    ![(4430806090895808585465226084363753/34115925664311086174699520000000000000), (4433538748405114878436819074181673/51173888496466629262049280000000000000), (136869796473066877949976651529/3123406280301918289920000000000000), (1483336966681845895217876503/1041135426767306096640000000000000)]]

private theorem tensor152 (u v : ℝ) :
    eval poly082 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern152 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern152, Fin.sum_univ_succ]
  <;> ring

private theorem cert152 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern152) (m := (1/1000000000000000))
    tensor152 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern152]

private def bern153 : Coeff :=
  ![![(4430806090895808585465226084363753/34115925664311086174699520000000000000), (4433538748405114878436819074181673/51173888496466629262049280000000000000), (136869796473066877949976651529/3123406280301918289920000000000000), (1483336966681845895217876503/1041135426767306096640000000000000)],
    ![(28147073633307958413691854157447/213224535401944288591872000000000000), (28288278713308993618777958524223/319836803102916432887808000000000000), (2998333006185964721713297/66173861870803353600000000000), (16895405790306373712378497/6507096417295663104000000000000)],
    ![(180975467560764469472058135817/1332653346262151803699200000000000), (1597672210640795708117494787/17382434951245458309120000000000), (5911583653996579314351049/122008057824293683200000000000), (220299694073537456046823/40669352608097894400000000000)]]

private theorem tensor153 (u v : ℝ) :
    eval poly082 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern153 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern153, Fin.sum_univ_succ]
  <;> ring

private theorem cert153 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern153) (m := (1/1000000000000000))
    tensor153 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern153]

private def bern154 : Coeff :=
  ![![(870782958630843633994116861709/163855291090992778444800000000000), (3038226470370274434171403225213/737348809909467503001600000000000), (18003054518285578285400179353259/5898790479275740024012800000000000), (4132378698195045330222294017063/1966263493091913341337600000000000)],
    ![(2764588817254727038191972991603/409638227727481946112000000000000), (424409804952607815850144421309/80146609772768206848000000000000), (58840148400734372649166468854709/14746976198189350060032000000000000), (603523104974603292253712417743/213724292727381884928000000000000)],
    ![(2145273585400122950454111577049/204819113863740973056000000000000), (1598528942686477673357922612229/184337202477366875750400000000000), (51940199954198826709352329028927/7373488099094675030016000000000000), (2743331612456793043791970417871/491565873272978335334400000000000)]]

private theorem tensor154 (u v : ℝ) :
    eval poly080 ((15/32)+((9/16)-(15/32))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern154 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern154, Fin.sum_univ_succ]
  <;> ring

private theorem cert154 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern154) (m := (1/1000000000000000))
    tensor154 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern154]

private def bern155 : Coeff :=
  ![![(4132378698195045330222294017063/1966263493091913341337600000000000), (4797088441367457421650116700077/2949395239637870012006400000000000), (27861709504514949676972088142851/23595161917102960096051200000000000), (2002462328668747026597433224329/2621684657455884455116800000000000)],
    ![(48423956319806978094782241301493/19662634930919133413376000000000000), (57030009371341541531926584309431/29493952396378700120064000000000000), (67797054262955848361365356867253/47190323834205920192102400000000000), (25454198013144428645664911584763/26216846574558844551168000000000000)],
    ![(131052651397774590414292420875091/39325269861838266826752000000000000), (32316859828440531243377784978749/11797580958551480048025600000000000), (44750473815770285460402994559609/20517532101828660953088000000000000), (86874856510580766108506936844637/52433693149117689102336000000000000)]]

private theorem tensor155 (u v : ℝ) :
    eval poly080 ((15/32)+((33/64)-(15/32))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern155 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern155, Fin.sum_univ_succ]
  <;> ring

private theorem cert155 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern155) (m := (1/1000000000000000))
    tensor155 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern155]

private def bern156 : Coeff :=
  ![![(3890302661957627755615424999/3470451422557686988800000000000), (22525695783676945878392666713/31234062803019182899200000000000), (42666375656428347937825109/122008057824293683200000000000), (220299694073537456046823/40669352608097894400000000000)],
    ![(83933702391717620134061114443/69409028451153739776000000000000), (491158783294421431572771102293/624681256060383657984000000000000), (958685245154659733525087137/2440161156485873664000000000000), (22758539142930368376049643/813387052161957888000000000000)],
    ![(78307571773488218278708615223/55527222760922991820800000000000), (12013499254371247490202845427361/12493625121207673159680000000000000), (26544412471615290683735643389/48803223129717473280000000000000), (2538700970154164934678682783/16267741043239157760000000000000)]]

private theorem tensor156 (u v : ℝ) :
    eval poly082 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern156 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly082, bern156, Fin.sum_univ_succ]
  <;> ring

private theorem cert156 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly082 δ p := by
  apply positive_on_box_from_tensor (β := bern156) (m := (1/1000000000000000))
    tensor156 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern156]

private def bern157 : Coeff :=
  ![![(228740895136533421223115247670269/209734772596470756409344000000000000), (202097999723391865416755869501511/235951619171029600960512000000000000), (4758564311025755727157009179917339/7550451813472947230736384000000000000), (9008735984367095838865427509291/21885367575283905016627200000000000)],
    ![(137783252536869623399836760014163/104867386298235378204672000000000000), (125807273631450298912041879802429/117975809585514800480256000000000000), (3122209356211875114415179647986837/3775225906736473615368192000000000000), (149922186504366760888285819964563/251681727115764907691212800000000000)],
    ![(86874856510580766108506936844637/52433693149117689102336000000000000), (82272514251435257458776151245887/58987904792757400240128000000000000), (430794476783672782197712006867903/377522590673647361536819200000000000), (22546557426287167040676130490521/25168172711576490769121280000000000)]]

private theorem tensor157 (u v : ℝ) :
    eval poly080 ((63/128)+((33/64)-(63/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern157 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern157, Fin.sum_univ_succ]
  <;> ring

private theorem cert157 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern157) (m := (1/1000000000000000))
    tensor157 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern157]

private def bern158 : Coeff :=
  ![![(2236366251898160816446111448513/3517190566716326805504000000000000), (9217597624309541091498874545283/21103143400297960833024000000000000), (32369296235214166893274683419/131894646251862255206400000000000), (211408488216524890723914571/3434756412808912896000000000000)],
    ![(4989241872297618743040783605599/7034381133432653611008000000000000), (21291210310952095374853724308733/42206286800595921666048000000000000), (405581420720567759255625496889/1318946462518622552064000000000000), (812159970722250163379651381/6869512825617825792000000000000)],
    ![(11374429141852890907522872935297/14068762266865307222016000000000000), (855024795439134953721664116569/1430721586460878700544000000000000), (1041402477676641387045430732039/2637892925037245104128000000000000), (2745117896925318857391089227/13739025651235651584000000000000)]]

private theorem tensor158 (u v : ℝ) :
    eval poly083 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern158 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly083, bern158, Fin.sum_univ_succ]
  <;> ring

private theorem cert158 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly083 δ p := by
  apply positive_on_box_from_tensor (β := bern158) (m := (1/1000000000000000))
    tensor158 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern158]

private def bern159 : Coeff :=
  ![![(251564164436730717732114144476473/402690763385223852305940480000000000), (15369322863358849830476857298991839/30201807253891788922945536000000000000), (47727412205670854405346135864515593/120807229015567155691782144000000000000), (633659891539735582932059536445759/2237170907695688068366336000000000000)],
    ![(375387760767238431295047124869773/503363454231529815382425600000000000), (4731147555238563235942410451236959/7550451813472947230736384000000000000), (15387696627583836649024577390838649/30201807253891788922945536000000000000), (220594055703838501598319397311911/559292726923922017091584000000000000)],
    ![(22546557426287167040676130490521/25168172711576490769121280000000000), (291900303699624867316356932602771/377522590673647361536819200000000000), (4927812415279582525205864714932969/7550451813472947230736384000000000000), (74689941596927168786104862486543/139823181730980504272896000000000000)]]

private theorem tensor159 (u v : ℝ) :
    eval poly080 ((129/256)+((33/64)-(129/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern159 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern159, Fin.sum_univ_succ]
  <;> ring

private theorem cert159 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern159) (m := (1/1000000000000000))
    tensor159 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern159]

private def bern160 : Coeff :=
  ![![(633659891539735582932059536445759/2237170907695688068366336000000000000), (10985098044753262005929501807939473/48322891606226862276712857600000000000), (2595985172116305193587860897547271/15100903626945894461472768000000000000), (7537491070781385969875317014450661/64430522141635816368950476800000000000)],
    ![(1516036114355089589325337125693403/4474341815391376136732672000000000000), (136319651809518312469260168934461097/483228916062268622767128576000000000000), (6821875363055898296888536466735357/30201807253891788922945536000000000000), (109629282839222818413256639046209117/644305221416358163689504768000000000000)],
    ![(718690280544255659259258502945147/1789736726156550454693068800000000000), (332465143370032215999162796955416781/966457832124537245534257152000000000000), (3466597430641258902551733760276439/12080722901556715569178214400000000000), (5032286577145167681133295445406819/21840854963266378430152704000000000000)]]

private theorem tensor160 (u v : ℝ) :
    eval poly080 ((129/256)+((261/512)-(129/256))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern160 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern160, Fin.sum_univ_succ]
  <;> ring

private theorem cert160 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern160) (m := (1/1000000000000000))
    tensor160 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern160]

private def bern161 : Coeff :=
  ![![(7537491070781385969875317014450661/64430522141635816368950476800000000000), (173044047169718836254766168207254401/1932915664249074491068514304000000000000), (240404949357891151714019248451476631/3865831328498148982137028608000000000000), (30044231239989703613371151730596741/859073628555144218252673024000000000000)],
    ![(185004193547036678112009809190715727/1288610442832716327379009536000000000000), (896151616656865547227975753959328007/7731662656996297964274057216000000000000), (1366479003199406704457810423662066721/15463325313992595928548114432000000000000), (41892162415056249906575509393689607/687258902844115374602138419200000000000)],
    ![(886171860824083886237397327752852009/5154441771330865309516038144000000000000), (4455263272607468033758063421230854833/30926650627985191857096228864000000000000), (7194722239407226098117826713466327271/61853301255970383714192457728000000000000), (1219251868539149181684570199711876469/13745178056882307492042768384000000000000)]]

private theorem tensor161 (u v : ℝ) :
    eval poly080 ((129/256)+((519/1024)-(129/256))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern161 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern161, Fin.sum_univ_succ]
  <;> ring

private theorem cert161 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern161) (m := (1/1000000000000000))
    tensor161 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern161]

private def bern162 : Coeff :=
  ![![(678108152373786365760208634819770219903703/3908495477728751034172335080865792000000000000), (5224799858868355239207607781557958860171733/35176459299558759307551015727792128000000000000), (33991940695526717466813666128499746658227/274816088277802807090242310373376000000000000), (35415310290655995301848169806617588899/357833448278389071732086341632000000000000)],
    ![(5764260127304573379365310790919999750914717/31267963821830008273378680646926336000000000000), (44827309895944890282673779453811458681751111/281411674396470074460408125822337024000000000000), (295399307842669413584212766499966611541553/2198528706222422456721938482987008000000000000), (313615381976758637488473141289366163393/2862667586227112573856690733056000000000000)],
    ![(425468746106034314224202823253330145120741/2175162700649044053800256045003571200000000000), (3336917042660714119184645110524623120510879/19576464305841396484202304405032140800000000000), (22242540885491610004865013529192225024313/152941127389385910032830503164313600000000000), (24003055510314428706553019324207289481/199142092954929570355248050995200000000000)]]

private theorem tensor162 (u v : ℝ) :
    eval poly084 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern162 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly084, bern162, Fin.sum_univ_succ]
  <;> ring

private theorem cert162 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly084 δ p := by
  apply positive_on_box_from_tensor (β := bern162) (m := (1/1000000000000000))
    tensor162 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern162]

private def bern163 : Coeff :=
  ![![(29353444043315082050100252201295727/478093149804601999723226726400000000000), (410403276913355247331756929817828331/8605676696482835995018081075200000000000), (585423075209101795903138651270591727/17211353392965671990036162150400000000000), (233715330838211499000958715499951953/11474235595310447993357441433600000000000)],
    ![(2057095116840274179816080387585668609/27490356113764614984085536768000000000000), (30220291650277697023136033648583864133/494826410047763069713539661824000000000000), (46856524394543694464393556245336694913/989652820095526139427079323648000000000000), (4440428743019234792115076955413749107/131953709346070151923610576486400000000000)],
    ![(1219251868539149181684570199711876469/13745178056882307492042768384000000000000), (18530355971742575709247741965288010121/247413205023881534856769830912000000000000), (30243787569214242674068519299989486069/494826410047763069713539661824000000000000), (3125637085407591853105377553403109007/65976854673035075961805288243200000000000)]]

private theorem tensor163 (u v : ℝ) :
    eval poly080 ((1035/2048)+((519/1024)-(1035/2048))*u) ((255/512)+((511/1024)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern163 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern163, Fin.sum_univ_succ]
  <;> ring

private theorem cert163 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern163) (m := (1/1000000000000000))
    tensor163 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern163]

private def bern164 : Coeff :=
  ![![(3827372778394653911605870406264124535349287/26101952407788528645603072540042854400000000000), (10502368998589904689897395704090409236875231/78305857223365585936809217620128563200000000000), (37207215606893158064743441570183423345721/305882254778771820065661006328627200000000000), (21744154526903013871426527917957289481/199142092954929570355248050995200000000000)],
    ![(182737643421967425561862538335666760216000107/1200689810758272317697741336841971302400000000000), (2515310962693755219230287274336048461221361487/18010347161374084765466120052629569536000000000000), (8945767100228473764807666642431682454054729/70352918599117518615102031455584256000000000000), (5252787525145136447371125082630335563801/45802681379633801181707051728896000000000000)],
    ![(75814209011562440422235064160827213769567909/480275924303308927079096534736788520960000000000), (5233733026181377249509712899592884492845833861/36020694322748169530932240105259139072000000000000), (162449732597539926387518299917992200671281/1223529019115087280262644025314508800000000000), (11017927511993179213972451178319744459507/91605362759267602363414103457792000000000000)]]

private theorem tensor164 (u v : ℝ) :
    eval poly085 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern164 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly085, bern164, Fin.sum_univ_succ]
  <;> ring

private theorem cert164 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly085 δ p := by
  apply positive_on_box_from_tensor (β := bern164) (m := (1/1000000000000000))
    tensor164 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern164]

private def bern165 : Coeff :=
  ![![(12396422929734320367966562953657853/367175539049934335787438125875200000000), (852337413526220787440255587974639186809/31668890243056836461666538356736000000000000), (55280813082028669970228690391197041111/2753816542874507518405785944064000000000000), (37277080958076664309210829276877121133/2815012466049496574370358965043200000000000)],
    ![(10691702913834418498325832062219967121/263907418692140303847221152972800000000000), (266438432056604472799601253109267186343/7917222560764209115416634589184000000000000), (424374713347031733290146260572547094223/15834445121528418230833269178368000000000000), (70221257468418566970523177748568683263/3518765582561870717962948706304000000000000)],
    ![(3125637085407591853105377553403109007/65976854673035075961805288243200000000000), (1129099911336804901994435933847337087/27877544228042989843016318976000000000000), (133156979586424290917394705970697923601/3958611280382104557708317294592000000000000), (23558352366713286728845280366660017633/879691395640467679490737176576000000000000)]]

private theorem tensor165 (u v : ℝ) :
    eval poly080 ((2073/4096)+((519/1024)-(2073/4096))*u) ((511/1024)+((1023/2048)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern165 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern165, Fin.sum_univ_succ]
  <;> ring

private theorem cert165 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern165) (m := (1/1000000000000000))
    tensor165 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern165]

private def bern166 : Coeff :=
  ![![(42618167559033562053722492740791144655983841/384951359268084930960693275170072166400000000000), (2217706410119905453701299843444963105356907/21215935293403333610815918411087872000000000000), (26622372185183112738811629543896915700063461/270668924485372217081737459103956992000000000000), (8122970827161625177690334723288114254531/88108373855915435247961412468736000000000000)],
    ![(436743284609903505121345427724154754841166609/3849513592680849309606932751700721664000000000000), (1061821050463584064547051355460476791302905577/9898749238322183938989255647230427136000000000000), (54723868177236958913046268296280424097392593/541337848970744434163474918207913984000000000000), (16726435455494818372865950873190064931127/176216747711830870495922824937472000000000000)],
    ![(894798234545427038655130009758352244102611469/7699027185361698619213865503401443328000000000000), (3049664389249413821866276001875902821306696647/27716497867302115029169915812245195980800000000000), (112432464887755852664150234104849377715277069/1082675697941488868326949836415827968000000000000), (4917496490815911069670801155436246586509/50347642203380248713120807124992000000000000)]]

private theorem tensor166 (u v : ℝ) :
    eval poly086 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern166 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern166, Fin.sum_univ_succ]
  <;> ring

private theorem cert166 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern166) (m := (1/1000000000000000))
    tensor166 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern166]

private def bern167 : Coeff :=
  ![![(1125089102405144444971764054239495353897/56300249320989931487407179300864000000000000), (284465586488940612773019304173698705107/17176347250471504521581851312128000000000000), (26634609799298944632946924618887624375761/2026808975555637533546658454831104000000000000), (571194737525163000491849960872563132301/58748086247989493725990100140032000000000000)],
    ![(32890933387054342777180859843041750759/1407506233024748287185179482521600000000000), (2526270743866878480999965909899958775211/126675560972227345846666153426944000000000000), (167408306757971612844225258250219490803/10134044877778187667733292274155520000000000), (96184534068886174897632857611541120207/7343510780998686715748762517504000000000000)],
    ![(23558352366713286728845280366660017633/879691395640467679490737176576000000000000), (369761554728410159844033157958424628889/15834445121528418230833269178368000000000000), (631007161486337326194151043263730077769/31668890243056836461666538356736000000000000), (15146458703947525691235100683856767013/917938847624835839468595314688000000000000)]]

private theorem tensor167 (u v : ℝ) :
    eval poly080 ((4149/8192)+((519/1024)-(4149/8192))*u) ((1023/2048)+((2047/4096)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern167 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern167, Fin.sum_univ_succ]
  <;> ring

private theorem cert167 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern167) (m := (1/1000000000000000))
    tensor167 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern167]

private def bern168 : Coeff :=
  ![![(571194737525163000491849960872563132301/58748086247989493725990100140032000000000000), (12993618213822170367183818532569063926957/1621447180444510026837326763864883200000000000), (102230492822928872324508286060203107055041/16214471804445100268373267638648832000000000000), (5520939154687967452929945846123917901939/1201071985514451871731353158418432000000000000)],
    ![(1340671010076252399672912821764892093957/117496172495978987451980200280064000000000000), (157286356783997712328709001567469618376377/16214471804445100268373267638648832000000000000), (259135985661763629781806611990611295122969/32428943608890200536746535277297664000000000000), (15090000964152064759833524603281926789627/2402143971028903743462706316836864000000000000)],
    ![(615904127935996688618604425284810828889/46998468998391594980792080112025600000000000), (369495990738530215426130190794070916551761/32428943608890200536746535277297664000000000000), (628067791219254782714517266711034836624561/64857887217780401073493070554595328000000000000), (38309268272902523804681209405802894174787/4804287942057807486925412633673728000000000000)]]

private theorem tensor168 (u v : ℝ) :
    eval poly080 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((4095/8192)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern168 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern168, Fin.sum_univ_succ]
  <;> ring

private theorem cert168 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern168) (m := (1/1000000000000000))
    tensor168 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern168]

private def bern169 : Coeff :=
  ![![(5520939154687967452929945846123917901939/1201071985514451871731353158418432000000000000), (242735085883867619038309041415631135946977/64857887217780401073493070554595328000000000000), (14987786599618921220462151141482241761993/5188630977422432085879445644367626240000000000), (7038264196046264766454256427121933698179/3459087318281621390586297096245084160000000000)],
    ![(227233732813286953614725359091563152987/41776416887459195538481848988467200000000000), (1189488278540525224059520351715875751607803/259431548871121604293972282218381312000000000000), (1935773163464725089595810698054163230008891/518863097742243208587944564436762624000000000000), (199017703546692349058886468745499371560661/69181746365632427811725941924901683200000000000)],
    ![(120753028748262652655735091203426272941051/19217151768231229947701650534694912000000000000), (5633927918293225282834988669648943217551929/1037726195484486417175889128873525248000000000000), (9494636652535384990004875126322397655021817/2075452390968972834351778257747050496000000000000), (1029555938171838666358594607055219064533943/276726985462529711246903767699606732800000000000)]]

private theorem tensor169 (u v : ℝ) :
    eval poly080 ((4149/8192)+((16599/32768)-(4149/8192))*u) ((4095/8192)+((8191/16384)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern169 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern169, Fin.sum_univ_succ]
  <;> ring

private theorem cert169 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (16599/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern169) (m := (1/1000000000000000))
    tensor169 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern169]

private def bern170 : Coeff :=
  ![![(94593545960527456269594543895507306366469323643/946056460537245526328999793057969356144640000000000), (35198609438824444903334907791716966528969518427/354771172701467072373374922396738508554240000000000), (852653376657293314159556590430356703889303821/8661405583531910946615598691326623744000000000000), (4917496490815911069670801155436246586509/50347642203380248713120807124992000000000000)],
    ![(3796765651119830403940281734559431746236877836089/37842258421489821053159991722318774245785600000000000), (7064135285163143316474461650207875905922958540349/70954234540293414474674984479347701710848000000000000), (977866016784463537289956851732355882035862741/9898749238322183938989255647230427136000000000000), (276349408010412760643528571046103405087813/2819467963389293927934765198999552000000000000)],
    ![(30478431380871904295183477603925148932992751907879/302738067371918568425279933778550193966284800000000000), (11341721266475783784114630775547845333319063761799/113526775264469463159479975166956322737356800000000000), (10990277910602302810769987568630377244000617641/110865991469208460116679663248980783923200000000000), (443712143440690923158186272518132386809631/4511148741422870284695624318399283200000000000)]]

private theorem tensor170 (u v : ℝ) :
    eval poly086 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern170 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly086, bern170, Fin.sum_univ_succ]
  <;> ring

private theorem cert170 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly086 δ p := by
  apply positive_on_box_from_tensor (β := bern170) (m := (1/1000000000000000))
    tensor170 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern170]

private def bern171 : Coeff :=
  ![![(3184758702229078640146026871188968732873551/1106907941850118844987615070798426931200000000000), (889589191384291599959437600661331080149/439714489612070515752495393590476800000000000), (1851311818692771984940359832444525909/1583444512152841823083326917836800000000000), (40636328440252844736828531822463/128861044283271632737900953600000000000)],
    ![(79375076189504698373658281827705067425069/24063216127176496630165545017357107200000000000), (158541749671638056101937333000299963852991/64857887217780401073493070554595328000000000000), (6295821580974343149583704891190706893/3958611280382104557708317294592000000000000), (237264274873500020978111550854119/322152610708179081844752384000000000000)],
    ![(1029555938171838666358594607055219064533943/276726985462529711246903767699606732800000000000), (92948475313159296958969437179779504890427/32428943608890200536746535277297664000000000000), (796506380386366004258788117535565901/395861128038210455770831729459200000000000), (186538042391342810095726286779907/161076305354089540922376192000000000000)]]

private theorem tensor171 (u v : ℝ) :
    eval poly080 ((33195/65536)+((16599/32768)-(33195/65536))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern171 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern171, Fin.sum_univ_succ]
  <;> ring

private theorem cert171 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33195/65536) (16599/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern171) (m := (1/1000000000000000))
    tensor171 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern171]

private def bern172 : Coeff :=
  ![![(120753028748262652655735091203426272941051/19217151768231229947701650534694912000000000000), (37087439720158338455158456361819278877243/8107235902222550134186633819324416000000000000), (2836442169479419796065798281702080897/989652820095526139427079323648000000000000), (186538042391342810095726286779907/161076305354089540922376192000000000000)],
    ![(68489270201206653324348258612366747754041/9608575884115614973850825267347456000000000000), (21964704152806174921227265370051398827769/4053617951111275067093316909662208000000000000), (1835628316143350183751603661181621467/494826410047763069713539661824000000000000), (161174926150264204654533654742801/80538152677044770461188096000000000000)],
    ![(38309268272902523804681209405802894174787/4804287942057807486925412633673728000000000000), (12696326629659792500371105851426353315459/2026808975555637533546658454831104000000000000), (1126942838046179143703371515874323929/247413205023881534856769830912000000000000), (114609593620587347169252483751691/40269076338522385230594048000000000000)]]

private theorem tensor172 (u v : ℝ) :
    eval poly080 ((16599/32768)+((8301/16384)-(16599/32768))*u) ((4095/8192)+((1/2)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern172 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern172, Fin.sum_univ_succ]
  <;> ring

private theorem cert172 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16599/32768) (8301/16384)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern172) (m := (1/1000000000000000))
    tensor172 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern172]

private def bern173 : Coeff :=
  ![![(615904127935996688618604425284810828889/46998468998391594980792080112025600000000000), (4906533331269104932897239502212849393283/506702243888909383386664613707776000000000000), (774862166443734813199427885789129177/123706602511940767428384915456000000000000), (114609593620587347169252483751691/40269076338522385230594048000000000000)],
    ![(217356203700466380427513663082395256311/14687021561997373431497525035008000000000000), (360269568405761957427475184394996549577/31668890243056836461666538356736000000000000), (61505472270091618284087961472228171/7731662656996297964274057216000000000000), (11415865919468614803326487282017/2516817271157649076912128000000000000)],
    ![(15146458703947525691235100683856767013/917938847624835839468595314688000000000000), (25881155567877621656316931495149177883/1979305640191052278854158647296000000000000), (4664699778079674687223908038851361/483228916062268622767128576000000000000), (196074084433627895852966181319/31460215889470613461401600000000000)]]

private theorem tensor173 (u v : ℝ) :
    eval poly080 ((8301/16384)+((519/1024)-(8301/16384))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern173 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern173, Fin.sum_univ_succ]
  <;> ring

private theorem cert173 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern173) (m := (1/1000000000000000))
    tensor173 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern173]

private def bern174 : Coeff :=
  ![![(886171860824083886237397327752852009/5154441771330865309516038144000000000000), (898373845067608187522935718986149403/7731662656996297964274057216000000000000), (31207338342973440456630424200979/511895038201555744456704000000000000), (196074084433627895852966181319/31460215889470613461401600000000000)],
    ![(103232694746002106002675541874284111/515444177133086530951603814400000000000), (557234809051852674630989392598968577/3865831328498148982137028608000000000000), (1336590967990176563746318686781363/15100903626945894461472768000000000000), (2625215628694878172087819065049/78650539723676533653504000000000000)],
    ![(5032286577145167681133295445406819/21840854963266378430152704000000000000), (336059135252093255152315892192776723/1932915664249074491068514304000000000000), (889599138433781615181260058624713/7550451813472947230736384000000000000), (2449301091311688340922012042267/39325269861838266826752000000000000)]]

private theorem tensor174 (u v : ℝ) :
    eval poly080 ((519/1024)+((261/512)-(519/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern174 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern174, Fin.sum_univ_succ]
  <;> ring

private theorem cert174 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern174) (m := (1/1000000000000000))
    tensor174 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern174]

private def bern175 : Coeff :=
  ![![(718690280544255659259258502945147/1789736726156550454693068800000000000), (138418767623083187999163001160227091/483228916062268622767128576000000000000), (654466233667859534452746902567081/3775225906736473615368192000000000000), (2449301091311688340922012042267/39325269861838266826752000000000000)],
    ![(519353822091547176742738847258083/1118585453847844034183168000000000000), (20991266497184928338367759253302439/60403614507783577845891072000000000000), (109853554171013793016544081395573/471903238342059201921024000000000000), (590335955655023356334777132719/4915658732729783353344000000000000)],
    ![(74689941596927168786104862486543/139823181730980504272896000000000000), (125548051087542068147738417344547/302018072538917889229455360000000000), (17654560920394028932049453823569/58987904792757400240128000000000000), (113637288621938523672437889011/614457341591222919168000000000000)]]

private theorem tensor175 (u v : ℝ) :
    eval poly080 ((261/512)+((33/64)-(261/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern175 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern175, Fin.sum_univ_succ]
  <;> ring

private theorem cert175 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern175) (m := (1/1000000000000000))
    tensor175 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern175]

private def bern176 : Coeff :=
  ![![(131052651397774590414292420875091/39325269861838266826752000000000000), (253179242375486853624678436949707/117975809585514800480256000000000000), (1621805735230238588712934229329/1474697619818935006003200000000000), (113637288621938523672437889011/614457341591222919168000000000000)],
    ![(41314347538983806159755089786799/9831317465459566706688000000000000), (85165536924770810890659411808231/29493952396378700120064000000000000), (3178981047342226351914809518157/1843372024773668757504000000000000), (366440374527477420946749041/520726560670527897600000000000)],
    ![(2743331612456793043791970417871/491565873272978335334400000000000), (30359748419504964604406783507203/7373488099094675030016000000000000), (1298765914879461420276613340357/460843006193417189376000000000000), (64242141743643021522718291451/38403583849451432448000000000000)]]

private theorem tensor176 (u v : ℝ) :
    eval poly080 ((33/64)+((9/16)-(33/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern176 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern176, Fin.sum_univ_succ]
  <;> ring

private theorem cert176 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern176) (m := (1/1000000000000000))
    tensor176 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern176]

private def bern177 : Coeff :=
  ![![(720961723593626373624712522391/30722867079561145958400000000000), (6127517770711336842221638815343/460843006193417189376000000000000), (15664926938840744055916276463/2504581555399006464000000000000), (64242141743643021522718291451/38403583849451432448000000000000)],
    ![(137368408408578733400149278247/3840358384945143244800000000000), (1261600841569234391880098282249/57605375774177148672000000000000), (349212835740399333389888193047/28802687887088574336000000000000), (2663884977907615855428756127/480044798118142905600000000000)],
    ![(22880578872848957129524719793/384035838494514324480000000000), (232193804709786422882706420497/5760537577417714867200000000000), (11875548939464312116423984121/450041998235758974000000000000), (39918232959809729371717844021/2400223990590714528000000000000)]]

private theorem tensor177 (u v : ℝ) :
    eval poly080 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern177 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly080, bern177, Fin.sum_univ_succ]
  <;> ring

private theorem cert177 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < eval poly080 δ p := by
  apply positive_on_box_from_tensor (β := bern177) (m := (1/1000000000000000))
    tensor177 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern177]

private def bern178 : Coeff :=
  ![![(349106899336217/5528097200000000), (12644210971943918097929/223704945526485600000000), (697571791084554696937/13981559095405350000000), (645205756184122146937/14913663035099040000000)],
    ![(2368305522030029/221123888000000000), (81466460986495622643929/8948197821059424000000000), (18183992198077847345129/2237049455264856000000000), (7738500156697026298867/994244202339936000000000)],
    ![(3160054222805689/110561944000000000), (58393958063608937164279/4474098910529712000000000), (2332276613403643525139/497122101169968000000000), (839177540544451544773/745683151754952000000000)]]

private theorem tensor178 (u v : ℝ) :
    eval poly087 (0+((3/8)-0)*u) (0+((1/2)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern178 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern178, Fin.sum_univ_succ]
  <;> ring

private theorem cert178 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern178) (m := (1/1000000000000000))
    tensor178 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern178]

private def bern179 : Coeff :=
  ![![(3160054222805689/110561944000000000), (186271549972356027747001/8948197821059424000000000), (265655997556597756637531/17896395642118848000000000), (274863703633139990017/26513178729064960000000)],
    ![(10271911369192727/221123888000000000), (567781760910102551864033/17896395642118848000000000), (182779280367065613850427/8948197821059424000000000), (14269537181323928947477/1193093042807923200000000)],
    ![(7442871916943519/55280972000000000), (462953503550179287797981/4474098910529712000000000), (117595594205470611007301/1491366303509904000000000), (8885455135348579114663/149136630350990400000000)]]

private theorem tensor179 (u v : ℝ) :
    eval poly087 ((3/8)+((3/4)-(3/8))*u) (0+((1/4)-0)*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern179 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern179, Fin.sum_univ_succ]
  <;> ring

private theorem cert179 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern179) (m := (1/1000000000000000))
    tensor179 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern179]

private def bern180 : Coeff :=
  ![![(274863703633139990017/26513178729064960000000), (145471501150255361573447/17896395642118848000000000), (448404114176450955022091/71585582568475392000000000), (37669810919625390331201/7953953618719488000000000)],
    ![(13319201922407614249121/1193093042807923200000000), (37834240981730419872167/4772372171231692800000000), (149844406032099309718079/28634233027390156800000000), (1924064631276673815203/636316289497559040000000)],
    ![(111991582108927790363023/4772372171231692800000000), (1912573361490728940559/104048811872784000000000), (4031262723727840744660991/286342330273901568000000000), (333239461435498849584361/31815814474877952000000000)]]

private theorem tensor180 (u v : ℝ) :
    eval poly087 ((3/8)+((9/16)-(3/8))*u) ((1/4)+((3/8)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern180 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern180, Fin.sum_univ_succ]
  <;> ring

private theorem cert180 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern180) (m := (1/1000000000000000))
    tensor180 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern180]

private def bern181 : Coeff :=
  ![![(153886716395983399253/28303857664000000000000), (2942253506453601998819/636836797440000000000000), (19774662276443042444311/5094694379520000000000000), (1823279069524410136313/566077153280000000000000)],
    ![(103816471714149920407/22643086131200000000000), (1813231167853058195761/509469437952000000000000), (10702095829415088309709/4075755503616000000000000), (2425234789439617968041/1358585167872000000000000)],
    ![(116306183393366527961/18114468904960000000000), (2080636426597382392703/407575550361600000000000), (4237192931638668874369/1086868134297600000000000), (3044858385738939159143/1086868134297600000000000)]]

private theorem tensor181 (u v : ℝ) :
    eval poly088 ((3/8)+((15/32)-(3/8))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern181 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern181, Fin.sum_univ_succ]
  <;> ring

private theorem cert181 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern181) (m := (1/1000000000000000))
    tensor181 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern181]

private def bern182 : Coeff :=
  ![![(1823279069524410136313/566077153280000000000000), (13044360974996340009323/5094694379520000000000000), (52486590878830266253/26534866560000000000000), (39107838786129711253/26534866560000000000000)],
    ![(34005522781491011475961/13585851678720000000000000), (23808002812032819176659/13585851678720000000000000), (692361238861551315641/636836797440000000000000), (35899133502769990349/70759644160000000000000)],
    ![(260648246558229884243239/108686813429760000000000000), (501621579876786928384423/326060440289280000000000000), (3932454197920394682059/5094694379520000000000000), (167245864817940867353/1698231459840000000000000)]]

private theorem tensor182 (u v : ℝ) :
    eval poly088 ((3/8)+((27/64)-(3/8))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern182 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern182, Fin.sum_univ_succ]
  <;> ring

private theorem cert182 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern182) (m := (1/1000000000000000))
    tensor182 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern182]

private def bern183 : Coeff :=
  ![![(260648246558229884243239/108686813429760000000000000), (64178315977573829055707/32606044028928000000000000), (2036864968095168769150339/1304241761157120000000000000), (34155021015009009593001/28983150247936000000000000)],
    ![(8308410362151055889293/3622893780992000000000000), (137163723820742003089/75828009369600000000000), (176032430015986366878979/130424176115712000000000000), (2654116626008186149161/2898315024793600000000000)],
    ![(3044858385738939159143/1086868134297600000000000), (244869111278907430153/108686813429760000000000), (22586795058234376699843/13042417611571200000000000), (358795683181416114537/289831502479360000000000)]]

private theorem tensor183 (u v : ℝ) :
    eval poly088 ((27/64)+((15/32)-(27/64))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern183 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly088, bern183, Fin.sum_univ_succ]
  <;> ring

private theorem cert183 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    0 < eval poly088 δ p := by
  apply positive_on_box_from_tensor (β := bern183) (m := (1/1000000000000000))
    tensor183 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern183]

private def bern184 : Coeff :=
  ![![(6569973859537799128543/5390865946116096000000000), (1750457602699362573887/1940711740601794560000000), (23062636932796457681/37904526183628800000000), (21305872741052553689/63174210306048000000000)],
    ![(11661356935576497186677/10781731892232192000000000), (72439984707377975022637/97035587030089728000000000), (165229827374331445603/379045261836288000000000), (6266432763315356209/42116140204032000000000)],
    ![(22795957469870606580391/21563463784464384000000000), (136110592848365019473519/194071174060179456000000000), (93809532298312902407/252696841224192000000000), (3327367529776970141/50539368244838400000000)]]

private theorem tensor184 (u v : ℝ) :
    eval poly089 ((27/64)+((57/128)-(27/64))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern184 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern184, Fin.sum_univ_succ]
  <;> ring

private theorem cert184 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern184) (m := (1/1000000000000000))
    tensor184 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern184]

private def bern185 : Coeff :=
  ![![(22795957469870606580391/21563463784464384000000000), (170637105038600239348519/194071174060179456000000000), (549430523730669807219133/776284696240717824000000000), (251615785395336621903/463730403966976000000000)],
    ![(5567300267147054696857/5390865946116096000000000), (40970503237408507248577/48517793515044864000000000), (128649753043948266209699/194071174060179456000000000), (20365758841456961261/41735736357027840000000)],
    ![(302160872912770566779/269543297305804800000000), (2234525515634795894891/2425889675752243200000000), (2355688476498517405043/3234519567669657600000000), (28297594143006867299/52169670446284800000000)]]

private theorem tensor185 (u v : ℝ) :
    eval poly089 ((57/128)+((15/32)-(57/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern185 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern185, Fin.sum_univ_succ]
  <;> ring

private theorem cert185 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern185) (m := (1/1000000000000000))
    tensor185 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern185]

private def bern186 : Coeff :=
  ![![(251615785395336621903/463730403966976000000000), (292979125772917202912111/776284696240717824000000000), (1533977360377746571/7019356700672000000000), (3327367529776970141/50539368244838400000000)],
    ![(4301117952703725723227/8347147271405568000000000), (35732422833288206465501/103504626165429043200000000), (3442261781477752969/18952263091814400000000), (132386197492068977/5434340671488000000000)],
    ![(8601501368289971233247/16694294542811136000000000), (1055764726561969184660839/3105138784962871296000000000), (129930316649107914263/758090523672576000000000), (9363450324821047577/1010787364896768000000000)]]

private theorem tensor186 (u v : ℝ) :
    eval poly089 ((57/128)+((117/256)-(57/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern186 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern186, Fin.sum_univ_succ]
  <;> ring

private theorem cert186 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern186) (m := (1/1000000000000000))
    tensor186 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern186]

private def bern187 : Coeff :=
  ![![(8601501368289971233247/16694294542811136000000000), (2655643981063903834044781/6210277569925742592000000000), (34222607134037250286507/100165767256866816000000000), (236760062391478907851361/920041121470480384000000000)],
    ![(71673056926437425167/139119121190092800000000), (329912424840421938135511/776284696240717824000000000), (130602035955026395863821/388142348120358912000000000), (28710761623837051188931/115005140183810048000000000)],
    ![(28297594143006867299/52169670446284800000000), (2907664034100759912571/6469039135339315200000000), (80848151633484686903/225664155883929600000000), (772773271399758873301/2875128504595251200000000)]]

private theorem tensor187 (u v : ℝ) :
    eval poly089 ((117/256)+((15/32)-(117/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern187 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern187, Fin.sum_univ_succ]
  <;> ring

private theorem cert187 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern187) (m := (1/1000000000000000))
    tensor187 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern187]

private def bern188 : Coeff :=
  ![![(236760062391478907851361/920041121470480384000000000), (2148918399949311476459879/12420555139851485184000000000), (547811617570894799783/6064724189380608000000000), (9363450324821047577/1010787364896768000000000)],
    ![(466446155382175317362809/1840082242940960768000000000), (4171177760137269865626703/24841110279702970368000000000), (1018801469475669435143/12129448378761216000000000), (1155506080312771003/673858243264512000000000)],
    ![(943419695220794566330577/3680164485881921536000000000), (8420315919312147752973047/49682220559405940736000000000), (681608176728589379981/8086298919174144000000000), (3075407117779852681/4043149459587072000000000)]]

private theorem tensor188 (u v : ℝ) :
    eval poly089 ((117/256)+((237/512)-(117/256))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern188 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern188, Fin.sum_univ_succ]
  <;> ring

private theorem cert188 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern188) (m := (1/1000000000000000))
    tensor188 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern188]

private def bern189 : Coeff :=
  ![![(943419695220794566330577/3680164485881921536000000000), (42312963609585748796871673/198728882237623762944000000000), (13505839344770190120804859/79491552895049505177600000000), (261489954312877561684423/2054045294445723648000000000)],
    ![(59621692479827406120971/230010280367620096000000000), (2672070236749059437102803/12420555139851485184000000000), (4259678583626349445796989/24841110279702970368000000000), (49390769335014474428071/385133492708573184000000000)],
    ![(772773271399758873301/2875128504595251200000000), (34782870821461736442749/155256939248143564800000000), (18601762795946043798401/103504626165429043200000000), (653914558734157354249/4814168658857164800000000)]]

private theorem tensor189 (u v : ℝ) :
    eval poly089 ((237/512)+((15/32)-(237/512))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern189 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern189, Fin.sum_univ_succ]
  <;> ring

private theorem cert189 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern189) (m := (1/1000000000000000))
    tensor189 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern189]

private def bern190 : Coeff :=
  ![![(261489954312877561684423/2054045294445723648000000000), (16833707797616332883923703/198728882237623762944000000000), (687758990964149085343/16172597838348288000000000), (3075407117779852681/4043149459587072000000000)],
    ![(314944434459772855180481/2464854353334868377600000000), (11242517694113491642439021/132485921491749175296000000000), (4110629760834743141693/97035587030089728000000000), (30575798286172427/107817318922321920000000)],
    ![(3201985116838817280190261/24648543533348683776000000000), (68893199767940244044577943/794915528950495051776000000000), (8510255087055717886877/194071174060179456000000000), (23534246468043108329/16172597838348288000000000)]]

private theorem tensor190 (u v : ℝ) :
    eval poly089 ((237/512)+((477/1024)-(237/512))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern190 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern190, Fin.sum_univ_succ]
  <;> ring

private theorem cert190 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern190) (m := (1/1000000000000000))
    tensor190 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern190]

private def bern191 : Coeff :=
  ![![(3201985116838817280190261/24648543533348683776000000000), (68893199767940244044577943/794915528950495051776000000000), (8510255087055717886877/194071174060179456000000000), (23534246468043108329/16172597838348288000000000)],
    ![(11300437114860784751999/85585220601905152000000000), (439570583569997113965761/4968222055940594073600000000), (45829430481468486929/1010787364896768000000000), (1327566349786261019/505393682448384000000000)],
    ![(653914558734157354249/4814168658857164800000000), (4758281614811361217153/51752313082714521600000000), (1837712920530217859/37904526183628800000000), (1911743389140373/350967835033600000000)]]

private theorem tensor191 (u v : ℝ) :
    eval poly089 ((477/1024)+((15/32)-(477/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern191 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern191, Fin.sum_univ_succ]
  <;> ring

private theorem cert191 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern191) (m := (1/1000000000000000))
    tensor191 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern191]

private def bern192 : Coeff :=
  ![![(135265033648333558485893/25452651579902361600000000), (471950612072469981824231/114536932109560627200000000), (310728658847900641030547/101810606319609446400000000), (641918411615400294636791/305431818958828339200000000)],
    ![(429442692999332540344511/63631628949755904000000000), (379077870433321546716251/71585582568475392000000000), (9140073778379243953603093/2290738642191212544000000000), (239583240539677775243577/84842171933007872000000000)],
    ![(333239461435498849584361/31815814474877952000000000), (1241550683757657048529189/143171165136950784000000000), (8068221924730848392785663/1145369321095606272000000000), (2130702946506871220189483/381789773698535424000000000)]]

private theorem tensor192 (u v : ℝ) :
    eval poly087 ((15/32)+((9/16)-(15/32))*u) ((3/8)+((7/16)-(3/8))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern192 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern192, Fin.sum_univ_succ]
  <;> ring

private theorem cert192 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern192) (m := (1/1000000000000000))
    tensor192 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern192]

private def bern193 : Coeff :=
  ![![(641918411615400294636791/305431818958828339200000000), (27599146063958304467187/16968434386601574400000000), (4328054432408933194137667/3665181827505940070400000000), (311068338815855482278313/407242425278437785600000000)],
    ![(7522090387791201427568341/3054318189588283392000000000), (8858969071301699023633567/4581477284382425088000000000), (10531565086301943257133941/7330363655011880140800000000), (3954083924524404678854011/4072424252784377856000000000)],
    ![(2261933389281431806967851/678737375464062976000000000), (25100158017800019533116573/9162954568764850176000000000), (1279068740883372180057547/586429092400950411264000000), (13495042892346645532805309/8144848505568755712000000000)]]

private theorem tensor193 (u v : ℝ) :
    eval poly087 ((15/32)+((33/64)-(15/32))*u) ((7/16)+((15/32)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern193 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern193, Fin.sum_univ_succ]
  <;> ring

private theorem cert193 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern193) (m := (1/1000000000000000))
    tensor193 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern193]

private def bern194 : Coeff :=
  ![![(302160872912770566779/269543297305804800000000), (56438812098537312541/78254505669427200000000), (3314106340512905221/9476131545907200000000), (1911743389140373/350967835033600000000)],
    ![(6519134649363767974303/5390865946116096000000000), (38148822931692745325399/48517793515044864000000000), (8273874317801397559/21058070102016000000000), (1769457940621143241/63174210306048000000000)],
    ![(30410632527604312799959/21563463784464384000000000), (186618743737958804273183/194071174060179456000000000), (412352469694210284997/758090523672576000000000), (39442343738098868321/252696841224192000000000)]]

private theorem tensor194 (u v : ℝ) :
    eval poly089 ((15/32)+((63/128)-(15/32))*u) ((15/32)+((1/2)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern194 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly089, bern194, Fin.sum_univ_succ]
  <;> ring

private theorem cert194 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    0 < eval poly089 δ p := by
  apply positive_on_box_from_tensor (β := bern194) (m := (1/1000000000000000))
    tensor194 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern194]

private def bern195 : Coeff :=
  ![![(35532745366761373893787613/32579394022275022848000000000), (31394258869869877724977501/36651818275059400704000000000), (739213062220191376520498011/1172858184801900822528000000000), (32188176295896023109865117/78190545653460054835200000000)],
    ![(21403210741395454890513331/16289697011137511424000000000), (19542965409014770435332947/18325909137529700352000000000), (161669792831871152101150919/195476364133650137088000000000), (4657897230505682317652087/7819054565346005483520000000)],
    ![(13495042892346645532805309/8144848505568755712000000000), (12780160342683619179909373/9162954568764850176000000000), (334598182759949309379002363/293214546200475205632000000000), (5837344373311783644548159/6515878804455004569600000000)]]

private theorem tensor195 (u v : ℝ) :
    eval poly087 ((63/128)+((33/64)-(63/128))*u) ((15/32)+((31/64)-(15/32))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern195 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern195, Fin.sum_univ_succ]
  <;> ring

private theorem cert195 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern195) (m := (1/1000000000000000))
    tensor195 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern195]

private def bern196 : Coeff :=
  ![![(109547813649785781349/172281237287731200000000), (2863830360684851826727843/6556162484984610816000000000), (6285841597610874024101/25610009706971136000000000), (131414427737276636597/2134167475580928000000000)],
    ![(68892362185821545677979/97128333110883123200000000), (30767160022856053549451/60987557999856844800000000), (87509550212709836897/284555663410790400000000), (20189722661780734091/170733398046474240000000)],
    ![(1413534341726441105852461/1748309995995896217600000000), (1741445214404103288526987/2913849993326493696000000000), (40444526198833197542131/102440038827884544000000000), (189542670708209540413/948518878035968000000000)]]

private theorem tensor196 (u v : ℝ) :
    eval poly090 ((63/128)+((129/256)-(63/128))*u) ((31/64)+((1/2)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern196 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly090, bern196, Fin.sum_univ_succ]
  <;> ring

private theorem cert196 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    0 < eval poly090 δ p := by
  apply positive_on_box_from_tensor (β := bern196) (m := (1/1000000000000000))
    tensor196 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern196]

private def bern197 : Coeff :=
  ![![(39078850677150214639496953/62552436522768043868160000000), (795849682519392642439415989/1563810913069201096704000000000), (7414340743674970204108829321/18765730956830413160448000000000), (98440401756481819311492271/347513536237600243712000000000)],
    ![(58313552392399113455549389/78190545653460054835200000000), (734952056821224015219132511/1172858184801900822528000000000), (2390400263901032147575276793/4691432739207603290112000000000), (34268716210607764827975703/86878384059400060928000000000)],
    ![(5837344373311783644548159/6515878804455004569600000000), (226721653818570741317499551/293214546200475205632000000000), (765500505597452333525090153/1172858184801900822528000000000), (11602658459477674625239423/21719596014850015232000000000)]]

private theorem tensor197 (u v : ℝ) :
    eval poly087 ((129/256)+((33/64)-(129/256))*u) ((31/64)+((63/128)-(31/64))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern197 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern197, Fin.sum_univ_succ]
  <;> ring

private theorem cert197 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern197) (m := (1/1000000000000000))
    tensor197 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern197]

private def bern198 : Coeff :=
  ![![(98440401756481819311492271/347513536237600243712000000000), (8533004340875084524352918581/37531461913660826320896000000000), (11203287310618971067712899/65158788044550045696000000000), (136178420082756884006396747/1163766260888707792896000000000)],
    ![(235515266598912878623395083/695027072475200487424000000000), (21177531389744787542580066953/75062923827321652641792000000000), (529909341730771284332648491/2345716369603801645056000000000), (44011011401988907439855999/258614724641935065088000000000)],
    ![(558232666792986731939128663/1390054144950400974848000000000), (51648141076021385853026357293/150125847654643305283584000000000), (168294176264916349680364877/586429092400950411264000000000), (1072692024912381400898045011/4655065043554831171584000000000)]]

private theorem tensor198 (u v : ℝ) :
    eval poly087 ((129/256)+((261/512)-(129/256))*u) ((63/128)+((127/256)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern198 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern198, Fin.sum_univ_succ]
  <;> ring

private theorem cert198 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern198) (m := (1/1000000000000000))
    tensor198 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern198]

private def bern199 : Coeff :=
  ![![(136178420082756884006396747/1163766260888707792896000000000), (2987630512040089418940557977/33361299478809623396352000000000), (7472183859516884877755036363/120100678123714644226867200000000), (4670804760217796860904028517/133445197915238493585408000000000)],
    ![(133691188556682786994299497/931013008710966234316800000000), (27847861237662049951873896251/240201356247429288453734400000000), (42466529568859549283890384781/480402712494858576907468800000000), (6510433554235623429497356967/106756158332190794868326400000000)],
    ![(355755790635001067195383107/2068917797135480520704000000000), (692201103465615040030467623057/4804027124948585769074688000000000), (223575100088513517108256170203/1921610849979434307629875200000000), (189454952497132037354820795733/2135123166643815897366528000000000)]]

private theorem tensor199 (u v : ℝ) :
    eval poly087 ((129/256)+((519/1024)-(129/256))*u) ((127/256)+((255/512)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern199 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern199, Fin.sum_univ_succ]
  <;> ring

private theorem cert199 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern199) (m := (1/1000000000000000))
    tensor199 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern199]

#check cert199

private def bern200 : Coeff :=
  ![![(421402582463738785552021450140274369/2428522702779476886491397881856000000000), (3246974209313762958058972748085599107/21856704325015291978422580936704000000000), (1320323776395332030273228301585851/10672218908698873036339150848000000000), (3668487917056163616522198319031/37056315655204420265066496000000000)],
    ![(3582100739253091855345496242450642571/19428181622235815091931183054848000000000), (27857781165466779250259292175465290593/174853634600122335827380647493632000000000), (3824592908028301928606002391342113/28459250423196994763571068928000000000), (97454823940757129581994483622247/889351575724906086361595904000000000)],
    ![(6081154639589646948791434949256412709/31085090595577304147089892887756800000000), (47694936624622644495150656860431310511/279765815360195737323809035989811200000000), (19870218012601496975197328093299667/136604402031345574865141130854400000000), (171550000435365617756673880585337/1422962521159849738178553446400000000)]]

private theorem tensor200 (u v : ℝ) :
    eval poly091 ((129/256)+((1035/2048)-(129/256))*u) ((255/512)+((1/2)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern200 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly091, bern200, Fin.sum_univ_succ]
  <;> ring

private theorem cert200 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    0 < eval poly091 δ p := by
  apply positive_on_box_from_tensor (β := bern200) (m := (1/1000000000000000))
    tensor200 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern200]

private def bern201 : Coeff :=
  ![![(104921034166008344861835906137/1708098533315052717893222400000000), (1467143365698905172422649805181/30745773599670948922078003200000000), (2093323904111451032273481491417/61491547199341897844156006400000000), (836177847194600010295369650023/40994364799561265229437337600000000)],
    ![(1041249588214477218061133339/13909597176832676855808000000000), (4696505653070284518070557153701/76864433999177372305195008000000000), (2427637907055908761056307457867/51242955999451581536796672000000000), (138069139636963291593610753591/4099436479956126522943733760000000)],
    ![(189454952497132037354820795733/2135123166643815897366528000000000), (2879532716537429837497599782761/38432216999588686152597504000000000), (4700149560819344159366984734421/76864433999177372305195008000000000), (161939030538859710821742300901/3416197066630105435786444800000000)]]

private theorem tensor201 (u v : ℝ) :
    eval poly087 ((1035/2048)+((519/1024)-(1035/2048))*u) ((255/512)+((511/1024)-(255/512))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern201 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern201, Fin.sum_univ_succ]
  <;> ring

private theorem cert201 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern201) (m := (1/1000000000000000))
    tensor201 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern201]

private def bern202 : Coeff :=
  ![![(54706431909768349029306937665659456143/373021087146927649765078714653081600000000), (150117753744757134657890754169708683439/1119063261440782949295236143959244800000000), (33239966666220265328838020629492019/273208804062691149730282261708800000000), (155409107788613894053548880585337/1422962521159849738178553446400000000)],
    ![(12618054409136836585503135326429530717/82893574921539477725573047700684800000000), (1563166340866618689549819969575390945081/11190632614407829492952361439592448000000000), (115823790084354453106351496209427959/910696013542303832434274205696000000000), (1632265758839297734522277339802079/14229625211598497381785534464000000000)],
    ![(1095686454441180486237461120049945217/6939927202733537670047976086568960000000), (1084178009509579472869724399356199859313/7460421742938552995301574293061632000000000), (725628660385440999632239774160436263/5464176081253822994605645234176000000000), (1141234807871697373098742163242087/9486416807732331587857022976000000000)]]

private theorem tensor202 (u v : ℝ) :
    eval poly092 ((1035/2048)+((2073/4096)-(1035/2048))*u) ((511/1024)+((1/2)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern202 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly092, bern202, Fin.sum_univ_succ]
  <;> ring

private theorem cert202 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    0 < eval poly092 δ p := by
  apply positive_on_box_from_tensor (β := bern202) (m := (1/1000000000000000))
    tensor202 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern202]

private def bern203 : Coeff :=
  ![![(1108165801280036474405698466531/32795491839649012183549870080000000), (44179853330332377626086694397043/1639774591982450609177493504000000000), (197784925309659710183257541325361/9838647551894703655064961024000000000), (29014914823508935109699171090177/2186366122643267478903324672000000000)],
    ![(1661979881417974722898507573361/40994364799561265229437337600000000), (41422668978196033326627057116359/1229830943986837956883120128000000000), (65991014222330189140726847171311/2459661887973675913766240256000000000), (10923513722942083046043240411167/546591530660816869725831168000000000)],
    ![(161939030538859710821742300901/3416197066630105435786444800000000), (12461470001107372642201241152793/307457735996709489220780032000000000), (20701643504555772320392214182897/614915471993418978441560064000000000), (3663363004002659055885134980289/136647882665204217431457792000000000)]]

private theorem tensor203 (u v : ℝ) :
    eval poly087 ((2073/4096)+((519/1024)-(2073/4096))*u) ((511/1024)+((1023/2048)-(511/1024))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern203 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern203, Fin.sum_univ_succ]
  <;> ring

private theorem cert203 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern203) (m := (1/1000000000000000))
    tensor203 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern203]

private def bern204 : Coeff :=
  ![![(151352567165497785032991928756004220329/1366785499908913175505766862290944000000000), (9003040578913728292716720815660761903021/86107486494261530056863312324329472000000000), (192395063730095315132556944070943/1955566099524471522003618103296000000), (841427679847148575419863458485721/9124277591097252110042923008000000000)],
    ![(434286972120170214420080067869313875591/3826999399744956891416147214414643200000000), (147820802342263501719044716458410624941/1377719783908184480909812997189271552000000), (141712465896206021952808860066743027/1401489037992537924102592974028800000000), (41582731381195951424624497865867/437965324372668101282060304384000000)],
    ![(4448804287653728906481988201527623118743/38269993997449568914161472144146432000000000), (37906666289201218979569499905879988262421/344429945977046120227453249297317888000000000), (873456488975264493781899010868134997/8408934227955227544615557844172800000000), (10696910572251850921838237286335203/109491331093167025320515076096000000000)]]

private theorem tensor204 (u v : ℝ) :
    eval poly093 ((2073/4096)+((4149/8192)-(2073/4096))*u) ((1023/2048)+((1/2)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern204 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern204, Fin.sum_univ_succ]
  <;> ring

private theorem cert204 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern204) (m := (1/1000000000000000))
    tensor204 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern204]

private def bern205 : Coeff :=
  ![![(175016832671088144372207254064137/8745464490573069915613298688000000000), (2611575811796992737178900368487297/157418360830315258481039376384000000000), (4146309151760950175990600225995441/314836721660630516962078752768000000000), (2046718934523685736524077606284107/209891147773753677974719168512000000000)],
    ![(25576965738952719269583780332323/1093183061321633739451662336000000000), (392982898470616863434170661166923/19677295103789407310129922048000000000), (217079120633011005116821948997833/13118196735859604873419948032000000000), (344390294401345885869771190029433/26236393471719209746839896064000000000)],
    ![(3663363004002659055885134980289/136647882665204217431457792000000000), (57507514098960249868114216102009/2459661887973675913766240256000000000), (98158561273975606250794327819817/4919323775947351827532480512000000000), (18069258863612262722480631945553/1093183061321633739451662336000000000)]]

private theorem tensor205 (u v : ℝ) :
    eval poly087 ((4149/8192)+((519/1024)-(4149/8192))*u) ((1023/2048)+((2047/4096)-(1023/2048))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern205 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern205, Fin.sum_univ_succ]
  <;> ring

private theorem cert205 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern205) (m := (1/1000000000000000))
    tensor205 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern205]

private def bern206 : Coeff :=
  ![![(2046718934523685736524077606284107/209891147773753677974719168512000000000), (10127852107191271276735498004566081/1259346886642522067848315011072000000000), (3190400931639216744595698826334957/503738754657008827139326004428800000000), (862928028655578788837013514006803/186569909132225491533083705344000000000)],
    ![(1600613763244817607827415708839857/139927431849169118649812779008000000000), (24504155513703646813751570134789273/2518693773285044135696630022144000000000), (8079394851527873045419562204799589/1007477509314017654278652008857600000000), (2354672951825607002984101594841499/373139818264450983066167410688000000000)],
    ![(11026261346758774353156697980301211/839564591095014711898876674048000000000), (19179947464489711578370833435330491/1679129182190029423797753348096000000000), (19569826071393835010036783895712541/2014955018628035308557304017715200000000), (5972109054462241788386376452780259/746279636528901966132334821376000000000)]]

private theorem tensor206 (u v : ℝ) :
    eval poly087 ((4149/8192)+((8301/16384)-(4149/8192))*u) ((2047/4096)+((4095/8192)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern206 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern206, Fin.sum_univ_succ]
  <;> ring

private theorem cert206 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern206) (m := (1/1000000000000000))
    tensor206 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern206]

private def bern207 : Coeff :=
  ![![(862928028655578788837013514006803/186569909132225491533083705344000000000), (37993161004709714449841106371201473/10074775093140176542786520088576000000000), (58778863493717726118594346341820033/20149550186280353085573040177152000000000), (5543180185176381620482948947605423/2686606691504047078076405356953600000000)],
    ![(18979204693659370142595947083047/3471068076878613795964348006400000000), (7436835303680594627487952795062739/1611964014902428246845843214172160000000), (4039949136589335446562105713084081/1074642676601618831230562142781440000000), (31221385670889176603873288639178037/10746426766016188312305621427814400000000)],
    ![(18842512976386984955670836888173467/2985118546115607864529339285504000000000), (879753459046723839708359507739543577/161196401490242824684584321417216000000000), (1484061592526500922410386774064760537/322392802980485649369168642834432000000000), (53718018764712995022565476071494301/14328569021354917749740828570419200000000)]]

private theorem tensor207 (u v : ℝ) :
    eval poly087 ((4149/8192)+((16599/32768)-(4149/8192))*u) ((4095/8192)+((8191/16384)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern207 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern207, Fin.sum_univ_succ]
  <;> ring

private theorem cert207 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (16599/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern207) (m := (1/1000000000000000))
    tensor207 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern207]

private def bern208 : Coeff :=
  ![![(146975570442304064065676022986947713403759/1469567769502063446303800530335222988800000000), (2187610539257981744629827039309267928618517/22043516542530951694557007955028344832000000000), (33120578063089297746810676880009700649/336357369118209101784622313766912000000000), (10696910572251850921838237286335203/109491331093167025320515076096000000000)],
    ![(393283560234016945185361453950001237842619/3918847385338835856810134747560594636800000000), (17561560534401889509799225536191943662258123/176348132340247613556456063640226758656000000000), (29543359233639313300596018172469154559/298984328105074757141886501126144000000000), (12268073186423952920055430158650011/125132949820762314652017229824000000000)],
    ![(1353030045500071810260080857999520147256473/13436048178304580080491890563064895897600000000), (447550581100859644527685712478007311365551/4478682726101526693497296854354965299200000000), (60986713081448066026542377333533085059/615053474959010928977595088030924800000000), (6565948545668418344410717536176939/66737573237739901147742522572800000000)]]

private theorem tensor208 (u v : ℝ) :
    eval poly093 ((4149/8192)+((33195/65536)-(4149/8192))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern208 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly093, bern208, Fin.sum_univ_succ]
  <;> ring

private theorem cert208 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly093 δ p := by
  apply positive_on_box_from_tensor (β := bern208) (m := (1/1000000000000000))
    tensor208 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern208]

private def bern209 : Coeff :=
  ![![(499616024624074503826409920489593967/171942828256259012996889942845030400000000), (918662319090809635121871202763743/447767781917341179679400892825600000000), (73648994871153272372173031737/61491547199341897844156006400000000), (2294529665711748555882827/6672259895761924679270400000000)],
    ![(286039598977695691483189582771195051/85971414128129506498444971422515200000000), (24914807049408340872950394587155327/10074775093140176542786520088576000000000), (248879579102332859967690254609/153728867998354744610390016000000000), (38283867466779252504328313/50041949218214435094528000000000)],
    ![(53718018764712995022565476071494301/14328569021354917749740828570419200000000), (14582019560712247712579057018007547/5037387546570088271393260044288000000000), (52283782705594185336912851783/25621477999725790768398336000000000), (29690127077917547929489373/25020974609107217547264000000000)]]

private theorem tensor209 (u v : ℝ) :
    eval poly087 ((33195/65536)+((16599/32768)-(33195/65536))*u) ((8191/16384)+((1/2)-(8191/16384))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern209 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern209, Fin.sum_univ_succ]
  <;> ring

private theorem cert209 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33195/65536) (16599/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern209) (m := (1/1000000000000000))
    tensor209 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern209]

private def bern210 : Coeff :=
  ![![(18842512976386984955670836888173467/2985118546115607864529339285504000000000), (5796962635691800717269482996232187/1259346886642522067848315011072000000000), (37082437641700400797014292807/12810738999862895384199168000000000), (29690127077917547929489373/25020974609107217547264000000000)],
    ![(10681454958113455794354579642463257/1492559273057803932264669642752000000000), (3429881406150481279474815900623417/629673443321261033924157505536000000000), (71833190050971839526043334711/19216108499794343076298752000000000), (25393256883486695642069903/12510487304553608773632000000000)],
    ![(5972109054462241788386376452780259/746279636528901966132334821376000000000), (1981181691047229788632757648328259/314836721660630516962078752768000000000), (44037868785879731981614733837/9608054249897171538149376000000000), (1997941219062740129935469/695027072475200487424000000000)]]

private theorem tensor210 (u v : ℝ) :
    eval poly087 ((16599/32768)+((8301/16384)-(16599/32768))*u) ((4095/8192)+((1/2)-(4095/8192))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern210 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern210, Fin.sum_univ_succ]
  <;> ring

private theorem cert210 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16599/32768) (8301/16384)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern210) (m := (1/1000000000000000))
    tensor210 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern210]

private def bern211 : Coeff :=
  ![![(11026261346758774353156697980301211/839564591095014711898876674048000000000), (5662282026202039739732038510437/583030966038204661040886579200000000), (30228099079718072203500772109/4804027124948585769074688000000000), (1997941219062740129935469/695027072475200487424000000000)],
    ![(155610501425608038241861271344541/10494557388687683898735958425600000000), (11220645866166033853388732507701/983864755189470365506496102400000000), (479414105933751991719608339/60050339061857322113433600000000), (356889450390091098327347/78190545653460054835200000000)],
    ![(18069258863612262722480631945553/1093183061321633739451662336000000000), (805809606231684478144141996127/61491547199341897844156006400000000), (60561425078123478873828247/6255243652276804386816000000000), (152983689535466111725949/24434545516706267136000000000)]]

private theorem tensor211 (u v : ℝ) :
    eval poly087 ((8301/16384)+((519/1024)-(8301/16384))*u) ((2047/4096)+((1/2)-(2047/4096))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern211 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern211, Fin.sum_univ_succ]
  <;> ring

private theorem cert211 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern211) (m := (1/1000000000000000))
    tensor211 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern211]

private def bern212 : Coeff :=
  ![![(355755790635001067195383107/2068917797135480520704000000000), (27916863053837880101662783583/240201356247429288453734400000000), (554542781153758419990709/9091923913193029632000000000), (152983689535466111725949/24434545516706267136000000000)],
    ![(1864890230148181734815452993/9310130087109662343168000000000), (1154344342665860644803568163/8006711874914309615124480000000), (51921905402880105210016171/586429092400950411264000000000), (45348637230692689316911/1357474750928125952000000000)],
    ![(1072692024912381400898045011/4655065043554831171584000000000), (10442130593212005935900197879/60050339061857322113433600000000), (34555030848523915031602597/293214546200475205632000000000), (8852038843016748503311/142061311143641088000000000)]]

private theorem tensor212 (u v : ℝ) :
    eval poly087 ((519/1024)+((261/512)-(519/1024))*u) ((127/256)+((1/2)-(127/256))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern212 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern212, Fin.sum_univ_succ]
  <;> ring

private theorem cert212 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern212) (m := (1/1000000000000000))
    tensor212 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern212]

private def bern213 : Coeff :=
  ![![(558232666792986731939128663/1390054144950400974848000000000), (21503577069200102328313409491/75062923827321652641792000000000), (5083945352506126115237129/29321454620047520563200000000), (8852038843016748503311/142061311143641088000000000)],
    ![(16135870009703692665786679/34751353623760024371200000000), (652193503789830511569833851/1876573095683041316044800000000), (1706629026327070370549677/7330363655011880140800000000), (6114793963941052942291/50905303159804723200000000)],
    ![(11602658459477674625239423/21719596014850015232000000000), (487586608026136526000767531/1172858184801900822528000000000), (5713847983913596195009/19089488684926771200000000), (17654629864461602490533/95447443424633856000000000)]]

private theorem tensor213 (u v : ℝ) :
    eval poly087 ((261/512)+((33/64)-(261/512))*u) ((63/128)+((1/2)-(63/128))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern213 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern213, Fin.sum_univ_succ]
  <;> ring

private theorem cert213 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern213) (m := (1/1000000000000000))
    tensor213 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern213]

private def bern214 : Coeff :=
  ![![(2261933389281431806967851/678737375464062976000000000), (7865686112120283868866863/3665181827505940070400000000), (2441197914077037915503/2219707986619392000000000), (17654629864461602490533/95447443424633856000000000)],
    ![(6417655057870842417571159/1527159094794141696000000000), (881960847958940917750169/305431818958828339200000000), (987636622134393540692911/572684660547803136000000000), (1399369985854971422509/1988488404679872000000000)],
    ![(2130702946506871220189483/381789773698535424000000000), (943199150862075785670247/229073864219121254400000000), (201747070576269841210291/71585582568475392000000000), (9979269937939105809811/5965465214039616000000000)]]

private theorem tensor214 (u v : ℝ) :
    eval poly087 ((33/64)+((9/16)-(33/64))*u) ((7/16)+((1/2)-(7/16))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern214 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern214, Fin.sum_univ_succ]
  <;> ring

private theorem cert214 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern214) (m := (1/1000000000000000))
    tensor214 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern214]

private def bern215 : Coeff :=
  ![![(111991582108927790363023/4772372171231692800000000), (951827213777326166763839/71585582568475392000000000), (13991705141852236115249/2237049455264856000000000), (9979269937939105809811/5965465214039616000000000)],
    ![(28451059421370853954927/795395361871948800000000), (195972414180899574038741/8948197821059424000000000), (48218189573162130643217/3976976809359744000000000), (33103909859435871978947/5965465214039616000000000)],
    ![(8885455135348579114663/149136630350990400000000), (6679278722388996809551/165707367056656000000000), (118060989326361449469929/4474098910529712000000000), (4133832500430944876447/248561050584984000000000)]]

private theorem tensor215 (u v : ℝ) :
    eval poly087 ((9/16)+((3/4)-(9/16))*u) ((1/4)+((1/2)-(1/4))*v) =
      Cycle61.Arithmetic.Bernstein.tensor bern215 u v := by
  simp [eval, Cycle61.Arithmetic.Bernstein.tensor,
    Cycle61.Arithmetic.Bernstein.basis2, Cycle61.Arithmetic.Bernstein.basis3,
    poly087, bern215, Fin.sum_univ_succ]
  <;> ring

private theorem cert215 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < eval poly087 δ p := by
  apply positive_on_box_from_tensor (β := bern215) (m := (1/1000000000000000))
    tensor215 (by norm_num) (by norm_num) (by norm_num) ?_ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [bern215]

#check cert215

structure Window where
  branch : ImprovedBranch
  deltaLo : ℝ
  deltaHi : ℝ
  pLo : ℝ

def window : Fin 17 → Window :=
  ![⟨branchPcap, (3/8), (15/32), (3/8)⟩,
    ⟨branchPcap, (3/8), (27/64), (7/16)⟩,
    ⟨branchPcap, (27/64), (15/32), (7/16)⟩,
    ⟨branchC, (27/64), (57/128), (15/32)⟩,
    ⟨branchC, (57/128), (15/32), (15/32)⟩,
    ⟨branchC, (57/128), (117/256), (31/64)⟩,
    ⟨branchC, (117/256), (15/32), (31/64)⟩,
    ⟨branchC, (117/256), (237/512), (63/128)⟩,
    ⟨branchC, (237/512), (15/32), (63/128)⟩,
    ⟨branchC, (237/512), (477/1024), (127/256)⟩,
    ⟨branchC, (477/1024), (15/32), (127/256)⟩,
    ⟨branchC, (15/32), (63/128), (15/32)⟩,
    ⟨branchP, (63/128), (129/256), (31/64)⟩,
    ⟨branchY, (129/256), (1035/2048), (255/512)⟩,
    ⟨branchY3, (1035/2048), (2073/4096), (511/1024)⟩,
    ⟨branchX8, (2073/4096), (4149/8192), (1023/2048)⟩,
    ⟨branchX8, (4149/8192), (33195/65536), (8191/16384)⟩]
def Window.Contains (w : Window) (δ p : ℝ) : Prop :=
  δ ∈ Set.Icc w.deltaLo w.deltaHi ∧ p ∈ Set.Icc w.pLo (1/2)
theorem window_bounds (i : Fin 17) :
    0 ≤ (window i).deltaLo ∧ (window i).deltaLo < (window i).deltaHi ∧
    (window i).deltaHi ≤ 3/4 ∧ 0 ≤ (window i).pLo ∧ (window i).pLo < 1/2 := by
  fin_cases i <;> norm_num [window]
private theorem admission00 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    Admitted branchPcap δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchPcap δ p (0 : Fin 15)
    rw [guard_Pcap_00_eq]
    apply cert000
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (1 : Fin 15)
    rw [guard_Pcap_01_eq]
    apply cert001
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (2 : Fin 15)
    rw [guard_Pcap_02_eq]
    apply cert002
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (3 : Fin 15)
    rw [guard_Pcap_03_eq]
    apply cert003
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (4 : Fin 15)
    rw [guard_Pcap_04_eq]
    apply cert004
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (5 : Fin 15)
    rw [guard_Pcap_05_eq]
    apply cert005
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (6 : Fin 15)
    rw [guard_Pcap_06_eq]
    apply cert006
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (7 : Fin 15)
    rw [guard_Pcap_07_eq]
    apply cert007
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (8 : Fin 15)
    rw [guard_Pcap_08_eq]
    apply cert008
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (9 : Fin 15)
    rw [guard_Pcap_09_eq]
    apply cert009
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (10 : Fin 15)
    rw [guard_Pcap_10_eq]
    apply cert010
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (11 : Fin 15)
    rw [guard_Pcap_11_eq]
    apply cert011
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (12 : Fin 15)
    rw [guard_Pcap_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (13 : Fin 15)
    rw [guard_Pcap_13_eq]
    apply cert013
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (14 : Fin 15)
    rw [guard_Pcap_14_eq]
    apply cert014
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission01 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Admitted branchPcap δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchPcap δ p (0 : Fin 15)
    rw [guard_Pcap_00_eq]
    apply cert000
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (1 : Fin 15)
    rw [guard_Pcap_01_eq]
    apply cert001
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (2 : Fin 15)
    rw [guard_Pcap_02_eq]
    apply cert002
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (3 : Fin 15)
    rw [guard_Pcap_03_eq]
    apply cert003
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (4 : Fin 15)
    rw [guard_Pcap_04_eq]
    apply cert015
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (5 : Fin 15)
    rw [guard_Pcap_05_eq]
    apply cert016
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (6 : Fin 15)
    rw [guard_Pcap_06_eq]
    apply cert017
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (7 : Fin 15)
    rw [guard_Pcap_07_eq]
    apply cert007
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (8 : Fin 15)
    rw [guard_Pcap_08_eq]
    apply cert018
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (9 : Fin 15)
    rw [guard_Pcap_09_eq]
    apply cert019
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (10 : Fin 15)
    rw [guard_Pcap_10_eq]
    apply cert020
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (11 : Fin 15)
    rw [guard_Pcap_11_eq]
    apply cert011
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (12 : Fin 15)
    rw [guard_Pcap_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (13 : Fin 15)
    rw [guard_Pcap_13_eq]
    apply cert013
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (14 : Fin 15)
    rw [guard_Pcap_14_eq]
    apply cert014
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission02 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Admitted branchPcap δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchPcap δ p (0 : Fin 15)
    rw [guard_Pcap_00_eq]
    apply cert000
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (1 : Fin 15)
    rw [guard_Pcap_01_eq]
    apply cert001
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (2 : Fin 15)
    rw [guard_Pcap_02_eq]
    apply cert002
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (3 : Fin 15)
    rw [guard_Pcap_03_eq]
    apply cert003
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (4 : Fin 15)
    rw [guard_Pcap_04_eq]
    apply cert021
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (5 : Fin 15)
    rw [guard_Pcap_05_eq]
    apply cert022
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (6 : Fin 15)
    rw [guard_Pcap_06_eq]
    apply cert023
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (7 : Fin 15)
    rw [guard_Pcap_07_eq]
    apply cert007
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (8 : Fin 15)
    rw [guard_Pcap_08_eq]
    apply cert024
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (9 : Fin 15)
    rw [guard_Pcap_09_eq]
    apply cert025
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (10 : Fin 15)
    rw [guard_Pcap_10_eq]
    apply cert026
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchPcap δ p (11 : Fin 15)
    rw [guard_Pcap_11_eq]
    apply cert011
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (12 : Fin 15)
    rw [guard_Pcap_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (13 : Fin 15)
    rw [guard_Pcap_13_eq]
    apply cert013
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchPcap δ p (14 : Fin 15)
    rw [guard_Pcap_14_eq]
    apply cert014
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission03 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert031
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert032
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert035
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert036
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert037
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission04 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert041
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert042
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert043
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert044
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert045
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission05 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert046
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert047
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert048
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert049
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert050
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission06 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert051
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert052
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert053
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert054
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert055
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission07 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert056
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert057
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert058
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert059
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert060
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission08 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert061
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert062
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert063
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert064
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert065
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission09 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert066
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert067
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert068
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert069
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert070
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission10 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert071
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert072
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert073
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert074
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert075
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission11 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Admitted branchC δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchC δ p (0 : Fin 15)
    rw [guard_C_00_eq]
    apply cert027
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (1 : Fin 15)
    rw [guard_C_01_eq]
    apply cert028
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (2 : Fin 15)
    rw [guard_C_02_eq]
    apply cert029
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (3 : Fin 15)
    rw [guard_C_03_eq]
    apply cert030
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (4 : Fin 15)
    rw [guard_C_04_eq]
    apply cert076
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (5 : Fin 15)
    rw [guard_C_05_eq]
    apply cert077
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (6 : Fin 15)
    rw [guard_C_06_eq]
    apply cert033
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (7 : Fin 15)
    rw [guard_C_07_eq]
    apply cert034
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (8 : Fin 15)
    rw [guard_C_08_eq]
    apply cert078
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (9 : Fin 15)
    rw [guard_C_09_eq]
    apply cert079
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (10 : Fin 15)
    rw [guard_C_10_eq]
    apply cert080
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchC δ p (11 : Fin 15)
    rw [guard_C_11_eq]
    apply cert038
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (12 : Fin 15)
    rw [guard_C_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (13 : Fin 15)
    rw [guard_C_13_eq]
    apply cert039
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchC δ p (14 : Fin 15)
    rw [guard_C_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission12 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Admitted branchP δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchP δ p (0 : Fin 15)
    rw [guard_P_00_eq]
    apply cert081
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (1 : Fin 15)
    rw [guard_P_01_eq]
    apply cert082
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (2 : Fin 15)
    rw [guard_P_02_eq]
    apply cert083
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (3 : Fin 15)
    rw [guard_P_03_eq]
    apply cert084
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (4 : Fin 15)
    rw [guard_P_04_eq]
    apply cert085
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchP δ p (5 : Fin 15)
    rw [guard_P_05_eq]
    apply cert086
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchP δ p (6 : Fin 15)
    rw [guard_P_06_eq]
    apply cert087
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (7 : Fin 15)
    rw [guard_P_07_eq]
    apply cert088
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (8 : Fin 15)
    rw [guard_P_08_eq]
    apply cert089
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchP δ p (9 : Fin 15)
    rw [guard_P_09_eq]
    apply cert090
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchP δ p (10 : Fin 15)
    rw [guard_P_10_eq]
    apply cert091
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchP δ p (11 : Fin 15)
    rw [guard_P_11_eq]
    apply cert092
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (12 : Fin 15)
    rw [guard_P_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (13 : Fin 15)
    rw [guard_P_13_eq]
    apply cert013
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchP δ p (14 : Fin 15)
    rw [guard_P_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission13 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    Admitted branchY δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchY δ p (0 : Fin 15)
    rw [guard_Y_00_eq]
    apply cert093
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (1 : Fin 15)
    rw [guard_Y_01_eq]
    apply cert094
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (2 : Fin 15)
    rw [guard_Y_02_eq]
    apply cert095
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (3 : Fin 15)
    rw [guard_Y_03_eq]
    apply cert096
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (4 : Fin 15)
    rw [guard_Y_04_eq]
    apply cert097
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY δ p (5 : Fin 15)
    rw [guard_Y_05_eq]
    apply cert098
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY δ p (6 : Fin 15)
    rw [guard_Y_06_eq]
    apply cert099
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (7 : Fin 15)
    rw [guard_Y_07_eq]
    apply cert100
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (8 : Fin 15)
    rw [guard_Y_08_eq]
    apply cert101
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY δ p (9 : Fin 15)
    rw [guard_Y_09_eq]
    apply cert102
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY δ p (10 : Fin 15)
    rw [guard_Y_10_eq]
    apply cert103
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY δ p (11 : Fin 15)
    rw [guard_Y_11_eq]
    apply cert104
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (12 : Fin 15)
    rw [guard_Y_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (13 : Fin 15)
    rw [guard_Y_13_eq]
    apply cert105
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY δ p (14 : Fin 15)
    rw [guard_Y_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission14 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    Admitted branchY3 δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchY3 δ p (0 : Fin 15)
    rw [guard_Y3_00_eq]
    apply cert093
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (1 : Fin 15)
    rw [guard_Y3_01_eq]
    apply cert094
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (2 : Fin 15)
    rw [guard_Y3_02_eq]
    apply cert106
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (3 : Fin 15)
    rw [guard_Y3_03_eq]
    apply cert096
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (4 : Fin 15)
    rw [guard_Y3_04_eq]
    apply cert107
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY3 δ p (5 : Fin 15)
    rw [guard_Y3_05_eq]
    apply cert108
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY3 δ p (6 : Fin 15)
    rw [guard_Y3_06_eq]
    apply cert109
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (7 : Fin 15)
    rw [guard_Y3_07_eq]
    apply cert110
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (8 : Fin 15)
    rw [guard_Y3_08_eq]
    apply cert111
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY3 δ p (9 : Fin 15)
    rw [guard_Y3_09_eq]
    apply cert112
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY3 δ p (10 : Fin 15)
    rw [guard_Y3_10_eq]
    apply cert113
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchY3 δ p (11 : Fin 15)
    rw [guard_Y3_11_eq]
    apply cert114
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (12 : Fin 15)
    rw [guard_Y3_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (13 : Fin 15)
    rw [guard_Y3_13_eq]
    apply cert115
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchY3 δ p (14 : Fin 15)
    rw [guard_Y3_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission15 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    Admitted branchX8 δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [guard_X8_00_eq]
    apply cert116
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [guard_X8_01_eq]
    apply cert117
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [guard_X8_02_eq]
    apply cert118
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [guard_X8_03_eq]
    apply cert119
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [guard_X8_04_eq]
    apply cert120
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [guard_X8_05_eq]
    apply cert121
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [guard_X8_06_eq]
    apply cert122
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [guard_X8_07_eq]
    apply cert123
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [guard_X8_08_eq]
    apply cert124
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [guard_X8_09_eq]
    apply cert125
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [guard_X8_10_eq]
    apply cert126
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [guard_X8_11_eq]
    apply cert127
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [guard_X8_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [guard_X8_13_eq]
    apply cert128
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [guard_X8_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

private theorem admission16 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    Admitted branchX8 δ p := by
  intro i
  fin_cases i
  · change 0 < admissionGuard branchX8 δ p (0 : Fin 15)
    rw [guard_X8_00_eq]
    apply cert116
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (1 : Fin 15)
    rw [guard_X8_01_eq]
    apply cert117
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (2 : Fin 15)
    rw [guard_X8_02_eq]
    apply cert118
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (3 : Fin 15)
    rw [guard_X8_03_eq]
    apply cert119
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (4 : Fin 15)
    rw [guard_X8_04_eq]
    apply cert129
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (5 : Fin 15)
    rw [guard_X8_05_eq]
    apply cert130
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (6 : Fin 15)
    rw [guard_X8_06_eq]
    apply cert122
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (7 : Fin 15)
    rw [guard_X8_07_eq]
    apply cert123
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (8 : Fin 15)
    rw [guard_X8_08_eq]
    apply cert131
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (9 : Fin 15)
    rw [guard_X8_09_eq]
    apply cert132
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (10 : Fin 15)
    rw [guard_X8_10_eq]
    apply cert133
    · exact hδ
    · exact hp
  · change 0 < admissionGuard branchX8 δ p (11 : Fin 15)
    rw [guard_X8_11_eq]
    apply cert127
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (12 : Fin 15)
    rw [guard_X8_12_eq]
    apply cert012
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (13 : Fin 15)
    rw [guard_X8_13_eq]
    apply cert128
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]
  · change 0 < admissionGuard branchX8 δ p (14 : Fin 15)
    rw [guard_X8_14_eq]
    apply cert040
    · constructor <;> linarith [hδ.1, hδ.2]
    · constructor <;> linarith [hp.1, hp.2]

theorem window_admitted (i : Fin 17) {δ p : ℝ}
    (hi : (window i).Contains δ p) : Admitted (window i).branch δ p := by
  fin_cases i
  · change δ ∈ Set.Icc (3/8) (15/32) ∧ p ∈ Set.Icc (3/8) (1/2) at hi
    change Admitted branchPcap δ p
    exact admission00 hi.1 hi.2
  · change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2) at hi
    change Admitted branchPcap δ p
    exact admission01 hi.1 hi.2
  · change δ ∈ Set.Icc (27/64) (15/32) ∧ p ∈ Set.Icc (7/16) (1/2) at hi
    change Admitted branchPcap δ p
    exact admission02 hi.1 hi.2
  · change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2) at hi
    change Admitted branchC δ p
    exact admission03 hi.1 hi.2
  · change δ ∈ Set.Icc (57/128) (15/32) ∧ p ∈ Set.Icc (15/32) (1/2) at hi
    change Admitted branchC δ p
    exact admission04 hi.1 hi.2
  · change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchC δ p
    exact admission05 hi.1 hi.2
  · change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchC δ p
    exact admission06 hi.1 hi.2
  · change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2) at hi
    change Admitted branchC δ p
    exact admission07 hi.1 hi.2
  · change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2) at hi
    change Admitted branchC δ p
    exact admission08 hi.1 hi.2
  · change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2) at hi
    change Admitted branchC δ p
    exact admission09 hi.1 hi.2
  · change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2) at hi
    change Admitted branchC δ p
    exact admission10 hi.1 hi.2
  · change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2) at hi
    change Admitted branchC δ p
    exact admission11 hi.1 hi.2
  · change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2) at hi
    change Admitted branchP δ p
    exact admission12 hi.1 hi.2
  · change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2) at hi
    change Admitted branchY δ p
    exact admission13 hi.1 hi.2
  · change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2) at hi
    change Admitted branchY3 δ p
    exact admission14 hi.1 hi.2
  · change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission15 hi.1 hi.2
  · change δ ∈ Set.Icc (4149/8192) (33195/65536) ∧ p ∈ Set.Icc (8191/16384) (1/2) at hi
    change Admitted branchX8 δ p
    exact admission16 hi.1 hi.2

def Available (b : Branch) (δ p : ℝ) : Prop :=
  b = .old ∨ ∃ i : Fin 17, b = .improved (window i).branch ∧ (window i).Contains δ p
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
private theorem row00 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldsmall δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldsmall_old_eq]
    exact cert134 hδ hp

private theorem row01 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldpeak δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldpeak_old_eq]
    exact cert135 hδ hp

private theorem row02 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldswitch_old_eq]
    exact cert136 hδ hp

private theorem row03 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    Certified .oldswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldswitch_old_eq]
    exact cert137 hδ hp

private theorem row04 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .oldswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldswitch_old_eq]
    exact cert138 hδ hp

private theorem row05 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .oldswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_oldswitch_old_eq]
    exact cert139 hδ hp

private theorem row06 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newswitch_old_eq]
    exact cert136 hδ hp

private theorem row07 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    Certified .newswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newswitch_old_eq]
    exact cert137 hδ hp

private theorem row08 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .newswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newswitch_old_eq]
    exact cert138 hδ hp

private theorem row09 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .newswitch δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newswitch_old_eq]
    exact cert139 hδ hp

private theorem row10 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert140 hδ hp

private theorem row11 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert141 hδ hp

private theorem row12 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert142 hδ hp

private theorem row13 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨0, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (15/32) ∧ p ∈ Set.Icc (3/8) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_Pcap_eq]
    exact cert143 hδ hp

private theorem row14 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨1, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_Pcap_eq]
    exact cert144 hδ hp

private theorem row15 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨2, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (15/32) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_Pcap_eq]
    exact cert145 hδ hp

private theorem row16 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨3, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert146 hδ hp

private theorem row17 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨4, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (15/32) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert147 hδ hp

private theorem row18 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨5, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert148 hδ hp

private theorem row19 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨6, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert149 hδ hp

private theorem row20 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨7, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert150 hδ hp

private theorem row21 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨8, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert151 hδ hp

private theorem row22 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨9, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert152 hδ hp

private theorem row23 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨10, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert153 hδ hp

private theorem row24 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert154 hδ hp

private theorem row25 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert155 hδ hp

private theorem row26 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨11, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_C_eq]
    exact cert156 hδ hp

private theorem row27 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert157 hδ hp

private theorem row28 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchP) δ p := by
    refine Or.inr ⟨⟨12, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchP), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_P_eq]
    exact cert158 hδ hp

private theorem row29 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert159 hδ hp

private theorem row30 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert160 hδ hp

private theorem row31 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert161 hδ hp

private theorem row32 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchY) δ p := by
    refine Or.inr ⟨⟨13, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchY), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_Y_eq]
    exact cert162 hδ hp

private theorem row33 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert163 hδ hp

private theorem row34 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchY3) δ p := by
    refine Or.inr ⟨⟨14, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchY3), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_Y3_eq]
    exact cert164 hδ hp

private theorem row35 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert165 hδ hp

private theorem row36 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by
    refine Or.inr ⟨⟨15, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_X8_eq]
    exact cert166 hδ hp

private theorem row37 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert167 hδ hp

private theorem row38 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert168 hδ hp

private theorem row39 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (16599/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert169 hδ hp

private theorem row40 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available (.improved branchX8) δ p := by
    refine Or.inr ⟨⟨16, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (4149/8192) (33195/65536) ∧ p ∈ Set.Icc (8191/16384) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_X8_eq]
    exact cert170 hδ hp

private theorem row41 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33195/65536) (16599/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert171 hδ hp

private theorem row42 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16599/32768) (8301/16384)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert172 hδ hp

private theorem row43 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert173 hδ hp

private theorem row44 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert174 hδ hp

private theorem row45 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert175 hδ hp

private theorem row46 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert176 hδ hp

private theorem row47 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .newtop δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newtop_old_eq]
    exact cert177 hδ hp

private theorem row48 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/8)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert178 hδ hp

private theorem row49 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc 0 (1/4)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert179 hδ hp

private theorem row50 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert180 hδ hp

private theorem row51 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨0, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (15/32) ∧ p ∈ Set.Icc (3/8) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_Pcap_eq]
    exact cert181 hδ hp

private theorem row52 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨1, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (3/8) (27/64) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_Pcap_eq]
    exact cert182 hδ hp

private theorem row53 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchPcap) δ p := by
    refine Or.inr ⟨⟨2, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (15/32) ∧ p ∈ Set.Icc (7/16) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchPcap), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_Pcap_eq]
    exact cert183 hδ hp

private theorem row54 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (57/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨3, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (27/64) (57/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert184 hδ hp

private theorem row55 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (15/32)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨4, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (15/32) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert185 hδ hp

private theorem row56 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128) (117/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨5, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (57/128) (117/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert186 hδ hp

private theorem row57 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (15/32)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨6, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (15/32) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert187 hδ hp

private theorem row58 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (117/256) (237/512)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨7, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (117/256) (237/512) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert188 hδ hp

private theorem row59 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (15/32)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨8, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (15/32) ∧ p ∈ Set.Icc (63/128) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert189 hδ hp

private theorem row60 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (237/512) (477/1024)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨9, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (237/512) (477/1024) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert190 hδ hp

private theorem row61 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (477/1024) (15/32)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨10, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (477/1024) (15/32) ∧ p ∈ Set.Icc (127/256) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert191 hδ hp

private theorem row62 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (7/16)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert192 hδ hp

private theorem row63 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (33/64)) (hp : p ∈ Set.Icc (7/16) (15/32)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert193 hδ hp

private theorem row64 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (63/128)) (hp : p ∈ Set.Icc (15/32) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchC) δ p := by
    refine Or.inr ⟨⟨11, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (15/32) (63/128) ∧ p ∈ Set.Icc (15/32) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchC), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_C_eq]
    exact cert194 hδ hp

private theorem row65 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (33/64)) (hp : p ∈ Set.Icc (15/32) (31/64)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert195 hδ hp

private theorem row66 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (63/128) (129/256)) (hp : p ∈ Set.Icc (31/64) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchP) δ p := by
    refine Or.inr ⟨⟨12, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (63/128) (129/256) ∧ p ∈ Set.Icc (31/64) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchP), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_P_eq]
    exact cert196 hδ hp

private theorem row67 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (33/64)) (hp : p ∈ Set.Icc (31/64) (63/128)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert197 hδ hp

private theorem row68 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (261/512)) (hp : p ∈ Set.Icc (63/128) (127/256)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert198 hδ hp

private theorem row69 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (519/1024)) (hp : p ∈ Set.Icc (127/256) (255/512)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert199 hδ hp

private theorem row70 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (129/256) (1035/2048)) (hp : p ∈ Set.Icc (255/512) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchY) δ p := by
    refine Or.inr ⟨⟨13, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (129/256) (1035/2048) ∧ p ∈ Set.Icc (255/512) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchY), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_Y_eq]
    exact cert200 hδ hp

private theorem row71 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (519/1024)) (hp : p ∈ Set.Icc (255/512) (511/1024)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert201 hδ hp

private theorem row72 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (1035/2048) (2073/4096)) (hp : p ∈ Set.Icc (511/1024) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchY3) δ p := by
    refine Or.inr ⟨⟨14, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (1035/2048) (2073/4096) ∧ p ∈ Set.Icc (511/1024) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchY3), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_Y3_eq]
    exact cert202 hδ hp

private theorem row73 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (519/1024)) (hp : p ∈ Set.Icc (511/1024) (1023/2048)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert203 hδ hp

private theorem row74 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (2073/4096) (4149/8192)) (hp : p ∈ Set.Icc (1023/2048) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by
    refine Or.inr ⟨⟨15, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (2073/4096) (4149/8192) ∧ p ∈ Set.Icc (1023/2048) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_X8_eq]
    exact cert204 hδ hp

private theorem row75 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (519/1024)) (hp : p ∈ Set.Icc (1023/2048) (2047/4096)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert205 hδ hp

private theorem row76 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (8301/16384)) (hp : p ∈ Set.Icc (2047/4096) (4095/8192)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert206 hδ hp

private theorem row77 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (16599/32768)) (hp : p ∈ Set.Icc (4095/8192) (8191/16384)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert207 hδ hp

private theorem row78 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (4149/8192) (33195/65536)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available (.improved branchX8) δ p := by
    refine Or.inr ⟨⟨16, by decide⟩, rfl, ?_⟩
    change δ ∈ Set.Icc (4149/8192) (33195/65536) ∧ p ∈ Set.Icc (8191/16384) (1/2)
    exact ⟨hδ, hp.1, by linarith [hp.2]⟩
  refine ⟨(.improved branchX8), ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_X8_eq]
    exact cert208 hδ hp

private theorem row79 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33195/65536) (16599/32768)) (hp : p ∈ Set.Icc (8191/16384) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert209 hδ hp

private theorem row80 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (16599/32768) (8301/16384)) (hp : p ∈ Set.Icc (4095/8192) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert210 hδ hp

private theorem row81 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (8301/16384) (519/1024)) (hp : p ∈ Set.Icc (2047/4096) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert211 hδ hp

private theorem row82 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (519/1024) (261/512)) (hp : p ∈ Set.Icc (127/256) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert212 hδ hp

private theorem row83 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (261/512) (33/64)) (hp : p ∈ Set.Icc (63/128) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert213 hδ hp

private theorem row84 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (33/64) (9/16)) (hp : p ∈ Set.Icc (7/16) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert214 hδ hp

private theorem row85 {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    Certified .newkink δ p := by
  have ha : Available .old δ p := by
    exact Or.inl rfl
  refine ⟨.old, ha, available_denominator ha ?_ ?_, ?_⟩
  · constructor <;> linarith [hδ.1, hδ.2]
  · constructor <;> linarith [hp.1, hp.2]
  · rw [return_newkink_old_eq]
    exact cert215 hδ hp

#check row85

theorem cover_oldsmall {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldsmall δ p := by
  exact row00 hδ hp

theorem cover_oldpeak {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldpeak δ p := by
  exact row01 hδ hp

theorem cover_oldswitch {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .oldswitch δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row02 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row03 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        exact row04 hδ hp
      · intro δ p hδ hp
        exact row05 hδ hp

theorem cover_newswitch {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newswitch δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row06 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row07 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        exact row08 hδ hp
      · intro δ p hδ hp
        exact row09 hδ hp

theorem cover_newtop {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newtop δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row10 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row11 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        refine split_p (m := (3/8)) ?_ ?_ hδ hp
        · intro δ p hδ hp
          exact row12 hδ hp
        · intro δ p hδ hp
          refine split_delta (m := (15/32)) ?_ ?_ hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row13 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (27/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                exact row14 hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row15 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (57/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row16 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row17 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (117/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row18 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row19 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (237/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            exact row20 hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row21 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (477/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                exact row22 hδ hp
                              · intro δ p hδ hp
                                exact row23 hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row24 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (33/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row25 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (63/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row26 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row27 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (129/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row28 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row29 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (261/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row30 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (519/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row31 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (1035/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    exact row32 hδ hp
                                  · intro δ p hδ hp
                                    refine split_p (m := (511/1024)) ?_ ?_ hδ hp
                                    · intro δ p hδ hp
                                      exact row33 hδ hp
                                    · intro δ p hδ hp
                                      refine split_delta (m := (2073/4096)) ?_ ?_ hδ hp
                                      · intro δ p hδ hp
                                        exact row34 hδ hp
                                      · intro δ p hδ hp
                                        refine split_p (m := (1023/2048)) ?_ ?_ hδ hp
                                        · intro δ p hδ hp
                                          exact row35 hδ hp
                                        · intro δ p hδ hp
                                          refine split_delta (m := (4149/8192)) ?_ ?_ hδ hp
                                          · intro δ p hδ hp
                                            exact row36 hδ hp
                                          · intro δ p hδ hp
                                            refine split_p (m := (2047/4096)) ?_ ?_ hδ hp
                                            · intro δ p hδ hp
                                              exact row37 hδ hp
                                            · intro δ p hδ hp
                                              refine split_delta (m := (8301/16384)) ?_ ?_ hδ hp
                                              · intro δ p hδ hp
                                                refine split_p (m := (4095/8192)) ?_ ?_ hδ hp
                                                · intro δ p hδ hp
                                                  exact row38 hδ hp
                                                · intro δ p hδ hp
                                                  refine split_delta (m := (16599/32768)) ?_ ?_ hδ hp
                                                  · intro δ p hδ hp
                                                    refine split_p (m := (8191/16384)) ?_ ?_ hδ hp
                                                    · intro δ p hδ hp
                                                      exact row39 hδ hp
                                                    · intro δ p hδ hp
                                                      refine split_delta (m := (33195/65536)) ?_ ?_ hδ hp
                                                      · intro δ p hδ hp
                                                        exact row40 hδ hp
                                                      · intro δ p hδ hp
                                                        exact row41 hδ hp
                                                  · intro δ p hδ hp
                                                    exact row42 hδ hp
                                              · intro δ p hδ hp
                                                exact row43 hδ hp
                              · intro δ p hδ hp
                                exact row44 hδ hp
                          · intro δ p hδ hp
                            exact row45 hδ hp
              · intro δ p hδ hp
                exact row46 hδ hp
      · intro δ p hδ hp
        exact row47 hδ hp

theorem cover_newkink {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Certified .newkink δ p := by
  refine split_delta (m := (3/8)) ?_ ?_ hδ hp
  · intro δ p hδ hp
    exact row48 hδ hp
  · intro δ p hδ hp
    refine split_p (m := (1/4)) ?_ ?_ hδ hp
    · intro δ p hδ hp
      exact row49 hδ hp
    · intro δ p hδ hp
      refine split_delta (m := (9/16)) ?_ ?_ hδ hp
      · intro δ p hδ hp
        refine split_p (m := (3/8)) ?_ ?_ hδ hp
        · intro δ p hδ hp
          exact row50 hδ hp
        · intro δ p hδ hp
          refine split_delta (m := (15/32)) ?_ ?_ hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row51 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (27/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                exact row52 hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row53 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (57/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row54 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row55 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (117/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row56 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row57 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (237/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            exact row58 hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row59 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (477/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                exact row60 hδ hp
                              · intro δ p hδ hp
                                exact row61 hδ hp
          · intro δ p hδ hp
            refine split_p (m := (7/16)) ?_ ?_ hδ hp
            · intro δ p hδ hp
              exact row62 hδ hp
            · intro δ p hδ hp
              refine split_delta (m := (33/64)) ?_ ?_ hδ hp
              · intro δ p hδ hp
                refine split_p (m := (15/32)) ?_ ?_ hδ hp
                · intro δ p hδ hp
                  exact row63 hδ hp
                · intro δ p hδ hp
                  refine split_delta (m := (63/128)) ?_ ?_ hδ hp
                  · intro δ p hδ hp
                    exact row64 hδ hp
                  · intro δ p hδ hp
                    refine split_p (m := (31/64)) ?_ ?_ hδ hp
                    · intro δ p hδ hp
                      exact row65 hδ hp
                    · intro δ p hδ hp
                      refine split_delta (m := (129/256)) ?_ ?_ hδ hp
                      · intro δ p hδ hp
                        exact row66 hδ hp
                      · intro δ p hδ hp
                        refine split_p (m := (63/128)) ?_ ?_ hδ hp
                        · intro δ p hδ hp
                          exact row67 hδ hp
                        · intro δ p hδ hp
                          refine split_delta (m := (261/512)) ?_ ?_ hδ hp
                          · intro δ p hδ hp
                            refine split_p (m := (127/256)) ?_ ?_ hδ hp
                            · intro δ p hδ hp
                              exact row68 hδ hp
                            · intro δ p hδ hp
                              refine split_delta (m := (519/1024)) ?_ ?_ hδ hp
                              · intro δ p hδ hp
                                refine split_p (m := (255/512)) ?_ ?_ hδ hp
                                · intro δ p hδ hp
                                  exact row69 hδ hp
                                · intro δ p hδ hp
                                  refine split_delta (m := (1035/2048)) ?_ ?_ hδ hp
                                  · intro δ p hδ hp
                                    exact row70 hδ hp
                                  · intro δ p hδ hp
                                    refine split_p (m := (511/1024)) ?_ ?_ hδ hp
                                    · intro δ p hδ hp
                                      exact row71 hδ hp
                                    · intro δ p hδ hp
                                      refine split_delta (m := (2073/4096)) ?_ ?_ hδ hp
                                      · intro δ p hδ hp
                                        exact row72 hδ hp
                                      · intro δ p hδ hp
                                        refine split_p (m := (1023/2048)) ?_ ?_ hδ hp
                                        · intro δ p hδ hp
                                          exact row73 hδ hp
                                        · intro δ p hδ hp
                                          refine split_delta (m := (4149/8192)) ?_ ?_ hδ hp
                                          · intro δ p hδ hp
                                            exact row74 hδ hp
                                          · intro δ p hδ hp
                                            refine split_p (m := (2047/4096)) ?_ ?_ hδ hp
                                            · intro δ p hδ hp
                                              exact row75 hδ hp
                                            · intro δ p hδ hp
                                              refine split_delta (m := (8301/16384)) ?_ ?_ hδ hp
                                              · intro δ p hδ hp
                                                refine split_p (m := (4095/8192)) ?_ ?_ hδ hp
                                                · intro δ p hδ hp
                                                  exact row76 hδ hp
                                                · intro δ p hδ hp
                                                  refine split_delta (m := (16599/32768)) ?_ ?_ hδ hp
                                                  · intro δ p hδ hp
                                                    refine split_p (m := (8191/16384)) ?_ ?_ hδ hp
                                                    · intro δ p hδ hp
                                                      exact row77 hδ hp
                                                    · intro δ p hδ hp
                                                      refine split_delta (m := (33195/65536)) ?_ ?_ hδ hp
                                                      · intro δ p hδ hp
                                                        exact row78 hδ hp
                                                      · intro δ p hδ hp
                                                        exact row79 hδ hp
                                                  · intro δ p hδ hp
                                                    exact row80 hδ hp
                                              · intro δ p hδ hp
                                                exact row81 hδ hp
                              · intro δ p hδ hp
                                exact row82 hδ hp
                          · intro δ p hδ hp
                            exact row83 hδ hp
              · intro δ p hδ hp
                exact row84 hδ hp
      · intro δ p hδ hp
        exact row85 hδ hp

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
def windowValue (δ p : ℝ) (i : Option (Fin 17)) : ℝ := by
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
      (Finset.inf'_le (windowValue δ p) (Finset.mem_univ (none : Option (Fin 17))))
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
end Candidate.FourthPower.ReturnFinite

