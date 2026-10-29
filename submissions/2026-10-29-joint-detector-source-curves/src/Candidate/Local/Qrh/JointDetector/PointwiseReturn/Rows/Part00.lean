/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.PowerRows
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def row000_coefficients : Fin 3 → Fin 4 → ℝ := ![![(392958253480975350231187245167/2150216419045408500234375000:ℝ), (1011859734222038932719671523661/2150216419045408500234375000:ℝ), (844844708001151814745781311821/2150216419045408500234375000:ℝ), (2789422558766521385892555967/26545881716609981484375000:ℝ)],
![(263065557306699926532536649839/1075108209522704250117187500:ℝ), (617088574479149955040990348429/1075108209522704250117187500:ℝ), (452684430217230932919750174341/1075108209522704250117187500:ℝ), (1218042136355319807546870071/13272940858304990742187500:ℝ)],
![(153560098290780968613886054511/2150216419045408500234375000:ℝ), (293588901729315478872999641797/2150216419045408500234375000:ℝ), (70177663527996097379400543643/1075108209522704250117187500:ℝ), (0:ℝ)]]
theorem row000_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (313456021414612749015934449553/515469897534741258240000000000:ℝ) row000_coefficients
      (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row000_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row000_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row000_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row000_coefficients]

def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2987754772228236018181127835421/119456467724744916679687500:ℝ), (8629234264242933818595603082583/119456467724744916679687500:ℝ), (8295204211801159582647822658903/119456467724744916679687500:ℝ), (98286100732831917860494348583/4424313619434996914062500:ℝ)],
![(1460373001644548084029121144509/59728233862372458339843750:ℝ), (4067718622767867812715641939351/59728233862372458339843750:ℝ), (150275448999804065632895210167/2389129354494898333593750:ℝ), (42575577921177107856883683679/2212156809717498457031250:ℝ)],
![(276436045107177231093563435497/119456467724744916679687500:ℝ), (548597481209547303763088131919/119456467724744916679687500:ℝ), (136089788151669972015309223211/59728233862372458339843750:ℝ), (0:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (3485036211868175757097649959139/6185638770416895098880000000000:ℝ) row001_coefficients
      (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row001_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row001_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]

def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11155028773250144536973322175733/59728233862372458339843750:ℝ), (32797026214866885139024405679839/59728233862372458339843750:ℝ), (32128966109983336667128844832479/59728233862372458339843750:ℝ), (129468748992180198334293349733/737385603239166152343750:ℝ)],
![(5138292309591425056583370366101/29864116931186229169921875:ℝ), (14798348102014763360920507345951/29864116931186229169921875:ℝ), (14184387259648261819569363402599/29864116931186229169921875:ℝ), (55855944039813870558422548429/368692801619583076171875:ℝ)],
![(540129894104297408039932528769/59728233862372458339843750:ℝ), (1076030529706212336058560693463/59728233862372458339843750:ℝ), (267954852851199931849587519847/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (4466671651122801873450222435929/8247518360555860131840000000000:ℝ) row002_coefficients
      (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row002_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row002_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]

def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8603097500324002769377891643261/5972823386237245833984375:ℝ), (25542068459018588919375450590839/5972823386237245833984375:ℝ), (5054968883413033906123445250379/1194564677247449166796875:ℝ), (308736054013725310393321011271/221215680971749845703125:ℝ)],
![(38329877394106647295014637187618/29864116931186229169921875:ℝ), (112544060750425976789553175025446/29864116931186229169921875:ℝ), (110103625287318032229019358106038/29864116931186229169921875:ℝ), (265847718007397798033191261246/221215680971749845703125:ℝ)],
![(1067612828153629586578412902813/29864116931186229169921875:ℝ), (2131019073056089032336888629051/29864116931186229169921875:ℝ), (1063410779952701913598749163738/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (10506489397063998578964851265667/19794044065334064316416000000000:ℝ) row003_coefficients
      (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row003_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row003_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]

def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(337680190963383014936743181661982/29864116931186229169921875:ℝ), (1007696092051080657035065058207066/29864116931186229169921875:ℝ), (1002351611212012269259900571428186/29864116931186229169921875:ℝ), (4102910001534748483476280183742/368692801619583076171875:ℝ)],
![(295606040705108981299759541124284/29864116931186229169921875:ℝ), (175415384827607849559394206833444/5972823386237245833984375:ℝ), (867345998098323592764577284197588/29864116931186229169921875:ℝ), (3529322403276460818115627051292/368692801619583076171875:ℝ)],
![(4245252628559679711956489489302/29864116931186229169921875:ℝ), (8482114765868231481474471812954/29864116931186229169921875:ℝ), (4236866672358794237358255761152/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (7703968949148153026789584465507/14662254863210418012160000000000:ℝ) row004_coefficients
      (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row004_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row004_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row004_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]

def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2675616389376701150696386934965624/29864116931186229169921875:ℝ), (8005471244773829900988502857781352/29864116931186229169921875:ℝ), (7984093321417556349887844910665832/29864116931186229169921875:ℝ), (98305128371126948133175147698152/1106078404858749228515625:ℝ)],
![(2320862334087514876946441081038832/29864116931186229169921875:ℝ), (6923704385853970174989403600181968/29864116931186229169921875:ℝ), (1376968462664107960255862327143888/5972823386237245833984375:ℝ), (84518528205706833453198115428752/1106078404858749228515625:ℝ)],
![(16930708382184133403757375900808/29864116931186229169921875:ℝ), (33844658457117223261839104657816/29864116931186229169921875:ℝ), (16913954609983332325922002194508/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (413897984706227246771167889149777/791761762613362572656640000000000:ℝ) row005_coefficients
      (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row005_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row005_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]

def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2671135675928310615779496163213312/29864116931186229169921875:ℝ), (7992029104428658296237830542524416/29864116931186229169921875:ℝ), (7970651181072384745137172595408896/29864116931186229169921875:ℝ), (3634784297080983627817336373248/40965866846620341796875:ℝ)],
![(463158936273970107120776693460544/5972823386237245833984375:ℝ), (6908542515451265315241386115917632/29864116931186229169921875:ℝ), (6869721530668123105810949508399104/29864116931186229169921875:ℝ), (3123420708623742559908706254848/40965866846620341796875:ℝ)],
![(16897209907883016183767175363208/29864116931186229169921875:ℝ), (33777675113665716225379523895116/29864116931186229169921875:ℝ), (16880469740832942509452621969408/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (50266825374480208709496703153/96650605787763985920000000000:ℝ) row006_coefficients
      (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row006_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row006_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]

def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(742608899314995477733416843287/238912935449489833359375000:ℝ), (1559461125372876725325616442917/238912935449489833359375000:ℝ), (946526826679583588868822224873/238912935449489833359375000:ℝ), (4754389116735985306587875009/8848627238869993828125000:ℝ)],
![(133921051994209901157529955947/23891293544948983335937500:ℝ), (1343794676872987074546955971829/119456467724744916679687500:ℝ), (738307424572091096761522833503/119456467724744916679687500:ℝ), (2318304844025345691494134867/4424313619434996914062500:ℝ)],
![(598866869200254252261882716183/238912935449489833359375000:ℝ), (1136047282483436812825038886141/238912935449489833359375000:ℝ), (269479076489114976975171834979/119456467724744916679687500:ℝ), (0:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1125455579506579392785865172969/2061879590138965032960000000000:ℝ) row007_coefficients
      (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row007_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row007_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]

def row008_coefficients : Fin 3 → Fin 3 → ℝ := ![![(727056089004502324668593/60578071020000000000:ℝ), (612129258931139082116857/30289035510000000000:ℝ), (55408080427851036334709/6730896780000000000:ℝ)],
![(471252291809203847102681/30289035510000000000:ℝ), (356293598683431434172877/15144517755000000000:ℝ), (26995418768430831704527/3365448390000000000:ℝ)],
![(227427136934999731475069/60578071020000000000:ℝ), (112819678641957364358527/30289035510000000000:ℝ), (0:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (4235314985765597785433023/7057856821985280000000000:ℝ) row008_coefficients
      (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row008_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row008_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]

def row009_coefficients : Fin 3 → Fin 3 → ℝ := ![![(2444181830319381762725617/60578071020000000000:ℝ), (443453752031684450503333/6057807102000000000:ℝ), (221313998332260692194997/6730896780000000000:ℝ)],
![(284265202116050879207813/6057807102000000000:ℝ), (1194656351045146498374797/15144517755000000000:ℝ), (107734506096473007200911/3365448390000000000:ℝ)],
![(449490934916744454676093/60578071020000000000:ℝ), (223851577632829725959039/30289035510000000000:ℝ), (0:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1832418778682849631895111/3136825254215680000000000:ℝ) row009_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row009_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row009_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]

def row010_coefficients : Fin 3 → Fin 3 → ℝ := ![![(8860922470841618820098033/60578071020000000000:ℝ), (8410036920505466774574649/30289035510000000000:ℝ), (35380540734054214295549/269235871200000000:ℝ)],
![(4772060750353262160310937/30289035510000000000:ℝ), (4321969157999483293177741/15144517755000000000:ℝ), (86077809533420508669827/673089678000000000:ℝ)],
![(893618530880233901078141/60578071020000000000:ℝ), (445915375614574449160063/30289035510000000000:ℝ), (0:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (13014691500340470569429171/22585141830352896000000000:ℝ) row010_coefficients
      (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row010_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row010_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]

def row011_coefficients : Fin 3 → Fin 3 → ℝ := ![![(33624360383456005659876337/60578071020000000000:ℝ), (32725529872769468543724089/30289035510000000000:ℝ), (3536463295230646101668789/6730896780000000000:ℝ)],
![(17275879438822904354451097/30289035510000000000:ℝ), (3275788796166356709676009/3028903551000000000:ℝ), (1720403598466542356267407/3365448390000000000:ℝ)],
![(1781873722807212793882237/60578071020000000000:ℝ), (890042971578063895562111/30289035510000000000:ℝ), (0:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (86170652094667399531567061/150567612202352640000000000:ℝ) row011_coefficients
      (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row011_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row011_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row011_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]

def row012_coefficients : Fin 3 → Fin 3 → ℝ := ![![(130871062734964430239566833/60578071020000000000:ℝ), (129076342303577122982156857/30289035510000000000:ℝ), (14142565796353633245799349/6730896780000000000:ℝ)],
![(65492913651456695405117081/30289035510000000000:ℝ), (63702290462190890721170317/15144517755000000000:ℝ), (6879254570698144944591247/3365448390000000000:ℝ)],
![(3558384106661170579490429/60578071020000000000:ℝ), (1778298163505042788366207/30289035510000000000:ℝ), (0:ℝ)]]
theorem row012_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1030489441029347623799314303/1806811346428231680000000000:ℝ) row012_coefficients
      (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row012_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row012_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row012_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row012_coefficients]

def row013_coefficients : Fin 3 → Fin 3 → ℝ := ![![(6541895035727084989308427/3028903551000000000:ℝ), (126020166580221949234576/29579136240234375:ℝ), (6903910087714069864024/3286570693359375:ℝ)],
![(32734049841821152537647811/15144517755000000000:ℝ), (124373242886200622764544/29579136240234375:ℝ), (6715681954772716048144/3286570693359375:ℝ)],
![(3554808547359000573974399/60578071020000000000:ℝ), (1734873421732380650008/29579136240234375:ℝ), (0:ℝ)]]
theorem row013_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (62679115752074500929281/110279012843520000000000:ℝ) row013_coefficients
      (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row013_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row013_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row013_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row013_coefficients]

def row014_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2642664355381251407791708087943/238912935449489833359375000:ℝ), (5285779765674450447532687214197/238912935449489833359375000:ℝ), (579484649530724602406781269893/47782587089897966671875000:ℝ), (9155439947416088842376934193/8848627238869993828125000:ℝ)],
![(2501187573839660900740173960839/119456467724744916679687500:ℝ), (4870284976895349924088853042821/119456467724744916679687500:ℝ), (19989797635727205811292384179/955651741797959333437500:ℝ), (4518830259365397459388664459/4424313619434996914062500:ℝ)],
![(472395208174244222421727966747/47782587089897966671875000:ℝ), (892541848445317757940352451369/47782587089897966671875000:ℝ), (210889629179180979008530992311/23891293544948983335937500:ℝ), (0:ℝ)]]
theorem row014_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (850925087889216634479856693733/1649503672111172026368000000000:ℝ) row014_coefficients
      (21/64:ℝ) (45/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row014_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row014_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row014_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row014_coefficients]

def row015_coefficients : Fin 3 → Fin 3 → ℝ := ![![(1868788437384604510932353/60578071020000000000:ℝ), (282071720842487008493237/6057807102000000000:ℝ), (106564432182733953892453/6730896780000000000:ℝ)],
![(1381138127636196279677129/30289035510000000000:ℝ), (184682152825897380567497/3028903551000000000:ℝ), (52573594645872290483399/3365448390000000000:ℝ)],
![(181093292041776482072041/12115614204000000000:ℝ), (89764932850554468267683/6057807102000000000:ℝ), (0:ℝ)]]
theorem row015_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (3196436010683557111340003/5646285457588224000000000:ℝ) row015_coefficients
      (21/64:ℝ) (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row015_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row015_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row015_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row015_coefficients]

def row016_coefficients : Fin 3 → Fin 3 → ℝ := ![![(5623801083886173977798593/60578071020000000000:ℝ), (4721243654750515062930377/30289035510000000000:ℝ), (425093038246577351010469/6730896780000000000:ℝ)],
![(3680130932559154095072649/30289035510000000000:ℝ), (2779634107925881518098861/15144517755000000000:ℝ), (209624026053631336608647/3365448390000000000:ℝ)],
![(357496305061550327534057/12115614204000000000:ℝ), (177966439360441390998691/6057807102000000000:ℝ), (0:ℝ)]]
theorem row016_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (276183283059392847062799/501892040674508800000000:ℝ) row016_coefficients
      (21/64:ℝ) (45/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row016_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row016_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row016_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row016_coefficients]

def row017_coefficients : Fin 3 → Fin 3 → ℝ := ![![(18854861032382274728667329/60578071020000000000:ℝ), (17064048411319636920995017/30289035510000000000:ℝ), (339564153530251980541217/1346179356000000000:ℝ)],
![(11097976593436218210201737/30289035510000000000:ℝ), (9311940846549819232959661/15144517755000000000:ℝ), (167408534463410963201563/673089678000000000:ℝ)],
![(710302331101098018458089/12115614204000000000:ℝ), (354369452380215236460707/6057807102000000000:ℝ), (0:ℝ)]]
theorem row017_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (49002688619589614452845731/90340567321411584000000000:ℝ) row017_coefficients
      (21/64:ℝ) (45/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row017_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row017_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row017_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row017_coefficients]

def row018_coefficients : Fin 3 → Fin 3 → ℝ := ![![(2728044782053852939957993/2423122840800000000:ℝ), (64633796546429727905669321/30289035510000000000:ℝ), (6785958295568608035935653/6730896780000000000:ℝ)],
![(7442621623862988075562421/6057807102000000000:ℝ), (33655994527922288600033453/15144517755000000000:ℝ), (3345151098635523323400839/3365448390000000000:ℝ)],
![(1415914383180193400306153/12115614204000000000:ℝ), (707175478419762927384739/6057807102000000000:ℝ), (0:ℝ)]]
theorem row018_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (64864946698392754803692257/120454089761882112000000000:ℝ) row018_coefficients
      (21/64:ℝ) (45/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row018_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row018_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row018_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row018_coefficients]

def row019_coefficients : Fin 3 → Fin 3 → ℝ := ![![(258430191077161810113694913/60578071020000000000:ℝ), (10052393892181491957967921/1211561420400000000:ℝ), (27132961627835236421748133/6730896780000000000:ℝ)],
![(134561131987570760462441609/30289035510000000000:ℝ), (25492372541433120616717961/3028903551000000000:ℝ), (13374452486438946532565639/3365448390000000000:ℝ)],
![(2827138487338384164002281/12115614204000000000:ℝ), (1412787530498858309232803/6057807102000000000:ℝ), (0:ℝ)]]
theorem row019_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (775552221893374673480304803/1445449077142585344000000000:ℝ) row019_coefficients
      (21/64:ℝ) (45/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row019_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row019_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row019_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row019_coefficients]

def row020_coefficients : Fin 3 → Fin 3 → ℝ := ![![(64579178205950593290094463/15144517755000000000:ℝ), (245315937665802931647376/29579136240234375:ℝ), (13243135776604078280408/3286570693359375:ℝ)],
![(67245065275617882078867703/15144517755000000000:ℝ), (248824883246134140365696/29579136240234375:ℝ), (13054907643662724464528/3286570693359375:ℝ)],
![(2824011634657049072928931/12115614204000000000:ℝ), (1378148539216983167672/5915827248046875:ℝ), (0:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (47163587051923683130333/88223210274816000000000:ℝ) row020_coefficients
      (21/64:ℝ) (45/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row020_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row020_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row020_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row020_coefficients]

def row021_coefficients : Fin 3 → Fin 4 → ℝ := ![![(325351603787806204872304796512/29864116931186229169921875:ℝ), (648152451315034296288894733991/29864116931186229169921875:ℝ), (2831406660085495370694705538193/238912935449489833359375000:ℝ), (8919881090045500995177723643/8848627238869993828125000:ℝ)],
![(615900324333502462586726061248/29864116931186229169921875:ℝ), (1194410968962878308981016771488/29864116931186229169921875:ℝ), (610394561852851108592116859732/29864116931186229169921875:ℝ), (1100262707670025883947264796/1106078404858749228515625:ℝ)],
![(290831876617340097516921264736/29864116931186229169921875:ℝ), (547248399411636436324214960672/29864116931186229169921875:ℝ), (257577495656368105917293695936/29864116931186229169921875:ℝ), (0:ℝ)]]
theorem row021_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (15678861914120525959099550509/32216868595921328640000000000:ℝ) row021_coefficients
      (45/128:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row021_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row021_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row021_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row021_coefficients]

def row022_coefficients : Fin 3 → Fin 3 → ℝ := ![![(459758994453919820682623/15144517755000000000:ℝ), (691197090929784606854351/15144517755000000000:ℝ), (103729946400755208041143/6730896780000000000:ℝ)],
![(21302567349818209584587/473266179843750000:ℝ), (28369002561964207881551/473266179843750000:ℝ), (3197271984680182347359/210340524375000000:ℝ)],
![(3514340958133382445449/236633089921875000:ℝ), (1740561415282709643907/118316544960937500:ℝ), (0:ℝ)]]
theorem row022_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (58783634905511674548163/110279012843520000000000:ℝ) row022_coefficients
      (45/128:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row022_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row022_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row022_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row022_coefficients]

def row023_coefficients : Fin 3 → Fin 3 → ℝ := ![![(1377027279754820899121839/15144517755000000000:ℝ), (2305229895256869456905263/15144517755000000000:ℝ), (413403065967947995424119/6730896780000000000:ℝ)],
![(56491557996373142798203/473266179843750000:ℝ), (17004111746187902191907/94653235968750000:ℝ), (12736189994644791175967/210340524375000000:ℝ)],
![(6929027533562875417993/236633089921875000:ℝ), (3447904702997456130179/118316544960937500:ℝ), (0:ℝ)]]
theorem row023_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (25356168009831535863851/49012894597120000000000:ℝ) row023_coefficients
      (45/128:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row023_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row023_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row023_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row023_coefficients]

def row024_coefficients : Fin 3 → Fin 3 → ℝ := ![![(920233047502906217210851/3028903551000000000:ℝ), (1662499655645371043423011/3028903551000000000:ℝ), (66013996864678374453007/269235871200000000:ℝ)],
![(169659312689490566036027/473266179843750000:ℝ), (283903217868905230736687/473266179843750000:ℝ), (10166340616248806816467/42068104875000000:ℝ)],
![(13758400684421861363081/236633089921875000:ℝ), (6862591278426949102723/118316544960937500:ℝ), (0:ℝ)]]
theorem row024_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (179812729533902685947111/352892841099264000000000:ℝ) row024_coefficients
      (45/128:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row024_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row024_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row024_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row024_coefficients]

def row025_coefficients : Fin 3 → Fin 3 → ℝ := ![![(16607846701665583580135023/15144517755000000000:ℝ), (31443846141430090977966511/15144517755000000000:ℝ), (6594646098973485257667703/6730896780000000000:ℝ)],
![(567153915675755639754043/473266179843750000:ℝ), (1023986723344897124775727/473266179843750000:ℝ), (203093437521122620891679/210340524375000000:ℝ)],
![(27417146986139833253257/236633089921875000:ℝ), (13691964429285935047811/118316544960937500:ℝ), (0:ℝ)]]
theorem row025_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1189612481230637961896321/2352618940661760000000000:ℝ) row025_coefficients
      (45/128:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row025_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row025_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row025_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row025_coefficients]

def row026_coefficients : Fin 3 → Fin 3 → ℝ := ![![(62854831824494217049160303/15144517755000000000:ℝ), (122173786256889619461396911/15144517755000000000:ℝ), (26364848317920549708514423/6730896780000000000:ℝ)],
![(2046779496048406696159547/473266179843750000:ℝ), (3873426483097122730792751/473266179843750000:ℝ), (811899739467600198496799/210340524375000000:ℝ)],
![(54734639589575777033609/236633089921875000:ℝ), (27350710731003906937987/118316544960937500:ℝ), (0:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (14220615135178079765722243/28231427287941120000000000:ℝ) row026_coefficients
      (45/128:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row026_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row026_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row026_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]

def row027_coefficients : Fin 3 → Fin 3 → ℝ := ![![(251278694914901549160524591/60578071020000000000:ℝ), (238490973889069587514024/29579136240234375:ℝ), (12866679510721370648648/3286570693359375:ℝ)],
![(1636357781711887879592923/378612943875000000:ℝ), (241938549924174866339072/29579136240234375:ℝ), (12678451377780016832768/3286570693359375:ℝ)],
![(54668203334439850718339/236633089921875000:ℝ), (6829373150858985945088/29579136240234375:ℝ), (0:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (864620784414284662781/1723109575680000000000:ℝ) row027_coefficients
      (45/128:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSmall_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row027_coefficients, Fin.sum_univ_succ, power_oldSmall_capP] <;> ring
theorem row027_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
  rw [row027_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]

def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(139462416217708010912591557003/47782587089897966671875000:ℝ), (1441441782384852451235775687973/238912935449489833359375000:ℝ), (862099974874315790421933158501/238912935449489833359375000:ℝ), (4283271401994809612189453909/8848627238869993828125000:ℝ)],
![(628838938890895519457190721463/119456467724744916679687500:ℝ), (248322688421128315714120397537/23891293544948983335937500:ℝ), (671620833794085996906874222781/119456467724744916679687500:ℝ), (2082745986654757844294924317/4424313619434996914062500:ℝ)],
![(562631045266401702771423657911/238912935449489833359375000:ℝ), (1049704155936770094962171672797/238912935449489833359375000:ℝ), (245005911613743776343967757443/119456467724744916679687500:ℝ), (0:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (887798834649853801853255977033/2061879590138965032960000000000:ℝ) row028_coefficients
      (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row028_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row028_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row028_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]

def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2344740006016090598779664298613/13272940858304990742187500:ℝ), (1200782007084559874533963622419/2654588171660998148437500:ℝ), (4994995658196593765327061707551/13272940858304990742187500:ℝ), (148410736867245594516323099341/1474771206478332304687500:ℝ)],
![(326353954289182765196367342161/1327294085830499074218750:ℝ), (3889472496587640254907539426207/6636470429152495371093750:ℝ), (2905993745316374021917816190599/6636470429152495371093750:ℝ), (72016210951876513567040386133/737385603239166152343750:ℝ)],
![(956960071769772284430281232097/13272940858304990742187500:ℝ), (1890856568854341747914972666519/13272940858304990742187500:ℝ), (467029879446649152867267592211/6636470429152495371093750:ℝ), (0:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (9696625944028473337808790492299/24742555081667580395520000000000:ℝ) row029_coefficients
      (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row029_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row029_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row029_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row029_coefficients]

def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1437650124968811459747144304489/1327294085830499074218750:ℝ), (19588940348970246469434488516647/6636470429152495371093750:ℝ), (17634137437853563936618230845159/6636470429152495371093750:ℝ), (193829007971668053537943105591/245795201079722050781250:ℝ)],
![(4438047691890770384561543846957/3318235214576247685546875:ℝ), (2278206195288178968493836002171/663647042915249537109375:ℝ), (9489841578865036608635725951439/3318235214576247685546875:ℝ), (93955027167075283899396843983/122897600539861025390625:ℝ)],
![(1845464097623215896148089946169/6636470429152495371093750:ℝ), (3668272775083051076975199469663/6636470429152495371093750:ℝ), (911445154182099800976015699247/3318235214576247685546875:ℝ), (0:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (12313679892830225818362357341009/32990073442223440527360000000000:ℝ) row030_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row030_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row030_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row030_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row030_coefficients]

def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24556862134766079323493242465641/3318235214576247685546875:ℝ), (69802610820001334770390048812347/3318235214576247685546875:ℝ), (65955450354672662503071788606971/3318235214576247685546875:ℝ), (460214876004249742132832939117/73738560323916615234375:ℝ)],
![(27540944415740120405060492423954/3318235214576247685546875:ℝ), (75104895733892606764043150916598/3318235214576247685546875:ℝ), (67630368259052691555002569502534/3318235214576247685546875:ℝ), (445918764002140571346123022442/73738560323916615234375:ℝ)],
![(3623329273825929541395387061813/3318235214576247685546875:ℝ), (7224207204749389420282098388451/3318235214576247685546875:ℝ), (3600918746375642089449172264138/3318235214576247685546875:ℝ), (0:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
    Record12518109.Bernstein.bsum 2 3 (28828165888027356055790580206059/79176176261336257265664000000000:ℝ) row031_coefficients
      (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSmall_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row031_coefficients, Fin.sum_univ_succ, power_oldSmall_old] <;> ring
theorem row031_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
  rw [row031_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]

end
end Qrh.JointDetector.PointwiseReturn.FinalEdges
