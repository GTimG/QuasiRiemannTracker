/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell1 : Cell := ⟨(991173/1000000:ℝ), (2034191/500000:ℝ), (429/625:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (9958353/10000000:ℝ), (2129819/500000:ℝ), (39/2000:ℝ), (3/125:ℝ), (1/4:ℝ), (13/25:ℝ), (17/10000:ℝ), (1/25:ℝ)⟩
def cell1_regular0_g : Fin 2 → Fin 5 → ℝ := ![![(229765671103819852051763562419497673861369/341966517985797888040470703125000:ℝ), (35964420441525344570314126967981326357664557/6155397323744361984728472656250000:ℝ), (54681955714288654765938247078670633422997057/4103598215829574656485648437500000:ℝ), (96702768843032260388383442172153853436261701/8207196431659149312971296875000000:ℝ), (178724564546646483251635255651144184329197239/49243178589954895877827781250000000:ℝ)],
  ![(667497310021683869579171963702774639222460109/499613082777250714427127697265625000:ℝ), (24544015485078822743761670138289022151495139259/2997678496663504286562766183593750000:ℝ), (32764257730623825908534791439658761953562066759/1998452331109002857708510789062500000:ℝ), (18045210407495269152514993277347391231257316129/1332301554072668571805673859375000000:ℝ), (95983839961334134076090395845719888666756555393/23981427973308034292502129468750000000:ℝ)]]
theorem cell1_regular0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell1 0 b ν := by
 have heq : highRegular cell1 0 b ν = Record12518109.Bernstein.bsum 1 4 (2067891039934378668465872061775479064752321/17914650260325469970703125000000000000000:ℝ) cell1_regular0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_regular0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_regular0_g]
def cell1_regular1_g : Fin 2 → Fin 5 → ℝ := ![![(364253591461363520454230883110737074413/666601399582452023470703125000:ℝ), (2124589544810344646745191075678710934120503/323968280197071683406761718750000:ℝ), (3467739129755464460727405378298391350388003/215978853464714455604507812500000:ℝ), (6307094874912839795761664253999332540230879/431957706929428911209015625000000:ℝ), (11813477727643182117831047537722320709760381/2591746241576573467254093750000000:ℝ)],
  ![(9668204218842382170854867702574032014456537/8765141803109661656616275390625000:ℝ), (1419071716269603868464560492814636203354184961/157772552455973909819092957031250000:ℝ), (2100792998086395012725703479967977329826457461/105181701637315939879395304687500000:ℝ), (3651014586336767735554370172609173970529938073/210363403274631879758790609375000000:ℝ), (6658444515959785966412473178901165693465805547/1262180419647791278552743656250000000:ℝ)]]
theorem cell1_regular1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell1 1 b ν := by
 have heq : highRegular cell1 1 b ν = Record12518109.Bernstein.bsum 1 4 (88513622725111335470378104595909109082359/942876329490814208984375000000000000000:ℝ) cell1_regular1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_regular1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_regular1_g]
def cell1_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(247727912576192017624596690122825921651/17998237788726204633708984375000:ℝ), (980208496780924252748149169183182293545503/323968280197071683406761718750000:ℝ), (1912124434409025912456650343393920366063003/215978853464714455604507812500000:ℝ), (3739915015055435233718077423291323701755879/431957706929428911209015625000000:ℝ), (7303091411484963113055975104468534991110381/2591746241576573467254093750000000:ℝ)],
  ![(2992018939300129811501080992521924340532111/26295425409328984969848826171875000:ℝ), (478839708829538394411481301769673130394159961/157772552455973909819092957031250000:ℝ), (874459863587882626992607232705828085460182461/105181701637315939879395304687500000:ℝ), (557632618459111908926164443707577680397537691/70121134424877293252930203125000000:ℝ), (3232364772849160812129226343847978298483255547/1262180419647791278552743656250000000:ℝ)]]
theorem cell1_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell1 2 b ν := by
 have heq : highRegular cell1 2 b ν = Record12518109.Bernstein.bsum 1 4 (2229551213185728158621370211105433294859/942876329490814208984375000000000000000:ℝ) cell1_regular2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_regular2_g]
def cell1_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(4305531358770348055110862498041971651/17998237788726204633708984375000:ℝ), (944817226658662179630335462642761019195503/323968280197071683406761718750000:ℝ), (43377598076880390436458239408809832074721/5022764034063126874523437500000:ℝ), (3670718584589592319261377141222306867205879/431957706929428911209015625000000:ℝ), (7201811255340264189630036002916523411160381/2591746241576573467254093750000000:ℝ)],
  ![(6812756603557266787836896472614989582111/26295425409328984969848826171875000:ℝ), (406904682112504143519975040678081719785709961/157772552455973909819092957031250000:ℝ), (804970149203522813971423657030531810664232461/105181701637315939879395304687500000:ℝ), (529044410785882207764132294370196864255587691/70121134424877293252930203125000000:ℝ), (3119180736241384865361795893481992409047605547/1262180419647791278552743656250000000:ℝ)]]
theorem cell1_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell1 3 b ν := by
 have heq : highRegular cell1 3 b ν = Record12518109.Bernstein.bsum 1 4 (38749782228933132495997762482377744859/942876329490814208984375000000000000000:ℝ) cell1_regular3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_regular3_g]
def cell1_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(12085703390241978420504419458241152793482111/26295425409328984969848826171875000:ℝ), (640592321778226320366761541416427041067609961/157772552455973909819092957031250000:ℝ), (994438782901640919439608889053577016571132461/105181701637315939879395304687500000:ℝ), (199929214681591448176199917183219791101495897/23373711474959097750976734375000000:ℝ), (3407947754514220728465623303465708953673905547/1262180419647791278552743656250000000:ℝ)],
  ![(6177408806740901841694791898618128462482111/26295425409328984969848826171875000:ℝ), (465231106804476123315794109464359144505109961/157772552455973909819092957031250000:ℝ), (787643393279961262369890700717972133758632461/105181701637315939879395304687500000:ℝ), (1484446962108577464174363233656180268350963073/210363403274631879758790609375000000:ℝ), (2880709588964734644175833851027354461486405547/1262180419647791278552743656250000000:ℝ)]]
theorem cell1_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highRegular cell1 4 b ν := by
 have heq : highRegular cell1 4 b ν = Record12518109.Bernstein.bsum 1 4 (18532226420222705525084375695854385387446333/459180772462026519775390625000000000000000:ℝ) cell1_regular4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_regular4_g]
def cell1_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(10809234750316780065466365107927314061/948594912120091542759468750000000:ℝ), (50606794043233686339345411513068111881/1897189824240183085518937500000000:ℝ), (2157934555352688718073251522046712153/140532579573346895223625000000000:ℝ)],
  ![(9385349815934985220213297912646314061/948594912120091542759468750000000:ℝ), (44541525083913339256789683960255611881/1897189824240183085518937500000000:ℝ), (5757379883635227282316722730202636459/421597738720040685670875000000000:ℝ)]]
theorem cell1_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 0 false b ν := by
 have heq : highBranch cell1 0 false b ν = Record12518109.Bernstein.bsum 1 2 (9385349815934985220213297912646314061/22334552772552969921875000000000000000:ℝ) cell1_exceptional0_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional0_0_g]
def cell1_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(405021004627762059654026894625327817623463/35556183090997391297253167156250000000:ℝ), (632115021885323737050103483315189085461841/23704122060664927531502111437500000000:ℝ), (2183385620474023565272219798886593832834273/142224732363989565189012668625000000000:ℝ)],
  ![(351693495676474056263987133904185094623463/35556183090997391297253167156250000000:ℝ), (556391128504863272072507184558173772961841/23704122060664927531502111437500000000:ℝ), (1941871919090093238699318769472336020334273/142224732363989565189012668625000000000:ℝ)]]
theorem cell1_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 0 true b ν := by
 have heq : highBranch cell1 0 true b ν = Record12518109.Bernstein.bsum 1 2 (351693495676474056263987133904185094623463/837166041573602971581640625000000000000000:ℝ) cell1_exceptional0_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional0_1_g]
theorem cell1_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
 (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell1 0 b ν :=
 highExceptional_pos_of_branches (cell1_exceptional0_0 hb hν) (cell1_exceptional0_1 hb hν)
def cell1_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(9295908389251100543884458132767473/942000905779634104031250000000:ℝ), (70288257971375976160527513804134483/1884001811559268208062500000000:ℝ), (11519829689040066861711160095285637/418667069235392935125000000000:ℝ)],
  ![(425086984041334523191440589837676069/49926048006320607513656250000000:ℝ), (3366252890868577088965763278181627599/99852096012641215027312500000000:ℝ), (560735480201724055709203789737638761/22189354669475825561625000000000:ℝ)]]
theorem cell1_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 1 false b ν := by
 have heq : highBranch cell1 1 false b ν = Record12518109.Bernstein.bsum 1 2 (425086984041334523191440589837676069/1175502777502787890625000000000000000:ℝ) cell1_exceptional1_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional1_0_g]
def cell1_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(18459792756579857218861959130776060919327/1871378057420915331434377218750000000:ℝ), (46535222482268706324888676486334222014439/1247585371613943554289584812500000000:ℝ), (205939506376404881789026668578941645807067/7485512229683661325737508875000000000:ℝ)],
  ![(15928400082073079051454877536488943919327/1871378057420915331434377218750000000:ℝ), (977964620911618419560850356571936849173/29013613293347524518362437500000000:ℝ), (189143331380947858741944313309605708307067/7485512229683661325737508875000000000:ℝ)]]
theorem cell1_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 1 true b ν := by
 have heq : highBranch cell1 1 true b ν = Record12518109.Bernstein.bsum 1 2 (15928400082073079051454877536488943919327/44061370609136998504296875000000000000000:ℝ) cell1_exceptional1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional1_1_g]
theorem cell1_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
 (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell1 1 b ν :=
 highExceptional_pos_of_branches (cell1_exceptional1_0 hb hν) (cell1_exceptional1_1 hb hν)
def cell1_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(494676157638181015107979897655529331/44378709338951651123250000000000:ℝ), (5395862074185907770750933063045337/319526707240451888087400000000:ℝ), (863292468052818773996930236499/146069351881349434554240000:ℝ)],
  ![(1319246631501435504943440683102587993/133136128016854953369750000000000:ℝ), (4692916360997620683271534212045337/319526707240451888087400000000:ℝ), (721546544758948310530451236499/146069351881349434554240000:ℝ)]]
theorem cell1_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 2 false b ν := by
 have heq : highBranch cell1 2 false b ν = Record12518109.Bernstein.bsum 1 2 (721546544758948310530451236499/3439185269036728000000000000000:ℝ) cell1_exceptional2_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional2_0_g]
def cell1_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(23830925802521946670507671374465335703551/2138717779909617521639288250000000000:ℝ), (28879751890999139447144256984047287733/1710974223927694017311430600000000:ℝ), (10779253546373597010787450428397019/1825039172189540285132192640000:ℝ)],
  ![(21186491576484130399830676830351487703551/2138717779909617521639288250000000000:ℝ), (25119835942528007312863474812488287733/1710974223927694017311430600000000:ℝ), (3003470164840599210876790476465673/608346390729846761710730880000:ℝ)]]
theorem cell1_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 2 true b ν := by
 have heq : highBranch cell1 2 true b ν = Record12518109.Bernstein.bsum 1 2 (27031231483565392897891114288191057/128910981439303675624000000000000000:ℝ) cell1_exceptional2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional2_1_g]
theorem cell1_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
 (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell1 2 b ν :=
 highExceptional_pos_of_branches (cell1_exceptional2_0 hb hν) (cell1_exceptional2_1 hb hν)
def cell1_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(1039894834886703195940369456436368229/105399434680010171417718750000000:ℝ), (4920137691594396906482091279229790209/210798869360020342835437500000000:ℝ), (5714255897968158974641244566140136459/421597738720040685670875000000000:ℝ)],
  ![(881685397733170435356695323627368229/105399434680010171417718750000000:ℝ), (1415406306112193521325299776305763403/70266289786673447611812500000000:ℝ), (1665944038515106700912737576734212153/140532579573346895223625000000000:ℝ)]]
theorem cell1_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 3 false b ν := by
 have heq : highBranch cell1 3 false b ν = Record12518109.Bernstein.bsum 1 2 (7935168579598533918210257912646314061/22334552772552969921875000000000000000:ℝ) cell1_exceptional3_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional3_0_g]
def cell1_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(350663861346162855501046946305327817623463/35556183090997391297253167156250000000:ℝ), (1659244294379737959303640436975567256385523/71112366181994782594506334312500000000:ℝ), (1927154459552197647962948185916593832834273/142224732363989565189012668625000000000:ℝ)],
  ![(297336352394874852111007185584185094623463/35556183090997391297253167156250000000:ℝ), (1432072614238356564370851540704521318885523/71112366181994782594506334312500000000:ℝ), (1685640758168267321390047156502336020334273/142224732363989565189012668625000000000:ℝ)]]
theorem cell1_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 3 true b ν := by
 have heq : highBranch cell1 3 true b ν = Record12518109.Bernstein.bsum 1 2 (297336352394874852111007185584185094623463/837166041573602971581640625000000000000000:ℝ) cell1_exceptional3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional3_1_g]
theorem cell1_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
 (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell1 3 b ν :=
 highExceptional_pos_of_branches (cell1_exceptional3_0 hb hν) (cell1_exceptional3_1 hb hν)
def cell1_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(419297563242906811321028781036676069/49926048006320607513656250000000:ℝ), (1116245464914947865785157743873042533/33284032004213738342437500000000:ℝ), (5036179309619933713055613365451248849/199704192025282430054625000000000:ℝ)],
  ![(351701402653933005686593089837676069/49926048006320607513656250000000:ℝ), (996570537710164649937759426060542533/33284032004213738342437500000000:ℝ), (4587839869763338321402224107638748849/199704192025282430054625000000000:ℝ)]]
theorem cell1_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 4 false b ν := by
 have heq : highBranch cell1 4 false b ν = Record12518109.Bernstein.bsum 1 2 (351701402653933005686593089837676069/1175502777502787890625000000000000000:ℝ) cell1_exceptional4_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional4_0_g]
def cell1_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(581817815164292079193620751417631885901/69310298422996864127199156250000000:ℝ), (125491770733349548669813434204002666043317/3742756114841830662868754437500000000:ℝ), (188743076175133087068813463948941645807067/7485512229683661325737508875000000000:ℝ)],
  ![(488062530923300295215580692369960885901/69310298422996864127199156250000000:ℝ), (2605663706607958274848769784715810547519/87040839880042573555087312500000000:ℝ), (171946901179676064021731108679605708307067/7485512229683661325737508875000000000:ℝ)]]
theorem cell1_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highBranch cell1 4 true b ν := by
 have heq : highBranch cell1 4 true b ν = Record12518109.Bernstein.bsum 1 2 (13177688334929107970820678693988943919327/44061370609136998504296875000000000000000:ℝ) cell1_exceptional4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_exceptional4_1_g]
theorem cell1_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
 (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < highExceptional cell1 4 b ν :=
 highExceptional_pos_of_branches (cell1_exceptional4_0 hb hν) (cell1_exceptional4_1 hb hν)
def cell1_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(22371098456109958641834837/20266420978329954137500000000:ℝ)],
  ![(51727770377803347626044565619/9869747016446687664962500000000:ℝ)]]
theorem cell1_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 0 false b := by
 have heq : domainBranch cell1 0 false b = Record12518109.Bernstein.bsum 1 0 (67113295368329875925504511/5790405993808558325000000000000:ℝ) cell1_domain0_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain0_0_g]
def cell1_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(22371098456109958641834837/20266420978329954137500000000:ℝ)],
  ![(51727770377803347626044565619/9869747016446687664962500000000:ℝ)]]
theorem cell1_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 0 true b := by
 have heq : domainBranch cell1 0 true b = Record12518109.Bernstein.bsum 1 0 (67113295368329875925504511/5790405993808558325000000000000:ℝ) cell1_domain0_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain0_1_g]
def cell1_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(109480939956774914365810068750569/210650097728499590000000000000000:ℝ)],
  ![(51413131202690596274824838750569/210650097728499590000000000000000:ℝ)]]
theorem cell1_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 1 false b := by
 have heq : domainBranch cell1 1 false b = Record12518109.Bernstein.bsum 1 0 (154239393608071788824474516251707/60185742208142740000000000000000000:ℝ) cell1_domain1_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain1_0_g]
def cell1_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(144502566495072330078779495284691/210650097728499590000000000000000:ℝ)],
  ![(86434757740988011987794265284691/210650097728499590000000000000000:ℝ)]]
theorem cell1_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 1 true b := by
 have heq : domainBranch cell1 1 true b = Record12518109.Bernstein.bsum 1 0 (259304273222964035963382795854073/60185742208142740000000000000000000:ℝ) cell1_domain1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain1_1_g]
def cell1_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(141660816207120125675184461137/324409801429927500000000000000:ℝ)],
  ![(98127162400625958404054102573719/157987573296374692500000000000000:ℝ)]]
theorem cell1_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 2 false b := by
 have heq : domainBranch cell1 2 false b = Record12518109.Bernstein.bsum 1 0 (141660816207120125675184461137/30896171564755000000000000000000:ℝ) cell1_domain2_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain2_0_g]
def cell1_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(88858711633698637740834886843/324409801429927500000000000000:ℝ)],
  ![(72412537473369693780025859892541/157987573296374692500000000000000:ℝ)]]
theorem cell1_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 2 true b := by
 have heq : domainBranch cell1 2 true b = Record12518109.Bernstein.bsum 1 0 (88858711633698637740834886843/30896171564755000000000000000000:ℝ) cell1_domain2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain2_1_g]
def cell1_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(2121972306844184080195969007/12976392057197100000000000000:ℝ)],
  ![(32192398293049392056690866906409/6319502931854987700000000000000:ℝ)]]
theorem cell1_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 3 false b := by
 have heq : domainBranch cell1 3 false b = Record12518109.Bernstein.bsum 1 0 (2121972306844184080195969007/1235846862590200000000000000000:ℝ) cell1_domain3_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain3_0_g]
def cell1_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(2121972306844184080195969007/12976392057197100000000000000:ℝ)],
  ![(32192398293049392056690866906409/6319502931854987700000000000000:ℝ)]]
theorem cell1_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 3 true b := by
 have heq : domainBranch cell1 3 true b = Record12518109.Bernstein.bsum 1 0 (2121972306844184080195969007/1235846862590200000000000000000:ℝ) cell1_domain3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain3_1_g]
def cell1_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(14653697286778849718124983/5266252443212489750000000:ℝ)],
  ![(1620932596692098108124983/5266252443212489750000000:ℝ)]]
theorem cell1_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 4 false b := by
 have heq : domainBranch cell1 4 false b = Record12518109.Bernstein.bsum 1 0 (4862797790076294324374949/1504643555203568500000000000:ℝ) cell1_domain4_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain4_0_g]
def cell1_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(14653697286778849718124983/5266252443212489750000000:ℝ)],
  ![(1620932596692098108124983/5266252443212489750000000:ℝ)]]
theorem cell1_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 4 true b := by
 have heq : domainBranch cell1 4 true b = Record12518109.Bernstein.bsum 1 0 (4862797790076294324374949/1504643555203568500000000000:ℝ) cell1_domain4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain4_1_g]
def cell1_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(15670291166155482713925189065197/31597514659274938500000000000000:ℝ)],
  ![(7032689144020266244568199065197/31597514659274938500000000000000:ℝ)]]
theorem cell1_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 5 false b := by
 have heq : domainBranch cell1 5 false b = Record12518109.Bernstein.bsum 1 0 (7032689144020266244568199065197/3009287110407137000000000000000000:ℝ) cell1_domain5_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain5_0_g]
def cell1_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(6973585926122618838299064577061/10532504886424979500000000000000:ℝ)],
  ![(4094385252077546681846734577061/10532504886424979500000000000000:ℝ)]]
theorem cell1_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 5 true b := by
 have heq : domainBranch cell1 5 true b = Record12518109.Bernstein.bsum 1 0 (12283155756232640045540203731183/3009287110407137000000000000000000:ℝ) cell1_domain5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain5_1_g]
def cell1_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(6167216016858460532077534072467418819/672969870741022902411315000000000000:ℝ)],
  ![(4241937322079442704370021373137418819/672969870741022902411315000000000000:ℝ)]]
theorem cell1_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 6 false b := by
 have heq : domainBranch cell1 6 false b = Record12518109.Bernstein.bsum 1 0 (4241937322079442704370021373137418819/64092368642002181182030000000000000000:ℝ) cell1_domain6_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain6_0_g]
def cell1_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(6130252880516599297728714417893660641/672969870741022902411315000000000000:ℝ)],
  ![(4204974185737581470021201718563660641/672969870741022902411315000000000000:ℝ)]]
theorem cell1_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 6 true b := by
 have heq : domainBranch cell1 6 true b = Record12518109.Bernstein.bsum 1 0 (4204974185737581470021201718563660641/64092368642002181182030000000000000000:ℝ) cell1_domain6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain6_1_g]
def cell1_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(39606293719020645780107641/64881960285985500000000000:ℝ)],
  ![(183239916309850659525865421167/31597514659274938500000000000:ℝ)]]
theorem cell1_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 7 false b := by
 have heq : domainBranch cell1 7 false b = Record12518109.Bernstein.bsum 1 0 (39606293719020645780107641/6179234312951000000000000000:ℝ) cell1_domain7_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain7_0_g]
def cell1_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(39606293719020645780107641/64881960285985500000000000:ℝ)],
  ![(183239916309850659525865421167/31597514659274938500000000000:ℝ)]]
theorem cell1_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 7 true b := by
 have heq : domainBranch cell1 7 true b = Record12518109.Bernstein.bsum 1 0 (39606293719020645780107641/6179234312951000000000000000:ℝ) cell1_domain7_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain7_1_g]
def cell1_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(4888430619443646374142145174223/658281555401561218750000000000:ℝ)],
  ![(3660189791877965297584735174223/658281555401561218750000000000:ℝ)]]
theorem cell1_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 8 false b := by
 have heq : domainBranch cell1 8 false b = Record12518109.Bernstein.bsum 1 0 (10980569375633895892754205522669/188080444400446062500000000000000:ℝ) cell1_domain8_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain8_0_g]
def cell1_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(14806313385972119678003464006591/1974844666204683656250000000000:ℝ)],
  ![(11121590903275076448331234006591/1974844666204683656250000000000:ℝ)]]
theorem cell1_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < domainBranch cell1 8 true b := by
 have heq : domainBranch cell1 8 true b = Record12518109.Bernstein.bsum 1 0 (11121590903275076448331234006591/188080444400446062500000000000000:ℝ) cell1_domain8_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_domain8_1_g]
def cell1_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(8803008591106306763/86509280381314000000:ℝ)],
  ![(37704410543065570393581/42130019545699918000000:ℝ)]]
theorem cell1_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 0 b := by
 have heq : ordinary cell1 0 b = Record12518109.Bernstein.bsum 1 0 (26409025773318920289/24716937251804000000000:ℝ) cell1_ordinary0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary0_g]
def cell1_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(352537436294137612957771/379170175911299262000000:ℝ)],
  ![(51781328061366421957771/379170175911299262000000:ℝ)]]
theorem cell1_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 1 b := by
 have heq : ordinary cell1 1 b = Record12518109.Bernstein.bsum 1 0 (51781328061366421957771/36111445324885644000000000:ℝ) cell1_ordinary1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary1_g]
def cell1_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(31159657894800828090170573/631950293185498770000000:ℝ)],
  ![(28152096812473116180170573/631950293185498770000000:ℝ)]]
theorem cell1_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 2 b := by
 have heq : ordinary cell1 2 b = Record12518109.Bernstein.bsum 1 0 (28152096812473116180170573/60185742208142740000000000:ℝ) cell1_ordinary2_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary2_g]
def cell1_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(81666663/70000000:ℝ)],
  ![(151666663/70000000:ℝ)]]
theorem cell1_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 3 b := by
 have heq : ordinary cell1 3 b = Record12518109.Bernstein.bsum 1 0 (244999989/20000000000:ℝ) cell1_ordinary3_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary3_g]
def cell1_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(10122738483656022496042529/210650097728499590000000:ℝ)],
  ![(8698917927423119346042529/210650097728499590000000:ℝ)]]
theorem cell1_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 4 b := by
 have heq : ordinary cell1 4 b = Record12518109.Bernstein.bsum 1 0 (26096753782269358038127587/60185742208142740000000000:ℝ) cell1_ordinary4_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary4_g]
def cell1_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(9863582118028677379/20955901463962500000000000:ℝ)],
  ![(9863582118028677379/20955901463962500000000000:ℝ)]]
theorem cell1_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < ordinary cell1 5 b := by
 have heq : ordinary cell1 5 b = Record12518109.Bernstein.bsum 1 0 (9863582118028677379/1995800139425000000000000000:ℝ) cell1_ordinary5_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_ordinary5_g]
def cell1_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(26407789926456330089/259527841143942000000:ℝ)],
  ![(113112629771774629753343/126390058637099754000000:ℝ)]]
theorem cell1_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 0 false b := by
 have heq : complementBranch cell1 0 false b = Record12518109.Bernstein.bsum 1 0 (26407789926456330089/24716937251804000000000:ℝ) cell1_complement0_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement0_0_g]
def cell1_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(1986179569517739334147709529/20266420978329954137500000000:ℝ)],
  ![(8809520191115700094050341540623/9869747016446687664962500000000:ℝ)]]
theorem cell1_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 0 true b := by
 have heq : complementBranch cell1 0 true b = Record12518109.Bernstein.bsum 1 0 (5958538708553218002443128587/5790405993808558325000000000000:ℝ) cell1_complement0_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement0_1_g]
def cell1_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(124497857001784630681854828833/31597514659274938500000000000:ℝ)],
  ![(96136057130051988776361828833/31597514659274938500000000000:ℝ)]]
theorem cell1_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 1 false b := by
 have heq : complementBranch cell1 1 false b = Record12518109.Bernstein.bsum 1 0 (96136057130051988776361828833/3009287110407137000000000000000:ℝ) cell1_complement1_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement1_0_g]
def cell1_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1553765146257379847835606118924033/394789880657867506598500000000000:ℝ)],
  ![(1199947805332390679624641025924033/394789880657867506598500000000000:ℝ)]]
theorem cell1_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 1 true b := by
 have heq : complementBranch cell1 1 true b = Record12518109.Bernstein.bsum 1 0 (3599843415997172038873923077772099/112797108759390716171000000000000000:ℝ) cell1_complement1_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement1_1_g]
def cell1_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(161762679488973515001111828833/31597514659274938500000000000:ℝ)],
  ![(33148843539650476095618828833/31597514659274938500000000000:ℝ)]]
theorem cell1_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 2 false b := by
 have heq : complementBranch cell1 2 false b = Record12518109.Bernstein.bsum 1 0 (33148843539650476095618828833/3009287110407137000000000000000:ℝ) cell1_complement2_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement2_0_g]
def cell1_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(2019364260019813498148509495924033/394789880657867506598500000000000:ℝ)],
  ![(412964562996050713020544402924033/394789880657867506598500000000000:ℝ)]]
theorem cell1_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 2 true b := by
 have heq : complementBranch cell1 2 true b = Record12518109.Bernstein.bsum 1 0 (1238893688988152139061633208772099/112797108759390716171000000000000000:ℝ) cell1_complement2_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement2_1_g]
def cell1_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(28362926758638679867346859611/10532504886424979500000000000:ℝ)],
  ![(27263329807860332315515859611/10532504886424979500000000000:ℝ)]]
theorem cell1_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 3 false b := by
 have heq : complementBranch cell1 3 false b = Record12518109.Bernstein.bsum 1 0 (81789989423580996946547578833/3009287110407137000000000000000:ℝ) cell1_complement3_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement3_0_g]
def cell1_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(454875002265201020580305832003157/169195663139086074256500000000000:ℝ)],
  ![(437444251450788550302427935003157/169195663139086074256500000000000:ℝ)]]
theorem cell1_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 3 true b := by
 have heq : complementBranch cell1 3 true b = Record12518109.Bernstein.bsum 1 0 (437444251450788550302427935003157/16113872679912959453000000000000000:ℝ) cell1_complement3_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement3_1_g]
def cell1_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(29915627695604883380649234611/10532504886424979500000000000:ℝ)],
  ![(24638862574926935953818234611/10532504886424979500000000000:ℝ)]]
theorem cell1_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 4 false b := by
 have heq : complementBranch cell1 4 false b = Record12518109.Bernstein.bsum 1 0 (73916587724780807861454703833/3009287110407137000000000000000:ℝ) cell1_complement4_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement4_0_g]
def cell1_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(3358724683517319762929479590397099/1184369641973602519795500000000000:ℝ)],
  ![(2766991044279392364640459311397099/1184369641973602519795500000000000:ℝ)]]
theorem cell1_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 4 true b := by
 have heq : complementBranch cell1 4 true b = Record12518109.Bernstein.bsum 1 0 (2766991044279392364640459311397099/112797108759390716171000000000000000:ℝ) cell1_complement4_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement4_1_g]
def cell1_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(3117141/350000:ℝ)],
  ![(308571/70000:ℝ)]]
theorem cell1_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 5 false b := by
 have heq : complementBranch cell1 5 false b = Record12518109.Bernstein.bsum 1 0 (925713/20000000:ℝ) cell1_complement5_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement5_0_g]
def cell1_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(263571925915873108088461678440619/29609241049340062994887500000000:ℝ)],
  ![(130431577091013156137744969940619/29609241049340062994887500000000:ℝ)]]
theorem cell1_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 5 true b := by
 have heq : complementBranch cell1 5 true b = Record12518109.Bernstein.bsum 1 0 (130431577091013156137744969940619/2819927718984767904275000000000000:ℝ) cell1_complement5_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement5_1_g]
def cell1_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(12010181705826317066717/859796317259182000000:ℝ)],
  ![(7236275225941060066717/859796317259182000000:ℝ)]]
theorem cell1_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 6 false b := by
 have heq : complementBranch cell1 6 false b = Record12518109.Bernstein.bsum 1 0 (151961779744762261401057/1719592634518364000000000:ℝ) cell1_complement6_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement6_0_g]
def cell1_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(413469264177385611191019699671869/29609241049340062994887500000000:ℝ)],
  ![(249108662984851251768430920671869/29609241049340062994887500000000:ℝ)]]
theorem cell1_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 6 true b := by
 have heq : complementBranch cell1 6 true b = Record12518109.Bernstein.bsum 1 0 (249108662984851251768430920671869/2819927718984767904275000000000000:ℝ) cell1_complement6_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement6_1_g]
def cell1_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(14405361372992479325142359/389291761715913000000000000:ℝ)],
  ![(68566381964633204775851328833/189585087955649631000000000000:ℝ)]]
theorem cell1_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 7 false b := by
 have heq : complementBranch cell1 7 false b = Record12518109.Bernstein.bsum 1 0 (14405361372992479325142359/37075405877706000000000000000:ℝ) cell1_complement7_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement7_0_g]
def cell1_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(485240665676605492041681403277/14591823104397566979000000000000:ℝ)],
  ![(2553227180180507811762647764395899/7106217851841615118773000000000000:ℝ)]]
theorem cell1_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 7 true b := by
 have heq : complementBranch cell1 7 true b = Record12518109.Bernstein.bsum 1 0 (485240665676605492041681403277/1389697438514053998000000000000000:ℝ) cell1_complement7_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement7_1_g]
def cell1_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(172859516012906001059142359/389291761715913000000000000:ℝ)],
  ![(747245771739813471860309328833/189585087955649631000000000000:ℝ)]]
theorem cell1_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 8 false b := by
 have heq : complementBranch cell1 8 false b = Record12518109.Bernstein.bsum 1 0 (172859516012906001059142359/37075405877706000000000000000:ℝ) cell1_complement8_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement8_0_g]
def cell1_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(6424577744044484027197203403277/14591823104397566979000000000000:ℝ)],
  ![(27992166747123589762889386978395899/7106217851841615118773000000000000:ℝ)]]
theorem cell1_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 8 true b := by
 have heq : complementBranch cell1 8 true b = Record12518109.Bernstein.bsum 1 0 (6424577744044484027197203403277/1389697438514053998000000000000000:ℝ) cell1_complement8_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement8_1_g]
def cell1_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(212473054672884381492642359/389291761715913000000000000:ℝ)],
  ![(916915619183608538631423828833/189585087955649631000000000000:ℝ)]]
theorem cell1_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 9 false b := by
 have heq : complementBranch cell1 9 false b = Record12518109.Bernstein.bsum 1 0 (212473054672884381492642359/37075405877706000000000000000:ℝ) cell1_complement9_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement9_0_g]
def cell1_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(7909412013636453660986083903277/14591823104397566979000000000000:ℝ)],
  ![(34351901638859360250671071781895899/7106217851841615118773000000000000:ℝ)]]
theorem cell1_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 9 true b := by
 have heq : complementBranch cell1 9 true b = Record12518109.Bernstein.bsum 1 0 (7909412013636453660986083903277/1389697438514053998000000000000000:ℝ) cell1_complement9_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement9_1_g]
def cell1_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(26407789926456330089/259527841143942000000:ℝ)],
  ![(113112629771774629753343/126390058637099754000000:ℝ)]]
theorem cell1_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 10 false b := by
 have heq : complementBranch cell1 10 false b = Record12518109.Bernstein.bsum 1 0 (26407789926456330089/24716937251804000000000:ℝ) cell1_complement10_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement10_0_g]
def cell1_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(1986179569517739334147709529/20266420978329954137500000000:ℝ)],
  ![(8809520191115700094050341540623/9869747016446687664962500000000:ℝ)]]
theorem cell1_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 10 true b := by
 have heq : complementBranch cell1 10 true b = Record12518109.Bernstein.bsum 1 0 (5958538708553218002443128587/5790405993808558325000000000000:ℝ) cell1_complement10_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement10_1_g]
def cell1_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(79226459396525465767/129763920571971000000:ℝ)],
  ![(339339393958879092828529/63195029318549877000000:ℝ)]]
theorem cell1_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 11 false b := by
 have heq : complementBranch cell1 11 false b = Record12518109.Bernstein.bsum 1 0 (79226459396525465767/12358468625902000000000:ℝ) cell1_complement11_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement11_0_g]
def cell1_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(12297528663906417346570490779/20266420978329954137500000000:ℝ)],
  ![(52974345828169661814756486009373/9869747016446687664962500000000:ℝ)]]
theorem cell1_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 11 true b := by
 have heq : complementBranch cell1 11 true b = Record12518109.Bernstein.bsum 1 0 (36892585991719252039711472337/5790405993808558325000000000000:ℝ) cell1_complement11_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement11_1_g]
def cell1_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(26408849223767121689/37075405877706000000:ℝ)],
  ![(113113145649564985262543/18055722662442822000000:ℝ)]]
theorem cell1_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 12 false b := by
 have heq : complementBranch cell1 12 false b = Record12518109.Bernstein.bsum 1 0 (26408849223767121689/3530991035972000000000:ℝ) cell1_complement12_0_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement12_0_g]
def cell1_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(14359798482784152949055047029/20266420978329954137500000000:ℝ)],
  ![(61807310955580454158897714903123/9869747016446687664962500000000:ℝ)]]
theorem cell1_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ))
    (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementBranch cell1 12 true b := by
 have heq : complementBranch cell1 12 true b = Record12518109.Bernstein.bsum 1 0 (43079395448352458847165141087/5790405993808558325000000000000:ℝ) cell1_complement12_1_g (49/2000:ℝ) (7/200:ℝ) (429/625:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell1, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell1_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell1_complement12_1_g]
theorem cell1_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 0 b := complementReserve_pos_of_branches (cell1_complement0_0 hb hν) (cell1_complement0_1 hb hν)
theorem cell1_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 1 b := complementReserve_pos_of_branches (cell1_complement1_0 hb hν) (cell1_complement1_1 hb hν)
theorem cell1_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 2 b := complementReserve_pos_of_branches (cell1_complement2_0 hb hν) (cell1_complement2_1 hb hν)
theorem cell1_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 3 b := complementReserve_pos_of_branches (cell1_complement3_0 hb hν) (cell1_complement3_1 hb hν)
theorem cell1_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 4 b := complementReserve_pos_of_branches (cell1_complement4_0 hb hν) (cell1_complement4_1 hb hν)
theorem cell1_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 5 b := complementReserve_pos_of_branches (cell1_complement5_0 hb hν) (cell1_complement5_1 hb hν)
theorem cell1_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 6 b := complementReserve_pos_of_branches (cell1_complement6_0 hb hν) (cell1_complement6_1 hb hν)
theorem cell1_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 7 b := complementReserve_pos_of_branches (cell1_complement7_0 hb hν) (cell1_complement7_1 hb hν)
theorem cell1_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 8 b := complementReserve_pos_of_branches (cell1_complement8_0 hb hν) (cell1_complement8_1 hb hν)
theorem cell1_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 9 b := complementReserve_pos_of_branches (cell1_complement9_0 hb hν) (cell1_complement9_1 hb hν)
theorem cell1_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 10 b := complementReserve_pos_of_branches (cell1_complement10_0 hb hν) (cell1_complement10_1 hb hν)
theorem cell1_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 11 b := complementReserve_pos_of_branches (cell1_complement11_0 hb hν) (cell1_complement11_1 hb hν)
theorem cell1_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (hν : ν ∈ Set.Icc (429/625:ℝ) (3/4:ℝ)) : 0 < complementReserve cell1 12 b := complementReserve_pos_of_branches (cell1_complement12_0 hb hν) (cell1_complement12_1 hb hν)
theorem cell1_all_domains {b : ℝ} (hb : b ∈ Set.Icc (49/2000:ℝ) (7/200:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell1 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell1_domain0_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain0_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain1_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain1_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain2_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain2_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain3_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain3_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain4_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain4_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain5_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain5_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain6_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain6_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain7_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain7_1 (ν := (429/625:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell1_domain8_0 (ν := (429/625:ℝ)) hb (by norm_num)
   | true => exact cell1_domain8_1 (ν := (429/625:ℝ)) hb (by norm_num)
end
end Record12518109Admission
