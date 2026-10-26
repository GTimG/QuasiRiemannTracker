/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell14 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (3123/5000:ℝ), (21/500:ℝ), (43/1000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (67/12500:ℝ), (1/50:ℝ)⟩
def cell14_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(1081543158936147789161903815589375151047452903/15479144818093802458068557062500000000:ℝ), (43323809586133963185315999575238505382042895041/11609358613570351843551417796875000000:ℝ), (11755745299844465044449053951587412368901091613/1105653201292414461290611218750000000:ℝ), (13162990981533263239907143287235658016708140699/1289928734841150204839046421875000000:ℝ), (150689179252015397740288944479083334507795141291/46437434454281407374205671187500000000:ℝ)],
  ![(22743655687136460653050124225674571846341279/271563944177084253650325562500000000:ℝ), (120069246327738894125046373042166139552057881/32158888126233661616485921875000000:ℝ), (4302388626443092928076891039203036135910928489/407345916265626380475488343750000000:ℝ), (2060037609908431169334147880695206693427601163/203672958132813190237744171875000000:ℝ), (7853442195169929278853139507174205105673428489/2444075497593758282852930062500000000:ℝ)]]
theorem cell14_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell14 2 b ν := by
 have heq : highRegular cell14 2 b ν = Record12518109.Bernstein.bsum 1 4 (3244629476808443367485711446768125453142358709/187792425872897617187500000000000000000000000:ℝ) cell14_regular2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_regular2_g]
def cell14_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(66098968521760455196338382240882151464777903/15479144818093802458068557062500000000:ℝ), (39932220896507208262661237526264989425259670041/11609358613570351843551417796875000000:ℝ), (79072989462784842034096266069735232299805666291/7739572409046901229034278531250000000:ℝ), (4295305110526641757718216589369503934342455233/429976244947050068279682140625000000:ℝ), (149394599807416109119152163204543852569043166291/46437434454281407374205671187500000000:ℝ)],
  ![(13750070624367146750747392753505877295419767/1719904979788200273118728562500000000:ℝ), (39569596846105389496954322561151147921509670041/11609358613570351843551417796875000000:ℝ), (78228431897825612834832031986918532299805666291/7739572409046901229034278531250000000:ℝ), (38235215524553451504110570484421238534082097097/3869786204523450614517139265625000000:ℝ), (147765920968967000976391472877395415069043166291/46437434454281407374205671187500000000:ℝ)]]
theorem cell14_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell14 3 b ν := by
 have heq : highRegular cell14 3 b ν = Record12518109.Bernstein.bsum 1 4 (198296905565281365589015146722646454394333709/187792425872897617187500000000000000000000000:ℝ) cell14_regular3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_regular3_g]
def cell14_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(1839754187382098735012740495387042828861459301/5159714939364600819356185687500000000:ℝ), (44390484682090903976294519765580950219943870041/11609358613570351843551417796875000000:ℝ), (73680054420668352382735014334211266549364866291/7739572409046901229034278531250000000:ℝ), (4933893125559550903387869452512869963181213871/552826600646207230645305609375000000:ℝ), (19073678630210516538678825597302373875871766613/6633919207754486767743667312500000000:ℝ)],
  ![(39264320560699623610299564008246884441942691/116384547504464680135853812500000000:ℝ), (324560498458126338462696470501831644482660677/87288410628348510101890359375000000:ℝ), (542626227454155167465607638088492981574171927/58192273752232340067926906250000000:ℝ), (255277355830771200264532462435607465167432309/29096136876116170033963453125000000:ℝ), (989111939780327582889273048244121651361671927/349153642513394040407561437500000000:ℝ)]]
theorem cell14_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell14 4 b ν := by
 have heq : highRegular cell14 4 b ν = Record12518109.Bernstein.bsum 1 4 (2238066271959878545787075148470072413190733387/26827489410413945312500000000000000000000000:ℝ) cell14_regular4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_regular4_g]
def cell14_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(212434756881064435024567107896741757373/8977320468663942269432250000000000:ℝ), (100405719235263574306563495643536204209/1496220078110657044905375000000000:ℝ), (396320694607411137431500019622138617627/8977320468663942269432250000000000:ℝ)],
  ![(29885167534809943089755409872427965339/1282474352666277467061750000000000:ℝ), (42509047065412418423605063580086944661/641237176333138733530875000000000:ℝ), (72113736487892532491539220950016293/1650546142427641527750000000000:ℝ)]]
theorem cell14_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 0 false b ν := by
 have heq : highBranch cell14 0 false b ν = Record12518109.Bernstein.bsum 1 2 (29885167534809943089755409872427965339/81555567807658393750000000000000000000:ℝ) cell14_exceptional0_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional0_0_g]
def cell14_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(7952754474996150094170276050094430748887159/336496903126930548085129026750000000000:ℝ), (3760413700004321755124246856627265261115947/56082817187821758014188171125000000000:ℝ), (14846662868600002984548452187219348659737841/336496903126930548085129026750000000000:ℝ)],
  ![(1118802770534972362888251110203904490126737/48070986160990078297875575250000000000:ℝ), (1592076119896833479066091666009901540478263/24035493080495039148937787625000000000:ℝ), (6303493778471376653284685773516183466211/144357315798769003897524250000000000:ℝ)]]
theorem cell14_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 0 true b ν := by
 have heq : highBranch cell14 0 true b ν = Record12518109.Bernstein.bsum 1 2 (1118802770534972362888251110203904490126737/3056947348134459572931250000000000000000000:ℝ) cell14_exceptional0_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional0_1_g]
theorem cell14_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 0 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional0_0 hb hν) (cell14_exceptional0_1 hb hν)
def cell14_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(1245793259419349334205991584197756967/472490550982312751022750000000000:ℝ), (7461528678356072588965615540654866011/78748425163718791837125000000000:ℝ), (43856070183185198126781709746976868033/472490550982312751022750000000000:ℝ)],
  ![(166989806099471770916631870751965281/67498650140330393003250000000000:ℝ), (85744960357670924078848369273994587/912143920815275581125000000000:ℝ), (296451264666849522796782102870590939/3214221435253828238250000000000:ℝ)]]
theorem cell14_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 1 false b ν := by
 have heq : highBranch cell14 1 false b ν = Record12518109.Bernstein.bsum 1 2 (166989806099471770916631870751965281/4292398305666231250000000000000000000:ℝ) cell14_exceptional1_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional1_0_g]
def cell14_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(4197549229362228836991615374450073783551/1610033029315457167871430750000000000:ℝ), (25410694906576698122407141283816068085483/268338838219242861311905125000000000:ℝ), (149400281184118163476270596431557281341449/1610033029315457167871430750000000000:ℝ)],
  ![(6186491314010251234265432514326812802723/2530051903210004120940819750000000000:ℝ), (3212142657399495035717036822136545354521/34189890583918974607308375000000000:ℝ), (77762161408943317141525942016083575940759/843350634403334706980273250000000000:ℝ)]]
theorem cell14_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 1 true b ν := by
 have heq : highBranch cell14 1 true b ν = Record12518109.Bernstein.bsum 1 2 (6186491314010251234265432514326812802723/160891965691287345943750000000000000000000:ℝ) cell14_exceptional1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional1_1_g]
theorem cell14_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 1 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional1_0 hb hν) (cell14_exceptional1_1 hb hν)
def cell14_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(3314223225924460703522475203071437739/78748425163718791837125000000000:ℝ), (5264284809972601351719412097161967/94498110196462550204550000000:ℝ), (659639327819132539188440979931/43199136089811451522080000:ℝ)],
  ![(11624724217719482371020941133113711/278920041902191706625000000000:ℝ), (7503455152794168416613170281619/136360909374404834350000000:ℝ), (8409626970235419580890636103/561027741426122747040000:ℝ)]]
theorem cell14_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 2 false b ν := by
 have heq : highBranch cell14 2 false b ν = Record12518109.Bernstein.bsum 1 2 (92505896672589615389796997133/392447845089484000000000000000:ℝ) cell14_exceptional2_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional2_0_g]
def cell14_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(124134179812494912685837755963289426720937/2951727220411671474430956375000000000:ℝ), (197112157370367055740180916208218523951/3542072664494005769317147650000000:ℝ), (24680638787941466891354121163174813/1619233218054402637402124640000:ℝ)],
  ![(2772865620441111107451617241089185858367/66580313242368529498442625000000000:ℝ), (487979542184556105249651978001735649/8877375098982470599792350000000:ℝ), (9587780172418117034645661708419/640772939475426449308320000:ℝ)]]
theorem cell14_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 2 true b ν := by
 have heq : highBranch cell14 2 true b ν = Record12518109.Bernstein.bsum 1 2 (3461188642242940249507083876739259/14710122577489128772000000000000000:ℝ) cell14_exceptional2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional2_1_g]
theorem cell14_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 2 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional2_0 hb hν) (cell14_exceptional2_1 hb hν)
def cell14_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(10292215316298089742884483178775881967/472490550982312751022750000000000:ℝ), (14786299932619346823649469180558348033/236245275491156375511375000000000:ℝ), (6540841910809454028876306089862081011/157496850327437583674250000000000:ℝ)],
  ![(27473358124609838816932277372427965339/1282474352666277467061750000000000:ℝ), (13204089070088752175946898693362314887/213745725444379577843625000000000:ℝ), (203383291266616230797535162850048879/4951638427282924583250000000000:ℝ)]]
theorem cell14_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 3 false b ν := by
 have heq : highBranch cell14 3 false b ν = Record12518109.Bernstein.bsum 1 2 (27473358124609838816932277372427965339/81555567807658393750000000000000000000:ℝ) cell14_exceptional3_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional3_0_g]
def cell14_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(385260079480970343945403669558522670994061/17710363322470028846585738250000000000:ℝ), (553746373938940008473694213729699778070939/8855181661235014423292869125000000000:ℝ), (12895739410133005490279464522808724524227/310708128464386470992732250000000000:ℝ)],
  ![(1028400918412441854430021634706404490126737/48070986160990078297875575250000000000:ℝ), (164832902287376654747461764334155726719807/2670610342277226572104198625000000000:ℝ), (53331532471779231429462588529145651195899/1299215842188921035077718250000000000:ℝ)]]
theorem cell14_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 3 true b ν := by
 have heq : highBranch cell14 3 true b ν = Record12518109.Bernstein.bsum 1 2 (1028400918412441854430021634706404490126737/3056947348134459572931250000000000000000000:ℝ) cell14_exceptional3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional3_1_g]
theorem cell14_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 3 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional3_0 hb hν) (cell14_exceptional3_1 hb hν)
def cell14_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(188909461280259219337698028065918989/157496850327437583674250000000000:ℝ), (21177989603971849889386619121964598033/236245275491156375511375000000000:ℝ), (42131392007590680302974607246976868033/472490550982312751022750000000000:ℝ)],
  ![(69980538159675817174789370751965281/67498650140330393003250000000000:ℝ), (27028762292844789522408623091331529/304047973605091860375000000000:ℝ), (854156280212905347496323808611772817/9642664305761484714750000000000:ℝ)]]
theorem cell14_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 4 false b ν := by
 have heq : highBranch cell14 4 false b ν = Record12518109.Bernstein.bsum 1 2 (69980538159675817174789370751965281/4292398305666231250000000000000000000:ℝ) cell14_exceptional4_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional4_0_g]
def cell14_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(6906550930557638356056464042150270539687/5903454440823342948861912750000000000:ℝ), (793326077890245880886719804983430246820939/8855181661235014423292869125000000000:ℝ), (1578756980969490486649214937739630094755939/17710363322470028846585738250000000000:ℝ)],
  ![(2550292923822879500159950086826812802723/2530051903210004120940819750000000000:ℝ), (1012507199793673175158296884878848451507/11396630194639658202436125000000000:ℝ), (224051325361714335483183308475750727822277/2530051903210004120940819750000000000:ℝ)]]
theorem cell14_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 4 true b ν := by
 have heq : highBranch cell14 4 true b ν = Record12518109.Bernstein.bsum 1 2 (2550292923822879500159950086826812802723/160891965691287345943750000000000000000000:ℝ) cell14_exceptional4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional4_1_g]
theorem cell14_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 4 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional4_0 hb hν) (cell14_exceptional4_1 hb hν)
def cell14_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(10191399335526552575595641782760256967/472490550982312751022750000000000:ℝ), (36241299200005040081653463727088714547647/738423982760191111056721125000000000:ℝ), (129185105325194414370699309130497810295441/4430543896561146666340326750000000000:ℝ)],
  ![(1432895348165149549953403327689465281/67498650140330393003250000000000:ℝ), (15307586936682216054498384489090163377563/316467421182939047595737625000000000:ℝ), (6072491709024831369956369296541562395021/210978280788626031730491750000000000:ℝ)]]
theorem cell14_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 5 false b ν := by
 have heq : highBranch cell14 5 false b ν = Record12518109.Bernstein.bsum 1 2 (1432895348165149549953403327689465281/4292398305666231250000000000000000000:ℝ) cell14_exceptional5_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional5_0_g]
def cell14_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(381481194073710816303916027511668999119061/17710363322470028846585738250000000000:ℝ), (1356905709632110186785483968014937066795702501/27678346145800243415739077928375000000000:ℝ), (4837988279454544704885794098680765724432690003/166070076874801460494434467570250000000000:ℝ)],
  ![(53636428747258051425900737034715125302723/2530051903210004120940819750000000000:ℝ), (573137389752517324264489496705211952912443929/11862148348200104321031033397875000000000:ℝ), (75806040734519696759348555802545537292582381/2636032966266689849118007421750000000000:ℝ)]]
theorem cell14_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 5 true b ν := by
 have heq : highBranch cell14 5 true b ν = Record12518109.Bernstein.bsum 1 2 (53636428747258051425900737034715125302723/160891965691287345943750000000000000000000:ℝ) cell14_exceptional5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional5_1_g]
theorem cell14_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 5 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional5_0 hb hν) (cell14_exceptional5_1 hb hν)
def cell14_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(3314223225924460703522475203071437739/78748425163718791837125000000000:ℝ), (5264284809972601351719412097161967/94498110196462550204550000000:ℝ), (659639327819132539188440979931/43199136089811451522080000:ℝ)],
  ![(11624724217719482371020941133113711/278920041902191706625000000000:ℝ), (7503455152794168416613170281619/136360909374404834350000000:ℝ), (8409626970235419580890636103/561027741426122747040000:ℝ)]]
theorem cell14_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 6 false b ν := by
 have heq : highBranch cell14 6 false b ν = Record12518109.Bernstein.bsum 1 2 (92505896672589615389796997133/392447845089484000000000000000:ℝ) cell14_exceptional6_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional6_0_g]
def cell14_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(124134179812494912685837755963289426720937/2951727220411671474430956375000000000:ℝ), (197112157370367055740180916208218523951/3542072664494005769317147650000000:ℝ), (24680638787941466891354121163174813/1619233218054402637402124640000:ℝ)],
  ![(2772865620441111107451617241089185858367/66580313242368529498442625000000000:ℝ), (487979542184556105249651978001735649/8877375098982470599792350000000:ℝ), (9587780172418117034645661708419/640772939475426449308320000:ℝ)]]
theorem cell14_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 6 true b ν := by
 have heq : highBranch cell14 6 true b ν = Record12518109.Bernstein.bsum 1 2 (3461188642242940249507083876739259/14710122577489128772000000000000000:ℝ) cell14_exceptional6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional6_1_g]
theorem cell14_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 6 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional6_0 hb hν) (cell14_exceptional6_1 hb hν)
def cell14_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(9323700724007172700890244282760256967/472490550982312751022750000000000:ℝ), (99561590068923122261600663056266143642941/2215271948280573333170163375000000000:ℝ), (39665633381075881163030788412665936765147/1476847965520382222113442250000000000:ℝ)],
  ![(1308938403662380996424060827689465281/67498650140330393003250000000000:ℝ), (1555409540090214514256015290454462597507/35163046798104338621748625000000000:ℝ), (16762017243936383983925258762124687185063/632934842365878095191475250000000000:ℝ)]]
theorem cell14_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 7 false b ν := by
 have heq : highBranch cell14 7 false b ν = Record12518109.Bernstein.bsum 1 2 (1308938403662380996424060827689465281/4292398305666231250000000000000000000:ℝ) cell14_exceptional7_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional7_0_g]
def cell14_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(348957247018129900460333613019168999119061/17710363322470028846585738250000000000:ℝ), (3727286355708409199946179214735436200387107503/83035038437400730247217233785125000000000:ℝ), (1485367928206294743976840340252729408144230001/55356692291600486831478155856750000000000:ℝ)],
  ![(48990150596460777733960392107215125302723/2530051903210004120940819750000000000:ℝ), (174691950241890471878150180363195650970814643/3954049449400034773677011132625000000000:ℝ), (627699438777011488983383705376827335633241429/23724296696400208642062066795750000000000:ℝ)]]
theorem cell14_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell14 7 true b ν := by
 have heq : highBranch cell14 7 true b ν = Record12518109.Bernstein.bsum 1 2 (48990150596460777733960392107215125302723/160891965691287345943750000000000000000000:ℝ) cell14_exceptional7_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_exceptional7_1_g]
theorem cell14_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
 (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell14 7 b ν :=
 highExceptional_pos_of_branches (cell14_exceptional7_0 hb hν) (cell14_exceptional7_1 hb hν)
def cell14_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(2681510138204770454728577383/487024328579031966100000000000:ℝ)],
  ![(7355662379788335341782577383/487024328579031966100000000000:ℝ)]]
theorem cell14_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 0 false b := by
 have heq : domainBranch cell14 0 false b = Record12518109.Bernstein.bsum 1 0 (2681510138204770454728577383/487024328579031966100000000000000:ℝ) cell14_domain0_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain0_0_g]
def cell14_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(2681510138204770454728577383/487024328579031966100000000000:ℝ)],
  ![(7355662379788335341782577383/487024328579031966100000000000:ℝ)]]
theorem cell14_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 0 true b := by
 have heq : domainBranch cell14 0 true b = Record12518109.Bernstein.bsum 1 0 (2681510138204770454728577383/487024328579031966100000000000000:ℝ) cell14_domain0_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain0_1_g]
def cell14_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(629216548810500950683738518574363/96149722046923580000000000000000:ℝ)],
  ![(84998329694395602652387759224909/13735674578131940000000000000000:ℝ)]]
theorem cell14_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 1 false b := by
 have heq : domainBranch cell14 1 false b = Record12518109.Bernstein.bsum 1 0 (84998329694395602652387759224909/13735674578131940000000000000000000:ℝ) cell14_domain1_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain1_0_g]
def cell14_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1146091577219683508597511729701841/96149722046923580000000000000000:ℝ)],
  ![(158837619467135968068641075100263/13735674578131940000000000000000:ℝ)]]
theorem cell14_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 1 true b := by
 have heq : domainBranch cell14 1 true b = Record12518109.Bernstein.bsum 1 0 (158837619467135968068641075100263/13735674578131940000000000000000000:ℝ) cell14_domain1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain1_1_g]
def cell14_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(2859071301520637325241727337843/259864113640334000000000000000:ℝ)],
  ![(2901989736304918792897683337843/259864113640334000000000000000:ℝ)]]
theorem cell14_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 2 false b := by
 have heq : domainBranch cell14 2 false b = Record12518109.Bernstein.bsum 1 0 (2859071301520637325241727337843/259864113640334000000000000000000:ℝ) cell14_domain2_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain2_0_g]
def cell14_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(1529050061121599209703250178201/259864113640334000000000000000:ℝ)],
  ![(1571968495905880677359206178201/259864113640334000000000000000:ℝ)]]
theorem cell14_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 2 true b := by
 have heq : domainBranch cell14 2 true b = Record12518109.Bernstein.bsum 1 0 (1529050061121599209703250178201/259864113640334000000000000000000:ℝ) cell14_domain2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain2_1_g]
def cell14_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(1481706446058016646668827787147/96149722046923580000000000000:ℝ)],
  ![(1949921465674066468230159787147/96149722046923580000000000000:ℝ)]]
theorem cell14_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 3 false b := by
 have heq : domainBranch cell14 3 false b = Record12518109.Bernstein.bsum 1 0 (1481706446058016646668827787147/96149722046923580000000000000000:ℝ) cell14_domain3_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain3_0_g]
def cell14_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1481706446058016646668827787147/96149722046923580000000000000:ℝ)],
  ![(1949921465674066468230159787147/96149722046923580000000000000:ℝ)]]
theorem cell14_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 3 true b := by
 have heq : domainBranch cell14 3 true b = Record12518109.Bernstein.bsum 1 0 (1481706446058016646668827787147/96149722046923580000000000000000:ℝ) cell14_domain3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain3_1_g]
def cell14_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1906384003271482184314827/300467881396636187500000:ℝ)],
  ![(180299668990587159759261/42923983056662312500000:ℝ)]]
theorem cell14_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 4 false b := by
 have heq : domainBranch cell14 4 false b = Record12518109.Bernstein.bsum 1 0 (180299668990587159759261/42923983056662312500000000:ℝ) cell14_domain4_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain4_0_g]
def cell14_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1906384003271482184314827/300467881396636187500000:ℝ)],
  ![(180299668990587159759261/42923983056662312500000:ℝ)]]
theorem cell14_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 4 true b := by
 have heq : domainBranch cell14 4 true b = Record12518109.Bernstein.bsum 1 0 (180299668990587159759261/42923983056662312500000000:ℝ) cell14_domain4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain4_1_g]
def cell14_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(27612268467065922841166383360157/4807486102346179000000000000000:ℝ)],
  ![(3705330820696430240278061051451/686783728906597000000000000000:ℝ)]]
theorem cell14_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 5 false b := by
 have heq : domainBranch cell14 5 false b = Record12518109.Bernstein.bsum 1 0 (3705330820696430240278061051451/686783728906597000000000000000000:ℝ) cell14_domain5_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain5_0_g]
def cell14_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(53406806152275012017433998687799/4807486102346179000000000000000:ℝ)],
  ![(7390264775726300122602006098257/686783728906597000000000000000:ℝ)]]
theorem cell14_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 5 true b := by
 have heq : domainBranch cell14 5 true b = Record12518109.Bernstein.bsum 1 0 (7390264775726300122602006098257/686783728906597000000000000000000:ℝ) cell14_domain5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain5_1_g]
def cell14_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(699228352320413205781457293283602869/9779344962017676206189000000000000:ℝ)],
  ![(96446646391360912112871784415943267/1397049280288239458027000000000000:ℝ)]]
theorem cell14_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 6 false b := by
 have heq : domainBranch cell14 6 false b = Record12518109.Bernstein.bsum 1 0 (96446646391360912112871784415943267/1397049280288239458027000000000000000:ℝ) cell14_domain6_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain6_0_g]
def cell14_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(678834925884516927715900583501755503/9779344962017676206189000000000000:ℝ)],
  ![(93533299757661443817792254447107929/1397049280288239458027000000000000:ℝ)]]
theorem cell14_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 6 true b := by
 have heq : domainBranch cell14 6 true b = Record12518109.Bernstein.bsum 1 0 (93533299757661443817792254447107929/1397049280288239458027000000000000000:ℝ) cell14_domain6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain6_1_g]
def cell14_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(76460456072132318801913640023/2403743051173089500000000000:ℝ)],
  ![(89293211950797364169287640023/2403743051173089500000000000:ℝ)]]
theorem cell14_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 7 false b := by
 have heq : domainBranch cell14 7 false b = Record12518109.Bernstein.bsum 1 0 (76460456072132318801913640023/2403743051173089500000000000000:ℝ) cell14_domain7_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain7_0_g]
def cell14_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(76460456072132318801913640023/2403743051173089500000000000:ℝ)],
  ![(89293211950797364169287640023/2403743051173089500000000000:ℝ)]]
theorem cell14_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 7 true b := by
 have heq : domainBranch cell14 7 true b = Record12518109.Bernstein.bsum 1 0 (76460456072132318801913640023/2403743051173089500000000000000:ℝ) cell14_domain7_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain7_1_g]
def cell14_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(17566580531310862149284195129451/480748610234617900000000000000:ℝ)],
  ![(2404409567921160297054641018493/68678372890659700000000000000:ℝ)]]
theorem cell14_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 8 false b := by
 have heq : domainBranch cell14 8 false b = Record12518109.Bernstein.bsum 1 0 (2404409567921160297054641018493/68678372890659700000000000000000:ℝ) cell14_domain8_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain8_0_g]
def cell14_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(18559665616250382711179335176257/480748610234617900000000000000:ℝ)],
  ![(2546278865769663234468232453751/68678372890659700000000000000:ℝ)]]
theorem cell14_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell14 8 true b := by
 have heq : domainBranch cell14 8 true b = Record12518109.Bernstein.bsum 1 0 (2546278865769663234468232453751/68678372890659700000000000000000:ℝ) cell14_domain8_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_domain8_1_g]
def cell14_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(448732599183406518931663/96149722046923580000000:ℝ)],
  ![(520319968109781192931663/96149722046923580000000:ℝ)]]
theorem cell14_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 0 b := by
 have heq : ordinary cell14 0 b = Record12518109.Bernstein.bsum 1 0 (448732599183406518931663/96149722046923580000000000:ℝ) cell14_ordinary0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary0_g]
def cell14_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(684177696777814054205011/288449166140770740000000:ℝ)],
  ![(67059369999812861743573/41207023734395820000000:ℝ)]]
theorem cell14_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 1 b := by
 have heq : ordinary cell14 1 b = Record12518109.Bernstein.bsum 1 0 (67059369999812861743573/41207023734395820000000000:ℝ) cell14_ordinary1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary1_g]
def cell14_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(45339546275247233611663843/96149722046923580000000:ℝ)],
  ![(6415717437384140795380549/13735674578131940000000:ℝ)]]
theorem cell14_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 2 b := by
 have heq : ordinary cell14 2 b = Record12518109.Bernstein.bsum 1 0 (6415717437384140795380549/13735674578131940000000000:ℝ) cell14_ordinary2_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary2_g]
def cell14_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(419999989/20000000:ℝ)],
  ![(439999989/20000000:ℝ)]]
theorem cell14_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 3 b := by
 have heq : ordinary cell14 3 b = Record12518109.Bernstein.bsum 1 0 (419999989/20000000000:ℝ) cell14_ordinary3_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary3_g]
def cell14_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(41655089032173816277679781/96149722046923580000000:ℝ)],
  ![(5861895053503103010525683/13735674578131940000000:ℝ)]]
theorem cell14_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 4 b := by
 have heq : ordinary cell14 4 b = Record12518109.Bernstein.bsum 1 0 (5861895053503103010525683/13735674578131940000000000:ℝ) cell14_ordinary4_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary4_g]
def cell14_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(7537405109205615393/1524951625060000000000000:ℝ)],
  ![(7537405109205615393/1524951625060000000000000:ℝ)]]
theorem cell14_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell14 5 b := by
 have heq : ordinary cell14 5 b = Record12518109.Bernstein.bsum 1 0 (7537405109205615393/1524951625060000000000000000:ℝ) cell14_ordinary5_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_ordinary5_g]
def cell14_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(448727791697304172752663/96149722046923580000000:ℝ)],
  ![(520315160623678846752663/96149722046923580000000:ℝ)]]
theorem cell14_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 0 false b := by
 have heq : complementBranch cell14 0 false b = Record12518109.Bernstein.bsum 1 0 (448727791697304172752663/96149722046923580000000000:ℝ) cell14_complement0_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement0_0_g]
def cell14_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(11699433740659922347752366395151/2574271451060597535100000000000:ℝ)],
  ![(13624318687086023323178604395151/2574271451060597535100000000000:ℝ)]]
theorem cell14_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 0 true b := by
 have heq : complementBranch cell14 0 true b = Record12518109.Bernstein.bsum 1 0 (11699433740659922347752366395151/2574271451060597535100000000000000:ℝ) cell14_complement0_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement0_1_g]
def cell14_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(106205270539463102072252434977/2403743051173089500000000000:ℝ)],
  ![(14795770846748406243185490711/343391864453298500000000000:ℝ)]]
theorem cell14_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 1 false b := by
 have heq : complementBranch cell14 1 false b = Record12518109.Bernstein.bsum 1 0 (14795770846748406243185490711/343391864453298500000000000000:ℝ) cell14_complement1_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement1_0_g]
def cell14_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(248108538840932871013292812396761/5631218799195057108031250000000:ℝ)],
  ![(34564837997796027198509531663823/804459828456436729718750000000:ℝ)]]
theorem cell14_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 1 true b := by
 have heq : complementBranch cell14 1 true b = Record12518109.Bernstein.bsum 1 0 (34564837997796027198509531663823/804459828456436729718750000000000:ℝ) cell14_complement1_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement1_1_g]
def cell14_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(64911379067441183879086134977/2403743051173089500000000000:ℝ)],
  ![(7873966794654208301304590711/343391864453298500000000000:ℝ)]]
theorem cell14_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 2 false b := by
 have heq : complementBranch cell14 2 false b = Record12518109.Bernstein.bsum 1 0 (7873966794654208301304590711/343391864453298500000000000000:ℝ) cell14_complement2_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement2_0_g]
def cell14_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(151369855463070523536139535965511/5631218799195057108031250000000:ℝ)],
  ![(18349214167505600857539420745073/804459828456436729718750000000:ℝ)]]
theorem cell14_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 2 true b := by
 have heq : complementBranch cell14 2 true b = Record12518109.Bernstein.bsum 1 0 (18349214167505600857539420745073/804459828456436729718750000000000:ℝ) cell14_complement2_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement2_1_g]
def cell14_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(92491312895737686620544009977/2403743051173089500000000000:ℝ)],
  ![(13092303215238970728655715711/343391864453298500000000000:ℝ)]]
theorem cell14_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 3 false b := by
 have heq : complementBranch cell14 3 false b = Record12518109.Bernstein.bsum 1 0 (13092303215238970728655715711/343391864453298500000000000000:ℝ) cell14_complement3_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement3_0_g]
def cell14_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(431962043386895773604537263009147/11262437598390114216062500000000:ℝ)],
  ![(61148291341608532973129118787021/1608919656912873459437500000000:ℝ)]]
theorem cell14_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 3 true b := by
 have heq : complementBranch cell14 3 true b = Record12518109.Bernstein.bsum 1 0 (61148291341608532973129118787021/1608919656912873459437500000000000:ℝ) cell14_complement3_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement3_1_g]
def cell14_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(87329576461734946846398222477/2403743051173089500000000000:ℝ)],
  ![(12227077708727195985920603211/343391864453298500000000000:ℝ)]]
theorem cell14_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 4 false b := by
 have heq : complementBranch cell14 4 false b = Record12518109.Bernstein.bsum 1 0 (12227077708727195985920603211/343391864453298500000000000000:ℝ) cell14_complement4_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement4_0_g]
def cell14_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(815554745084860373470497887802669/22524875196780228432125000000000:ℝ)],
  ![(114188770768071852775773182114667/3217839313825746918875000000000:ℝ)]]
theorem cell14_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 4 true b := by
 have heq : complementBranch cell14 4 true b = Record12518109.Bernstein.bsum 1 0 (114188770768071852775773182114667/3217839313825746918875000000000000:ℝ) cell14_complement4_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement4_1_g]
def cell14_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(3279177/100000:ℝ)],
  ![(2829381/100000:ℝ)]]
theorem cell14_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 5 false b := by
 have heq : complementBranch cell14 5 false b = Record12518109.Bernstein.bsum 1 0 (2829381/100000000:ℝ) cell14_complement5_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement5_0_g]
def cell14_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(15910089582434153764396007692461/487024328579031966100000000000:ℝ)],
  ![(1960147383458000809112267098923/69574904082718852300000000000:ℝ)]]
theorem cell14_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 5 true b := by
 have heq : complementBranch cell14 5 true b = Record12518109.Bernstein.bsum 1 0 (1960147383458000809112267098923/69574904082718852300000000000000:ℝ) cell14_complement5_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement5_1_g]
def cell14_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(1304019720762544411471337/13735674578131940000000:ℝ)],
  ![(176061764548024248210191/1962239225447420000000:ℝ)]]
theorem cell14_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 6 false b := by
 have heq : complementBranch cell14 6 false b = Record12518109.Bernstein.bsum 1 0 (176061764548024248210191/1962239225447420000000000:ℝ) cell14_complement6_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement6_0_g]
def cell14_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(1708518884931831922378993762606057/18019900157424182745700000000000:ℝ)],
  ![(230665815082588936140756775515151/2574271451060597535100000000000:ℝ)]]
theorem cell14_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 6 true b := by
 have heq : complementBranch cell14 6 true b = Record12518109.Bernstein.bsum 1 0 (230665815082588936140756775515151/2574271451060597535100000000000000:ℝ) cell14_complement6_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement6_1_g]
def cell14_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(5986212624349135050411011659/4807486102346179000000000000:ℝ)],
  ![(21228136366992268331279034977/14422458307038537000000000000:ℝ)]]
theorem cell14_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 7 false b := by
 have heq : complementBranch cell14 7 false b = Record12518109.Bernstein.bsum 1 0 (5986212624349135050411011659/4807486102346179000000000000000:ℝ) cell14_complement7_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement7_0_g]
def cell14_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(202358378835170578072818236224867/180199001574241827457000000000000:ℝ)],
  ![(731355184883432959804328906674601/540597004722725482371000000000000:ℝ)]]
theorem cell14_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 7 true b := by
 have heq : complementBranch cell14 7 true b = Record12518109.Bernstein.bsum 1 0 (202358378835170578072818236224867/180199001574241827457000000000000000:ℝ) cell14_complement7_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement7_1_g]
def cell14_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(95732732461030438836743611659/4807486102346179000000000000:ℝ)],
  ![(333420117232860984090276834977/14422458307038537000000000000:ℝ)]]
theorem cell14_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 8 false b := by
 have heq : complementBranch cell14 8 false b = Record12518109.Bernstein.bsum 1 0 (95732732461030438836743611659/4807486102346179000000000000000:ℝ) cell14_complement8_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement8_0_g]
def cell14_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(509475311696213698270846154574981/25742714510605975351000000000000:ℝ)],
  ![(1776178171954112861799834777724943/77228143531817926053000000000000:ℝ)]]
theorem cell14_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 8 true b := by
 have heq : complementBranch cell14 8 true b = Record12518109.Bernstein.bsum 1 0 (509475311696213698270846154574981/25742714510605975351000000000000000:ℝ) cell14_complement8_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement8_1_g]
def cell14_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(118169362420200764783326761659/4807486102346179000000000000:ℝ)],
  ![(411468112449328163030026284977/14422458307038537000000000000:ℝ)]]
theorem cell14_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 9 false b := by
 have heq : complementBranch cell14 9 false b = Record12518109.Bernstein.bsum 1 0 (118169362420200764783326761659/4807486102346179000000000000000:ℝ) cell14_complement9_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement9_0_g]
def cell14_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(4407319382633077215351699293474867/180199001574241827457000000000000:ℝ)],
  ![(15358720208377629300797472078424601/540597004722725482371000000000000:ℝ)]]
theorem cell14_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 9 true b := by
 have heq : complementBranch cell14 9 true b = Record12518109.Bernstein.bsum 1 0 (4407319382633077215351699293474867/180199001574241827457000000000000000:ℝ) cell14_complement9_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement9_1_g]
def cell14_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(448727791697304172752663/96149722046923580000000:ℝ)],
  ![(520315160623678846752663/96149722046923580000000:ℝ)]]
theorem cell14_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 10 false b := by
 have heq : complementBranch cell14 10 false b = Record12518109.Bernstein.bsum 1 0 (448727791697304172752663/96149722046923580000000000:ℝ) cell14_complement10_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement10_0_g]
def cell14_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(11699433740659922347752366395151/2574271451060597535100000000000:ℝ)],
  ![(13624318687086023323178604395151/2574271451060597535100000000000:ℝ)]]
theorem cell14_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 10 true b := by
 have heq : complementBranch cell14 10 true b = Record12518109.Bernstein.bsum 1 0 (11699433740659922347752366395151/2574271451060597535100000000000000:ℝ) cell14_complement10_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement10_1_g]
def cell14_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(1346195393807168383705489/48074861023461790000000:ℝ)],
  ![(1560957500586292405705489/48074861023461790000000:ℝ)]]
theorem cell14_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 11 false b := by
 have heq : complementBranch cell14 11 false b = Record12518109.Bernstein.bsum 1 0 (1346195393807168383705489/48074861023461790000000000:ℝ) cell14_complement11_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement11_0_g]
def cell14_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(502392136564410120162154670491057/18019900157424182745700000000000:ℝ)],
  ![(582949064926075374628688336491057/18019900157424182745700000000000:ℝ)]]
theorem cell14_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 11 true b := by
 have heq : complementBranch cell14 11 true b = Record12518109.Bernstein.bsum 1 0 (502392136564410120162154670491057/18019900157424182745700000000000000:ℝ) cell14_complement11_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement11_1_g]
def cell14_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(448731912399677612334663/13735674578131940000000:ℝ)],
  ![(520319281326052286334663/13735674578131940000000:ℝ)]]
theorem cell14_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 12 false b := by
 have heq : complementBranch cell14 12 false b = Record12518109.Bernstein.bsum 1 0 (448731912399677612334663/13735674578131940000000000:ℝ) cell14_complement12_0_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement12_0_g]
def cell14_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(586491356640368252907732291636057/18019900157424182745700000000000:ℝ)],
  ![(680464831749370016901975957636057/18019900157424182745700000000000:ℝ)]]
theorem cell14_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ))
    (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell14 12 true b := by
 have heq : complementBranch cell14 12 true b = Record12518109.Bernstein.bsum 1 0 (586491356640368252907732291636057/18019900157424182745700000000000000:ℝ) cell14_complement12_1_g (21/500:ℝ) (43/1000:ℝ) (3123/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell14, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell14_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell14_complement12_1_g]
theorem cell14_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 0 b := complementReserve_pos_of_branches (cell14_complement0_0 hb hν) (cell14_complement0_1 hb hν)
theorem cell14_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 1 b := complementReserve_pos_of_branches (cell14_complement1_0 hb hν) (cell14_complement1_1 hb hν)
theorem cell14_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 2 b := complementReserve_pos_of_branches (cell14_complement2_0 hb hν) (cell14_complement2_1 hb hν)
theorem cell14_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 3 b := complementReserve_pos_of_branches (cell14_complement3_0 hb hν) (cell14_complement3_1 hb hν)
theorem cell14_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 4 b := complementReserve_pos_of_branches (cell14_complement4_0 hb hν) (cell14_complement4_1 hb hν)
theorem cell14_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 5 b := complementReserve_pos_of_branches (cell14_complement5_0 hb hν) (cell14_complement5_1 hb hν)
theorem cell14_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 6 b := complementReserve_pos_of_branches (cell14_complement6_0 hb hν) (cell14_complement6_1 hb hν)
theorem cell14_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 7 b := complementReserve_pos_of_branches (cell14_complement7_0 hb hν) (cell14_complement7_1 hb hν)
theorem cell14_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 8 b := complementReserve_pos_of_branches (cell14_complement8_0 hb hν) (cell14_complement8_1 hb hν)
theorem cell14_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 9 b := complementReserve_pos_of_branches (cell14_complement9_0 hb hν) (cell14_complement9_1 hb hν)
theorem cell14_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 10 b := complementReserve_pos_of_branches (cell14_complement10_0 hb hν) (cell14_complement10_1 hb hν)
theorem cell14_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 11 b := complementReserve_pos_of_branches (cell14_complement11_0 hb hν) (cell14_complement11_1 hb hν)
theorem cell14_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (hν : ν ∈ Set.Icc (3123/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell14 12 b := complementReserve_pos_of_branches (cell14_complement12_0 hb hν) (cell14_complement12_1 hb hν)
theorem cell14_all_domains {b : ℝ} (hb : b ∈ Set.Icc (21/500:ℝ) (43/1000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell14 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell14_domain0_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain0_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain1_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain1_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain2_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain2_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain3_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain3_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain4_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain4_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain5_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain5_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain6_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain6_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain7_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain7_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell14_domain8_0 (ν := (3123/5000:ℝ)) hb (by norm_num)
   | true => exact cell14_domain8_1 (ν := (3123/5000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
