/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell8 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (6287/10000:ℝ), (3/80:ℝ), (39/1000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (67/12500:ℝ), (1/25:ℝ)⟩
def cell8_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(74515206825708921998530950366350460160639827941/1862699381790998533318746460406250000000:ℝ), (1335746524557529853276393410484493193357014204559/465674845447749633329686615101562500000:ℝ), (851991453314906065771629829588247792484145057353/103483298988388807406597025578125000000:ℝ), (3688092393470954134162598076394837305511235172059/465674845447749633329686615101562500000:ℝ), (4699159768079157048021029536005567586714360172059/1862699381790998533318746460406250000000:ℝ)],
  ![(75761244152211434650431013630722391351816827941/1862699381790998533318746460406250000000:ℝ), (1309304217361586381182584031040353618558264204559/465674845447749633329686615101562500000:ℝ), (2504580009718024235547895536178948764952435172059/310449896965166422219791076734375000000:ℝ), (3614814471195615535803509625019766993011235172059/465674845447749633329686615101562500000:ℝ), (4607242711849949960339671854247755086714360172059/1862699381790998533318746460406250000000:ℝ)]]
theorem cell8_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell8 2 b ν := by
 have heq : highRegular cell8 2 b ν = Record12518109.Bernstein.bsum 1 4 (74515206825708921998530950366350460160639827941/5735988974896719375000000000000000000000000000:ℝ) cell8_regular2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_regular2_g]
def cell8_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(22084670483377408425110099109406322181203102941/1862699381790998533318746460406250000000:ℝ), (421068874075849086041533818381140333065778809853/155224948482583211109895538367187500000:ℝ), (826232093476635808605674279266580442280231632353/103483298988388807406597025578125000000:ℝ), (3622591824118926188492994741888837303024494897059/465674845447749633329686615101562500000:ℝ), (517793585510416133982589024183980469428068877451/206966597976777614813194051156250000000:ℝ)],
  ![(706414062145168070890462176848982340793367647/620899793930332844439582153468750000000:ℝ), (1219463940653383322584536683902716361898586429559/465674845447749633329686615101562500000:ℝ), (804579605604839930727645377078398904780231632353/103483298988388807406597025578125000000:ℝ), (1179723284452550987313741129259797330174831632353/155224948482583211109895538367187500000:ℝ), (4561106830620695376773394707773011724852619897059/1862699381790998533318746460406250000000:ℝ)]]
theorem cell8_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell8 3 b ν := by
 have heq : highRegular cell8 3 b ν = Record12518109.Bernstein.bsum 1 4 (706414062145168070890462176848982340793367647/1911996324965573125000000000000000000000000000:ℝ) cell8_regular3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_regular3_g]
def cell8_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(578101355153363625456888195642541367397933302941/1862699381790998533318746460406250000000:ℝ), (482588944459801454607791895588505478262785409853/155224948482583211109895538367187500000:ℝ), (2352905959570285096147275019410231936673964697059/310449896965166422219791076734375000000:ℝ), (3271454039855960046702656107533083454107764697059/465674845447749633329686615101562500000:ℝ), (465022936760807704465316277439695145937321077451/206966597976777614813194051156250000000:ℝ)],
  ![(169953193055030215787839371503454952813036767647/620899793930332844439582153468750000000:ℝ), (1364899985365115567850555581931131297489606229559/465674845447749633329686615101562500000:ℝ), (752530094872263704395621884798979108057988232353/103483298988388807406597025578125000000:ℝ), (1055216874517786214857298593849546047202588232353/155224948482583211109895538367187500000:ℝ), (4070679260389936111755057174574443813435889697059/1862699381790998533318746460406250000000:ℝ)]]
theorem cell8_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell8 4 b ν := by
 have heq : highRegular cell8 4 b ν = Record12518109.Bernstein.bsum 1 4 (169953193055030215787839371503454952813036767647/1911996324965573125000000000000000000000000000:ℝ) cell8_regular4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_regular4_g]
def cell8_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(1698640214873388960382301392395614715757/96213222526854846426847875000000000:ℝ), (263017387004884838068178771871186186027/5345179029269713690380437500000000:ℝ), (3081766392922022303371080458590243784243/96213222526854846426847875000000000:ℝ)],
  ![(1657485439591704939942232302035843715757/96213222526854846426847875000000000:ℝ), (2320902317241823033824168417755675674243/48106611263427423213423937500000000:ℝ), (3030168240552922541525844452340243784243/96213222526854846426847875000000000:ℝ)]]
theorem cell8_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 0 false b ν := by
 have heq : highBranch cell8 0 false b ν = Record12518109.Bernstein.bsum 1 2 (1657485439591704939942232302035843715757/4359351620921506725000000000000000000000:ℝ) cell8_exceptional0_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional0_0_g]
def cell8_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(21197439881475091228482369328447009167064877/1202120073324700069539179632875000000000:ℝ), (88655213547574936931612148895693317610150369/1803180109987050104308769449312500000000:ℝ), (115445835422846229641473393417690449279305369/3606360219974100208617538898625000000000:ℝ)],
  ![(20684731914151376625998853946908852036064877/1202120073324700069539179632875000000000:ℝ), (86925803973632765642084481637639425110150369/1803180109987050104308769449312500000000:ℝ), (113515971983321967740377712813359199279305369/3606360219974100208617538898625000000000:ℝ)]]
theorem cell8_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 0 true b ν := by
 have heq : highBranch cell8 0 true b ν = Record12518109.Bernstein.bsum 1 2 (20684731914151376625998853946908852036064877/54467192269000278857725000000000000000000000:ℝ) cell8_exceptional0_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional0_1_g]
theorem cell8_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 0 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional0_0 hb hν) (cell8_exceptional0_1 hb hν)
def cell8_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(16099380223332206681484870136895840303/5063853817202886654044625000000000:ℝ), (175247129452119575614322298793423719697/2531926908601443327022312500000000:ℝ), (112273619941135370612670154014975219899/1687951272400962218014875000000000:ℝ)],
  ![(5000737263330106254474377276162280101/1687951272400962218014875000000000:ℝ), (172971146171499987019002792328423719697/2531926908601443327022312500000000:ℝ), (333353188219377098107200343294925659697/5063853817202886654044625000000000:ℝ)]]
theorem cell8_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 1 false b ν := by
 have heq : highBranch cell8 1 false b ν = Record12518109.Bernstein.bsum 1 2 (5000737263330106254474377276162280101/76479852998622925000000000000000000000:ℝ) cell8_exceptional1_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional1_0_g]
def cell8_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(599357725244110328486166065982119472102349/189808432630215800453554678875000000000:ℝ), (6564950631866327077163550343635178722902651/94904216315107900226777339437500000000:ℝ), (4207158863217613371134630902037216895799217/63269477543405266817851559625000000000:ℝ)],
  ![(558468378747273097901066537880699925102349/189808432630215800453554678875000000000:ℝ), (6479868125444097848446606761420171222902651/94904216315107900226777339437500000000:ℝ), (12491718386799373458687163373317900687397651/189808432630215800453554678875000000000:ℝ)]]
theorem cell8_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 1 true b ν := by
 have heq : highBranch cell8 1 true b ν = Record12518109.Bernstein.bsum 1 2 (558468378747273097901066537880699925102349/8600082989842149293325000000000000000000000:ℝ) cell8_exceptional1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional1_1_g]
theorem cell8_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 1 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional1_0 hb hν) (cell8_exceptional1_1 hb hν)
def cell8_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(25422776754462572472068319862109917601/843975636200481109007437500000000:ℝ), (2550689685015607311769173608962139/63298172715036083175557812500:ℝ), (9150814051264610538161104159873/810216610752461864647140000:ℝ)],
  ![(75070077746117197980807466519625252803/2531926908601443327022312500000000:ℝ), (2499801538113412349939783603587139/63298172715036083175557812500:ℝ), (8877009997584499007931485159873/810216610752461864647140000:ℝ)]]
theorem cell8_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 2 false b ν := by
 have heq : highBranch cell8 2 false b ν = Record12518109.Bernstein.bsum 1 2 (8877009997584499007931485159873/36710329439339004000000000000000:ℝ) cell8_exceptional2_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional2_0_g]
def cell8_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(317399229087965277441424548331628427287761/10544912923900877802975259937500000000:ℝ), (764042471575086304754403436866010887101/18980843263021580045355467887500000:ℝ), (342387182542337151691188466946338049/30369349220834528072568748620000:ℝ)],
  ![(2811796871631894994099621006821708572089849/94904216315107900226777339437500000000:ℝ), (748828583269453476840678728016759387101/18980843263021580045355467887500000:ℝ), (36906607811011332212936430411037561/3374372135648280896952083180000:ℝ)]]
theorem cell8_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 2 true b ν := by
 have heq : highBranch cell8 2 true b ν = Record12518109.Bernstein.bsum 1 2 (110719823433033996638809291233112683/458671092791581295644000000000000000:ℝ) cell8_exceptional2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional2_1_g]
theorem cell8_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 2 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional2_0 hb hν) (cell8_exceptional2_1 hb hν)
def cell8_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(479703974007875928190180899131871571919/32071074175618282142282625000000000:ℝ), (685854744225413381640555880613558558081/16035537087809141071141312500000000:ℝ), (908225290323462048790113051196747928081/32071074175618282142282625000000000:ℝ)],
  ![(24525563977928837967201291351506030101/1687951272400962218014875000000000:ℝ), (105858424572321033480643532250298719697/2531926908601443327022312500000000:ℝ), (140688300979015072869742270912644409697/5063853817202886654044625000000000:ℝ)]]
theorem cell8_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 3 false b ν := by
 have heq : highBranch cell8 3 false b ν = Record12518109.Bernstein.bsum 1 2 (24525563977928837967201291351506030101/76479852998622925000000000000000000000:ℝ) cell8_exceptional3_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional3_0_g]
def cell8_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(53864420643537675532494956820656027501194631/3606360219974100208617538898625000000000:ℝ), (77050767227041560815925112960378317610150369/1803180109987050104308769449312500000000:ℝ), (34020337129511017189538202360791816426435123/1202120073324700069539179632875000000000:ℝ)],
  ![(2754015617977185880265495298739029268852349/189808432630215800453554678875000000000:ℝ), (3964281981742073132968286615911811847902651/94904216315107900226777339437500000000:ℝ), (5270060418368883666711522446212852593647651/189808432630215800453554678875000000000:ℝ)]]
theorem cell8_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 3 true b ν := by
 have heq : highBranch cell8 3 true b ν = Record12518109.Bernstein.bsum 1 2 (2754015617977185880265495298739029268852349/8600082989842149293325000000000000000000000:ℝ) cell8_exceptional3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional3_1_g]
theorem cell8_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 3 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional3_0 hb hν) (cell8_exceptional3_1 hb hν)
def cell8_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(5465263643763435832267965136895840303/5063853817202886654044625000000000:ℝ), (156824446681554035125601703793423719697/2531926908601443327022312500000000:ℝ), (103581548987878626229075789014975219899/1687951272400962218014875000000000:ℝ)],
  ![(1456031736807182638068742276162280101/1687951272400962218014875000000000:ℝ), (154548463400934446530282197328423719697/2531926908601443327022312500000000:ℝ), (307276975359606864956417248294925659697/5063853817202886654044625000000000:ℝ)]]
theorem cell8_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 4 false b ν := by
 have heq : highBranch cell8 4 false b ν = Record12518109.Bernstein.bsum 1 2 (1456031736807182638068742276162280101/76479852998622925000000000000000000000:ℝ) cell8_exceptional4_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional4_0_g]
def cell8_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(200759133492134090744968815867119472102349/189808432630215800453554678875000000000:ℝ), (5874413213577218923024836281250178722902651/94904216315107900226777339437500000000:ℝ), (3881353967676690821404363318742216895799217/63269477543405266817851559625000000000:ℝ)],
  ![(159869786995296860159869287765699925102349/189808432630215800453554678875000000000:ℝ), (5789330707154989694307892699035171222902651/94904216315107900226777339437500000000:ℝ), (11514303700176605809496360623432900687397651/189808432630215800453554678875000000000:ℝ)]]
theorem cell8_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 4 true b ν := by
 have heq : highBranch cell8 4 true b ν = Record12518109.Bernstein.bsum 1 2 (159869786995296860159869287765699925102349/8600082989842149293325000000000000000000000:ℝ) cell8_exceptional4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional4_1_g]
theorem cell8_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 4 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional4_0 hb hν) (cell8_exceptional4_1 hb hν)
def cell8_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(82711622778017621234620211424020840303/5063853817202886654044625000000000:ℝ), (1745417413131600732215784190325389300452461/47379948240658808978568533812500000000:ℝ), (683077055827719422176629386862839977469987/31586632160439205985712355875000000000:ℝ)],
  ![(26881046728899506639327241038537280101/1687951272400962218014875000000000:ℝ), (1705071691650856817415740061370456800452461/47379948240658808978568533812500000000:ℝ), (2006559936626895720978521495357269932409961/94759896481317617957137067625000000000:ℝ)]]
theorem cell8_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 5 false b ν := by
 have heq : highBranch cell8 5 false b ν = Record12518109.Bernstein.bsum 1 2 (26881046728899506639327241038537280101/76479852998622925000000000000000000000:ℝ) cell8_exceptional5_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional5_0_g]
def cell8_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(3096184412921383722181338063447425847102349/189808432630215800453554678875000000000:ℝ), (65351669358688045879464266060875951836797095663/1775942599904614136943684352893937500000000:ℝ), (25581448313788417905414998416583995204653247721/1183961733269742757962456235262625000000000:ℝ)],
  ![(3018887297841086601777386215096006300102349/189808432630215800453554678875000000000:ℝ), (21281220172350906910599512417511855608932365221/591980866634871378981228117631312500000000:ℝ), (75149026008257007920676269192860854363959743163/3551885199809228273887368705787875000000000:ℝ)]]
theorem cell8_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 5 true b ν := by
 have heq : highBranch cell8 5 true b ν = Record12518109.Bernstein.bsum 1 2 (3018887297841086601777386215096006300102349/8600082989842149293325000000000000000000000:ℝ) cell8_exceptional5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional5_1_g]
theorem cell8_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 5 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional5_0 hb hν) (cell8_exceptional5_1 hb hν)
def cell8_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(25422776754462572472068319862109917601/843975636200481109007437500000000:ℝ), (2550689685015607311769173608962139/63298172715036083175557812500:ℝ), (9150814051264610538161104159873/810216610752461864647140000:ℝ)],
  ![(75070077746117197980807466519625252803/2531926908601443327022312500000000:ℝ), (2499801538113412349939783603587139/63298172715036083175557812500:ℝ), (8877009997584499007931485159873/810216610752461864647140000:ℝ)]]
theorem cell8_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 6 false b ν := by
 have heq : highBranch cell8 6 false b ν = Record12518109.Bernstein.bsum 1 2 (8877009997584499007931485159873/36710329439339004000000000000000:ℝ) cell8_exceptional6_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional6_0_g]
def cell8_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(317399229087965277441424548331628427287761/10544912923900877802975259937500000000:ℝ), (764042471575086304754403436866010887101/18980843263021580045355467887500000:ℝ), (342387182542337151691188466946338049/30369349220834528072568748620000:ℝ)],
  ![(2811796871631894994099621006821708572089849/94904216315107900226777339437500000000:ℝ), (748828583269453476840678728016759387101/18980843263021580045355467887500000:ℝ), (36906607811011332212936430411037561/3374372135648280896952083180000:ℝ)]]
theorem cell8_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 6 true b ν := by
 have heq : highBranch cell8 6 true b ν = Record12518109.Bernstein.bsum 1 2 (110719823433033996638809291233112683/458671092791581295644000000000000000:ℝ) cell8_exceptional6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional6_1_g]
theorem cell8_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 6 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional6_0 hb hν) (cell8_exceptional6_1 hb hν)
def cell8_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(69328361402560350723353306424020840303/5063853817202886654044625000000000:ℝ), (488275102739144564752037784275129766817487/15793316080219602992856177937500000000:ℝ), (1738487927773756093687884078853519932409961/94759896481317617957137067625000000000:ℝ)],
  ![(22419959603747083135571606038537280101/1687951272400962218014875000000000:ℝ), (1424479586736689779456069223870456800452461/47379948240658808978568533812500000000:ℝ), (1695816696917493548136517413622269932409961/94759896481317617957137067625000000000:ℝ)]]
theorem cell8_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 7 false b ν := by
 have heq : highBranch cell8 7 false b ν = Record12518109.Bernstein.bsum 1 2 (22419959603747083135571606038537280101/76479852998622925000000000000000000000:ℝ) cell8_exceptional7_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional7_0_g]
def cell8_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(2594539626785118851607520663332425847102349/189808432630215800453554678875000000000:ℝ), (54834235490190322795621924058863451836797095663/1775942599904614136943684352893937500000000:ℝ), (65096756087337732071608156254078980613959743163/3551885199809228273887368705787875000000000:ℝ)],
  ![(2517242511704821731203568814981006300102349/189808432630215800453554678875000000000:ℝ), (53326226648554997647956195250523066826797095663/1775942599904614136943684352893937500000000:ℝ), (63501437154229486276039430197187849363959743163/3551885199809228273887368705787875000000000:ℝ)]]
theorem cell8_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell8 7 true b ν := by
 have heq : highBranch cell8 7 true b ν = Record12518109.Bernstein.bsum 1 2 (2517242511704821731203568814981006300102349/8600082989842149293325000000000000000000000:ℝ) cell8_exceptional7_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_exceptional7_1_g]
theorem cell8_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
 (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell8 7 b ν :=
 highExceptional_pos_of_branches (cell8_exceptional7_0 hb hν) (cell8_exceptional7_1 hb hν)
def cell8_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(266167704856708561627163577931/103200995878105791519900000000000:ℝ)],
  ![(1778386312990653397464980577931/103200995878105791519900000000000:ℝ)]]
theorem cell8_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 0 false b := by
 have heq : domainBranch cell8 0 false b = Record12518109.Bernstein.bsum 1 0 (266167704856708561627163577931/68800663918737194346600000000000000:ℝ) cell8_domain0_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain0_0_g]
def cell8_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(266167704856708561627163577931/103200995878105791519900000000000:ℝ)],
  ![(1778386312990653397464980577931/103200995878105791519900000000000:ℝ)]]
theorem cell8_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 0 true b := by
 have heq : domainBranch cell8 0 true b = Record12518109.Bernstein.bsum 1 0 (266167704856708561627163577931/68800663918737194346600000000000000:ℝ) cell8_domain0_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain0_1_g]
def cell8_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(411416372673007277435140664541949/91775823598347510000000000000000:ℝ)],
  ![(119604138777484211281895475513983/30591941199449170000000000000000:ℝ)]]
theorem cell8_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 1 false b := by
 have heq : domainBranch cell8 1 false b = Record12518109.Bernstein.bsum 1 0 (358812416332452633845686426541949/61183882398898340000000000000000000:ℝ) cell8_domain1_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain1_0_g]
def cell8_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(246774819229115628468409964541181/30591941199449170000000000000000:ℝ)],
  ![(687720501346792241815775655623543/91775823598347510000000000000000:ℝ)]]
theorem cell8_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 1 true b := by
 have heq : domainBranch cell8 1 true b = Record12518109.Bernstein.bsum 1 0 (687720501346792241815775655623543/61183882398898340000000000000000000:ℝ) cell8_domain1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain1_1_g]
def cell8_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(23375286786320250085397651068531/3059194119944917000000000000000:ℝ)],
  ![(73539369713155252518226387205593/9177582359834751000000000000000:ℝ)]]
theorem cell8_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 2 false b := by
 have heq : domainBranch cell8 2 false b = Record12518109.Bernstein.bsum 1 0 (70125860358960750256192953205593/6118388239889834000000000000000000:ℝ) cell8_domain2_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain2_0_g]
def cell8_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(38811085101750651015201536277451/9177582359834751000000000000000:ℝ)],
  ![(42224594455945153277234970277451/9177582359834751000000000000000:ℝ)]]
theorem cell8_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 2 true b := by
 have heq : domainBranch cell8 2 true b = Record12518109.Bernstein.bsum 1 0 (38811085101750651015201536277451/6118388239889834000000000000000000:ℝ) cell8_domain2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain2_1_g]
def cell8_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(331862683716038206613046504781/91775823598347510000000000000:ℝ)],
  ![(800939762016040871892600504781/91775823598347510000000000000:ℝ)]]
theorem cell8_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 3 false b := by
 have heq : domainBranch cell8 3 false b = Record12518109.Bernstein.bsum 1 0 (331862683716038206613046504781/61183882398898340000000000000000:ℝ) cell8_domain3_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain3_0_g]
def cell8_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(331862683716038206613046504781/91775823598347510000000000000:ℝ)],
  ![(800939762016040871892600504781/91775823598347510000000000000:ℝ)]]
theorem cell8_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 3 true b := by
 have heq : domainBranch cell8 3 true b = Record12518109.Bernstein.bsum 1 0 (331862683716038206613046504781/61183882398898340000000000000000:ℝ) cell8_domain3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain3_1_g]
def cell8_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(721664900553494794305807/95599816248278656250000:ℝ)],
  ![(505493052119240435305807/95599816248278656250000:ℝ)]]
theorem cell8_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 4 false b := by
 have heq : domainBranch cell8 4 false b = Record12518109.Bernstein.bsum 1 0 (1516479156357721305917421/191199632496557312500000000:ℝ) cell8_domain4_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain4_0_g]
def cell8_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(721664900553494794305807/95599816248278656250000:ℝ)],
  ![(505493052119240435305807/95599816248278656250000:ℝ)]]
theorem cell8_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 4 true b := by
 have heq : domainBranch cell8 4 true b = Record12518109.Bernstein.bsum 1 0 (1516479156357721305917421/191199632496557312500000000:ℝ) cell8_domain4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain4_1_g]
def cell8_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(18067961842317070788096645216011/4588791179917375500000000000000:ℝ)],
  ![(5158154225642604359186454405337/1529597059972458500000000000000:ℝ)]]
theorem cell8_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 5 false b := by
 have heq : domainBranch cell8 5 false b = Record12518109.Bernstein.bsum 1 0 (15474462676927813077559363216011/3059194119944917000000000000000000:ℝ) cell8_domain5_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain5_0_g]
def cell8_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(11494016480328359697016043262059/1529597059972458500000000000000:ℝ)],
  ![(31888550275595821380510847786177/4588791179917375500000000000000:ℝ)]]
theorem cell8_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 5 true b := by
 have heq : domainBranch cell8 5 true b = Record12518109.Bernstein.bsum 1 0 (31888550275595821380510847786177/3059194119944917000000000000000000:ℝ) cell8_domain5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain5_1_g]
def cell8_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(161667564578964870426143392484118929/3111492573022435328573500000000000:ℝ)],
  ![(154261240857673769398592230006118929/3111492573022435328573500000000000:ℝ)]]
theorem cell8_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 6 false b := by
 have heq : domainBranch cell8 6 false b = Record12518109.Bernstein.bsum 1 0 (462783722573021308195776690018356787/6222985146044870657147000000000000000:ℝ) cell8_domain6_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain6_0_g]
def cell8_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(157341849162767313337606642717318723/3111492573022435328573500000000000:ℝ)],
  ![(149935525441476212310055480239318723/3111492573022435328573500000000000:ℝ)]]
theorem cell8_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 6 true b := by
 have heq : domainBranch cell8 6 true b = Record12518109.Bernstein.bsum 1 0 (449806576324428636930166440717956169/6222985146044870657147000000000000000:ℝ) cell8_domain6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain6_1_g]
def cell8_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(10592916127597858226165688043/764798529986229250000000000:ℝ)],
  ![(44586704654343372638100064129/2294395589958687750000000000:ℝ)]]
theorem cell8_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 7 false b := by
 have heq : domainBranch cell8 7 false b = Record12518109.Bernstein.bsum 1 0 (31778748382793574678497064129/1529597059972458500000000000000:ℝ) cell8_domain7_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain7_0_g]
def cell8_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(10592916127597858226165688043/764798529986229250000000000:ℝ)],
  ![(44586704654343372638100064129/2294395589958687750000000000:ℝ)]]
theorem cell8_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 7 true b := by
 have heq : domainBranch cell8 7 true b = Record12518109.Bernstein.bsum 1 0 (31778748382793574678497064129/1529597059972458500000000000000:ℝ) cell8_domain7_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain7_1_g]
def cell8_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(12265276190694453520973418710573/458879117991737550000000000000:ℝ)],
  ![(11524733263107350283786092710573/458879117991737550000000000000:ℝ)]]
theorem cell8_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 8 false b := by
 have heq : domainBranch cell8 8 false b = Record12518109.Bernstein.bsum 1 0 (11524733263107350283786092710573/305919411994491700000000000000000:ℝ) cell8_domain8_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain8_0_g]
def cell8_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(12897215625936780424549401506311/458879117991737550000000000000:ℝ)],
  ![(4052224232783225729120691835437/152959705997245850000000000000:ℝ)]]
theorem cell8_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell8 8 true b := by
 have heq : domainBranch cell8 8 true b = Record12518109.Bernstein.bsum 1 0 (12156672698349677187362075506311/305919411994491700000000000000000:ℝ) cell8_domain8_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_domain8_1_g]
def cell8_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(193032839232390935119849/91775823598347510000000:ℝ)],
  ![(795270366131427164359547/275327470795042530000000:ℝ)]]
theorem cell8_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 0 b := by
 have heq : ordinary cell8 0 b = Record12518109.Bernstein.bsum 1 0 (193032839232390935119849/61183882398898340000000000:ℝ) cell8_ordinary0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary0_g]
def cell8_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(752665054497921174140453/275327470795042530000000:ℝ)],
  ![(178831068687888938380151/91775823598347510000000:ℝ)]]
theorem cell8_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 1 b := by
 have heq : ordinary cell8 1 b = Record12518109.Bernstein.bsum 1 0 (178831068687888938380151/61183882398898340000000000:ℝ) cell8_ordinary1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary1_g]
def cell8_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(9828647734866945692378663/30591941199449170000000:ℝ)],
  ![(29053599507732328359135989/91775823598347510000000:ℝ)]]
theorem cell8_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 2 b := by
 have heq : ordinary cell8 2 b = Record12518109.Bernstein.bsum 1 0 (29053599507732328359135989/61183882398898340000000000:ℝ) cell8_ordinary2_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary2_g]
def cell8_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(374999989/30000000:ℝ)],
  ![(404999989/30000000:ℝ)]]
theorem cell8_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 3 b := by
 have heq : ordinary cell8 3 b = Record12518109.Bernstein.bsum 1 0 (374999989/20000000000:ℝ) cell8_ordinary3_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary3_g]
def cell8_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(9149098770123938342374721/30591941199449170000000:ℝ)],
  ![(26831400966306611289124163/91775823598347510000000:ℝ)]]
theorem cell8_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 4 b := by
 have heq : ordinary cell8 4 b = Record12518109.Bernstein.bsum 1 0 (26831400966306611289124163/61183882398898340000000000:ℝ) cell8_ordinary4_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary4_g]
def cell8_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(45223993265388834751/13724564625540000000000000:ℝ)],
  ![(45223993265388834751/13724564625540000000000000:ℝ)]]
theorem cell8_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell8 5 b := by
 have heq : ordinary cell8 5 b = Record12518109.Bernstein.bsum 1 0 (45223993265388834751/9149709750360000000000000000:ℝ) cell8_ordinary5_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_ordinary5_g]
def cell8_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(64343260012756996734283/30591941199449170000000:ℝ)],
  ![(795261188549067329608547/275327470795042530000000:ℝ)]]
theorem cell8_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 0 false b := by
 have heq : complementBranch cell8 0 false b = Record12518109.Bernstein.bsum 1 0 (193029780038270990202849/61183882398898340000000000:ℝ) cell8_complement0_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement0_0_g]
def cell8_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(208558086058292263569114637535977/103200995878105791519900000000000:ℝ)],
  ![(32232205875142422951670064059553/11466777319789532391100000000000:ℝ)]]
theorem cell8_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 0 true b := by
 have heq : complementBranch cell8 0 true b = Record12518109.Bernstein.bsum 1 0 (208558086058292263569114637535977/68800663918737194346600000000000000:ℝ) cell8_complement0_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement0_1_g]
def cell8_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(212278135272919742226389482613/6883186769876063250000000000:ℝ)],
  ![(203335674662682381528550482613/6883186769876063250000000000:ℝ)]]
theorem cell8_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 1 false b := by
 have heq : complementBranch cell8 1 false b = Record12518109.Bernstein.bsum 1 0 (203335674662682381528550482613/4588791179917375500000000000000:ℝ) cell8_complement1_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement1_0_g]
def cell8_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(5289957550070513676897737977898681/172001659796842985866500000000000:ℝ)],
  ![(15202012512451376956678745154696043/516004979390528957599500000000000:ℝ)]]
theorem cell8_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 1 true b := by
 have heq : complementBranch cell8 1 true b = Record12518109.Bernstein.bsum 1 0 (15202012512451376956678745154696043/344003319593685971733000000000000000:ℝ) cell8_complement1_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement1_1_g]
def cell8_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(55058958641638393213478260871/2294395589958687750000000000:ℝ)],
  ![(44872410157084127680865260871/2294395589958687750000000000:ℝ)]]
theorem cell8_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 2 false b := by
 have heq : complementBranch cell8 2 false b = Record12518109.Bernstein.bsum 1 0 (44872410157084127680865260871/1529597059972458500000000000000:ℝ) cell8_complement2_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement2_0_g]
def cell8_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(12338879641929030991874533893496043/516004979390528957599500000000000:ℝ)],
  ![(10050465625196635690180665114496043/516004979390528957599500000000000:ℝ)]]
theorem cell8_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 2 true b := by
 have heq : complementBranch cell8 2 true b = Record12518109.Bernstein.bsum 1 0 (10050465625196635690180665114496043/344003319593685971733000000000000000:ℝ) cell8_complement2_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement2_1_g]
def cell8_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(178165538310747127872878157613/6883186769876063250000000000:ℝ)],
  ![(174627373911366126150039157613/6883186769876063250000000000:ℝ)]]
theorem cell8_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 3 false b := by
 have heq : complementBranch cell8 3 false b = Record12518109.Bernstein.bsum 1 0 (174627373911366126150039157613/4588791179917375500000000000000:ℝ) cell8_complement3_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement3_0_g]
def cell8_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(13312587706345308823067883943746043/516004979390528957599500000000000:ℝ)],
  ![(4349955346109400851991088388248681/172001659796842985866500000000000:ℝ)]]
theorem cell8_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 3 true b := by
 have heq : complementBranch cell8 3 true b = Record12518109.Bernstein.bsum 1 0 (4349955346109400851991088388248681/114667773197895323911000000000000000:ℝ) cell8_complement3_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement3_1_g]
def cell8_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(19141986765805173061070424457/764798529986229250000000000:ℝ)],
  ![(18448618709715264037699424457/764798529986229250000000000:ℝ)]]
theorem cell8_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 4 false b := by
 have heq : complementBranch cell8 4 false b = Record12518109.Bernstein.bsum 1 0 (55345856129145792113098273371/1529597059972458500000000000000:ℝ) cell8_complement4_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement4_0_g]
def cell8_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(12871213580309995068215548938721043/516004979390528957599500000000000:ℝ)],
  ![(12405922677421359897661005159721043/516004979390528957599500000000000:ℝ)]]
theorem cell8_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 4 true b := by
 have heq : complementBranch cell8 4 true b = Record12518109.Bernstein.bsum 1 0 (12405922677421359897661005159721043/344003319593685971733000000000000000:ℝ) cell8_complement4_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement4_1_g]
def cell8_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(1467889/50000:ℝ)],
  ![(1242991/50000:ℝ)]]
theorem cell8_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 5 false b := by
 have heq : complementBranch cell8 5 false b = Record12518109.Bernstein.bsum 1 0 (3728973/100000000:ℝ) cell8_complement5_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement5_0_g]
def cell8_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(3020998125038704571157029818025977/103200995878105791519900000000000:ℝ)],
  ![(2557308246488197826744126353025977/103200995878105791519900000000000:ℝ)]]
theorem cell8_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 5 true b := by
 have heq : complementBranch cell8 5 true b = Record12518109.Bernstein.bsum 1 0 (2557308246488197826744126353025977/68800663918737194346600000000000000:ℝ) cell8_complement5_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement5_1_g]
def cell8_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(19646858567644198284232171/275327470795042530000000:ℝ)],
  ![(18133655628604417771232171/275327470795042530000000:ℝ)]]
theorem cell8_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 6 false b := by
 have heq : complementBranch cell8 6 false b = Record12518109.Bernstein.bsum 1 0 (18133655628604417771232171/183551647196695020000000000:ℝ) cell8_complement6_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement6_0_g]
def cell8_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(7355477989178442769868684651955977/103200995878105791519900000000000:ℝ)],
  ![(2262929401469179940597613530318659/34400331959368597173300000000000:ℝ)]]
theorem cell8_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 6 true b := by
 have heq : complementBranch cell8 6 true b = Record12518109.Bernstein.bsum 1 0 (2262929401469179940597613530318659/22933554639579064782200000000000000:ℝ) cell8_complement6_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement6_1_g]
def cell8_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(2498448903040319602000486957/4588791179917375500000000000:ℝ)],
  ![(10895598503136722048388460871/13766373539752126500000000000:ℝ)]]
theorem cell8_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 7 false b := by
 have heq : complementBranch cell8 7 false b = Record12518109.Bernstein.bsum 1 0 (2498448903040319602000486957/3059194119944917000000000000000:ℝ) cell8_complement7_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement7_0_g]
def cell8_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(119219112106632743952458792728789/258002489695264478799750000000000:ℝ)],
  ![(184205113277624124789519600728789/258002489695264478799750000000000:ℝ)]]
theorem cell8_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 7 true b := by
 have heq : complementBranch cell8 7 true b = Record12518109.Bernstein.bsum 1 0 (119219112106632743952458792728789/172001659796842985866500000000000000:ℝ) cell8_complement7_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement7_1_g]
def cell8_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(13701672249839502208656762319/1529597059972458500000000000:ℝ)],
  ![(56649890576474051640099286957/4588791179917375500000000000:ℝ)]]
theorem cell8_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 8 false b := by
 have heq : complementBranch cell8 8 false b = Record12518109.Bernstein.bsum 1 0 (41105016749518506625970286957/3059194119944917000000000000000:ℝ) cell8_complement8_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement8_0_g]
def cell8_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(2289854085990945570281648812828789/258002489695264478799750000000000:ℝ)],
  ![(3165117026648052564958409620828789/258002489695264478799750000000000:ℝ)]]
theorem cell8_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 8 true b := by
 have heq : complementBranch cell8 8 true b = Record12518109.Bernstein.bsum 1 0 (2289854085990945570281648812828789/172001659796842985866500000000000000:ℝ) cell8_complement8_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement8_1_g]
def cell8_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(50756658711138053381962736957/4588791179917375500000000000:ℝ)],
  ![(209713190035993513138275210871/13766373539752126500000000000:ℝ)]]
theorem cell8_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 9 false b := by
 have heq : complementBranch cell8 9 false b = Record12518109.Bernstein.bsum 1 0 (50756658711138053381962736957/3059194119944917000000000000000:ℝ) cell8_complement9_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement9_0_g]
def cell8_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(2832512829462023776863946317853789/258002489695264478799750000000000:ℝ)],
  ![(434482778332295519444514680650421/28666943299473830977750000000000:ℝ)]]
theorem cell8_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 9 true b := by
 have heq : complementBranch cell8 9 true b = Record12518109.Bernstein.bsum 1 0 (2832512829462023776863946317853789/172001659796842985866500000000000000:ℝ) cell8_complement9_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement9_1_g]
def cell8_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(64343260012756996734283/30591941199449170000000:ℝ)],
  ![(795261188549067329608547/275327470795042530000000:ℝ)]]
theorem cell8_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 10 false b := by
 have heq : complementBranch cell8 10 false b = Record12518109.Bernstein.bsum 1 0 (193029780038270990202849/61183882398898340000000000:ℝ) cell8_complement10_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement10_0_g]
def cell8_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(208558086058292263569114637535977/103200995878105791519900000000000:ℝ)],
  ![(32232205875142422951670064059553/11466777319789532391100000000000:ℝ)]]
theorem cell8_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 10 true b := by
 have heq : complementBranch cell8 10 true b = Record12518109.Bernstein.bsum 1 0 (208558086058292263569114637535977/68800663918737194346600000000000000:ℝ) cell8_complement10_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement10_1_g]
def cell8_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(579096988100112832901047/45887911799173755000000:ℝ)],
  ![(265089612178122397300349/15295970599724585000000:ℝ)]]
theorem cell8_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 11 false b := by
 have heq : complementBranch cell8 11 false b = Record12518109.Bernstein.bsum 1 0 (579096988100112832901047/30591941199449170000000000:ℝ) cell8_complement11_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement11_0_g]
def cell8_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(1293875573000448676733709647585977/103200995878105791519900000000000:ℝ)],
  ![(1780545809561496026649475586585977/103200995878105791519900000000000:ℝ)]]
theorem cell8_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 11 true b := by
 have heq : complementBranch cell8 11 true b = Record12518109.Bernstein.bsum 1 0 (1293875573000448676733709647585977/68800663918737194346600000000000000:ℝ) cell8_complement11_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement11_1_g]
def cell8_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(450408938477538866973981/30591941199449170000000:ℝ)],
  ![(5566883385337630315765829/275327470795042530000000:ℝ)]]
theorem cell8_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 12 false b := by
 have heq : complementBranch cell8 12 false b = Record12518109.Bernstein.bsum 1 0 (1351226815432616600921943/61183882398898340000000000:ℝ) cell8_complement12_0_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement12_0_g]
def cell8_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(1510939070388879959366628649595977/103200995878105791519900000000000:ℝ)],
  ![(692879000299512956888788196198659/34400331959368597173300000000000:ℝ)]]
theorem cell8_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ))
    (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell8 12 true b := by
 have heq : complementBranch cell8 12 true b = Record12518109.Bernstein.bsum 1 0 (1510939070388879959366628649595977/68800663918737194346600000000000000:ℝ) cell8_complement12_1_g (3/80:ℝ) (39/1000:ℝ) (6287/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell8, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell8_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell8_complement12_1_g]
theorem cell8_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 0 b := complementReserve_pos_of_branches (cell8_complement0_0 hb hν) (cell8_complement0_1 hb hν)
theorem cell8_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 1 b := complementReserve_pos_of_branches (cell8_complement1_0 hb hν) (cell8_complement1_1 hb hν)
theorem cell8_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 2 b := complementReserve_pos_of_branches (cell8_complement2_0 hb hν) (cell8_complement2_1 hb hν)
theorem cell8_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 3 b := complementReserve_pos_of_branches (cell8_complement3_0 hb hν) (cell8_complement3_1 hb hν)
theorem cell8_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 4 b := complementReserve_pos_of_branches (cell8_complement4_0 hb hν) (cell8_complement4_1 hb hν)
theorem cell8_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 5 b := complementReserve_pos_of_branches (cell8_complement5_0 hb hν) (cell8_complement5_1 hb hν)
theorem cell8_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 6 b := complementReserve_pos_of_branches (cell8_complement6_0 hb hν) (cell8_complement6_1 hb hν)
theorem cell8_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 7 b := complementReserve_pos_of_branches (cell8_complement7_0 hb hν) (cell8_complement7_1 hb hν)
theorem cell8_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 8 b := complementReserve_pos_of_branches (cell8_complement8_0 hb hν) (cell8_complement8_1 hb hν)
theorem cell8_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 9 b := complementReserve_pos_of_branches (cell8_complement9_0 hb hν) (cell8_complement9_1 hb hν)
theorem cell8_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 10 b := complementReserve_pos_of_branches (cell8_complement10_0 hb hν) (cell8_complement10_1 hb hν)
theorem cell8_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 11 b := complementReserve_pos_of_branches (cell8_complement11_0 hb hν) (cell8_complement11_1 hb hν)
theorem cell8_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (hν : ν ∈ Set.Icc (6287/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell8 12 b := complementReserve_pos_of_branches (cell8_complement12_0 hb hν) (cell8_complement12_1 hb hν)
theorem cell8_all_domains {b : ℝ} (hb : b ∈ Set.Icc (3/80:ℝ) (39/1000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell8 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell8_domain0_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain0_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain1_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain1_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain2_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain2_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain3_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain3_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain4_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain4_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain5_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain5_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain6_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain6_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain7_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain7_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell8_domain8_0 (ν := (6287/10000:ℝ)) hb (by norm_num)
   | true => exact cell8_domain8_1 (ν := (6287/10000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
