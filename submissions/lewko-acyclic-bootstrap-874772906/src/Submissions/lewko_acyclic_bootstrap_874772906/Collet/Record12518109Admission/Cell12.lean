/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell12 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (1557/2500:ℝ), (41/1000:ℝ), (83/2000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (7/1250:ℝ), (1/50:ℝ)⟩
def cell12_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(10697389908769340886445070551550760968629249/87054664062367694379334500000000000:ℝ), (1415062167970117079503550004807618793534029259/195872994140327312353502625000000000:ℝ), (2696132648262450131637801004529280897728430509/130581996093551541569001750000000000:ℝ), (1294420606753625224564996176317789830375362253/65290998046775770784500875000000000:ℝ), (4937638546461984136966477764481008056067493009/783491976561309249414010500000000000:ℝ)],
  ![(36873864577947760429681132915091970158887747/261163992187103083138003500000000000:ℝ), (1419343011079575104594927953998305447284029259/195872994140327312353502625000000000:ℝ), (2691244763280977506952845167091604725853430509/130581996093551541569001750000000000:ℝ), (1290083822417635877017563922546305455375362253/65290998046775770784500875000000000:ℝ), (4917637030075755064099797426804006102942493009/783491976561309249414010500000000000:ℝ)]]
theorem cell12_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell12 2 b ν := by
 have heq : highRegular cell12 2 b ν = Record12518109.Bernstein.bsum 1 4 (96276509178924067978005634963956848717663241/5985715951312160644531250000000000000000000:ℝ) cell12_regular2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_regular2_g]
def cell12_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(271345240381171250917352840859693908868083/29018221354122564793111500000000000:ℝ), (1311249733816510603448212799091765736837254259/195872994140327312353502625000000000:ℝ), (2594610431755242628437808791126365874187905509/130581996093551541569001750000000000:ℝ), (1267446171428259071936706085596574985288937253/65290998046775770784500875000000000:ℝ), (4893233793456488612711800037620598384089468009/783491976561309249414010500000000000:ℝ)],
  ![(4698358330323256902913738183911782432812747/261163992187103083138003500000000000:ℝ), (1309369812253521013395455122623827390587254259/195872994140327312353502625000000000:ℝ), (2584919624143371810410134154098845952312905509/130581996093551541569001750000000000:ℝ), (1261922334920568234189407108192278110288937253/65290998046775770784500875000000000:ℝ), (4870766658603743302299579843986565180964468009/783491976561309249414010500000000000:ℝ)]]
theorem cell12_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell12 3 b ν := by
 have heq : highRegular cell12 3 b ν = Record12518109.Bernstein.bsum 1 4 (7326321490291623774768526703211735539438241/5985715951312160644531250000000000000000000:ℝ) cell12_regular3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_regular3_g]
def cell12_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(183013777269542337185390443521228195891712747/261163992187103083138003500000000000:ℝ), (1458090980514580955382506762963742000817554259/195872994140327312353502625000000000:ℝ), (2413351562368004715578211723968391041543205509/130581996093551541569001750000000000:ℝ), (1129312755448679743064458565082487619199037253/65290998046775770784500875000000000:ℝ), (4359825901338407994924264567080631207694768009/783491976561309249414010500000000000:ℝ)],
  ![(179590758499591472918293864274744533144712747/261163992187103083138003500000000000:ℝ), (1442430358556351817837408318362428654567554259/195872994140327312353502625000000000:ℝ), (2393016196745325915513298978112746119668205509/130581996093551541569001750000000000:ℝ), (373731105286791406563697580658355248066345751/21763666015591923594833625000000000:ℝ), (4332036193297549448095021668368473004569768009/783491976561309249414010500000000000:ℝ)]]
theorem cell12_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell12 4 b ν := by
 have heq : highRegular cell12 4 b ν = Record12518109.Bernstein.bsum 1 4 (538772275498774418754881592824233599434138241/5985715951312160644531250000000000000000000:ℝ) cell12_regular4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_regular4_g]
def cell12_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(475750073712980859842742973678848281/10330445480285711923500000000000:ℝ), (38668744075540344696635537044196789233/294417696188142789819750000000000:ℝ), (51050879736413230244765652053382804233/588835392376285579639500000000000:ℝ)],
  ![(1416869564519924113586001363693544843/30991336440857135770500000000000:ℝ), (38445860437252938350352232786071789233/294417696188142789819750000000000:ℝ), (5644516176575994773703090809750867137/65426154708476175515500000000000:ℝ)]]
theorem cell12_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 0 false b ν := by
 have heq : highBranch cell12 0 false b ν = Record12518109.Bernstein.bsum 1 2 (1416869564519924113586001363693544843/3830858208839782812500000000000000000:ℝ) cell12_exceptional0_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional0_0_g]
def cell12_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(17809539778780251770383682772087568291723/387216087937549340028550500000000000:ℝ), (1448197919774878297614600034251776078945539/11035658506220156190813689250000000000:ℝ), (1912405909692370582514576904653295311340539/22071317012440312381627378500000000000:ℝ)],
  ![(53040198448469681882977349411600035875169/1161648263812648020085651500000000000:ℝ), (1439856004408685401177226481585926703945539/11035658506220156190813689250000000000:ℝ), (634346126409277058190377369966332812113513/7357105670813437460542459500000000000:ℝ)]]
theorem cell12_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 0 true b ν := by
 have heq : highBranch cell12 0 true b ν = Record12518109.Bernstein.bsum 1 2 (53040198448469681882977349411600035875169/143592058241941579160937500000000000000000:ℝ) cell12_exceptional0_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional0_1_g]
theorem cell12_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 0 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional0_0 hb hν) (cell12_exceptional0_1 hb hν)
def cell12_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(13970384746185999411573180338261927/3443481826761903974500000000000:ℝ), (2875857527340183351818034232023926407/15495668220428567885250000000000:ℝ), (5669726107068505859591432339144736407/30991336440857135770500000000000:ℝ)],
  ![(121324557170395550060540440701357343/30991336440857135770500000000000:ℝ), (2865172782818070727463273152648926407/15495668220428567885250000000000:ℝ), (1884225361428172045845815597423245469/10330445480285711923500000000000:ℝ)]]
theorem cell12_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 1 false b ν := by
 have heq : highBranch cell12 1 false b ν = Record12518109.Bernstein.bsum 1 2 (121324557170395550060540440701357343/3830858208839782812500000000000000000:ℝ) cell12_exceptional1_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional1_0_g]
def cell12_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(1547955560120459648730140445540513604223/387216087937549340028550500000000000:ℝ), (107731419570523648226227492867592192888581/580824131906324010042825750000000000:ℝ), (212458648120322145832435446196390978968581/1161648263812648020085651500000000000:ℝ)],
  ![(4479284937987302736352497635083871812669/1161648263812648020085651500000000000:ℝ), (107331577609903087866504485478929067888581/580824131906324010042825750000000000:ℝ), (70606731162911279209293364538250117989527/387216087937549340028550500000000000:ℝ)]]
theorem cell12_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 1 true b ν := by
 have heq : highBranch cell12 1 true b ν = Record12518109.Bernstein.bsum 1 2 (4479284937987302736352497635083871812669/143592058241941579160937500000000000000000:ℝ) cell12_exceptional1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional1_1_g]
theorem cell12_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 1 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional1_0 hb hν) (cell12_exceptional1_1 hb hν)
def cell12_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(2577709580695106545762044216587367811/30991336440857135770500000000000:ℝ), (2723297569324835085908171165858579/24793069152685708616400000000:ℝ), (792760952966719673364661769401/26445940429531422524160000:ℝ)],
  ![(2565823677200611917097385384244367811/30991336440857135770500000000000:ℝ), (902526098084727647176476146286193/8264356384228569538800000000:ℝ), (2357833646785741389535782308203/79337821288594267572480000:ℝ)]]
theorem cell12_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 2 false b ν := by
 have heq : highBranch cell12 2 false b ν = Record12518109.Bernstein.bsum 1 2 (2357833646785741389535782308203/9806997014629844000000000000000:ℝ) cell12_exceptional2_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional2_0_g]
def cell12_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(96546657880620472801927789437479737334713/1161648263812648020085651500000000000:ℝ), (101966998380230920236242792844636947897/929318611050118416068521200000000:ℝ), (9886722659674959223244688076304201/330424395040042103491029760000:ℝ)],
  ![(96101815824115926366429199051992068334713/1161648263812648020085651500000000000:ℝ), (11264315522448947258982309183086216433/103257623450013157340946800000000:ℝ), (88215622432795302043806190077737809/2973819555360378931419267840000:ℝ)]]
theorem cell12_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 2 true b ν := by
 have heq : highBranch cell12 2 true b ν = Record12518109.Bernstein.bsum 1 2 (88215622432795302043806190077737809/367595669099370442652000000000000000:ℝ) cell12_exceptional2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional2_1_g]
theorem cell12_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 2 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional2_0 hb hν) (cell12_exceptional2_1 hb hν)
def cell12_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(146032103648207666848425157892949427/3443481826761903974500000000000:ℝ), (36083109508628589907894309544196789233/294417696188142789819750000000000:ℝ), (48049428496081170070424424553382804233/588835392376285579639500000000000:ℝ)],
  ![(1303908276214850535693598863693544843/30991336440857135770500000000000:ℝ), (11953408623447061187203668428690596411/98139232062714263273250000000000:ℝ), (47799194348851892788986589787757804233/588835392376285579639500000000000:ℝ)]]
theorem cell12_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 3 false b ν := by
 have heq : highBranch cell12 3 false b ν = Record12518109.Bernstein.bsum 1 2 (1303908276214850535693598863693544843/3830858208839782812500000000000000000:ℝ) cell12_exceptional3_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional3_0_g]
def cell12_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(16398163788933894130336708469587568291723/387216087937549340028550500000000000:ℝ), (1351280579303324992868212603869276078945539/11035658506220156190813689250000000000:ℝ), (1799902512851003970999744674270795311340539/22071317012440312381627378500000000000:ℝ)],
  ![(48806070478930608962836426504100035875169/1161648263812648020085651500000000000:ℝ), (149215407104125788492315450133714078216171/1226184278468906243423743250000000000:ℝ), (1790534982386464563056299879516498436340539/22071317012440312381627378500000000000:ℝ)]]
theorem cell12_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 3 true b ν := by
 have heq : highBranch cell12 3 true b ν = Record12518109.Bernstein.bsum 1 2 (48806070478930608962836426504100035875169/143592058241941579160937500000000000000000:ℝ) cell12_exceptional3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional3_1_g]
theorem cell12_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 3 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional3_0 hb hν) (cell12_exceptional3_1 hb hν)
def cell12_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(40120671163507626310193623044357343/30991336440857135770500000000000:ℝ), (2722003372257774896602624232023926407/15495668220428567885250000000000:ℝ), (1816290080637829867661799113048245469/10330445480285711923500000000000:ℝ)],
  ![(35711765618229181666575440701357343/30991336440857135770500000000000:ℝ), (301257625303962474694207016960991823/1721740913380951987250000000000:ℝ), (5431820219129499880931411792269736407/30991336440857135770500000000000:ℝ)]]
theorem cell12_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 4 false b ν := by
 have heq : highBranch cell12 4 false b ν = Record12518109.Bernstein.bsum 1 2 (35711765618229181666575440701357343/3830858208839782812500000000000000000:ℝ) cell12_exceptional4_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional4_0_g]
def cell12_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(1434842414611526959679431241621540812669/1161648263812648020085651500000000000:ℝ), (101964504275569732099388279837592192888581/580824131906324010042825750000000000:ℝ), (68060102575572223828690478763796992989527/387216087937549340028550500000000000:ℝ)],
  ![(1270260672237450749841507540083871812669/1161648263812648020085651500000000000:ℝ), (33854887438316390579888424149643022629527/193608043968774670014275250000000000:ℝ), (203541853095128363281516083709750353968581/1161648263812648020085651500000000000:ℝ)]]
theorem cell12_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 4 true b ν := by
 have heq : highBranch cell12 4 true b ν = Record12518109.Bernstein.bsum 1 2 (1270260672237450749841507540083871812669/143592058241941579160937500000000000000000:ℝ) cell12_exceptional4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional4_1_g]
theorem cell12_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 4 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional4_0 hb hν) (cell12_exceptional4_1 hb hν)
def cell12_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(431083929181015486081446262233535781/10330445480285711923500000000000:ℝ), (6926562313843765731452277445114308703051/72721170958471269085478250000000000:ℝ), (8265416253968041209549569031671122958051/145442341916942538170956500000000000:ℝ)],
  ![(1283485956115119029653908104357607343/30991336440857135770500000000000:ℝ), (6878984538525163628041521866082433703051/72721170958471269085478250000000000:ℝ), (912781871439301335205234605992971995339/16160260212993615352328500000000000:ℝ)]]
theorem cell12_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 5 false b ν := by
 have heq : highBranch cell12 5 false b ν = Record12518109.Bernstein.bsum 1 2 (1283485956115119029653908104357607343/3830858208839782812500000000000000000:ℝ) cell12_exceptional5_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional5_0_g]
def cell12_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(16135318683288593665688998136982919854223/387216087937549340028550500000000000:ℝ), (259326349450881561577626434683584146663335633/2725807651036378579130981244750000000000:ℝ), (309532446226985276550302910292006573924550633/5451615302072757158261962489500000000000:ℝ)],
  ![(48040580654632372921950697771911090562669/1161648263812648020085651500000000000:ℝ), (257546062414404685978650877902570526038335633/2725807651036378579130981244750000000000:ℝ), (102549012598240302247406338549966123599850211/1817205100690919052753987496500000000000:ℝ)]]
theorem cell12_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 5 true b ν := by
 have heq : highBranch cell12 5 true b ν = Record12518109.Bernstein.bsum 1 2 (48040580654632372921950697771911090562669/143592058241941579160937500000000000000000:ℝ) cell12_exceptional5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional5_1_g]
theorem cell12_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 5 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional5_0 hb hν) (cell12_exceptional5_1 hb hν)
def cell12_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(2577709580695106545762044216587367811/30991336440857135770500000000000:ℝ), (2723297569324835085908171165858579/24793069152685708616400000000:ℝ), (792760952966719673364661769401/26445940429531422524160000:ℝ)],
  ![(2565823677200611917097385384244367811/30991336440857135770500000000000:ℝ), (902526098084727647176476146286193/8264356384228569538800000000:ℝ), (2357833646785741389535782308203/79337821288594267572480000:ℝ)]]
theorem cell12_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 6 false b ν := by
 have heq : highBranch cell12 6 false b ν = Record12518109.Bernstein.bsum 1 2 (2357833646785741389535782308203/9806997014629844000000000000000:ℝ) cell12_exceptional6_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional6_0_g]
def cell12_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(96546657880620472801927789437479737334713/1161648263812648020085651500000000000:ℝ), (101966998380230920236242792844636947897/929318611050118416068521200000000:ℝ), (9886722659674959223244688076304201/330424395040042103491029760000:ℝ)],
  ![(96101815824115926366429199051992068334713/1161648263812648020085651500000000000:ℝ), (11264315522448947258982309183086216433/103257623450013157340946800000000:ℝ), (88215622432795302043806190077737809/2973819555360378931419267840000:ℝ)]]
theorem cell12_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 6 true b ν := by
 have heq : highBranch cell12 6 true b ν = Record12518109.Bernstein.bsum 1 2 (88215622432795302043806190077737809/367595669099370442652000000000000000:ℝ) cell12_exceptional6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional6_1_g]
theorem cell12_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 6 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional6_0 hb hν) (cell12_exceptional6_1 hb hν)
def cell12_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(394368726673823373573041262233535781/10330445480285711923500000000000:ℝ), (6343157538402615010248211820114308703051/72721170958471269085478250000000000:ℝ), (7615520039184497519147271776671122958051/145442341916942538170956500000000000:ℝ)],
  ![(1173340348593542692128693104357607343/30991336440857135770500000000000:ℝ), (2098526587694670968945818747027477901017/24240390319490423028492750000000000:ℝ), (7565140628170168326444814198936747958051/145442341916942538170956500000000000:ℝ)]]
theorem cell12_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 7 false b ν := by
 have heq : highBranch cell12 7 false b ν = Record12518109.Bernstein.bsum 1 2 (1173340348593542692128693104357607343/3830858208839782812500000000000000000:ℝ) cell12_exceptional7_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional7_0_g]
def cell12_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(4919707582570503904178817840660973284741/129072029312516446676183500000000000:ℝ), (237458588253020909094734442861709146663335633/2725807651036378579130981244750000000000:ℝ), (285172386408253708402953602282841573924550633/5451615302072757158261962489500000000000:ℝ)],
  ![(43911992847901127062493063926911090562669/1161648263812648020085651500000000000:ℝ), (26186477912949337055084320675632836226481737/302867516781819842125664582750000000000:ℝ), (283286977975989338594869707640733370799550633/5451615302072757158261962489500000000000:ℝ)]]
theorem cell12_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell12 7 true b ν := by
 have heq : highBranch cell12 7 true b ν = Record12518109.Bernstein.bsum 1 2 (43911992847901127062493063926911090562669/143592058241941579160937500000000000000000:ℝ) cell12_exceptional7_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_exceptional7_1_g]
theorem cell12_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
 (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell12 7 b ν :=
 highExceptional_pos_of_branches (cell12_exceptional7_0 hb hν) (cell12_exceptional7_1 hb hν)
def cell12_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(25729036078174588674851386051/2297472931871065266575000000000:ℝ)],
  ![(43046679707300454572570386051/2297472931871065266575000000000:ℝ)]]
theorem cell12_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 0 false b := by
 have heq : domainBranch cell12 0 false b = Record12518109.Bernstein.bsum 1 0 (25729036078174588674851386051/4594945863742130533150000000000000:ℝ) cell12_domain0_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain0_0_g]
def cell12_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(25729036078174588674851386051/2297472931871065266575000000000:ℝ)],
  ![(43046679707300454572570386051/2297472931871065266575000000000:ℝ)]]
theorem cell12_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 0 true b := by
 have heq : domainBranch cell12 0 true b = Record12518109.Bernstein.bsum 1 0 (25729036078174588674851386051/4594945863742130533150000000000000:ℝ) cell12_domain0_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain0_1_g]
def cell12_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(344154996341714725996490689078717/24517492536574610000000000000000:ℝ)],
  ![(337614782915469673494696471078717/24517492536574610000000000000000:ℝ)]]
theorem cell12_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 1 false b := by
 have heq : domainBranch cell12 1 false b = Record12518109.Bernstein.bsum 1 0 (337614782915469673494696471078717/49034985073149220000000000000000000:ℝ) cell12_domain1_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain1_0_g]
def cell12_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(619556813884023352962002022177719/24517492536574610000000000000000:ℝ)],
  ![(613016600457778300460207804177719/24517492536574610000000000000000:ℝ)]]
theorem cell12_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 1 true b := by
 have heq : domainBranch cell12 1 true b = Record12518109.Bernstein.bsum 1 0 (613016600457778300460207804177719/49034985073149220000000000000000000:ℝ) cell12_domain1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain1_1_g]
def cell12_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(51052279977257392395184857065369/2451749253657461000000000000000:ℝ)],
  ![(51248912750175596073089431065369/2451749253657461000000000000000:ℝ)]]
theorem cell12_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 2 false b := by
 have heq : domainBranch cell12 2 false b = Record12518109.Bernstein.bsum 1 0 (51052279977257392395184857065369/4903498507314922000000000000000000:ℝ) cell12_domain2_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain2_0_g]
def cell12_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(24831744773969263252328860201483/2451749253657461000000000000000:ℝ)],
  ![(25028377546887466930233434201483/2451749253657461000000000000000:ℝ)]]
theorem cell12_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 2 true b := by
 have heq : domainBranch cell12 2 true b = Record12518109.Bernstein.bsum 1 0 (24831744773969263252328860201483/4903498507314922000000000000000000:ℝ) cell12_domain2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain2_1_g]
def cell12_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(576967057421384527762751551373/24517492536574610000000000000:ℝ)],
  ![(693926196128377768598645551373/24517492536574610000000000000:ℝ)]]
theorem cell12_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 3 false b := by
 have heq : domainBranch cell12 3 false b = Record12518109.Bernstein.bsum 1 0 (576967057421384527762751551373/49034985073149220000000000000000:ℝ) cell12_domain3_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain3_0_g]
def cell12_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(576967057421384527762751551373/24517492536574610000000000000:ℝ)],
  ![(693926196128377768598645551373/24517492536574610000000000000:ℝ)]]
theorem cell12_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 3 true b := by
 have heq : domainBranch cell12 3 true b = Record12518109.Bernstein.bsum 1 0 (576967057421384527762751551373/49034985073149220000000000000000:ℝ) cell12_domain3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain3_1_g]
def cell12_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1086172508271254032202493/76617164176795656250000:ℝ)],
  ![(925565111414819785202493/76617164176795656250000:ℝ)]]
theorem cell12_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 4 false b := by
 have heq : domainBranch cell12 4 false b = Record12518109.Bernstein.bsum 1 0 (925565111414819785202493/153234328353591312500000000:ℝ) cell12_domain4_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain4_0_g]
def cell12_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1086172508271254032202493/76617164176795656250000:ℝ)],
  ![(925565111414819785202493/76617164176795656250000:ℝ)]]
theorem cell12_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 4 true b := by
 have heq : domainBranch cell12 4 true b = Record12518109.Bernstein.bsum 1 0 (925565111414819785202493/153234328353591312500000000:ℝ) cell12_domain4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain4_1_g]
def cell12_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(15238591767391637607010948709963/1225874626828730500000000000000:ℝ)],
  ![(14920669659877874682594446709963/1225874626828730500000000000000:ℝ)]]
theorem cell12_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 5 false b := by
 have heq : domainBranch cell12 5 false b = Record12518109.Bernstein.bsum 1 0 (14920669659877874682594446709963/2451749253657461000000000000000000:ℝ) cell12_domain5_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain5_0_g]
def cell12_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(28982460537825650759253235175041/1225874626828730500000000000000:ℝ)],
  ![(28664538430311887834836733175041/1225874626828730500000000000000:ℝ)]]
theorem cell12_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 5 true b := by
 have heq : domainBranch cell12 5 true b = Record12518109.Bernstein.bsum 1 0 (28664538430311887834836733175041/2451749253657461000000000000000000:ℝ) cell12_domain5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain5_1_g]
def cell12_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(358262011579448889158642424659421171/2493663133023362124525500000000000:ℝ)],
  ![(352029899711628139262287726085421171/2493663133023362124525500000000000:ℝ)]]
theorem cell12_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 6 false b := by
 have heq : domainBranch cell12 6 false b = Record12518109.Bernstein.bsum 1 0 (352029899711628139262287726085421171/4987326266046724249051000000000000000:ℝ) cell12_domain6_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain6_0_g]
def cell12_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(347395967762925014669747098484179977/2493663133023362124525500000000000:ℝ)],
  ![(341163855895104264773392399910179977/2493663133023362124525500000000000:ℝ)]]
theorem cell12_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 6 true b := by
 have heq : domainBranch cell12 6 true b = Record12518109.Bernstein.bsum 1 0 (341163855895104264773392399910179977/4987326266046724249051000000000000000:ℝ) cell12_domain6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain6_1_g]
def cell12_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(34866599690462781839127518657/612937313414365250000000000:ℝ)],
  ![(38077510568227058140360518657/612937313414365250000000000:ℝ)]]
theorem cell12_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 7 false b := by
 have heq : domainBranch cell12 7 false b = Record12518109.Bernstein.bsum 1 0 (34866599690462781839127518657/1225874626828730500000000000000:ℝ) cell12_domain7_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain7_0_g]
def cell12_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(34866599690462781839127518657/612937313414365250000000000:ℝ)],
  ![(38077510568227058140360518657/612937313414365250000000000:ℝ)]]
theorem cell12_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 7 true b := by
 have heq : domainBranch cell12 7 true b = Record12518109.Bernstein.bsum 1 0 (34866599690462781839127518657/1225874626828730500000000000000:ℝ) cell12_domain7_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain7_1_g]
def cell12_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(9088818255211679483024026217709/122587462682873050000000000000:ℝ)],
  ![(8905419919240131886348240217709/122587462682873050000000000000:ℝ)]]
theorem cell12_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 8 false b := by
 have heq : domainBranch cell12 8 false b = Record12518109.Bernstein.bsum 1 0 (8905419919240131886348240217709/245174925365746100000000000000000:ℝ) cell12_domain8_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain8_0_g]
def cell12_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(9617954743403537892953643569863/122587462682873050000000000000:ℝ)],
  ![(9434556407431990296277857569863/122587462682873050000000000000:ℝ)]]
theorem cell12_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell12 8 true b := by
 have heq : domainBranch cell12 8 true b = Record12518109.Bernstein.bsum 1 0 (9434556407431990296277857569863/245174925365746100000000000000000:ℝ) cell12_domain8_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_domain8_1_g]
def cell12_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(205874450008032996539417/24517492536574610000000:ℝ)],
  ![(223719716325414579539417/24517492536574610000000:ℝ)]]
theorem cell12_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 0 b := by
 have heq : ordinary cell12 0 b = Record12518109.Bernstein.bsum 1 0 (205874450008032996539417/49034985073149220000000000:ℝ) cell12_ordinary0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary0_g]
def cell12_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(389844250914957784881749/73552477609723830000000:ℝ)],
  ![(336308451962813035881749/73552477609723830000000:ℝ)]]
theorem cell12_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 1 b := by
 have heq : ordinary cell12 1 b = Record12518109.Bernstein.bsum 1 0 (336308451962813035881749/147104955219447660000000000:ℝ) cell12_ordinary1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary1_g]
def cell12_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(23198483674821989700106037/24517492536574610000000:ℝ)],
  ![(23091412076917700202106037/24517492536574610000000:ℝ)]]
theorem cell12_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 2 b := by
 have heq : ordinary cell12 2 b = Record12518109.Bernstein.bsum 1 0 (23091412076917700202106037/49034985073149220000000000:ℝ) cell12_ordinary2_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary2_g]
def cell12_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(409999989/10000000:ℝ)],
  ![(419999989/10000000:ℝ)]]
theorem cell12_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 3 b := by
 have heq : ordinary cell12 3 b = Record12518109.Bernstein.bsum 1 0 (409999989/20000000000:ℝ) cell12_ordinary3_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary3_g]
def cell12_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(21349864791502747686570179/24517492536574610000000:ℝ)],
  ![(21193758208525308968570179/24517492536574610000000:ℝ)]]
theorem cell12_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 4 b := by
 have heq : ordinary cell12 4 b = Record12518109.Bernstein.bsum 1 0 (21193758208525308968570179/49034985073149220000000000:ℝ) cell12_ordinary4_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary4_g]
def cell12_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(3768718556670302487/381237906265000000000000:ℝ)],
  ![(3768718556670302487/381237906265000000000000:ℝ)]]
theorem cell12_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell12 5 b := by
 have heq : ordinary cell12 5 b = Record12518109.Bernstein.bsum 1 0 (3768718556670302487/762475812530000000000000000:ℝ) cell12_ordinary5_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_ordinary5_g]
def cell12_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(205871998258779339078417/24517492536574610000000:ℝ)],
  ![(223717264576160922078417/24517492536574610000000:ℝ)]]
theorem cell12_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 0 false b := by
 have heq : complementBranch cell12 0 false b = Record12518109.Bernstein.bsum 1 0 (205871998258779339078417/49034985073149220000000000:ℝ) cell12_complement0_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement0_0_g]
def cell12_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(18706520611201225628933266739517/2297472931871065266575000000000:ℝ)],
  ![(20384528452513635606538339739517/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 0 true b := by
 have heq : complementBranch cell12 0 true b = Record12518109.Bernstein.bsum 1 0 (18706520611201225628933266739517/4594945863742130533150000000000000:ℝ) cell12_complement0_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement0_1_g]
def cell12_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(55063358087079969787841906343/612937313414365250000000000:ℝ)],
  ![(54442609072081146131498906343/612937313414365250000000000:ℝ)]]
theorem cell12_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 1 false b := by
 have heq : complementBranch cell12 1 false b = Record12518109.Bernstein.bsum 1 0 (54442609072081146131498906343/1225874626828730500000000000000:ℝ) cell12_complement1_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement1_0_g]
def cell12_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(2058058691782303238236940367574839/22974729318710652665750000000000:ℝ)],
  ![(2034848881931866084012561428574839/22974729318710652665750000000000:ℝ)]]
theorem cell12_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 1 true b := by
 have heq : complementBranch cell12 1 true b = Record12518109.Bernstein.bsum 1 0 (2034848881931866084012561428574839/45949458637421305331500000000000000:ℝ) cell12_complement1_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement1_1_g]
def cell12_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(35368176402145749283900206343/612937313414365250000000000:ℝ)],
  ![(32962900755408767327557206343/612937313414365250000000000:ℝ)]]
theorem cell12_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 2 false b := by
 have heq : complementBranch cell12 2 false b = Record12518109.Bernstein.bsum 1 0 (32962900755408767327557206343/1225874626828730500000000000000:ℝ) cell12_complement2_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement2_0_g]
def cell12_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(1319824196685913851087693626474839/22974729318710652665750000000000:ℝ)],
  ![(1229724975098035309304414687474839/22974729318710652665750000000000:ℝ)]]
theorem cell12_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 2 true b := by
 have heq : complementBranch cell12 2 true b = Record12518109.Bernstein.bsum 1 0 (1229724975098035309304414687474839/45949458637421305331500000000000000:ℝ) cell12_complement2_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement2_1_g]
def cell12_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(47728407240026219913827331343/612937313414365250000000000:ℝ)],
  ![(47553789882961935832484331343/612937313414365250000000000:ℝ)]]
theorem cell12_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 3 false b := by
 have heq : complementBranch cell12 3 false b = Record12518109.Bernstein.bsum 1 0 (47553789882961935832484331343/1225874626828730500000000000000:ℝ) cell12_complement3_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement3_0_g]
def cell12_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1783122729182187531709252052849839/22974729318710652665750000000000:ℝ)],
  ![(1776635272266110724374598113849839/22974729318710652665750000000000:ℝ)]]
theorem cell12_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 3 true b := by
 have heq : complementBranch cell12 3 true b = Record12518109.Bernstein.bsum 1 0 (1776635272266110724374598113849839/45949458637421305331500000000000000:ℝ) cell12_complement3_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement3_1_g]
def cell12_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(45266509529409442350834618843/612937313414365250000000000:ℝ)],
  ![(44868826343377888481991618843/612937313414365250000000000:ℝ)]]
theorem cell12_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 4 false b := by
 have heq : complementBranch cell12 4 false b = Record12518109.Bernstein.bsum 1 0 (44868826343377888481991618843/1225874626828730500000000000000:ℝ) cell12_complement4_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement4_0_g]
def cell12_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1690843417295138858315596210212339/22974729318710652665750000000000:ℝ)],
  ![(1675994783911881877536079771212339/22974729318710652665750000000000:ℝ)]]
theorem cell12_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 4 true b := by
 have heq : complementBranch cell12 4 true b = Record12518109.Bernstein.bsum 1 0 (1675994783911881877536079771212339/45949458637421305331500000000000000:ℝ) cell12_complement4_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement4_1_g]
def cell12_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(1695813/25000:ℝ)],
  ![(395841/6250:ℝ)]]
theorem cell12_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 5 false b := by
 have heq : complementBranch cell12 5 false b = Record12518109.Bernstein.bsum 1 0 (395841/12500000:ℝ) cell12_complement5_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement5_0_g]
def cell12_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(155255262661031145184180238212017/2297472931871065266575000000000:ℝ)],
  ![(144927093860268743746369124212017/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 5 true b := by
 have heq : complementBranch cell12 5 true b = Record12518109.Bernstein.bsum 1 0 (144927093860268743746369124212017/4594945863742130533150000000000000:ℝ) cell12_complement5_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement5_1_g]
def cell12_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(4750707964449003407263081/24517492536574610000000:ℝ)],
  ![(4625791100227332326263081/24517492536574610000000:ℝ)]]
theorem cell12_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 6 false b := by
 have heq : complementBranch cell12 6 false b = Record12518109.Bernstein.bsum 1 0 (4625791100227332326263081/49034985073149220000000000:ℝ) cell12_complement6_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement6_0_g]
def cell12_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(444588850639033459854031382019517/2297472931871065266575000000000:ℝ)],
  ![(432888976132857592319856455019517/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 6 true b := by
 have heq : complementBranch cell12 6 true b = Record12518109.Bernstein.bsum 1 0 (432888976132857592319856455019517/4594945863742130533150000000000000:ℝ) cell12_complement6_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement6_1_g]
def cell12_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(7971062637569036709928806343/3677623880486191500000000000:ℝ)],
  ![(2924695429698750426195268781/1225874626828730500000000000:ℝ)]]
theorem cell12_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 7 false b := by
 have heq : complementBranch cell12 7 false b = Record12518109.Bernstein.bsum 1 0 (7971062637569036709928806343/7355247760972383000000000000000:ℝ) cell12_complement7_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement7_0_g]
def cell12_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(263665560905999845732811790875689/137848375912263915994500000000000:ℝ)],
  ![(98037216436258982242578833958563/45949458637421305331500000000000:ℝ)]]
theorem cell12_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 7 true b := by
 have heq : complementBranch cell12 7 true b = Record12518109.Bernstein.bsum 1 0 (263665560905999845732811790875689/275696751824527831989000000000000000:ℝ) cell12_complement7_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement7_1_g]
def cell12_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(131495732642388834633579006343/3677623880486191500000000000:ℝ)],
  ![(47668638694781666334078668781/1225874626828730500000000000:ℝ)]]
theorem cell12_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 8 false b := by
 have heq : complementBranch cell12 8 false b = Record12518109.Bernstein.bsum 1 0 (131495732642388834633579006343/7355247760972383000000000000000:ℝ) cell12_complement8_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement8_0_g]
def cell12_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(4893740766696660331304992237475689/137848375912263915994500000000000:ℝ)],
  ![(1775174441841361919217772316158563/45949458637421305331500000000000:ℝ)]]
theorem cell12_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 8 true b := by
 have heq : complementBranch cell12 8 true b = Record12518109.Bernstein.bsum 1 0 (4893740766696660331304992237475689/275696751824527831989000000000000000:ℝ) cell12_complement8_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement8_1_g]
def cell12_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(162376900143593784114491556343/3677623880486191500000000000:ℝ)],
  ![(58854624511052395311049518781/1225874626828730500000000000:ℝ)]]
theorem cell12_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 9 false b := by
 have heq : complementBranch cell12 9 false b = Record12518109.Bernstein.bsum 1 0 (162376900143593784114491556343/7355247760972383000000000000000:ℝ) cell12_complement9_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement9_0_g]
def cell12_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(6051259568144325452698037349125689/137848375912263915994500000000000:ℝ)],
  ![(2194458748192637653461570686708563/45949458637421305331500000000000:ℝ)]]
theorem cell12_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 9 true b := by
 have heq : complementBranch cell12 9 true b = Record12518109.Bernstein.bsum 1 0 (6051259568144325452698037349125689/275696751824527831989000000000000000:ℝ) cell12_complement9_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement9_1_g]
def cell12_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(205871998258779339078417/24517492536574610000000:ℝ)],
  ![(223717264576160922078417/24517492536574610000000:ℝ)]]
theorem cell12_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 10 false b := by
 have heq : complementBranch cell12 10 false b = Record12518109.Bernstein.bsum 1 0 (205871998258779339078417/49034985073149220000000000:ℝ) cell12_complement10_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement10_0_g]
def cell12_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(18706520611201225628933266739517/2297472931871065266575000000000:ℝ)],
  ![(20384528452513635606538339739517/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 10 true b := by
 have heq : complementBranch cell12 10 true b = Record12518109.Bernstein.bsum 1 0 (18706520611201225628933266739517/4594945863742130533150000000000000:ℝ) cell12_complement10_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement10_1_g]
def cell12_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(617622124149472160887751/12258746268287305000000:ℝ)],
  ![(671157923101616909887751/12258746268287305000000:ℝ)]]
theorem cell12_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 11 false b := by
 have heq : complementBranch cell12 11 false b = Record12518109.Bernstein.bsum 1 0 (617622124149472160887751/24517492536574610000000000:ℝ) cell12_complement11_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement11_0_g]
def cell12_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(115166420731839985745020359377017/2297472931871065266575000000000:ℝ)],
  ![(125205605040332569167487932377017/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 11 true b := by
 have heq : complementBranch cell12 11 true b = Record12518109.Bernstein.bsum 1 0 (115166420731839985745020359377017/4594945863742130533150000000000000:ℝ) cell12_complement11_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement11_1_g]
def cell12_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(1441118698306977318314919/24517492536574610000000:ℝ)],
  ![(1566035562528648399314919/24517492536574610000000:ℝ)]]
theorem cell12_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 12 false b := by
 have heq : complementBranch cell12 12 false b = Record12518109.Bernstein.bsum 1 0 (1441118698306977318314919/49034985073149220000000000:ℝ) cell12_complement12_0_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement12_0_g]
def cell12_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(134458400755967737768237777904517/2297472931871065266575000000000:ℝ)],
  ![(146169820357896355879677850904517/2297472931871065266575000000000:ℝ)]]
theorem cell12_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ))
    (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell12 12 true b := by
 have heq : complementBranch cell12 12 true b = Record12518109.Bernstein.bsum 1 0 (134458400755967737768237777904517/4594945863742130533150000000000000:ℝ) cell12_complement12_1_g (41/1000:ℝ) (83/2000:ℝ) (1557/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell12, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell12_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell12_complement12_1_g]
theorem cell12_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 0 b := complementReserve_pos_of_branches (cell12_complement0_0 hb hν) (cell12_complement0_1 hb hν)
theorem cell12_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 1 b := complementReserve_pos_of_branches (cell12_complement1_0 hb hν) (cell12_complement1_1 hb hν)
theorem cell12_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 2 b := complementReserve_pos_of_branches (cell12_complement2_0 hb hν) (cell12_complement2_1 hb hν)
theorem cell12_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 3 b := complementReserve_pos_of_branches (cell12_complement3_0 hb hν) (cell12_complement3_1 hb hν)
theorem cell12_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 4 b := complementReserve_pos_of_branches (cell12_complement4_0 hb hν) (cell12_complement4_1 hb hν)
theorem cell12_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 5 b := complementReserve_pos_of_branches (cell12_complement5_0 hb hν) (cell12_complement5_1 hb hν)
theorem cell12_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 6 b := complementReserve_pos_of_branches (cell12_complement6_0 hb hν) (cell12_complement6_1 hb hν)
theorem cell12_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 7 b := complementReserve_pos_of_branches (cell12_complement7_0 hb hν) (cell12_complement7_1 hb hν)
theorem cell12_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 8 b := complementReserve_pos_of_branches (cell12_complement8_0 hb hν) (cell12_complement8_1 hb hν)
theorem cell12_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 9 b := complementReserve_pos_of_branches (cell12_complement9_0 hb hν) (cell12_complement9_1 hb hν)
theorem cell12_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 10 b := complementReserve_pos_of_branches (cell12_complement10_0 hb hν) (cell12_complement10_1 hb hν)
theorem cell12_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 11 b := complementReserve_pos_of_branches (cell12_complement11_0 hb hν) (cell12_complement11_1 hb hν)
theorem cell12_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (hν : ν ∈ Set.Icc (1557/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell12 12 b := complementReserve_pos_of_branches (cell12_complement12_0 hb hν) (cell12_complement12_1 hb hν)
theorem cell12_all_domains {b : ℝ} (hb : b ∈ Set.Icc (41/1000:ℝ) (83/2000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell12 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell12_domain0_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain0_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain1_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain1_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain2_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain2_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain3_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain3_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain4_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain4_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain5_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain5_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain6_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain6_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain7_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain7_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell12_domain8_0 (ν := (1557/2500:ℝ)) hb (by norm_num)
   | true => exact cell12_domain8_1 (ν := (1557/2500:ℝ)) hb (by norm_num)
end
end Record12518109Admission
