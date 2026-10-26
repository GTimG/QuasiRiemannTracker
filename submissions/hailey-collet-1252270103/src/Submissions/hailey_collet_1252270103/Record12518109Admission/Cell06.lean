/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell6 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (1289/2000:ℝ), (17/500:ℝ), (9/250:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (493/100000:ℝ), (1/25:ℝ)⟩
def cell6_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(6452970968091578402518502006295933979675199/28557886142239700622753625000000000:ℝ), (379638185293311518783762878531770434210648913/92813129962279027023949281250000000:ℝ), (1993018794919343084433859778028771111823667239/185626259924558054047898562500000000:ℝ), (930023143328736856254990324821209846987222413/92813129962279027023949281250000000:ℝ), (1170891060773952890170457029540937793612222413/371252519849116108095797125000000000:ℝ)],
  ![(8501970604694297703350770540820999551025597/85673658426719101868260875000000000:ℝ), (972631937589179536163774637364745743631946739/278439389886837081071847843750000000:ℝ), (1804791504955322697311371771716797111823667239/185626259924558054047898562500000000:ℝ), (2583222646705808689184504863143379540961667239/278439389886837081071847843750000000:ℝ), (3290566168154957180502057865872813380836667239/1113757559547348324287391375000000000:ℝ)]]
theorem cell6_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell6 2 b ν := by
 have heq : highRegular cell6 2 b ν = Record12518109.Bernstein.bsum 1 4 (8501970604694297703350770540820999551025597/345786057710007000000000000000000000000000:ℝ) cell6_regular2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_regular2_g]
def cell6_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(226475956726250600707178501722936288544607761/1113757559547348324287391375000000000:ℝ), (366135414621475061837293640144813614010723913/92813129962279027023949281250000000:ℝ), (1946682977835704500572681596123745598486392239/185626259924558054047898562500000000:ℝ), (2747941269994254434368987480613803102624392239/278439389886837081071847843750000000:ℝ), (89331918783906615232801230020882597884599801/28557886142239700622753625000000000:ℝ)],
  ![(64707083189249705043390176904690057500607761/1113757559547348324287391375000000000:ℝ), (915139749734316957157477728117825283032171739/278439389886837081071847843750000000:ℝ), (1744924171542648506500321738011771598486392239/185626259924558054047898562500000000:ℝ), (194671182029724953732189260137965623278799403/21418414606679775467065218750000000:ℝ), (3254289354099339306696947248064421317499392239/1113757559547348324287391375000000000:ℝ)]]
theorem cell6_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell6 3 b ν := by
 have heq : highRegular cell6 3 b ν = Record12518109.Bernstein.bsum 1 4 (64707083189249705043390176904690057500607761/4495218750230091000000000000000000000000000:ℝ) cell6_regular3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_regular3_g]
def cell6_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(48499252759396454647157952521678652467600597/85673658426719101868260875000000000:ℝ), (417970321254051782500722349424493345049323913/92813129962279027023949281250000000:ℝ), (1893970776523626171559384973115554454952192239/185626259924558054047898562500000000:ℝ), (195347700954067707096449904003607754545399403/21418414606679775467065218750000000:ℝ), (1060384346908748226641195585406560507988397413/371252519849116108095797125000000000:ℝ)],
  ![(32304255022791467824328081857648450079600597/85673658426719101868260875000000000:ℝ), (1030863790671234607712977902900464476147971739/278439389886837081071847843750000000:ℝ), (1660930201088576601778575943603580454952192239/185626259924558054047898562500000000:ℝ), (176825506158142796622362904094357754545399403/21418414606679775467065218750000000:ℝ), (2934613354560516082356136033469681523965192239/1113757559547348324287391375000000000:ℝ)]]
theorem cell6_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highRegular cell6 4 b ν := by
 have heq : highRegular cell6 4 b ν = Record12518109.Bernstein.bsum 1 4 (32304255022791467824328081857648450079600597/345786057710007000000000000000000000000000:ℝ) cell6_regular4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_regular4_g]
def cell6_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(917927831799603576236769225753767047/48750013405139535215500000000000:ℝ), (1214696016535849702797790827283486953/24375006702569767607750000000000:ℝ), (19881298007195877068366592441589528389/633750174266813957801500000000000:ℝ)],
  ![(2629892463947259681628479122697301141/146250040215418605646500000000000:ℝ), (1169007907908179646822492319283486953/24375006702569767607750000000000:ℝ), (57688262307012828378947610324768585167/1901250522800441873404500000000000:ℝ)]]
theorem cell6_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 0 false b ν := by
 have heq : highBranch cell6 0 false b ν = Record12518109.Bernstein.bsum 1 2 (2629892463947259681628479122697301141/6569935096490133000000000000000000000:ℝ) cell6_exceptional0_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional0_0_g]
def cell6_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(446773139430495576615912244718302503820113/23754857782042987580273624500000000000:ℝ), (1774224693021352692608141806252070804412661/35632286673064481370410436750000000000:ℝ), (2234247753767391084926903547314523100039661/71264573346128962740820873500000000000:ℝ)],
  ![(1280269378166933249124130343951416155460339/71264573346128962740820873500000000000:ℝ), (1707746501295652322719021073805824804412661/35632286673064481370410436750000000000:ℝ), (2161246104272350772102145350803523100039661/71264573346128962740820873500000000000:ℝ)]]
theorem cell6_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 0 true b ν := by
 have heq : highBranch cell6 0 true b ν = Record12518109.Bernstein.bsum 1 2 (1280269378166933249124130343951416155460339/3201391403882615518107000000000000000000000:ℝ) cell6_exceptional0_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional0_1_g]
theorem cell6_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 0 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional0_0 hb hν) (cell6_exceptional0_1 hb hν)
def cell6_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(748480408096662532466891016570561307/100065816989496940705500000000000:ℝ), (3494181012063004667252843232154262693/50032908494748470352750000000000:ℝ), (2092184927658482159628828177334646231/33355272329832313568500000000000:ℝ)],
  ![(690995991267030009278358321342561307/100065816989496940705500000000000:ℝ), (1133902560815231949860012361384754231/16677636164916156784250000000000:ℝ), (6148958716860634941879791532003938693/100065816989496940705500000000000:ℝ)]]
theorem cell6_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 1 false b ν := by
 have heq : highBranch cell6 1 false b ν = Record12518109.Bernstein.bsum 1 2 (690995991267030009278358321342561307/4495218750230091000000000000000000000:ℝ) cell6_exceptional1_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional1_0_g]
def cell6_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(27974162212321393113535776999730031195281/3750767018217313828464256500000000000:ℝ), (43631797595168951675955364758147130340573/625127836369552304744042750000000000:ℝ), (235191243675332971129478341494694277304719/3750767018217313828464256500000000000:ℝ)],
  ![(25836287384197691033564213670598907195281/3750767018217313828464256500000000000:ℝ), (127445550546526897127017444197007391021719/1875383509108656914232128250000000000:ℝ), (230424417911381333525114545625694277304719/3750767018217313828464256500000000000:ℝ)]]
theorem cell6_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 1 true b ν := by
 have heq : highBranch cell6 1 true b ν = Record12518109.Bernstein.bsum 1 2 (25836287384197691033564213670598907195281/168494284414874500953000000000000000000000:ℝ) cell6_exceptional1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional1_1_g]
theorem cell6_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 1 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional1_0 hb hν) (cell6_exceptional1_1 hb hν)
def cell6_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(1392443184626580111855275997003523807/50032908494748470352750000000000:ℝ), (481090600479324339559051915635581/12508227123687117588187500000:ℝ), (4596806993413363499688109856693/400263267957987762822000000:ℝ)],
  ![(1348961920547845520520619699389523807/50032908494748470352750000000000:ℝ), (461563646187839795499881628635581/12508227123687117588187500000:ℝ), (1438963806935987270420445952231/133421089319329254274000000:ℝ)]]
theorem cell6_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 2 false b ν := by
 have heq : highBranch cell6 2 false b ν = Record12518109.Bernstein.bsum 1 2 (1438963806935987270420445952231/5993625000306788000000000000000:ℝ) cell6_exceptional2_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional2_0_g]
def cell6_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(52150555006235560836498257978522183332781/1875383509108656914232128250000000000:ℝ), (72050224979536033562570137758739612217/1875383509108656914232128250000000:ℝ), (57332017382284416499537589015012123/5001022690956418437952342000000:ℝ)],
  ![(50529153568723059042853439818106621332781/1875383509108656914232128250000000000:ℝ), (69138845243770801414671761056305612217/1875383509108656914232128250000000:ℝ), (161567407067804350960344383569036369/15003068072869255313857026000000:ℝ)]]
theorem cell6_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 2 true b ν := by
 have heq : highBranch cell6 2 true b ν = Record12518109.Bernstein.bsum 1 2 (161567407067804350960344383569036369/673977137659498003812000000000000000:ℝ) cell6_exceptional2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional2_1_g]
theorem cell6_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 2 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional2_0 hb hν) (cell6_exceptional2_1 hb hν)
def cell6_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(2352855913064022135556772677261301141/146250040215418605646500000000000:ℝ), (1059325178052524338695635827283486953/24375006702569767607750000000000:ℝ), (52775052200696513353595732324768585167/1901250522800441873404500000000000:ℝ)],
  ![(742988293870823696158314707565767047/48750013405139535215500000000000:ℝ), (1013637069424854282720337319283486953/24375006702569767607750000000000:ℝ), (16939806828707236842481188441589528389/633750174266813957801500000000000:ℝ)]]
theorem cell6_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 3 false b ν := by
 have heq : highBranch cell6 3 false b ν = Record12518109.Bernstein.bsum 1 2 (742988293870823696158314707565767047/2189978365496711000000000000000000000:ℝ) cell6_exceptional3_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional3_0_g]
def cell6_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(1144955826898973278964475352889907511460339/71264573346128962740820873500000000000:ℝ), (1547097852605403792325139847517070804412661/35632286673064481370410436750000000000:ℝ), (658927651931643104832992476193174366679887/23754857782042987580273624500000000000:ℝ)],
  ![(361635262258139932746956320895472051820113/23754857782042987580273624500000000000:ℝ), (1480619660879703422436019115070824804412661/35632286673064481370410436750000000000:ℝ), (1903781306299889001674219232068523100039661/71264573346128962740820873500000000000:ℝ)]]
theorem cell6_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 3 true b ν := by
 have heq : highBranch cell6 3 true b ν = Record12518109.Bernstein.bsum 1 2 (361635262258139932746956320895472051820113/1067130467960871839369000000000000000000000:ℝ) cell6_exceptional3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional3_1_g]
theorem cell6_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 3 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional3_0 hb hν) (cell6_exceptional3_1 hb hν)
def cell6_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(520281100239200737011446016570561307/100065816989496940705500000000000:ℝ), (3133562853874702417845788232154262693/50032908494748470352750000000000:ℝ), (1928506363598697904780643177334646231/33355272329832313568500000000000:ℝ)],
  ![(462796683409568213822913321342561307/100065816989496940705500000000000:ℝ), (1013696508085797866724327361384754231/16677636164916156784250000000000:ℝ), (5657923024681282177335236532003938693/100065816989496940705500000000000:ℝ)]]
theorem cell6_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 4 false b ν := by
 have heq : highBranch cell6 4 false b ν = Record12518109.Bernstein.bsum 1 2 (462796683409568213822913321342561307/4495218750230091000000000000000000000:ℝ) cell6_exceptional4_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional4_0_g]
def cell6_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(19420567555900152634479332064730031195281/3750767018217313828464256500000000000:ℝ), (39126114120711573937780483903147130340573/625127836369552304744042750000000000:ℝ), (216785752825374291456054786429694277304719/3750767018217313828464256500000000000:ℝ)],
  ![(17282692727776450554507768735598907195281/3750767018217313828464256500000000000:ℝ), (113928500123154763912492801632007391021719/1875383509108656914232128250000000000:ℝ), (212018927061422653851690990560694277304719/3750767018217313828464256500000000000:ℝ)]]
theorem cell6_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 4 true b ν := by
 have heq : highBranch cell6 4 true b ν = Record12518109.Bernstein.bsum 1 2 (17282692727776450554507768735598907195281/168494284414874500953000000000000000000000:ℝ) cell6_exceptional4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional4_1_g]
theorem cell6_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 4 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional4_0 hb hν) (cell6_exceptional4_1 hb hν)
def cell6_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(1829961541961272301158033062045561307/100065816989496940705500000000000:ℝ), (574916402395798904969762315194496203171/14282471032616274883004250000000000:ℝ), (8473622437480034603812728599723778989723/371344246848023146958110500000000000:ℝ)],
  ![(1746496212215346773696900366817561307/100065816989496940705500000000000:ℝ), (2383301906203482389143559662250150213741/61890707808003857826351750000000000:ℝ), (903628206180650070285935614080419887747/41260471872002571884234500000000000:ℝ)]]
theorem cell6_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 5 false b ν := by
 have heq : highBranch cell6 5 false b ν = Record12518109.Bernstein.bsum 1 2 (1746496212215346773696900366817561307/4495218750230091000000000000000000000:ℝ) cell6_exceptional5_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional5_0_g]
def cell6_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(68511319552968561073385854290269456195281/3750767018217313828464256500000000000:ℝ), (279858964576328565392041070864430251422461709/6959548202302225808715427935750000000000:ℝ), (317346409128997794290179739354929285065312209/13919096404604451617430855871500000000000:ℝ)],
  ![(65399602166003448314264425161138332195281/3750767018217313828464256500000000000:ℝ), (29752756922561112151338491216819114158051301/773283133589136200968380881750000000000:ℝ), (101541577087670788249893827252006761688437403/4639698801534817205810285290500000000000:ℝ)]]
theorem cell6_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 5 true b ν := by
 have heq : highBranch cell6 5 true b ν = Record12518109.Bernstein.bsum 1 2 (65399602166003448314264425161138332195281/168494284414874500953000000000000000000000:ℝ) cell6_exceptional5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional5_1_g]
theorem cell6_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 5 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional5_0 hb hν) (cell6_exceptional5_1 hb hν)
def cell6_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(1392443184626580111855275997003523807/50032908494748470352750000000000:ℝ), (481090600479324339559051915635581/12508227123687117588187500000:ℝ), (4596806993413363499688109856693/400263267957987762822000000:ℝ)],
  ![(1348961920547845520520619699389523807/50032908494748470352750000000000:ℝ), (461563646187839795499881628635581/12508227123687117588187500000:ℝ), (1438963806935987270420445952231/133421089319329254274000000:ℝ)]]
theorem cell6_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 6 false b ν := by
 have heq : highBranch cell6 6 false b ν = Record12518109.Bernstein.bsum 1 2 (1438963806935987270420445952231/5993625000306788000000000000000:ℝ) cell6_exceptional6_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional6_0_g]
def cell6_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(52150555006235560836498257978522183332781/1875383509108656914232128250000000000:ℝ), (72050224979536033562570137758739612217/1875383509108656914232128250000000:ℝ), (57332017382284416499537589015012123/5001022690956418437952342000000:ℝ)],
  ![(50529153568723059042853439818106621332781/1875383509108656914232128250000000000:ℝ), (69138845243770801414671761056305612217/1875383509108656914232128250000000:ℝ), (161567407067804350960344383569036369/15003068072869255313857026000000:ℝ)]]
theorem cell6_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 6 true b ν := by
 have heq : highBranch cell6 6 true b ν = Record12518109.Bernstein.bsum 1 2 (161567407067804350960344383569036369/673977137659498003812000000000000000:ℝ) cell6_exceptional6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional6_1_g]
theorem cell6_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 6 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional6_0 hb hν) (cell6_exceptional6_1 hb hν)
def cell6_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(1557843946914062516632588062045561307/100065816989496940705500000000000:ℝ), (163164609976847691929944938398165401057/4760823677538758294334750000000000:ℝ), (2420821316201192851836179998241259663241/123781415616007715652703500000000000:ℝ)],
  ![(1474378617168136989171455366817561307/100065816989496940705500000000000:ℝ), (6039412276562121388091621486750450641223/185672123424011573479055250000000000:ℝ), (6921495366749394584269231921723778989723/371344246848023146958110500000000000:ℝ)]]
theorem cell6_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 7 false b ν := by
 have heq : highBranch cell6 7 false b ν = Record12518109.Bernstein.bsum 1 2 (1474378617168136989171455366817561307/4495218750230091000000000000000000000:ℝ) cell6_exceptional7_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional7_0_g]
def cell6_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(58311535737813996720018599355269456195281/3750767018217313828464256500000000000:ℝ), (79411446296010390068358392863976750474153903/2319849400767408602905142645250000000000:ℝ), (30216506165604621359065981985968253896145801/1546566267178272401936761763500000000000:ℝ)],
  ![(55199818350848883960897170226138332195281/3750767018217313828464256500000000000:ℝ), (226150186614752614175080528678872027422461709/6959548202302225808715427935750000000000:ℝ), (259226877624456162691095580274805285065312209/13919096404604451617430855871500000000000:ℝ)]]
theorem cell6_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highBranch cell6 7 true b ν := by
 have heq : highBranch cell6 7 true b ν = Record12518109.Bernstein.bsum 1 2 (55199818350848883960897170226138332195281/168494284414874500953000000000000000000000:ℝ) cell6_exceptional7_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_exceptional7_1_g]
theorem cell6_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
 (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell6 7 b ν :=
 highExceptional_pos_of_branches (cell6_exceptional7_0 hb hν) (cell6_exceptional7_1 hb hν)
def cell6_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(28908305734506382225174999537/13479542753189960076240000000000:ℝ)],
  ![(44045910717625512280383615349/1036887904091535390480000000000:ℝ)]]
theorem cell6_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 0 false b := by
 have heq : domainBranch cell6 0 false b = Record12518109.Bernstein.bsum 1 0 (28908305734506382225174999537/6739771376594980038120000000000000:ℝ) cell6_domain0_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain0_0_g]
def cell6_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(28908305734506382225174999537/13479542753189960076240000000000:ℝ)],
  ![(44045910717625512280383615349/1036887904091535390480000000000:ℝ)]]
theorem cell6_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 0 true b := by
 have heq : domainBranch cell6 0 true b = Record12518109.Bernstein.bsum 1 0 (28908305734506382225174999537/6739771376594980038120000000000000:ℝ) cell6_domain0_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain0_1_g]
def cell6_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(200784712084997510526364788524609/59936250003067880000000000000000:ℝ)],
  ![(102050561027187551505651244524609/59936250003067880000000000000000:ℝ)]]
theorem cell6_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 1 false b := by
 have heq : domainBranch cell6 1 false b = Record12518109.Bernstein.bsum 1 0 (102050561027187551505651244524609/29968125001533940000000000000000000:ℝ) cell6_domain1_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain1_0_g]
def cell6_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(348961173563395047921552041393163/59936250003067880000000000000000:ℝ)],
  ![(250227022505585088900838497393163/59936250003067880000000000000000:ℝ)]]
theorem cell6_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 1 true b := by
 have heq : domainBranch cell6 1 true b = Record12518109.Bernstein.bsum 1 0 (250227022505585088900838497393163/29968125001533940000000000000000000:ℝ) cell6_domain1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain1_1_g]
def cell6_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(39446589943079713774306646147213/5993625000306788000000000000000:ℝ)],
  ![(3677335724305638755964202934401/461048076946676000000000000000:ℝ)]]
theorem cell6_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 2 false b := by
 have heq : domainBranch cell6 2 false b = Record12518109.Bernstein.bsum 1 0 (39446589943079713774306646147213/2996812500153394000000000000000000:ℝ) cell6_domain2_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain2_0_g]
def cell6_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(25338962915904718166752570715791/5993625000306788000000000000000:ℝ)],
  ![(2592133645292177555383120208907/461048076946676000000000000000:ℝ)]]
theorem cell6_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 2 true b := by
 have heq : domainBranch cell6 2 true b = Record12518109.Bernstein.bsum 1 0 (25338962915904718166752570715791/2996812500153394000000000000000000:ℝ) cell6_domain2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain2_1_g]
def cell6_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(9875951039014406260093585321/59936250003067880000000000000:ℝ)],
  ![(29830405963398344322357352717/4610480769466760000000000000:ℝ)]]
theorem cell6_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 3 false b := by
 have heq : domainBranch cell6 3 false b = Record12518109.Bernstein.bsum 1 0 (9875951039014406260093585321/29968125001533940000000000000000:ℝ) cell6_domain3_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain3_0_g]
def cell6_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(9875951039014406260093585321/59936250003067880000000000000:ℝ)],
  ![(29830405963398344322357352717/4610480769466760000000000000:ℝ)]]
theorem cell6_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 3 true b := by
 have heq : domainBranch cell6 3 true b = Record12518109.Bernstein.bsum 1 0 (9875951039014406260093585321/29968125001533940000000000000000:ℝ) cell6_domain3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain3_1_g]
def cell6_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1424921883233858782470561/187300781259587125000000:ℝ)],
  ![(893071055878833106470561/187300781259587125000000:ℝ)]]
theorem cell6_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 4 false b := by
 have heq : domainBranch cell6 4 false b = Record12518109.Bernstein.bsum 1 0 (893071055878833106470561/93650390629793562500000000:ℝ) cell6_domain4_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain4_0_g]
def cell6_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1424921883233858782470561/187300781259587125000000:ℝ)],
  ![(893071055878833106470561/187300781259587125000000:ℝ)]]
theorem cell6_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 4 true b := by
 have heq : domainBranch cell6 4 true b = Record12518109.Bernstein.bsum 1 0 (893071055878833106470561/93650390629793562500000000:ℝ) cell6_domain4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain4_1_g]
def cell6_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(8792699251527266587220027739751/2996812500153394000000000000000:ℝ)],
  ![(3886088445550713977655811739751/2996812500153394000000000000000:ℝ)]]
theorem cell6_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 5 false b := by
 have heq : domainBranch cell6 5 false b = Record12518109.Bernstein.bsum 1 0 (3886088445550713977655811739751/1498406250076697000000000000000000:ℝ) cell6_domain5_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain5_0_g]
def cell6_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(16187413852906054711589661921357/2996812500153394000000000000000:ℝ)],
  ![(11280803046929502102025445921357/2996812500153394000000000000000:ℝ)]]
theorem cell6_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 5 true b := by
 have heq : domainBranch cell6 5 true b = Record12518109.Bernstein.bsum 1 0 (11280803046929502102025445921357/1498406250076697000000000000000000:ℝ) cell6_domain5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain5_1_g]
def cell6_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(254175702582852245511607452308024367/6096089016499532694254000000000000:ℝ)],
  ![(242205234215424546061578472316024367/6096089016499532694254000000000000:ℝ)]]
theorem cell6_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 6 false b := by
 have heq : domainBranch cell6 6 false b = Record12518109.Bernstein.bsum 1 0 (242205234215424546061578472316024367/3048044508249766347127000000000000000:ℝ) cell6_domain6_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain6_0_g]
def cell6_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(248329365266090059865623191820048629/6096089016499532694254000000000000:ℝ)],
  ![(236358896898662360415594211828048629/6096089016499532694254000000000000:ℝ)]]
theorem cell6_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 6 true b := by
 have heq : domainBranch cell6 6 true b = Record12518109.Bernstein.bsum 1 0 (236358896898662360415594211828048629/3048044508249766347127000000000000000:ℝ) cell6_domain6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain6_1_g]
def cell6_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(10455081370576583498989187989/1498406250076697000000000000:ℝ)],
  ![(1586537770283500983473322153/115262019236669000000000000:ℝ)]]
theorem cell6_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 7 false b := by
 have heq : domainBranch cell6 7 false b = Record12518109.Bernstein.bsum 1 0 (10455081370576583498989187989/749203125038348500000000000000:ℝ) cell6_domain7_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain7_0_g]
def cell6_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(10455081370576583498989187989/1498406250076697000000000000:ℝ)],
  ![(1586537770283500983473322153/115262019236669000000000000:ℝ)]]
theorem cell6_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 7 true b := by
 have heq : domainBranch cell6 7 true b = Record12518109.Bernstein.bsum 1 0 (10455081370576583498989187989/749203125038348500000000000000:ℝ) cell6_domain7_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain7_1_g]
def cell6_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(6423806588607310478799158745393/299681250015339400000000000000:ℝ)],
  ![(5816483646880079002588270745393/299681250015339400000000000000:ℝ)]]
theorem cell6_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 8 false b := by
 have heq : domainBranch cell6 8 false b = Record12518109.Bernstein.bsum 1 0 (5816483646880079002588270745393/149840625007669700000000000000000:ℝ) cell6_domain8_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain8_0_g]
def cell6_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(6708501777473776106059420057051/299681250015339400000000000000:ℝ)],
  ![(6101178835746544629848532057051/299681250015339400000000000000:ℝ)]]
theorem cell6_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell6 8 true b := by
 have heq : domainBranch cell6 8 true b = Record12518109.Bernstein.bsum 1 0 (6101178835746544629848532057051/149840625007669700000000000000000:ℝ) cell6_domain8_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_domain8_1_g]
def cell6_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(201067910115597012765527/179808750009203640000000:ℝ)],
  ![(29103963017995300366579/13831442308400280000000:ℝ)]]
theorem cell6_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 0 b := by
 have heq : ordinary cell6 0 b = Record12518109.Bernstein.bsum 1 0 (201067910115597012765527/89904375004601820000000000:ℝ) cell6_ordinary0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary0_g]
def cell6_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(486936394474252733234473/179808750009203640000000:ℝ)],
  ![(309652785355910841234473/179808750009203640000000:ℝ)]]
theorem cell6_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 1 b := by
 have heq : ordinary cell6 1 b = Record12518109.Bernstein.bsum 1 0 (309652785355910841234473/89904375004601820000000000:ℝ) cell6_ordinary1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary1_g]
def cell6_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(14685338860026930454292249/59936250003067880000000:ℝ)],
  ![(14330771641790246670292249/59936250003067880000000:ℝ)]]
theorem cell6_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 2 b := by
 have heq : ordinary cell6 2 b = Record12518109.Bernstein.bsum 1 0 (14330771641790246670292249/29968125001533940000000000:ℝ) cell6_ordinary2_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary2_g]
def cell6_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(339999989/40000000:ℝ)],
  ![(379999989/40000000:ℝ)]]
theorem cell6_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 3 b := by
 have heq : ordinary cell6 3 b = Record12518109.Bernstein.bsum 1 0 (339999989/20000000000:ℝ) cell6_ordinary3_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary3_g]
def cell6_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(13800230321071563038079583/59936250003067880000000:ℝ)],
  ![(13325790602828743494079583/59936250003067880000000:ℝ)]]
theorem cell6_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 4 b := by
 have heq : ordinary cell6 4 b = Record12518109.Bernstein.bsum 1 0 (13325790602828743494079583/29968125001533940000000000:ℝ) cell6_ordinary4_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary4_g]
def cell6_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(9044461542855876697/3659883900144000000000000:ℝ)],
  ![(9044461542855876697/3659883900144000000000000:ℝ)]]
theorem cell6_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < ordinary cell6 5 b := by
 have heq : ordinary cell6 5 b = Record12518109.Bernstein.bsum 1 0 (9044461542855876697/1829941950072000000000000000:ℝ) cell6_ordinary5_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_ordinary5_g]
def cell6_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(201063414896846782674527/179808750009203640000000:ℝ)],
  ![(29103617231937590359579/13831442308400280000000:ℝ)]]
theorem cell6_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 0 false b := by
 have heq : complementBranch cell6 0 false b = Record12518109.Bernstein.bsum 1 0 (201063414896846782674527/89904375004601820000000000:ℝ) cell6_complement0_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement0_0_g]
def cell6_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(4763021679623607126487626538393/4493180917729986692080000000000:ℝ)],
  ![(2135425968556511390841652585783/1036887904091535390480000000000:ℝ)]]
theorem cell6_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 0 true b := by
 have heq : complementBranch cell6 0 true b = Record12518109.Bernstein.bsum 1 0 (4763021679623607126487626538393/2246590458864993346040000000000000:ℝ) cell6_complement0_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement0_1_g]
def cell6_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(106952555300108869531294111033/4495218750230091000000000000:ℝ)],
  ![(32199670659431826029054037011/1498406250076697000000000000:ℝ)]]
theorem cell6_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 1 false b := by
 have heq : complementBranch cell6 1 false b = Record12518109.Bernstein.bsum 1 0 (32199670659431826029054037011/749203125038348500000000000000:ℝ) cell6_complement1_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement1_0_g]
def cell6_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(7995943518680829044697518991029353/336988568829749001906000000000000:ℝ)],
  ![(7224310527797721552341884579029353/336988568829749001906000000000000:ℝ)]]
theorem cell6_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 1 true b := by
 have heq : complementBranch cell6 1 true b = Record12518109.Bernstein.bsum 1 0 (7224310527797721552341884579029353/168494284414874500953000000000000000:ℝ) cell6_complement1_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement1_1_g]
def cell6_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(31903314914822087618247137011/1498406250076697000000000000:ℝ)],
  ![(22542680170272894070203137011/1498406250076697000000000000:ℝ)]]
theorem cell6_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 2 false b := by
 have heq : complementBranch cell6 2 false b = Record12518109.Bernstein.bsum 1 0 (22542680170272894070203137011/749203125038348500000000000000:ℝ) cell6_complement2_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement2_0_g]
def cell6_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(7153129975766525392583069282829353/336988568829749001906000000000000:ℝ)],
  ![(5052472680766856072660234870829353/336988568829749001906000000000000:ℝ)]]
theorem cell6_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 2 true b := by
 have heq : complementBranch cell6 2 true b = Record12518109.Bernstein.bsum 1 0 (5052472680766856072660234870829353/168494284414874500953000000000000000:ℝ) cell6_complement2_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement2_1_g]
def cell6_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(87287114187869066200432286033/4495218750230091000000000000:ℝ)],
  ![(27121887031338074018766762011/1498406250076697000000000000:ℝ)]]
theorem cell6_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 3 false b := by
 have heq : complementBranch cell6 3 false b = Record12518109.Bernstein.bsum 1 0 (27121887031338074018766762011/749203125038348500000000000000:ℝ) cell6_complement3_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement3_0_g]
def cell6_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(2173901353420219982732043806026451/112329522943249667302000000000000:ℝ)],
  ![(6082327145406692912732297006079353/336988568829749001906000000000000:ℝ)]]
theorem cell6_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 3 true b := by
 have heq : complementBranch cell6 3 true b = Record12518109.Bernstein.bsum 1 0 (6082327145406692912732297006079353/168494284414874500953000000000000000:ℝ) cell6_complement3_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement3_1_g]
def cell6_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(28627262622804580121954399511/1498406250076697000000000000:ℝ)],
  ![(25914763220193207523910399511/1498406250076697000000000000:ℝ)]]
theorem cell6_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 4 false b := by
 have heq : complementBranch cell6 4 false b = Record12518109.Bernstein.bsum 1 0 (25914763220193207523910399511/749203125038348500000000000000:ℝ) cell6_complement4_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement4_0_g]
def cell6_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(6416352367396371991681825204554353/336988568829749001906000000000000:ℝ)],
  ![(5810847414527834727772090792554353/336988568829749001906000000000000:ℝ)]]
theorem cell6_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 4 true b := by
 have heq : complementBranch cell6 4 true b = Record12518109.Bernstein.bsum 1 0 (5810847414527834727772090792554353/168494284414874500953000000000000000:ℝ) cell6_complement4_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement4_1_g]
def cell6_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(5303259/200000:ℝ)],
  ![(4403667/200000:ℝ)]]
theorem cell6_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 5 false b := by
 have heq : complementBranch cell6 5 false b = Record12518109.Bernstein.bsum 1 0 (4403667/100000000:ℝ) cell6_complement5_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement5_0_g]
def cell6_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(356553062430811873676383317333179/13479542753189960076240000000000:ℝ)],
  ![(296103847819871769277665450933179/13479542753189960076240000000000:ℝ)]]
theorem cell6_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 5 true b := by
 have heq : complementBranch cell6 5 true b = Record12518109.Bernstein.bsum 1 0 (296103847819871769277665450933179/6739771376594980038120000000000000:ℝ) cell6_complement5_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement5_1_g]
def cell6_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(10451059641461494802550311/179808750009203640000000:ℝ)],
  ![(3070024792544367186183437/59936250003067880000000:ℝ)]]
theorem cell6_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 6 false b := by
 have heq : complementBranch cell6 6 false b = Record12518109.Bernstein.bsum 1 0 (3070024792544367186183437/29968125001533940000000000:ℝ) cell6_complement6_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement6_0_g]
def cell6_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(260866555801305706874855866986393/4493180917729986692080000000000:ℝ)],
  ![(689749195626956001120670204959179/13479542753189960076240000000000:ℝ)]]
theorem cell6_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 6 true b := by
 have heq : complementBranch cell6 6 true b = Record12518109.Bernstein.bsum 1 0 (689749195626956001120670204959179/6739771376594980038120000000000000:ℝ) cell6_complement6_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement6_1_g]
def cell6_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(2752015313544196783652837011/8990437500460182000000000000:ℝ)],
  ![(451947661966211764277602847/691572115420014000000000000:ℝ)]]
theorem cell6_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 7 false b := by
 have heq : complementBranch cell6 7 false b = Record12518109.Bernstein.bsum 1 0 (2752015313544196783652837011/4495218750230091000000000000000:ℝ) cell6_complement7_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement7_0_g]
def cell6_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(6963118078368522064897208584399/28082380735812416825500000000000:ℝ)],
  ![(3945364798039116339763429827169/6480549400572096190500000000000:ℝ)]]
theorem cell6_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 7 true b := by
 have heq : complementBranch cell6 7 true b = Record12518109.Bernstein.bsum 1 0 (6963118078368522064897208584399/14041190367906208412750000000000000:ℝ) cell6_complement7_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement7_1_g]
def cell6_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(42965597336663599336758237011/8990437500460182000000000000:ℝ)],
  ![(6272740265565271837593402847/691572115420014000000000000:ℝ)]]
theorem cell6_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 8 false b := by
 have heq : complementBranch cell6 8 false b = Record12518109.Bernstein.bsum 1 0 (42965597336663599336758237011/4495218750230091000000000000000:ℝ) cell6_complement8_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement8_0_g]
def cell6_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(397720777978251707669204052803197/84247142207437250476500000000000:ℝ)],
  ![(19496852362738336173929154225723/2160183133524032063500000000000:ℝ)]]
theorem cell6_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 8 true b := by
 have heq : complementBranch cell6 8 true b = Record12518109.Bernstein.bsum 1 0 (397720777978251707669204052803197/42123571103718625238250000000000000:ℝ) cell6_complement8_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement8_1_g]
def cell6_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(17672997614147816658344862337/2996812500153394000000000000:ℝ)],
  ![(2575979472155012285307450949/230524038473338000000000000:ℝ)]]
theorem cell6_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 9 false b := by
 have heq : complementBranch cell6 9 false b = Record12518109.Bernstein.bsum 1 0 (17672997614147816658344862337/1498406250076697000000000000000:ℝ) cell6_complement9_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement9_0_g]
def cell6_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(491928633914038243037832159565697/84247142207437250476500000000000:ℝ)],
  ![(72126855160758981567293470889669/6480549400572096190500000000000:ℝ)]]
theorem cell6_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 9 true b := by
 have heq : complementBranch cell6 9 true b = Record12518109.Bernstein.bsum 1 0 (491928633914038243037832159565697/42123571103718625238250000000000000:ℝ) cell6_complement9_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement9_1_g]
def cell6_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(201063414896846782674527/179808750009203640000000:ℝ)],
  ![(29103617231937590359579/13831442308400280000000:ℝ)]]
theorem cell6_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 10 false b := by
 have heq : complementBranch cell6 10 false b = Record12518109.Bernstein.bsum 1 0 (201063414896846782674527/89904375004601820000000000:ℝ) cell6_complement10_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement10_0_g]
def cell6_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(4763021679623607126487626538393/4493180917729986692080000000000:ℝ)],
  ![(2135425968556511390841652585783/1036887904091535390480000000000:ℝ)]]
theorem cell6_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 10 true b := by
 have heq : complementBranch cell6 10 true b = Record12518109.Bernstein.bsum 1 0 (4763021679623607126487626538393/2246590458864993346040000000000000:ℝ) cell6_complement10_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement10_1_g]
def cell6_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(201067160912471974417027/29968125001533940000000:ℝ)],
  ![(29103905386985682032079/2305240384733380000000:ℝ)]]
theorem cell6_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 11 false b := by
 have heq : complementBranch cell6 11 false b = Record12518109.Bernstein.bsum 1 0 (201067160912471974417027/14984062500766970000000000:ℝ) cell6_complement11_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement11_0_g]
def cell6_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(89655349787500049674365365025179/13479542753189960076240000000000:ℝ)],
  ![(13044464426591689827246459155783/1036887904091535390480000000000:ℝ)]]
theorem cell6_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 11 true b := by
 have heq : complementBranch cell6 11 true b = Record12518109.Bernstein.bsum 1 0 (89655349787500049674365365025179/6739771376594980038120000000000000:ℝ) cell6_complement11_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement11_1_g]
def cell6_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(1407470875590428859267689/179808750009203640000000:ℝ)],
  ![(203727395339909392559053/13831442308400280000000:ℝ)]]
theorem cell6_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 12 false b := by
 have heq : complementBranch cell6 12 false b = Record12518109.Bernstein.bsum 1 0 (1407470875590428859267689/89904375004601820000000000:ℝ) cell6_complement12_0_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement12_0_g]
def cell6_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(34909535579075298444448620702393/4493180917729986692080000000000:ℝ)],
  ![(15226272118198725514527420469783/1036887904091535390480000000000:ℝ)]]
theorem cell6_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ))
    (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell6 12 true b := by
 have heq : complementBranch cell6 12 true b = Record12518109.Bernstein.bsum 1 0 (34909535579075298444448620702393/2246590458864993346040000000000000:ℝ) cell6_complement12_1_g (17/500:ℝ) (9/250:ℝ) (1289/2000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell6, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell6_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell6_complement12_1_g]
theorem cell6_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 0 b := complementReserve_pos_of_branches (cell6_complement0_0 hb hν) (cell6_complement0_1 hb hν)
theorem cell6_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 1 b := complementReserve_pos_of_branches (cell6_complement1_0 hb hν) (cell6_complement1_1 hb hν)
theorem cell6_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 2 b := complementReserve_pos_of_branches (cell6_complement2_0 hb hν) (cell6_complement2_1 hb hν)
theorem cell6_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 3 b := complementReserve_pos_of_branches (cell6_complement3_0 hb hν) (cell6_complement3_1 hb hν)
theorem cell6_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 4 b := complementReserve_pos_of_branches (cell6_complement4_0 hb hν) (cell6_complement4_1 hb hν)
theorem cell6_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 5 b := complementReserve_pos_of_branches (cell6_complement5_0 hb hν) (cell6_complement5_1 hb hν)
theorem cell6_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 6 b := complementReserve_pos_of_branches (cell6_complement6_0 hb hν) (cell6_complement6_1 hb hν)
theorem cell6_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 7 b := complementReserve_pos_of_branches (cell6_complement7_0 hb hν) (cell6_complement7_1 hb hν)
theorem cell6_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 8 b := complementReserve_pos_of_branches (cell6_complement8_0 hb hν) (cell6_complement8_1 hb hν)
theorem cell6_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 9 b := complementReserve_pos_of_branches (cell6_complement9_0 hb hν) (cell6_complement9_1 hb hν)
theorem cell6_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 10 b := complementReserve_pos_of_branches (cell6_complement10_0 hb hν) (cell6_complement10_1 hb hν)
theorem cell6_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 11 b := complementReserve_pos_of_branches (cell6_complement11_0 hb hν) (cell6_complement11_1 hb hν)
theorem cell6_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (hν : ν ∈ Set.Icc (1289/2000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell6 12 b := complementReserve_pos_of_branches (cell6_complement12_0 hb hν) (cell6_complement12_1 hb hν)
theorem cell6_all_domains {b : ℝ} (hb : b ∈ Set.Icc (17/500:ℝ) (9/250:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell6 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell6_domain0_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain0_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain1_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain1_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain2_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain2_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain3_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain3_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain4_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain4_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain5_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain5_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain6_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain6_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain7_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain7_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell6_domain8_0 (ν := (1289/2000:ℝ)) hb (by norm_num)
   | true => exact cell6_domain8_1 (ν := (1289/2000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
