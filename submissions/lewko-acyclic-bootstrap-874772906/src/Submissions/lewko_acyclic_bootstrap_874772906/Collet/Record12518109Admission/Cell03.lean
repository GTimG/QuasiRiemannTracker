/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell3 : Cell := ⟨(306003/312500:ℝ), (74001/20000:ℝ), (1589/2500:ℝ), (9/250:ℝ), (3/80:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (481/100000:ℝ), (1/25:ℝ)⟩
def cell3_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(210435932527027377065262583019021650685479/5573535513794212831855560000000000:ℝ), (271882861633482342885576148141726052633135197/79422881071567532853941730000000000:ℝ), (522981796920117660934541777774847957846083947/52948587381045021902627820000000000:ℝ), (252265916342359803508356327774821131605725899/26474293690522510951313910000000000:ℝ), (967280032841572697814210242940536310344521447/317691524286270131415766920000000000:ℝ)],
  ![(284277622686909054112032297601327213685479/5573535513794212831855560000000000:ℝ), (270510196565133480070474365979647741383135197/79422881071567532853941730000000000:ℝ), (516522946323245415963767053645538973471083947/52948587381045021902627820000000000:ℝ), (248603877681206913531374558843180506605725899/26474293690522510951313910000000000:ℝ), (952362046855194670515655718862167169719521447/317691524286270131415766920000000000:ℝ)]]
theorem cell3_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell3 2 b ν := by
 have heq : highRegular cell3 2 b ν = Record12518109.Bernstein.bsum 1 4 (210435932527027377065262583019021650685479/21693789204035742187500000000000000000000:ℝ) cell3_regular2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_regular2_g]
def cell3_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(185087521948772585324352622249388391178303/317691524286270131415766920000000000:ℝ), (85274928375824768712190067385355281126676399/26474293690522510951313910000000000:ℝ), (26614040634459512935211216422785009040288313/2786767756897106415927780000000000:ℝ), (741415854320473030962256330575551097799071697/79422881071567532853941730000000000:ℝ), (35433612966500452569305630128675636199589461/11766352751343338200583960000000000:ℝ)],
  ![(26041447101785607014985896986765482178303/317691524286270131415766920000000000:ℝ), (83623031463293172574229950005104177376676399/26474293690522510951313910000000000:ℝ), (496374099669934943691217705731731187390477947/52948587381045021902627820000000000:ℝ), (728284066633185375990728767921254222799071697/79422881071567532853941730000000000:ℝ), (104473043441443392640217933934610892973768383/35299058254030014601751880000000000:ℝ)]]
theorem cell3_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell3 3 b ν := by
 have heq : highRegular cell3 3 b ν = Record12518109.Bernstein.bsum 1 4 (26041447101785607014985896986765482178303/1236545984630037304687500000000000000000000:ℝ) cell3_regular3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_regular3_g]
def cell3_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(8835488943526679312741195394249692680194331/24437809560482317801212840000000000:ℝ), (842677664510246146306601179091898754269747/226276014448910350011230000000000:ℝ), (4129569651651228393841708918562179997342991/452552028897820700022460000000000:ℝ), (3982242590312342015666401274708398343773513/469957876163121496177170000000000:ℝ), (22101592367545700720239418217648093181091473/8145936520160772600404280000000000:ℝ)],
  ![(104818826943844306201288845739642761933526303/317691524286270131415766920000000000:ℝ), (31418599086390189177187573169775350166520133/8824764563507503650437970000000000:ℝ), (2734248530557452522562618560345196346866257/309640861877456268436420000000000:ℝ), (655151838603868127364554076990172445097723697/79422881071567532853941730000000000:ℝ), (280729113644427888051565250092364664479189149/105897174762090043805255640000000000:ℝ)]]
theorem cell3_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highRegular cell3 4 b ν := by
 have heq : highRegular cell3 4 b ν = Record12518109.Bernstein.bsum 1 4 (104818826943844306201288845739642761933526303/1236545984630037304687500000000000000000000:ℝ) cell3_regular4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_regular4_g]
def cell3_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(1990816539606734851487415542350192153/98393384541039211320840000000000:ℝ), (8152006613729452769801517355841377291/147590076811558816981260000000000:ℝ), (10474704065006361205503626290475642291/295180153623117633962520000000000:ℝ)],
  ![(1946406612436726967097510424891192153/98393384541039211320840000000000:ℝ), (8003198992853855982151480550216377291/147590076811558816981260000000000:ℝ), (10309487542268076046025043087350642291/295180153623117633962520000000000:ℝ)]]
theorem cell3_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 0 false b ν := by
 have heq : highBranch cell3 0 false b ν = Record12518109.Bernstein.bsum 1 2 (1946406612436726967097510424891192153/5012133057700417875000000000000000000:ℝ) cell3_exceptional0_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional0_0_g]
def cell3_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(74541404975629439492403149459100271245899/3688079232751772757939045720000000000:ℝ), (305335005399340530605102090864681579373553/5532118849127659136908568580000000000:ℝ), (392411129597821750772854997821692912418553/11064237698255318273817137160000000000:ℝ)],
  ![(72880472851984025890133901153999574245899/3688079232751772757939045720000000000:ℝ), (299767965690588998474164201290549704373553/5532118849127659136908568580000000000:ℝ), (386228695835675556876263448003333537418553/11064237698255318273817137160000000000:ℝ)]]
theorem cell3_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 0 true b ν := by
 have heq : highBranch cell3 0 true b ν = Record12518109.Bernstein.bsum 1 2 (72880472851984025890133901153999574245899/187869783401784763208625000000000000000000:ℝ) cell3_exceptional0_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional0_1_g]
theorem cell3_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 0 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional0_0 hb hν) (cell3_exceptional0_1 hb hν)
def cell3_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(7769191702936624797563869794536251/1412345232646495856280000000000:ℝ), (4995622189155592645487025111963409/64197510574840720740000000000:ℝ), (3808125149068105727737255162784537/52309082690610957640000000000:ℝ)],
  ![(81689338353469690871356529456898761/15535797559111454419080000000000:ℝ), (596996336748668099969426456672572489/7767898779555727209540000000000:ℝ), (124421478138035138335070435996889721/1726199728790161602120000000000:ℝ)]]
theorem cell3_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 1 false b ν := by
 have heq : highBranch cell3 1 false b ν = Record12518109.Bernstein.bsum 1 2 (81689338353469690871356529456898761/791389430163223875000000000000000000:ℝ) cell3_exceptional1_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional1_0_g]
def cell3_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(3190648520962939693963270691624312433563/582328299908174645990375640000000000:ℝ), (22645430293551432387174652572545987730187/291164149954087322995187820000000000:ℝ), (4709177561302266576416344556055650087243/64703144434241627332263960000000000:ℝ)],
  ![(3049853121821765841207570145917623433563/582328299908174645990375640000000000:ℝ), (22365848313584427164584551655815362730187/291164149954087322995187820000000000:ℝ), (1554169999243751108907613799284175029081/21567714811413875777421320000000000:ℝ)]]
theorem cell3_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 1 true b ν := by
 have heq : highBranch cell3 1 true b ν = Record12518109.Bernstein.bsum 1 2 (3049853121821765841207570145917623433563/29663650010808120506625000000000000000000:ℝ) cell3_exceptional1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional1_1_g]
theorem cell3_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 1 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional1_0 hb hν) (cell3_exceptional1_1 hb hν)
def cell3_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(56257936859444852988231244139296933/1726199728790161602120000000000:ℝ), (547443338343284909401144453544029/12428638047289163535264000000:ℝ), (500498643173680893131054124389/39771641751325323312844800:ℝ)],
  ![(55419533971134279843121056552296933/1726199728790161602120000000000:ℝ), (537239643099709288366313722544029/12428638047289163535264000000:ℝ), (486869306814790528557887124389/39771641751325323312844800:ℝ)]]
theorem cell3_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 2 false b ν := by
 have heq : highBranch cell3 2 false b ν = Record12518109.Bernstein.bsum 1 2 (486869306814790528557887124389/2025956941217853120000000000000:ℝ) cell3_exceptional2_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional2_0_g]
def cell3_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(110906508989226518009778584407113734981/3405428654433769859592840000000000:ℝ), (1078923308727278073189217050923280973/24519086311923142989068448000000:ℝ), (985773531149300970311709351904613/78461076198154057565019033600:ℝ)],
  ![(3310785434691380110820458264922870757/103194807710114238169480000000000:ℝ), (96258278401991681938167266152025543/2229007846538467544460768000000:ℝ), (7925283541895646525409945594253/648438646265736012934041600:ℝ)]]
theorem cell3_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 2 true b ν := by
 have heq : highBranch cell3 2 true b ν = Record12518109.Bernstein.bsum 1 2 (958959308569373229574603416904613/3996786527772041499840000000000000:ℝ) cell3_exceptional2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional2_1_g]
theorem cell3_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 2 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional2_0 hb hν) (cell3_exceptional2_1 hb hν)
def cell3_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(563052087792988404315092247450064051/32797794847013070440280000000000:ℝ), (7084641331565979119317433755841377291/147590076811558816981260000000000:ℝ), (9252825800126005957067542690475642291/295180153623117633962520000000000:ℝ)],
  ![(548248778736319109518457208297064051/32797794847013070440280000000000:ℝ), (6935833710690382331667396950216377291/147590076811558816981260000000000:ℝ), (9087609277387720797588959487350642291/295180153623117633962520000000000:ℝ)]]
theorem cell3_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 3 false b ν := by
 have heq : highBranch cell3 3 false b ν = Record12518109.Bernstein.bsum 1 2 (548248778736319109518457208297064051/1670711019233472625000000000000000000:ℝ) cell3_exceptional3_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional3_0_g]
def cell3_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(63234272841783950130928160818700271245899/3688079232751772757939045720000000000:ℝ), (265326952528007047764007185285881579373553/5532118849127659136908568580000000000:ℝ), (346611466595311394995725276242892912418553/11064237698255318273817137160000000000:ℝ)],
  ![(61573340718138536528658912513599574245899/3688079232751772757939045720000000000:ℝ), (259759912819255515633069295711749704373553/5532118849127659136908568580000000000:ℝ), (340429032833165201099133726424533537418553/11064237698255318273817137160000000000:ℝ)]]
theorem cell3_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 3 true b ν := by
 have heq : highBranch cell3 3 true b ν = Record12518109.Bernstein.bsum 1 2 (61573340718138536528658912513599574245899/187869783401784763208625000000000000000000:ℝ) cell3_exceptional3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional3_1_g]
theorem cell3_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 3 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional3_0 hb hν) (cell3_exceptional3_1 hb hν)
def cell3_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(47254209759634805272956967739898761/15535797559111454419080000000000:ℝ), (540951986507313980711675638547572489/7767898779555727209540000000000:ℝ), (38614731830362209208822606790629907/575399909596720534040000000000:ℝ)],
  ![(43482439380801623371110929456898761/15535797559111454419080000000000:ℝ), (533478038368155370577172056672572489/7767898779555727209540000000000:ℝ), (114597543709874276946208835996889721/1726199728790161602120000000000:ℝ)]]
theorem cell3_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 4 false b ν := by
 have heq : highBranch cell3 4 false b ν = Record12518109.Bernstein.bsum 1 2 (43482439380801623371110929456898761/791389430163223875000000000000000000:ℝ) cell3_exceptional4_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional4_0_g]
def cell3_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(1758539326770422519851564866824312433563/582328299908174645990375640000000000:ℝ), (20264573915354673751364780897345987730187/291164149954087322995187820000000000:ℝ), (4340947027131513008977645203255650087243/64703144434241627332263960000000000:ℝ)],
  ![(1617743927629248667095864321117623433563/582328299908174645990375640000000000:ℝ), (19984991935387668528774679980615362730187/291164149954087322995187820000000000:ℝ), (1431426487853499919761380681684175029081/21567714811413875777421320000000000:ℝ)]]
theorem cell3_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 4 true b ν := by
 have heq : highBranch cell3 4 true b ν = Record12518109.Bernstein.bsum 1 2 (1617743927629248667095864321117623433563/29663650010808120506625000000000000000000:ℝ) cell3_exceptional4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional4_1_g]
theorem cell3_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 4 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional4_0 hb hν) (cell3_exceptional4_1 hb hν)
def cell3_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(297199087664581056040336700909898761/15535797559111454419080000000000:ℝ), (1545333991114072735056848801832550467229/36206176211509244523665940000000000:ℝ), (1787104921602402322391084107481721906229/72412352423018489047331880000000000:ℝ)],
  ![(290429657000647849717428162626898761/15535797559111454419080000000000:ℝ), (1512630704745174234882295950288175467229/36206176211509244523665940000000000:ℝ), (1752714806540032417592255940684846906229/72412352423018489047331880000000000:ℝ)]]
theorem cell3_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 5 false b ν := by
 have heq : highBranch cell3 5 false b ν = Record12518109.Bernstein.bsum 1 2 (290429657000647849717428162626898761/791389430163223875000000000000000000:ℝ) cell3_exceptional5_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional5_0_g]
def cell3_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(11127223185281522837365259405235422433563/582328299908174645990375640000000000:ℝ), (57868151079304660317494752771556905553769607/1357116102936001012480570429020000000000:ℝ), (20142641306542610655268189205232874832909/816801747177851948528781480000000000:ℝ)],
  ![(10874066485673944769234873172028733433563/582328299908174645990375640000000000:ℝ), (56644962684857509551052845020897187428769607/1357116102936001012480570429020000000000:ℝ), (3455131476835317981470694343272747497092453/142854326624842211840060045160000000000:ℝ)]]
theorem cell3_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 5 true b ν := by
 have heq : highBranch cell3 5 true b ν = Record12518109.Bernstein.bsum 1 2 (10874066485673944769234873172028733433563/29663650010808120506625000000000000000000:ℝ) cell3_exceptional5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional5_1_g]
theorem cell3_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 5 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional5_0 hb hν) (cell3_exceptional5_1 hb hν)
def cell3_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(56257936859444852988231244139296933/1726199728790161602120000000000:ℝ), (547443338343284909401144453544029/12428638047289163535264000000:ℝ), (500498643173680893131054124389/39771641751325323312844800:ℝ)],
  ![(55419533971134279843121056552296933/1726199728790161602120000000000:ℝ), (537239643099709288366313722544029/12428638047289163535264000000:ℝ), (486869306814790528557887124389/39771641751325323312844800:ℝ)]]
theorem cell3_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 6 false b ν := by
 have heq : highBranch cell3 6 false b ν = Record12518109.Bernstein.bsum 1 2 (486869306814790528557887124389/2025956941217853120000000000000:ℝ) cell3_exceptional6_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional6_0_g]
def cell3_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(110906508989226518009778584407113734981/3405428654433769859592840000000000:ℝ), (1078923308727278073189217050923280973/24519086311923142989068448000000:ℝ), (985773531149300970311709351904613/78461076198154057565019033600:ℝ)],
  ![(3310785434691380110820458264922870757/103194807710114238169480000000000:ℝ), (96258278401991681938167266152025543/2229007846538467544460768000000:ℝ), (7925283541895646525409945594253/648438646265736012934041600:ℝ)]]
theorem cell3_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 6 true b ν := by
 have heq : highBranch cell3 6 true b ν = Record12518109.Bernstein.bsum 1 2 (958959308569373229574603416904613/3996786527772041499840000000000000:ℝ) cell3_exceptional6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional6_1_g]
theorem cell3_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 6 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional6_0 hb hν) (cell3_exceptional6_1 hb hν)
def cell3_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(250274242729234914333091100909898761/15535797559111454419080000000000:ℝ), (1302314898350819693712649301832550467229/36206176211509244523665940000000000:ℝ), (1519783438319544606200156849081721906229/72412352423018489047331880000000000:ℝ)],
  ![(243504812065301708010182562626898761/15535797559111454419080000000000:ℝ), (1269611611981921193538096450288175467229/36206176211509244523665940000000000:ℝ), (1485393323257174701401328682284846906229/72412352423018489047331880000000000:ℝ)]]
theorem cell3_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 7 false b ν := by
 have heq : highBranch cell3 7 false b ν = Record12518109.Bernstein.bsum 1 2 (243504812065301708010182562626898761/791389430163223875000000000000000000:ℝ) cell3_exceptional7_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional7_0_g]
def cell3_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(9368339222569943407752572580435422433563/582328299908174645990375640000000000:ℝ), (48759066425259646568790122913056905553769607/1357116102936001012480570429020000000000:ℝ), (17127290371275877048291202618832874832909/816801747177851948528781480000000000:ℝ)],
  ![(9115182522962365339622186347228733433563/582328299908174645990375640000000000:ℝ), (47535878030812495802348215162397187428769607/1357116102936001012480570429020000000000:ℝ), (2927762468525246624839929794503947497092453/142854326624842211840060045160000000000:ℝ)]]
theorem cell3_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highBranch cell3 7 true b ν := by
 have heq : highBranch cell3 7 true b ν = Record12518109.Bernstein.bsum 1 2 (9115182522962365339622186347228733433563/29663650010808120506625000000000000000000:ℝ) cell3_exceptional7_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_exceptional7_1_g]
theorem cell3_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
 (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < highExceptional cell3 7 b ν :=
 highExceptional_pos_of_branches (cell3_exceptional7_0 hb hν) (cell3_exceptional7_1 hb hν)
def cell3_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(1121386283361749591340443267/474618400172929928106000000000:ℝ)],
  ![(6114906717863397059218643267/474618400172929928106000000000:ℝ)]]
theorem cell3_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 0 false b := by
 have heq : domainBranch cell3 0 false b = Record12518109.Bernstein.bsum 1 0 (1121386283361749591340443267/316412266781953285404000000000000:ℝ) cell3_domain0_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain0_0_g]
def cell3_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(1121386283361749591340443267/474618400172929928106000000000:ℝ)],
  ![(6114906717863397059218643267/474618400172929928106000000000:ℝ)]]
theorem cell3_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 0 true b := by
 have heq : domainBranch cell3 0 true b = Record12518109.Bernstein.bsum 1 0 (1121386283361749591340443267/316412266781953285404000000000000:ℝ) cell3_domain0_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain0_1_g]
def cell3_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(54065138839890449298865446441887/15827788603264477500000000000000:ℝ)],
  ![(47937218826684601194318527691887/15827788603264477500000000000000:ℝ)]]
theorem cell3_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 1 false b := by
 have heq : domainBranch cell3 1 false b = Record12518109.Bernstein.bsum 1 0 (47937218826684601194318527691887/10551859068842985000000000000000000:ℝ) cell3_domain1_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain1_0_g]
def cell3_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(209937076759013406154684209925951/31655577206528955000000000000000:ℝ)],
  ![(197681236732601709945590372425951/31655577206528955000000000000000:ℝ)]]
theorem cell3_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 1 true b := by
 have heq : domainBranch cell3 1 true b = Record12518109.Bernstein.bsum 1 0 (197681236732601709945590372425951/21103718137685970000000000000000000:ℝ) cell3_domain1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain1_1_g]
def cell3_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(13994237500194877725338667795559/1582778860326447750000000000000:ℝ)],
  ![(14297046240723484856492424045559/1582778860326447750000000000000:ℝ)]]
theorem cell3_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 2 false b := by
 have heq : domainBranch cell3 2 false b = Record12518109.Bernstein.bsum 1 0 (13994237500194877725338667795559/1055185906884298500000000000000000:ℝ) cell3_domain2_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain2_0_g]
def cell3_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(18295624085268230362069384875707/3165557720652895500000000000000:ℝ)],
  ![(18901241566325444624376897375707/3165557720652895500000000000000:ℝ)]]
theorem cell3_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 2 true b := by
 have heq : domainBranch cell3 2 true b = Record12518109.Bernstein.bsum 1 0 (18295624085268230362069384875707/2110371813768597000000000000000000:ℝ) cell3_domain2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain2_1_g]
def cell3_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(668221176132336069009812957/185120334541105000000000000:ℝ)],
  ![(1577628813773798082132312957/185120334541105000000000000:ℝ)]]
theorem cell3_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 3 false b := by
 have heq : domainBranch cell3 3 false b = Record12518109.Bernstein.bsum 1 0 (2004663528397008207029438871/370240669082210000000000000000:ℝ) cell3_domain3_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain3_0_g]
def cell3_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(668221176132336069009812957/185120334541105000000000000:ℝ)],
  ![(1577628813773798082132312957/185120334541105000000000000:ℝ)]]
theorem cell3_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 3 true b := by
 have heq : domainBranch cell3 3 true b = Record12518109.Bernstein.bsum 1 0 (2004663528397008207029438871/370240669082210000000000000000:ℝ) cell3_domain3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain3_1_g]
def cell3_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1055761776321803150665253/131898238360537312500000:ℝ)],
  ![(765501763240222475665253/131898238360537312500000:ℝ)]]
theorem cell3_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 4 false b := by
 have heq : domainBranch cell3 4 false b = Record12518109.Bernstein.bsum 1 0 (765501763240222475665253/87932158907024875000000000:ℝ) cell3_domain4_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain4_0_g]
def cell3_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1055761776321803150665253/131898238360537312500000:ℝ)],
  ![(765501763240222475665253/131898238360537312500000:ℝ)]]
theorem cell3_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 4 true b := by
 have heq : domainBranch cell3 4 true b = Record12518109.Bernstein.bsum 1 0 (765501763240222475665253/87932158907024875000000000:ℝ) cell3_domain4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain4_1_g]
def cell3_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(2270335621491470475447299751343/791389430163223875000000000000:ℝ)],
  ![(1970099159632029186848718501343/791389430163223875000000000000:ℝ)]]
theorem cell3_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 5 false b := by
 have heq : domainBranch cell3 5 false b = Record12518109.Bernstein.bsum 1 0 (1970099159632029186848718501343/527592953442149250000000000000000:ℝ) cell3_domain5_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain5_0_g]
def cell3_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(9621317765106778160214086101589/1582778860326447750000000000000:ℝ)],
  ![(9020844841387895583016923601589/1582778860326447750000000000000:ℝ)]]
theorem cell3_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 5 true b := by
 have heq : domainBranch cell3 5 true b = Record12518109.Bernstein.bsum 1 0 (9020844841387895583016923601589/1055185906884298500000000000000000:ℝ) cell3_domain5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain5_1_g]
def cell3_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(14474524522777075317576605437260931/268306209388859756251687500000000:ℝ)],
  ![(13802357903740119928648665852885931/268306209388859756251687500000000:ℝ)]]
theorem cell3_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 6 false b := by
 have heq : domainBranch cell3 6 false b = Record12518109.Bernstein.bsum 1 0 (13802357903740119928648665852885931/178870806259239837501125000000000000:ℝ) cell3_domain6_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain6_0_g]
def cell3_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(56559160982792573838501466081359001/1073224837555439025006750000000000:ℝ)],
  ![(53870494506644752282789707743859001/1073224837555439025006750000000000:ℝ)]]
theorem cell3_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 6 true b := by
 have heq : domainBranch cell3 6 true b = Record12518109.Bernstein.bsum 1 0 (53870494506644752282789707743859001/715483225036959350004500000000000000:ℝ) cell3_domain6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain6_1_g]
def cell3_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(1624875124388680555912496597/126622308826115820000000000:ℝ)],
  ![(2306428356987287979848696597/126622308826115820000000000:ℝ)]]
theorem cell3_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 7 false b := by
 have heq : domainBranch cell3 7 false b = Record12518109.Bernstein.bsum 1 0 (1624875124388680555912496597/84414872550743880000000000000:ℝ) cell3_domain7_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain7_0_g]
def cell3_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(1624875124388680555912496597/126622308826115820000000000:ℝ)],
  ![(2306428356987287979848696597/126622308826115820000000000:ℝ)]]
theorem cell3_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 7 true b := by
 have heq : domainBranch cell3 7 true b = Record12518109.Bernstein.bsum 1 0 (1624875124388680555912496597/84414872550743880000000000000:ℝ) cell3_domain7_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain7_1_g]
def cell3_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(2141017008667528582480641211799/79138943016322387500000000000:ℝ)],
  ![(2016723534860809324921022461799/79138943016322387500000000000:ℝ)]]
theorem cell3_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 8 false b := by
 have heq : domainBranch cell3 8 false b = Record12518109.Bernstein.bsum 1 0 (2016723534860809324921022461799/52759295344214925000000000000000:ℝ) cell3_domain8_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain8_0_g]
def cell3_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(4477637999253453464112544437727/158277886032644775000000000000:ℝ)],
  ![(4229051051640014948993306937727/158277886032644775000000000000:ℝ)]]
theorem cell3_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < domainBranch cell3 8 true b := by
 have heq : domainBranch cell3 8 true b = Record12518109.Bernstein.bsum 1 0 (4229051051640014948993306937727/105518590688429850000000000000000:ℝ) cell3_domain8_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_domain8_1_g]
def cell3_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(29860083293841952889671/15194677059133898400000:ℝ)],
  ![(41470483817105179889671/15194677059133898400000:ℝ)]]
theorem cell3_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 0 b := by
 have heq : ordinary cell3 0 b = Record12518109.Bernstein.bsum 1 0 (29860083293841952889671/10129784706089265600000000:ℝ) cell3_ordinary0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary0_g]
def cell3_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(43477015008384764610329/15194677059133898400000:ℝ)],
  ![(31866614485121537610329/15194677059133898400000:ℝ)]]
theorem cell3_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 1 b := by
 have heq : ordinary cell3 1 b = Record12518109.Bernstein.bsum 1 0 (31866614485121537610329/10129784706089265600000000:ℝ) cell3_ordinary1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary1_g]
def cell3_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(5100209293882017546447407/15827788603264477500000:ℝ)],
  ![(5027644290611622377697407/15827788603264477500000:ℝ)]]
theorem cell3_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 2 b := by
 have heq : ordinary cell3 2 b = Record12518109.Bernstein.bsum 1 0 (5027644290611622377697407/10551859068842985000000000:ℝ) cell3_ordinary2_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary2_g]
def cell3_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(359999989/30000000:ℝ)],
  ![(389999989/30000000:ℝ)]]
theorem cell3_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 3 b := by
 have heq : ordinary cell3 3 b = Record12518109.Bernstein.bsum 1 0 (359999989/20000000000:ℝ) cell3_ordinary3_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary3_g]
def cell3_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(9523094777349093837199381/31655577206528955000000:ℝ)],
  ![(9314653616395245589699381/31655577206528955000000:ℝ)]]
theorem cell3_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 4 b := by
 have heq : ordinary cell3 4 b = Record12518109.Bernstein.bsum 1 0 (9314653616395245589699381/21103718137685970000000000:ℝ) cell3_ordinary4_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary4_g]
def cell3_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(11305814292571018597/3431141156385000000000000:ℝ)],
  ![(11305814292571018597/3431141156385000000000000:ℝ)]]
theorem cell3_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < ordinary cell3 5 b := by
 have heq : ordinary cell3 5 b = Record12518109.Bernstein.bsum 1 0 (11305814292571018597/2287427437590000000000000000:ℝ) cell3_ordinary5_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_ordinary5_g]
def cell3_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(29859576804606648426391/15194677059133898400000:ℝ)],
  ![(41469977327869875426391/15194677059133898400000:ℝ)]]
theorem cell3_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 0 false b := by
 have heq : complementBranch cell3 0 false b = Record12518109.Bernstein.bsum 1 0 (29859576804606648426391/10129784706089265600000000:ℝ) cell3_complement0_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement0_0_g]
def cell3_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(2691657517055062326475602095767/1423855200518789784318000000000:ℝ)],
  ![(3784632644523252818045980295767/1423855200518789784318000000000:ℝ)]]
theorem cell3_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 0 true b := by
 have heq : complementBranch cell3 0 true b = Record12518109.Bernstein.bsum 1 0 (2691657517055062326475602095767/949236800345859856212000000000000:ℝ) cell3_complement0_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement0_1_g]
def cell3_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(11420741430287843219556785209/379866926478347460000000000:ℝ)],
  ![(10995101059717801903929785209/379866926478347460000000000:ℝ)]]
theorem cell3_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 1 false b := by
 have heq : complementBranch cell3 1 false b = Record12518109.Bernstein.bsum 1 0 (10995101059717801903929785209/253244617652231640000000000000:ℝ) cell3_complement1_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement1_0_g]
def cell3_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(426994595665680567351903263621617/14238552005187897843180000000000:ℝ)],
  ![(411090252859948725192935204621617/14238552005187897843180000000000:ℝ)]]
theorem cell3_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 1 true b := by
 have heq : complementBranch cell3 1 true b = Record12518109.Bernstein.bsum 1 0 (411090252859948725192935204621617/9492368003458598562120000000000000:ℝ) cell3_complement1_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement1_1_g]
def cell3_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(1001694791896312142287742801/42207436275371940000000000:ℝ)],
  ![(825396967130049473884742801/42207436275371940000000000:ℝ)]]
theorem cell3_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 2 false b := by
 have heq : complementBranch cell3 2 false b = Record12518109.Bernstein.bsum 1 0 (825396967130049473884742801/28138290850247960000000000000:ℝ) cell3_complement2_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement2_0_g]
def cell3_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(112276559198682184072533151440539/4746184001729299281060000000000:ℝ)],
  ![(92468690169655718764843798440539/4746184001729299281060000000000:ℝ)]]
theorem cell3_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 2 true b := by
 have heq : complementBranch cell3 2 true b = Record12518109.Bernstein.bsum 1 0 (92468690169655718764843798440539/3164122667819532854040000000000000:ℝ) cell3_complement2_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement2_1_g]
def cell3_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(9489667329570785304298560209/379866926478347460000000000:ℝ)],
  ![(9354286972082324663671560209/379866926478347460000000000:ℝ)]]
theorem cell3_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 3 false b := by
 have heq : complementBranch cell3 3 false b = Record12518109.Bernstein.bsum 1 0 (9354286972082324663671560209/253244617652231640000000000000:ℝ) cell3_complement3_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement3_0_g]
def cell3_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(18663797113079109763909432418243/749397473957257781220000000000:ℝ)],
  ![(18399348337532006936649271418243/749397473957257781220000000000:ℝ)]]
theorem cell3_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 3 true b := by
 have heq : complementBranch cell3 3 true b = Record12518109.Bernstein.bsum 1 0 (18399348337532006936649271418243/499598315971505187480000000000000:ℝ) cell3_complement3_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement3_1_g]
def cell3_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(1020997921296461784658630301/42207436275371940000000000:ℝ)],
  ![(989830103070989453755630301/42207436275371940000000000:ℝ)]]
theorem cell3_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 4 false b := by
 have heq : complementBranch cell3 4 false b = Record12518109.Bernstein.bsum 1 0 (989830103070989453755630301/28138290850247960000000000000:ℝ) cell3_complement4_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement4_0_g]
def cell3_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(114447176796599611207497079928039/4746184001729299281060000000000:ℝ)],
  ![(110959031873078478561345226928039/4746184001729299281060000000000:ℝ)]]
theorem cell3_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 4 true b := by
 have heq : complementBranch cell3 4 true b = Record12518109.Bernstein.bsum 1 0 (110959031873078478561345226928039/3164122667819532854040000000000000:ℝ) cell3_complement4_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement4_1_g]
def cell3_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(790169/25000:ℝ)],
  ![(16943/625:ℝ)]]
theorem cell3_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 5 false b := by
 have heq : complementBranch cell3 5 false b = Record12518109.Bernstein.bsum 1 0 (50829/1250000:ℝ) cell3_complement5_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement5_0_g]
def cell3_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(14964848020323132732905472681089/474618400172929928106000000000:ℝ)],
  ![(12831697947892801382637768321089/474618400172929928106000000000:ℝ)]]
theorem cell3_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 5 true b := by
 have heq : complementBranch cell3 5 true b = Record12518109.Bernstein.bsum 1 0 (12831697947892801382637768321089/316412266781953285404000000000000:ℝ) cell3_complement5_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement5_1_g]
def cell3_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(1097838400546450519809023/15194677059133898400000:ℝ)],
  ![(1016565596883607930809023/15194677059133898400000:ℝ)]]
theorem cell3_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 6 false b := by
 have heq : complementBranch cell3 6 false b = Record12518109.Bernstein.bsum 1 0 (1016565596883607930809023/10129784706089265600000000:ℝ) cell3_complement6_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement6_0_g]
def cell3_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(102766786382626646080329651135767/1423855200518789784318000000000:ℝ)],
  ![(95155908653825325819080029335767/1423855200518789784318000000000:ℝ)]]
theorem cell3_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 6 true b := by
 have heq : complementBranch cell3 6 true b = Record12518109.Bernstein.bsum 1 0 (95155908653825325819080029335767/949236800345859856212000000000000:ℝ) cell3_complement6_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement6_1_g]
def cell3_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(408487893508735587255828403/759733852956694920000000000:ℝ)],
  ![(597456390644864912046828403/759733852956694920000000000:ℝ)]]
theorem cell3_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 7 false b := by
 have heq : complementBranch cell3 7 false b = Record12518109.Bernstein.bsum 1 0 (408487893508735587255828403/506489235304463280000000000000:ℝ) cell3_complement7_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement7_0_g]
def cell3_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(13183176185135632398301565294989/28477104010375795686360000000000:ℝ)],
  ![(20366152771979200828800182294989/28477104010375795686360000000000:ℝ)]]
theorem cell3_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 7 true b := by
 have heq : complementBranch cell3 7 true b = Record12518109.Bernstein.bsum 1 0 (13183176185135632398301565294989/18984736006917197124240000000000000:ℝ) cell3_complement7_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement7_1_g]
def cell3_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(2126834850759042055063342801/253244617652231640000000000:ℝ)],
  ![(2963851051355300296660342801/253244617652231640000000000:ℝ)]]
theorem cell3_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 8 false b := by
 have heq : complementBranch cell3 8 false b = Record12518109.Bernstein.bsum 1 0 (2126834850759042055063342801/168829745101487760000000000000:ℝ) cell3_complement8_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement8_0_g]
def cell3_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(79010758868583738810336394631663/9492368003458598562120000000000:ℝ)],
  ![(110417927251763297463235933631663/9492368003458598562120000000000:ℝ)]]
theorem cell3_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 8 true b := by
 have heq : complementBranch cell3 8 true b = Record12518109.Bernstein.bsum 1 0 (79010758868583738810336394631663/6328245335639065708080000000000000:ℝ) cell3_complement8_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement8_1_g]
def cell3_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(7873508716969223809673578403/759733852956694920000000000:ℝ)],
  ![(10965077344921159884464578403/759733852956694920000000000:ℝ)]]
theorem cell3_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 9 false b := by
 have heq : complementBranch cell3 9 false b = Record12518109.Bernstein.bsum 1 0 (7873508716969223809673578403/506489235304463280000000000000:ℝ) cell3_complement9_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement9_0_g]
def cell3_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(15420765879521321707325583607631/1498794947914515562440000000000:ℝ)],
  ![(21525036263216713962101826607631/1498794947914515562440000000000:ℝ)]]
theorem cell3_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 9 true b := by
 have heq : complementBranch cell3 9 true b = Record12518109.Bernstein.bsum 1 0 (15420765879521321707325583607631/999196631943010374960000000000000:ℝ) cell3_complement9_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement9_1_g]
def cell3_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(29859576804606648426391/15194677059133898400000:ℝ)],
  ![(41469977327869875426391/15194677059133898400000:ℝ)]]
theorem cell3_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 10 false b := by
 have heq : complementBranch cell3 10 false b = Record12518109.Bernstein.bsum 1 0 (29859576804606648426391/10129784706089265600000000:ℝ) cell3_complement10_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement10_0_g]
def cell3_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(2691657517055062326475602095767/1423855200518789784318000000000:ℝ)],
  ![(3784632644523252818045980295767/1423855200518789784318000000000:ℝ)]]
theorem cell3_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 10 true b := by
 have heq : complementBranch cell3 10 true b = Record12518109.Bernstein.bsum 1 0 (2691657517055062326475602095767/949236800345859856212000000000000:ℝ) cell3_complement10_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement10_1_g]
def cell3_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(29859998878969402145791/2532446176522316400000:ℝ)],
  ![(41470399402232629145791/2532446176522316400000:ℝ)]]
theorem cell3_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 11 false b := by
 have heq : complementBranch cell3 11 false b = Record12518109.Bernstein.bsum 1 0 (29859998878969402145791/1688297451014877600000000:ℝ) cell3_complement11_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement11_0_g]
def cell3_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(5560742097781178776173276086089/474618400172929928106000000000:ℝ)],
  ![(7738369818660057013534235486089/474618400172929928106000000000:ℝ)]]
theorem cell3_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 11 true b := by
 have heq : complementBranch cell3 11 true b = Record12518109.Bernstein.bsum 1 0 (5560742097781178776173276086089/316412266781953285404000000000000:ℝ) cell3_complement11_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement11_1_g]
def cell3_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(209020076567658365764417/15194677059133898400000:ℝ)],
  ![(290292880230500954764417/15194677059133898400000:ℝ)]]
theorem cell3_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 12 false b := by
 have heq : complementBranch cell3 12 false b = Record12518109.Bernstein.bsum 1 0 (209020076567658365764417/10129784706089265600000000:ℝ) cell3_complement12_0_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement12_0_g]
def cell3_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(19480340048601231128928673490767/1423855200518789784318000000000:ℝ)],
  ![(27101204818271554685114051690767/1423855200518789784318000000000:ℝ)]]
theorem cell3_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ))
    (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementBranch cell3 12 true b := by
 have heq : complementBranch cell3 12 true b = Record12518109.Bernstein.bsum 1 0 (19480340048601231128928673490767/949236800345859856212000000000000:ℝ) cell3_complement12_1_g (9/250:ℝ) (3/80:ℝ) (1589/2500:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell3, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell3_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell3_complement12_1_g]
theorem cell3_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 0 b := complementReserve_pos_of_branches (cell3_complement0_0 hb hν) (cell3_complement0_1 hb hν)
theorem cell3_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 1 b := complementReserve_pos_of_branches (cell3_complement1_0 hb hν) (cell3_complement1_1 hb hν)
theorem cell3_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 2 b := complementReserve_pos_of_branches (cell3_complement2_0 hb hν) (cell3_complement2_1 hb hν)
theorem cell3_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 3 b := complementReserve_pos_of_branches (cell3_complement3_0 hb hν) (cell3_complement3_1 hb hν)
theorem cell3_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 4 b := complementReserve_pos_of_branches (cell3_complement4_0 hb hν) (cell3_complement4_1 hb hν)
theorem cell3_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 5 b := complementReserve_pos_of_branches (cell3_complement5_0 hb hν) (cell3_complement5_1 hb hν)
theorem cell3_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 6 b := complementReserve_pos_of_branches (cell3_complement6_0 hb hν) (cell3_complement6_1 hb hν)
theorem cell3_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 7 b := complementReserve_pos_of_branches (cell3_complement7_0 hb hν) (cell3_complement7_1 hb hν)
theorem cell3_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 8 b := complementReserve_pos_of_branches (cell3_complement8_0 hb hν) (cell3_complement8_1 hb hν)
theorem cell3_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 9 b := complementReserve_pos_of_branches (cell3_complement9_0 hb hν) (cell3_complement9_1 hb hν)
theorem cell3_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 10 b := complementReserve_pos_of_branches (cell3_complement10_0 hb hν) (cell3_complement10_1 hb hν)
theorem cell3_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 11 b := complementReserve_pos_of_branches (cell3_complement11_0 hb hν) (cell3_complement11_1 hb hν)
theorem cell3_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (hν : ν ∈ Set.Icc (1589/2500:ℝ) (3/4:ℝ)) : 0 < complementReserve cell3 12 b := complementReserve_pos_of_branches (cell3_complement12_0 hb hν) (cell3_complement12_1 hb hν)
theorem cell3_all_domains {b : ℝ} (hb : b ∈ Set.Icc (9/250:ℝ) (3/80:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell3 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell3_domain0_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain0_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain1_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain1_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain2_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain2_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain3_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain3_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain4_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain4_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain5_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain5_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain6_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain6_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain7_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain7_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell3_domain8_0 (ν := (1589/2500:ℝ)) hb (by norm_num)
   | true => exact cell3_domain8_1 (ν := (1589/2500:ℝ)) hb (by norm_num)
end
end Record12518109Admission
