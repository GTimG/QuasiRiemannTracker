/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell13 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (3111/5000:ℝ), (83/2000:ℝ), (21/500:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (563/100000:ℝ), (1/50:ℝ)⟩
def cell13_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(3374873058331678252286104274276755239287590913/25714900194619350793378175718750000000:ℝ), (45756289364059344031960191470245820590975412837/6428725048654837698344543929687500000:ℝ), (86947514444376533998041950410726790654437409087/4285816699103225132229695953125000000:ℝ), (125115147164418038602956875516433745301728034087/6428725048654837698344543929687500000:ℝ), (158995205449628894106762058745410271127899909087/25714900194619350793378175718750000000:ℝ)],
  ![(1293213389684191941943792342219500524458196971/8571633398206450264459391906250000000:ℝ), (5103946391665288040483900354578508857122268093/714302783183870855371615992187500000:ℝ), (28943282320133136999825149619598517718145803029/1428605566367741710743231984375000000:ℝ), (41578068848408807972775727971208058329742678029/2142908349551612566114847976562500000:ℝ), (1955400456886184081129179999732350955282714927/317467903637275935720718218750000000:ℝ)]]
theorem cell13_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell13 2 b ν := by
 have heq : highRegular cell13 2 b ν = Record12518109.Bernstein.bsum 1 4 (3374873058331678252286104274276755239287590913/192793071965019648437500000000000000000000000:ℝ) cell13_regular2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_regular2_g]
def cell13_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(394487670016112997062481582478809018887665913/25714900194619350793378175718750000000:ℝ), (42331460907411788544944118057527049674594087837/6428725048654837698344543929687500000:ℝ), (83633958256877552868882826365052357343587334087/4285816699103225132229695953125000000:ℝ), (122505052231696265130779119707162209100252959087/6428725048654837698344543929687500000:ℝ), (157601734103260728996735874395338100160799834087/25714900194619350793378175718750000000:ℝ)],
  ![(218192013917952957556734085928476167658221971/8571633398206450264459391906250000000:ℝ), (14103928110130488994915631773127634182573029279/2142908349551612566114847976562500000:ℝ), (9262367928504380931869971807898874427065259343/476201855455913903581077328125000000:ℝ), (40669767046907831585208558668247754595917653029/2142908349551612566114847976562500000:ℝ), (52304860940872815703202642618270252136933278029/8571633398206450264459391906250000000:ℝ)]]
theorem cell13_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell13 3 b ν := by
 have heq : highRegular cell13 3 b ν = Record12518109.Bernstein.bsum 1 4 (394487670016112997062481582478809018887665913/192793071965019648437500000000000000000000000:ℝ) cell13_regular3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_regular3_g]
def cell13_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(1964499795119779261610705890507491768753640657/2857211132735483421486463968750000000:ℝ), (15635516730192419203329091911406529999412329279/2142908349551612566114847976562500000:ℝ), (25885830033146588482468220138793679899035078029/1428605566367741710743231984375000000:ℝ), (4039030078755360909800692744486952183472994781/238100927727956951790538664062500000:ℝ), (46791818885544240337875177968520692192272578029/8571633398206450264459391906250000000:ℝ)],
  ![(17390989503497834233803492871082957602869765913/25714900194619350793378175718750000000:ℝ), (46442425358946350321878129016013692871361987837/6428725048654837698344543929687500000:ℝ), (77041694696832022426352744828356052197105234087/4285816699103225132229695953125000000:ℝ), (108307233481034838607174278758103763641270859087/6428725048654837698344543929687500000:ℝ), (139517072850337764223324247521284732826817734087/25714900194619350793378175718750000000:ℝ)]]
theorem cell13_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell13 4 b ν := by
 have heq : highRegular cell13 4 b ν = Record12518109.Bernstein.bsum 1 4 (17390989503497834233803492871082957602869765913/192793071965019648437500000000000000000000000:ℝ) cell13_regular4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_regular4_g]
def cell13_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(217380125964657604471088881927259822689/4786264764219990302474625000000000:ℝ), (16350797493945278859571600283597674069/125954335900526060591437500000000:ℝ), (410688471735266126781646109072026052311/4786264764219990302474625000000000:ℝ)],
  ![(215816010200079803292347889317070822689/4786264764219990302474625000000000:ℝ), (308896670093072050094078598323355807311/2393132382109995151237312500000000:ℝ), (408701654473114444647978904384526052311/4786264764219990302474625000000000:ℝ)]]
theorem cell13_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 0 false b ν := by
 have heq : highBranch cell13 0 false b ν = Record12518109.Bernstein.bsum 1 2 (215816010200079803292347889317070822689/586090938773659731250000000000000000000:ℝ) cell13_exceptional0_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional0_0_g]
def cell13_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(2712485570526476158066385267373684061808929/59801187385752632169218789625000000000:ℝ), (68039635870455904075276805797726676208703/524571819173268703238761312500000000:ℝ), (5128223396670599404448510099328074026566071/59801187385752632169218789625000000000:ℝ)],
  ![(8078923446064526253769970985474512898426787/179403562157257896507656368875000000000:ℝ), (11568580982519077757406812654077579131688213/89701781078628948253828184437500000000:ℝ), (15310286373721729949238227329088909579698213/179403562157257896507656368875000000000:ℝ)]]
theorem cell13_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 0 true b ν := by
 have heq : highBranch cell13 0 true b ν = Record12518109.Bernstein.bsum 1 2 (8078923446064526253769970985474512898426787/21968446658053087706443750000000000000000000:ℝ) cell13_exceptional0_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional0_1_g]
theorem cell13_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 0 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional0_0 hb hν) (cell13_exceptional0_1 hb hν)
def cell13_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(899485397174669036185830967928970931/251908671801052121182875000000000:ℝ), (23107146845597530582396703584378924069/125954335900526060591437500000000:ℝ), (45669455290336346580660954107280154069/251908671801052121182875000000000:ℝ)],
  ![(12186801366607861972428290978844661/3548009461986649594125000000000:ℝ), (4567072853476965378377096771350709/24985982126666546437500000000:ℝ), (641322217279345200817289648518030339/3548009461986649594125000000000:ℝ)]]
theorem cell13_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 1 false b ν := by
 have heq : highBranch cell13 1 false b ν = Record12518109.Bernstein.bsum 1 2 (865262897029158200042408659497970931/30846891514403143750000000000000000000:ℝ) cell13_exceptional1_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional1_0_g]
def cell13_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(11052460732453188701632417229619701443891/3147430915039612219432567875000000000:ℝ), (96178329509120498667127177689191519958703/524571819173268703238761312500000000:ℝ), (570448594109906776876569570261367155181109/3147430915039612219432567875000000000:ℝ)],
  ![(31879593155393146652341974847264931331673/9442292745118836658297703625000000000:ℝ), (862441234171588380040848835858681179628327/4721146372559418329148851812500000000:ℝ), (1706268551753473123334333223523163965543327/9442292745118836658297703625000000000:ℝ)]]
theorem cell13_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 1 true b ν := by
 have heq : highBranch cell13 1 true b ν = Record12518109.Bernstein.bsum 1 2 (31879593155393146652341974847264931331673/1156234034634373037181250000000000000000000:ℝ) cell13_exceptional1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional1_1_g]
theorem cell13_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 1 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional1_0 hb hν) (cell13_exceptional1_1 hb hν)
def cell13_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(3462441907513867981389980554686400727/41984778633508686863812500000000:ℝ), (67665303561192941407446466838443/621996720496424990575000000:ℝ), (1591887858667741540466664845123/53740516650891119185680000:ℝ)],
  ![(3446673657890978124061994682447900727/41984778633508686863812500000000:ℝ), (1816567616723553609500447186637961/16793911453403474745525000000:ℝ), (526138526295661152957180615041/17913505550297039728560000:ℝ)]]
theorem cell13_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 2 false b ν := by
 have heq : highBranch cell13 2 false b ν = Record12518109.Bernstein.bsum 1 2 (4735246736660950376614625535369/19742010569218012000000000000000:ℝ) cell13_exceptional2_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional2_0_g]
def cell13_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(389050295541201792456210390181328077900423/4721146372559418329148851812500000000:ℝ), (205217040556055999323361446359440071259/1888458549023767331659540725000000:ℝ), (178673365559060906089713500473387247/6043067356876055461310530320000:ℝ)],
  ![(387279658104851332498840017606643491400423/4721146372559418329148851812500000000:ℝ), (204049989527366563770776734115573071259/1888458549023767331659540725000000:ℝ), (177161387238109412776514288626387247/6043067356876055461310530320000:ℝ)]]
theorem cell13_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 2 true b ν := by
 have heq : highBranch cell13 2 true b ν = Record12518109.Bernstein.bsum 1 2 (177161387238109412776514288626387247/739989782165998743796000000000000000:ℝ) cell13_exceptional2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional2_1_g]
theorem cell13_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 2 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional2_0 hb hν) (cell13_exceptional2_1 hb hν)
def cell13_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(66704878208232380438302374809086607563/1595421588073330100824875000000000:ℝ), (96614723951145428772926554296118602437/797710794036665050412437500000000:ℝ), (14314942688990643167546865428593557493/177269065341481122313875000000000:ℝ)],
  ![(198550518860119340136166131817070822689/4786264764219990302474625000000000:ℝ), (288075689561548038080997855823355807311/2393132382109995151237312500000000:ℝ), (384516635340595683390098161884526052311/4786264764219990302474625000000000:ℝ)]]
theorem cell13_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 3 false b ν := by
 have heq : highBranch cell13 3 false b ν = Record12518109.Bernstein.bsum 1 2 (198550518860119340136166131817070822689/586090938773659731250000000000000000000:ℝ) cell13_exceptional3_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional3_0_g]
def cell13_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(7490294299683690433715994985748552185426787/179403562157257896507656368875000000000:ℝ), (10854344920584845054586028320283761631688213/89701781078628948253828184437500000000:ℝ), (14478143117867597485116386426856722079698213/179403562157257896507656368875000000000:ℝ)],
  ![(2477253678056262737762270056367337632808929/59801187385752632169218789625000000000:ℝ), (1198683129917329246124500798105564347965357/9966864564292105361536464937500000000:ℝ), (4801253100525843073669694485987136526566071/59801187385752632169218789625000000000:ℝ)]]
theorem cell13_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 3 true b ν := by
 have heq : highBranch cell13 3 true b ν = Record12518109.Bernstein.bsum 1 2 (7431761034168788213286810169102012898426787/21968446658053087706443750000000000000000000:ℝ) cell13_exceptional3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional3_1_g]
theorem cell13_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 3 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional3_0 hb hν) (cell13_exceptional3_1 hb hν)
def cell13_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(70901637057137857385454489309656977/83969557267017373727625000000000:ℝ), (2429803667953931532219227342708769341/13994926211169562287937500000000:ℝ), (14629494818395783514896807202426718023/83969557267017373727625000000000:ℝ)],
  ![(178482411025902736012941159497970931/251908671801052121182875000000000:ℝ), (21783700420365235679975287324378924069/125954335900526060591437500000000:ℝ), (43752906591684513222057032544780154069/251908671801052121182875000000000:ℝ)]]
theorem cell13_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 4 false b ν := by
 have heq : highBranch cell13 4 false b ν = Record12518109.Bernstein.bsum 1 2 (178482411025902736012941159497970931/30846891514403143750000000000000000000:ℝ) cell13_exceptional4_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional4_0_g]
def cell13_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(7414789240499541546680721386359104331673/9442292745118836658297703625000000000:ℝ), (819166758341807189783728645130223679628327/4721146372559418329148851812500000000:ℝ), (1644589652515830512213425241086601465543327/9442292745118836658297703625000000000:ℝ)],
  ![(2045666732844374031375148181588310443891/3147430915039612219432567875000000000:ℝ), (272001008977103693940144293928727059876109/1573715457519806109716283937500000000:ℝ), (182168046882175922768672194869518218393703/1049143638346537406477522625000000000:ℝ)]]
theorem cell13_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 4 true b ν := by
 have heq : highBranch cell13 4 true b ν = Record12518109.Bernstein.bsum 1 2 (6137000198533122094125444544764931331673/1156234034634373037181250000000000000000000:ℝ) cell13_exceptional4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional4_1_g]
theorem cell13_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 4 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional4_0 hb hν) (cell13_exceptional4_1 hb hν)
def cell13_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(10344267944164624908375795384991470931/251908671801052121182875000000000:ℝ), (110980202528708831035845902626365318471341/1182585259770039182893006687500000000:ℝ), (132651391072280630490028209038717710303841/2365170519540078365786013375000000000:ℝ)],
  ![(10266950531306299828617248076560470931/251908671801052121182875000000000:ℝ), (110227000198303559050390304665137818471341/1182585259770039182893006687500000000:ℝ), (131853764791962306628735444724655210303841/2365170519540078365786013375000000000:ℝ)]]
theorem cell13_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 5 false b ν := by
 have heq : highBranch cell13 5 false b ν = Record12518109.Bernstein.bsum 1 2 (10266950531306299828617248076560470931/30846891514403143750000000000000000000:ℝ) cell13_exceptional5_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional5_0_g]
def cell13_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(4779952671681284963730786270785343109033/116571515371837489608613625000000000:ℝ), (1384995529754643393768924773947540968451674901/14775614430653459564126189889187500000000:ℝ), (1655880913695665695169459267523702885589182401/29551228861306919128252379778375000000000:ℝ)],
  ![(384283050751003246316212680717018618831673/9442292745118836658297703625000000000:ℝ), (4126799408310942889987113036567257610355024703/44326843291960378692378569667562500000000:ℝ), (4937788828367968280378366556308697719267547203/88653686583920757384757139335125000000000:ℝ)]]
theorem cell13_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 5 true b ν := by
 have heq : highBranch cell13 5 true b ν = Record12518109.Bernstein.bsum 1 2 (384283050751003246316212680717018618831673/1156234034634373037181250000000000000000000:ℝ) cell13_exceptional5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional5_1_g]
theorem cell13_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 5 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional5_0 hb hν) (cell13_exceptional5_1 hb hν)
def cell13_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(3462441907513867981389980554686400727/41984778633508686863812500000000:ℝ), (67665303561192941407446466838443/621996720496424990575000000:ℝ), (1591887858667741540466664845123/53740516650891119185680000:ℝ)],
  ![(3446673657890978124061994682447900727/41984778633508686863812500000000:ℝ), (1816567616723553609500447186637961/16793911453403474745525000000:ℝ), (526138526295661152957180615041/17913505550297039728560000:ℝ)]]
theorem cell13_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 6 false b ν := by
 have heq : highBranch cell13 6 false b ν = Record12518109.Bernstein.bsum 1 2 (4735246736660950376614625535369/19742010569218012000000000000000:ℝ) cell13_exceptional6_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional6_0_g]
def cell13_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(389050295541201792456210390181328077900423/4721146372559418329148851812500000000:ℝ), (205217040556055999323361446359440071259/1888458549023767331659540725000000:ℝ), (178673365559060906089713500473387247/6043067356876055461310530320000:ℝ)],
  ![(387279658104851332498840017606643491400423/4721146372559418329148851812500000000:ℝ), (204049989527366563770776734115573071259/1888458549023767331659540725000000:ℝ), (177161387238109412776514288626387247/6043067356876055461310530320000:ℝ)]]
theorem cell13_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 6 true b ν := by
 have heq : highBranch cell13 6 true b ν = Record12518109.Bernstein.bsum 1 2 (177161387238109412776514288626387247/739989782165998743796000000000000000:ℝ) cell13_exceptional6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional6_1_g]
theorem cell13_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 6 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional6_0 hb hν) (cell13_exceptional6_1 hb hν)
def cell13_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(9458648395459526779733827884991470931/251908671801052121182875000000000:ℝ), (101588434504397255005541187001365318471341/1182585259770039182893006687500000000:ℝ), (122182936966449644759238210646217710303841/2365170519540078365786013375000000000:ℝ)],
  ![(9381330982601201699975280576560470931/251908671801052121182875000000000:ℝ), (100835232173991983020085589040137818471341/1182585259770039182893006687500000000:ℝ), (121385310686131320897945446332155210303841/2365170519540078365786013375000000000:ℝ)]]
theorem cell13_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 7 false b ν := by
 have heq : highBranch cell13 7 false b ν = Record12518109.Bernstein.bsum 1 2 (9381330982601201699975280576560470931/30846891514403143750000000000000000000:ℝ) cell13_exceptional7_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional7_0_g]
def cell13_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(117993496287356962968768940043704263943891/3147430915039612219432567875000000000:ℝ), (1267651649469553125654287555356915968451674901/14775614430653459564126189889187500000000:ℝ), (508361519537570471929019588091670128529727467/9850409620435639709417459926125000000000:ℝ)],
  ![(351087373206890053160325812914518618831673/9442292745118836658297703625000000000:ℝ), (3774767767455672085643201380795382610355024703/44326843291960378692378569667562500000000:ℝ), (4545399763119105442231165046562620219267547203/88653686583920757384757139335125000000000:ℝ)]]
theorem cell13_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell13 7 true b ν := by
 have heq : highBranch cell13 7 true b ν = Record12518109.Bernstein.bsum 1 2 (351087373206890053160325812914518618831673/1156234034634373037181250000000000000000000:ℝ) cell13_exceptional7_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_exceptional7_1_g]
theorem cell13_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
 (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell13 7 b ν :=
 highExceptional_pos_of_branches (cell13_exceptional7_0 hb hν) (cell13_exceptional7_1 hb hν)
def cell13_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(103315547522366573844364660379/9249872277074984297450000000000:ℝ)],
  ![(166874149986056661503815660379/9249872277074984297450000000000:ℝ)]]
theorem cell13_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 0 false b := by
 have heq : domainBranch cell13 0 false b = Record12518109.Bernstein.bsum 1 0 (103315547522366573844364660379/18499744554149968594900000000000000:ℝ) cell13_domain0_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain0_0_g]
def cell13_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(103315547522366573844364660379/9249872277074984297450000000000:ℝ)],
  ![(166874149986056661503815660379/9249872277074984297450000000000:ℝ)]]
theorem cell13_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 0 true b := by
 have heq : domainBranch cell13 0 true b = Record12518109.Bernstein.bsum 1 0 (103315547522366573844364660379/18499744554149968594900000000000000:ℝ) cell13_domain0_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain0_1_g]
def cell13_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(701396216066088618906974471651791/49355026423045030000000000000000:ℝ)],
  ![(689660353754390434255027257651791/49355026423045030000000000000000:ℝ)]]
theorem cell13_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 1 false b := by
 have heq : domainBranch cell13 1 false b = Record12518109.Bernstein.bsum 1 0 (689660353754390434255027257651791/98710052846090060000000000000000000:ℝ) cell13_domain1_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain1_0_g]
def cell13_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1258764826724162197763811986531637/49355026423045030000000000000000:ℝ)],
  ![(1247028964412464013111864772531637/49355026423045030000000000000000:ℝ)]]
theorem cell13_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 1 true b := by
 have heq : domainBranch cell13 1 true b = Record12518109.Bernstein.bsum 1 0 (1247028964412464013111864772531637/98710052846090060000000000000000000:ℝ) cell13_domain1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain1_1_g]
def cell13_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(101307811488509832631617793107587/4935502642304503000000000000000:ℝ)],
  ![(101567501868455306722151595107587/4935502642304503000000000000000:ℝ)]]
theorem cell13_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 2 false b := by
 have heq : domainBranch cell13 2 false b = Record12518109.Bernstein.bsum 1 0 (101307811488509832631617793107587/9871005284609006000000000000000000:ℝ) cell13_domain2_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain2_0_g]
def cell13_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(48241701005333158833231110797809/4935502642304503000000000000000:ℝ)],
  ![(48501391385278632923764912797809/4935502642304503000000000000000:ℝ)]]
theorem cell13_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 2 true b := by
 have heq : domainBranch cell13 2 true b = Record12518109.Bernstein.bsum 1 0 (48241701005333158833231110797809/9871005284609006000000000000000000:ℝ) cell13_domain2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain2_1_g]
def cell13_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(1252193780649979161940983016279/49355026423045030000000000000:ℝ)],
  ![(1486048980599286167243145016279/49355026423045030000000000000:ℝ)]]
theorem cell13_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 3 false b := by
 have heq : domainBranch cell13 3 false b = Record12518109.Bernstein.bsum 1 0 (1252193780649979161940983016279/98710052846090060000000000000000:ℝ) cell13_domain3_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain3_0_g]
def cell13_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1252193780649979161940983016279/49355026423045030000000000000:ℝ)],
  ![(1486048980599286167243145016279/49355026423045030000000000000:ℝ)]]
theorem cell13_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 3 true b := by
 have heq : domainBranch cell13 3 true b = Record12518109.Bernstein.bsum 1 0 (1252193780649979161940983016279/98710052846090060000000000000000:ℝ) cell13_domain3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain3_1_g]
def cell13_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(2050403498958049416885039/154234457572015718750000:ℝ)],
  ![(1729498160730453435885039/154234457572015718750000:ℝ)]]
theorem cell13_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 4 false b := by
 have heq : domainBranch cell13 4 false b = Record12518109.Bernstein.bsum 1 0 (1729498160730453435885039/308468915144031437500000000:ℝ) cell13_domain4_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain4_0_g]
def cell13_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(2050403498958049416885039/154234457572015718750000:ℝ)],
  ![(1729498160730453435885039/154234457572015718750000:ℝ)]]
theorem cell13_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 4 true b := by
 have heq : domainBranch cell13 4 true b = Record12518109.Bernstein.bsum 1 0 (1729498160730453435885039/308468915144031437500000000:ℝ) cell13_domain4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain4_1_g]
def cell13_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(31113492969893237684659807139849/2467751321152251500000000000000:ℝ)],
  ![(30544859470221688412752461139849/2467751321152251500000000000000:ℝ)]]
theorem cell13_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 5 false b := by
 have heq : domainBranch cell13 5 false b = Record12518109.Bernstein.bsum 1 0 (30544859470221688412752461139849/4935502642304503000000000000000000:ℝ) cell13_domain5_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain5_0_g]
def cell13_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(58928854211896886312673531945843/2467751321152251500000000000000:ℝ)],
  ![(58360220712225337040766185945843/2467751321152251500000000000000:ℝ)]]
theorem cell13_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 5 true b := by
 have heq : domainBranch cell13 5 true b = Record12518109.Bernstein.bsum 1 0 (58360220712225337040766185945843/4935502642304503000000000000000000:ℝ) cell13_domain5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain5_1_g]
def cell13_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(714162545190386932140886345061488833/5019877527726019631036500000000000:ℝ)],
  ![(701560551473012735915832949259488833/5019877527726019631036500000000000:ℝ)]]
theorem cell13_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 6 false b := by
 have heq : domainBranch cell13 6 false b = Record12518109.Bernstein.bsum 1 0 (701560551473012735915832949259488833/10039755055452039262073000000000000000:ℝ) cell13_domain6_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain6_0_g]
def cell13_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(692171434894118645472941992738269771/5019877527726019631036500000000000:ℝ)],
  ![(679569441176744449247888596936269771/5019877527726019631036500000000000:ℝ)]]
theorem cell13_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 6 true b := by
 have heq : domainBranch cell13 6 true b = Record12518109.Bernstein.bsum 1 0 (679569441176744449247888596936269771/10039755055452039262073000000000000000:ℝ) cell13_domain6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain6_1_g]
def cell13_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(72900524762994073960127336411/1233875660576125750000000000:ℝ)],
  ![(79324161123921303202186336411/1233875660576125750000000000:ℝ)]]
theorem cell13_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 7 false b := by
 have heq : domainBranch cell13 7 false b = Record12518109.Bernstein.bsum 1 0 (72900524762994073960127336411/2467751321152251500000000000000:ℝ) cell13_domain7_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain7_0_g]
def cell13_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(72900524762994073960127336411/1233875660576125750000000000:ℝ)],
  ![(79324161123921303202186336411/1233875660576125750000000000:ℝ)]]
theorem cell13_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 7 true b := by
 have heq : domainBranch cell13 7 true b = Record12518109.Bernstein.bsum 1 0 (72900524762994073960127336411/2467751321152251500000000000000:ℝ) cell13_domain7_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain7_1_g]
def cell13_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(18140842208068889275471824637407/246775132115225150000000000000:ℝ)],
  ![(17774398904788552362653346637407/246775132115225150000000000000:ℝ)]]
theorem cell13_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 8 false b := by
 have heq : domainBranch cell13 8 false b = Record12518109.Bernstein.bsum 1 0 (17774398904788552362653346637407/493550264230450300000000000000000:ℝ) cell13_domain8_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain8_0_g]
def cell13_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(19211728638317958140994471752549/246775132115225150000000000000:ℝ)],
  ![(18845285335037621228175993752549/246775132115225150000000000000:ℝ)]]
theorem cell13_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell13 8 true b := by
 have heq : domainBranch cell13 8 true b = Record12518109.Bernstein.bsum 1 0 (18845285335037621228175993752549/493550264230450300000000000000000:ℝ) cell13_domain8_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_domain8_1_g]
def cell13_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(429180302793992484627891/49355026423045030000000:ℝ)],
  ![(464836451485947593627891/49355026423045030000000:ℝ)]]
theorem cell13_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 0 b := by
 have heq : ordinary cell13 0 b = Record12518109.Bernstein.bsum 1 0 (429180302793992484627891/98710052846090060000000000:ℝ) cell13_ordinary0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary0_g]
def cell13_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(740144371577756409616327/148065079269135090000000:ℝ)],
  ![(633175925501891082616327/148065079269135090000000:ℝ)]]
theorem cell13_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 1 b := by
 have heq : ordinary cell13 1 b = Record12518109.Bernstein.bsum 1 0 (633175925501891082616327/296130158538270180000000000:ℝ) cell13_ordinary1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary1_g]
def cell13_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(46609044248659694258028151/49355026423045030000000:ℝ)],
  ![(46395107356507963604028151/49355026423045030000000:ℝ)]]
theorem cell13_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 2 b := by
 have heq : ordinary cell13 2 b = Record12518109.Bernstein.bsum 1 0 (46395107356507963604028151/98710052846090060000000000:ℝ) cell13_ordinary2_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary2_g]
def cell13_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(414999989/10000000:ℝ)],
  ![(424999989/10000000:ℝ)]]
theorem cell13_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 3 b := by
 have heq : ordinary cell13 3 b = Record12518109.Bernstein.bsum 1 0 (414999989/20000000000:ℝ) cell13_ordinary3_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary3_g]
def cell13_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(42839800989312803447627217/49355026423045030000000:ℝ)],
  ![(42527154044314982733627217/49355026423045030000000:ℝ)]]
theorem cell13_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 4 b := by
 have heq : ordinary cell13 4 b = Record12518109.Bernstein.bsum 1 0 (42527154044314982733627217/98710052846090060000000000:ℝ) cell13_ordinary4_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary4_g]
def cell13_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(7537447781385601501/762475812530000000000000:ℝ)],
  ![(7537447781385601501/762475812530000000000000:ℝ)]]
theorem cell13_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell13 5 b := by
 have heq : ordinary cell13 5 b = Record12518109.Bernstein.bsum 1 0 (7537447781385601501/1524951625060000000000000000:ℝ) cell13_ordinary5_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_ordinary5_g]
def cell13_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(429175367291350180124891/49355026423045030000000:ℝ)],
  ![(464831515983305289124891/49355026423045030000000:ℝ)]]
theorem cell13_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 0 false b := by
 have heq : complementBranch cell13 0 false b = Record12518109.Bernstein.bsum 1 0 (429175367291350180124891/98710052846090060000000000:ℝ) cell13_complement0_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement0_0_g]
def cell13_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(78067121273690706206841393151793/9249872277074984297450000000000:ℝ)],
  ![(84770804581614702989296210151793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 0 true b := by
 have heq : complementBranch cell13 0 true b = Record12518109.Bernstein.bsum 1 0 (78067121273690706206841393151793/18499744554149968594900000000000000:ℝ) cell13_complement0_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement0_1_g]
def cell13_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(110606199365727120535036938589/1233875660576125750000000000:ℝ)],
  ![(109390014427767633846447938589/1233875660576125750000000000:ℝ)]]
theorem cell13_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 1 false b := by
 have heq : complementBranch cell13 1 false b = Record12518109.Bernstein.bsum 1 0 (109390014427767633846447938589/2467751321152251500000000000000:ℝ) cell13_complement1_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement1_0_g]
def cell13_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1033491326096852036233853689641363/11562340346343730371812500000000:ℝ)],
  ![(1022121243840494713883283089141363/11562340346343730371812500000000:ℝ)]]
theorem cell13_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 1 true b := by
 have heq : complementBranch cell13 1 true b = Record12518109.Bernstein.bsum 1 0 (1022121243840494713883283089141363/23124680692687460743625000000000000:ℝ) cell13_complement1_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement1_1_g]
def cell13_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(69470976520925627522247838589/1233875660576125750000000000:ℝ)],
  ![(64689176713770629933658838589/1233875660576125750000000000:ℝ)]]
theorem cell13_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 2 false b := by
 have heq : complementBranch cell13 2 false b = Record12518109.Bernstein.bsum 1 0 (64689176713770629933658838589/2467751321152251500000000000000:ℝ) cell13_complement2_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement2_0_g]
def cell13_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(648023436623928445584260230816363/11562340346343730371812500000000:ℝ)],
  ![(603240868832057289467514630316363/11562340346343730371812500000000:ℝ)]]
theorem cell13_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 2 true b := by
 have heq : complementBranch cell13 2 true b = Record12518109.Bernstein.bsum 1 0 (603240868832057289467514630316363/23124680692687460743625000000000000:ℝ) cell13_complement2_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement2_1_g]
def cell13_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(96212491865404978788234213589/1233875660576125750000000000:ℝ)],
  ![(95887710644744369824645213589/1233875660576125750000000000:ℝ)]]
theorem cell13_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 3 false b := by
 have heq : complementBranch cell13 3 false b = Record12518109.Bernstein.bsum 1 0 (95887710644744369824645213589/2467751321152251500000000000000:ℝ) cell13_complement3_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement3_0_g]
def cell13_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(898611491538208326460002054347613/11562340346343730371812500000000:ℝ)],
  ![(895594530665729462550975203847613/11562340346343730371812500000000:ℝ)]]
theorem cell13_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 3 true b := by
 have heq : complementBranch cell13 3 true b = Record12518109.Bernstein.bsum 1 0 (895594530665729462550975203847613/23124680692687460743625000000000000:ℝ) cell13_complement3_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement3_1_g]
def cell13_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(91070589009804792161635576089/1233875660576125750000000000:ℝ)],
  ![(90300105930494744335546576089/1233875660576125750000000000:ℝ)]]
theorem cell13_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 4 false b := by
 have heq : complementBranch cell13 4 false b = Record12518109.Bernstein.bsum 1 0 (90300105930494744335546576089/2467751321152251500000000000000:ℝ) cell13_complement4_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement4_0_g]
def cell13_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(106303500669261609703600358999311/1445292543292966296476562500000:ℝ)],
  ![(105404310473709348062375518311811/1445292543292966296476562500000:ℝ)]]
theorem cell13_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 4 true b := by
 have heq : complementBranch cell13 4 true b = Record12518109.Bernstein.bsum 1 0 (105404310473709348062375518311811/2890585086585932592953125000000000:ℝ) cell13_complement4_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement4_1_g]
def cell13_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(3279177/50000:ℝ)],
  ![(3054279/50000:ℝ)]]
theorem cell13_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 5 false b := by
 have heq : complementBranch cell13 5 false b = Record12518109.Bernstein.bsum 1 0 (3054279/100000000:ℝ) cell13_complement5_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement5_0_g]
def cell13_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(604261995190810012855309010886793/9249872277074984297450000000000:ℝ)],
  ![(562677625884239046513970625886793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 5 true b := by
 have heq : complementBranch cell13 5 true b = Record12518109.Bernstein.bsum 1 0 (562677625884239046513970625886793/18499744554149968594900000000000000:ℝ) cell13_complement5_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement5_1_g]
def cell13_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(9459286071122510684601763/49355026423045030000000:ℝ)],
  ![(9209693030278824921601763/49355026423045030000000:ℝ)]]
theorem cell13_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 6 false b := by
 have heq : complementBranch cell13 6 false b = Record12518109.Bernstein.bsum 1 0 (9209693030278824921601763/98710052846090060000000000:ℝ) cell13_complement6_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement6_0_g]
def cell13_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(1770434725731797037138764450531793/9249872277074984297450000000000:ℝ)],
  ![(1723678432182898899895339267531793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 6 true b := by
 have heq : complementBranch cell13 6 true b = Record12518109.Bernstein.bsum 1 0 (1723678432182898899895339267531793/18499744554149968594900000000000000:ℝ) cell13_complement6_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement6_1_g]
def cell13_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(16613110819033320865945638589/7403253963456754500000000000:ℝ)],
  ![(18209590807448415852356638589/7403253963456754500000000000:ℝ)]]
theorem cell13_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 7 false b := by
 have heq : complementBranch cell13 7 false b = Record12518109.Bernstein.bsum 1 0 (16613110819033320865945638589/14806507926913509000000000000000:ℝ) cell13_complement7_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement7_0_g]
def cell13_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(551705827213295331980288762835277/277496168312249528923500000000000:ℝ)],
  ![(612182272643695238232526785835277/277496168312249528923500000000000:ℝ)]]
theorem cell13_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 7 true b := by
 have heq : complementBranch cell13 7 true b = Record12518109.Bernstein.bsum 1 0 (551705827213295331980288762835277/554992336624499057847000000000000000:ℝ) cell13_complement7_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement7_1_g]
def cell13_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(274121292495428811642680238589/7403253963456754500000000000:ℝ)],
  ![(297111461699016972029091238589/7403253963456754500000000000:ℝ)]]
theorem cell13_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 8 false b := by
 have heq : complementBranch cell13 8 false b = Record12518109.Bernstein.bsum 1 0 (274121292495428811642680238589/14806507926913509000000000000000:ℝ) cell13_complement8_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement8_0_g]
def cell13_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(10203885000989627512764631774635277/277496168312249528923500000000000:ℝ)],
  ![(11066261099272359429405069797635277/277496168312249528923500000000000:ℝ)]]
theorem cell13_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 8 true b := by
 have heq : complementBranch cell13 8 true b = Record12518109.Bernstein.bsum 1 0 (10203885000989627512764631774635277/554992336624499057847000000000000000:ℝ) cell13_complement8_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement8_1_g]
def cell13_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(338498337914527684336863888589/7403253963456754500000000000:ℝ)],
  ![(366836929421909111073274888589/7403253963456754500000000000:ℝ)]]
theorem cell13_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 9 false b := by
 have heq : complementBranch cell13 9 false b = Record12518109.Bernstein.bsum 1 0 (338498337914527684336863888589/14806507926913509000000000000000:ℝ) cell13_complement9_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement9_0_g]
def cell13_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(12616929794433710557960717527585277/277496168312249528923500000000000:ℝ)],
  ![(13679780805929525477198205550585277/277496168312249528923500000000000:ℝ)]]
theorem cell13_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 9 true b := by
 have heq : complementBranch cell13 9 true b = Record12518109.Bernstein.bsum 1 0 (12616929794433710557960717527585277/554992336624499057847000000000000000:ℝ) cell13_complement9_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement9_1_g]
def cell13_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(429175367291350180124891/49355026423045030000000:ℝ)],
  ![(464831515983305289124891/49355026423045030000000:ℝ)]]
theorem cell13_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 10 false b := by
 have heq : complementBranch cell13 10 false b = Record12518109.Bernstein.bsum 1 0 (429175367291350180124891/98710052846090060000000000:ℝ) cell13_complement10_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement10_0_g]
def cell13_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(78067121273690706206841393151793/9249872277074984297450000000000:ℝ)],
  ![(84770804581614702989296210151793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 10 true b := by
 have heq : complementBranch cell13 10 true b = Record12518109.Bernstein.bsum 1 0 (78067121273690706206841393151793/18499744554149968594900000000000000:ℝ) cell13_complement10_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement10_1_g]
def cell13_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(1287538440630656301632173/24677513211522515000000:ℝ)],
  ![(1394506886706521628632173/24677513211522515000000:ℝ)]]
theorem cell13_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 11 false b := by
 have heq : complementBranch cell13 11 false b = Record12518109.Bernstein.bsum 1 0 (1287538440630656301632173/49355026423045030000000000:ℝ) cell13_complement11_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement11_0_g]
def cell13_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(480241253514371213739522351976793/9249872277074984297450000000000:ℝ)],
  ![(520357422357809044288152168976793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 11 true b := by
 have heq : complementBranch cell13 11 true b = Record12518109.Bernstein.bsum 1 0 (480241253514371213739522351976793/18499744554149968594900000000000000:ℝ) cell13_complement11_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement11_1_g]
def cell13_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(3004257184055305087892237/49355026423045030000000:ℝ)],
  ![(3253850224898990850892237/49355026423045030000000:ℝ)]]
theorem cell13_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 12 false b := by
 have heq : complementBranch cell13 12 false b = Record12518109.Bernstein.bsum 1 0 (3004257184055305087892237/98710052846090060000000000:ℝ) cell13_complement12_0_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement12_0_g]
def cell13_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(560676079962507315246058543741793/9249872277074984297450000000000:ℝ)],
  ![(607474745913047912547923360741793/9249872277074984297450000000000:ℝ)]]
theorem cell13_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ))
    (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell13 12 true b := by
 have heq : complementBranch cell13 12 true b = Record12518109.Bernstein.bsum 1 0 (560676079962507315246058543741793/18499744554149968594900000000000000:ℝ) cell13_complement12_1_g (83/2000:ℝ) (21/500:ℝ) (3111/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell13, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell13_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell13_complement12_1_g]
theorem cell13_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 0 b := complementReserve_pos_of_branches (cell13_complement0_0 hb hν) (cell13_complement0_1 hb hν)
theorem cell13_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 1 b := complementReserve_pos_of_branches (cell13_complement1_0 hb hν) (cell13_complement1_1 hb hν)
theorem cell13_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 2 b := complementReserve_pos_of_branches (cell13_complement2_0 hb hν) (cell13_complement2_1 hb hν)
theorem cell13_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 3 b := complementReserve_pos_of_branches (cell13_complement3_0 hb hν) (cell13_complement3_1 hb hν)
theorem cell13_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 4 b := complementReserve_pos_of_branches (cell13_complement4_0 hb hν) (cell13_complement4_1 hb hν)
theorem cell13_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 5 b := complementReserve_pos_of_branches (cell13_complement5_0 hb hν) (cell13_complement5_1 hb hν)
theorem cell13_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 6 b := complementReserve_pos_of_branches (cell13_complement6_0 hb hν) (cell13_complement6_1 hb hν)
theorem cell13_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 7 b := complementReserve_pos_of_branches (cell13_complement7_0 hb hν) (cell13_complement7_1 hb hν)
theorem cell13_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 8 b := complementReserve_pos_of_branches (cell13_complement8_0 hb hν) (cell13_complement8_1 hb hν)
theorem cell13_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 9 b := complementReserve_pos_of_branches (cell13_complement9_0 hb hν) (cell13_complement9_1 hb hν)
theorem cell13_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 10 b := complementReserve_pos_of_branches (cell13_complement10_0 hb hν) (cell13_complement10_1 hb hν)
theorem cell13_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 11 b := complementReserve_pos_of_branches (cell13_complement11_0 hb hν) (cell13_complement11_1 hb hν)
theorem cell13_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (hν : ν ∈ Set.Icc (3111/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell13 12 b := complementReserve_pos_of_branches (cell13_complement12_0 hb hν) (cell13_complement12_1 hb hν)
theorem cell13_all_domains {b : ℝ} (hb : b ∈ Set.Icc (83/2000:ℝ) (21/500:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell13 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell13_domain0_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain0_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain1_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain1_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain2_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain2_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain3_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain3_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain4_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain4_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain5_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain5_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain6_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain6_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain7_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain7_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell13_domain8_0 (ν := (3111/5000:ℝ)) hb (by norm_num)
   | true => exact cell13_domain8_1 (ν := (3111/5000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
