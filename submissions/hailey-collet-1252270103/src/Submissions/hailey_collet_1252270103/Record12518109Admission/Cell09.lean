/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell9 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (3129/5000:ℝ), (39/1000:ℝ), (1/25:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (109/20000:ℝ), (1/25:ℝ)⟩
def cell9_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(2325946617044513283823007569245575803964605687/44090324316327357762375123562500000000:ℝ), (43264336946626670331348836305451916630386173063/11022581079081839440593780890625000000:ℝ), (82943308623370786748547825334192037795247894313/7348387386054559627062520593750000000:ℝ), (119733338565511432765165347639161206651113519313/11022581079081839440593780890625000000:ℝ), (152502305064631339849425520184443960328847894313/44090324316327357762375123562500000000:ℝ)],
  ![(929594540612201604076578785395794580863535229/14696774772109119254125041187500000000:ℝ), (14372518022763453741545793977365615700545391021/3674193693027279813531260296875000000:ℝ), (27414729009583020169590879745458025098415964771/2449462462018186542354173531250000000:ℝ), (39515782722348732330216736519292667842037839771/3674193693027279813531260296875000000:ℝ), (50299802396933070407201686062457882609615964771/14696774772109119254125041187500000000:ℝ)]]
theorem cell9_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell9 2 b ν := by
 have heq : highRegular cell9 2 b ν = Record12518109.Bernstein.bsum 1 4 (2325946617044513283823007569245575803964605687/185292102826836601562500000000000000000000000:ℝ) cell9_regular2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_regular2_g]
def cell9_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(2889729806439781321962830973537448979530687/44090324316327357762375123562500000000:ℝ), (40363745166515216356105791801227081692964998063/11022581079081839440593780890625000000:ℝ), (79979152939561884150341657542934404118982969313/7348387386054559627062520593750000000:ℝ), (117256909610266016136386530190364739146723594313/11022581079081839440593780890625000000:ℝ), (150999521024442506873493866827867365871332969313/44090324316327357762375123562500000000:ℝ)],
  ![(324679861742387554628812800139898622836743/4898924924036373084708347062500000000:ℝ), (491852635337777343956246420704024069928580223/136081247889899252353009640625000000:ℝ), (8776152398037592218264685984839326846553663257/816487487339395514118057843750000000:ℝ), (12872386896323477253932731686165309557969288257/1224731231009093271177086765625000000:ℝ), (5527542742496708390610399180654520495234554419/1632974974678791028236115687500000000:ℝ)]]
theorem cell9_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell9 3 b ν := by
 have heq : highRegular cell9 3 b ν = Record12518109.Bernstein.bsum 1 4 (2889729806439781321962830973537448979530687/185292102826836601562500000000000000000000000:ℝ) cell9_regular3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_regular3_g]
def cell9_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(5848695203110408131912102922448493306249310229/14696774772109119254125041187500000000:ℝ), (15250491492953572127284350793217797053231866021/3674193693027279813531260296875000000:ℝ), (25077672740566009001550013279432632407696189771/2449462462018186542354173531250000000:ℝ), (35073647522116716374909934655876333041943064771/3674193693027279813531260296875000000:ℝ), (45027468318421417474983380350106440387646189771/14696774772109119254125041187500000000:ℝ)],
  ![(16499114814827438971627174372193457157373930687/44090324316327357762375123562500000000:ℝ), (44380124943735713943523522246188759130945598063/11022581079081839440593780890625000000:ℝ), (73582979731309351509628866947042434723088569313/7348387386054559627062520593750000000:ℝ), (103333552292687111124260614421502046000829194313/11022581079081839440593780890625000000:ℝ), (132994995130524138345533731787624008662938569313/44090324316327357762375123562500000000:ℝ)]]
theorem cell9_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highRegular cell9 4 b ν := by
 have heq : highRegular cell9 4 b ν = Record12518109.Bernstein.bsum 1 4 (16499114814827438971627174372193457157373930687/185292102826836601562500000000000000000000000:ℝ) cell9_regular4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_regular4_g]
def cell9_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(214866005783302034487345355061959200391/8689077790071281813760750000000000:ℝ), (302788516033959383897032010378927779609/4344538895035640906880375000000000:ℝ), (396907539513525042176367648881725924609/8689077790071281813760750000000000:ℝ)],
  ![(23507982857108926165247895470686355599/965453087785697979306750000000000:ℝ), (11076892103894543110522846033293621467/160908847964282996551125000000000:ℝ), (43639248222336804943889728695191769401/965453087785697979306750000000000:ℝ)]]
theorem cell9_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 0 false b ν := by
 have heq : highBranch cell9 0 false b ν = Record12518109.Bernstein.bsum 1 2 (211571845713980335487231059236177200391/563287992593583268750000000000000000000:ℝ) cell9_exceptional0_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional0_0_g]
def cell9_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(2681260890135714567141493164525941605226951/108564234268413952075064730750000000000:ℝ), (3780012602911315824112632008193132789778049/54282117134206976037532365375000000000:ℝ), (4956185617473307128204121797445140512398049/108564234268413952075064730750000000000:ℝ)],
  ![(7920598463346477497419449073059688109680853/325692702805241856225194192250000000000:ℝ), (11201165983532907605640097753792633369334147/162846351402620928112597096125000000000:ℝ), (14713112543242042158101693289251046537194147/325692702805241856225194192250000000000:ℝ)]]
theorem cell9_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 0 true b ν := by
 have heq : highBranch cell9 0 true b ν = Record12518109.Bernstein.bsum 1 2 (7920598463346477497419449073059688109680853/21113723826385281662556250000000000000000000:ℝ) cell9_exceptional0_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional0_1_g]
theorem cell9_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 0 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional0_0 hb hν) (cell9_exceptional0_1 hb hν)
def cell9_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(1531923003859641825267251929327622389/457319883687962200724250000000000:ℝ), (22467985255951982496359475206004422611/228659941843981100362125000000000:ℝ), (43730179783250023634275329176672252611/457319883687962200724250000000000:ℝ)],
  ![(161202105593868188225894317727735821/50813320409773577858250000000000:ℝ), (825464544192141808477318260592756393/8468886734962262976375000000000:ℝ), (4827684025668375949269623033519139179/50813320409773577858250000000000:ℝ)]]
theorem cell9_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 1 false b ν := by
 have heq : highBranch cell9 1 false b ν = Record12518109.Bernstein.bsum 1 2 (1450818950344813694033048859549622389/29646736452293856250000000000000000000:ℝ) cell9_exceptional1_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional1_0_g]
def cell9_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(18964219381603187349625775913388881360629/5713907066758629056582354250000000000:ℝ), (280557863120371279369039423742678247159371/2856953533379314528291177125000000000:ℝ), (546226312216317794921103121339589536014371/5713907066758629056582354250000000000:ℝ)],
  ![(53867939897319524448786416703027870081887/17141721200275887169747062750000000000:ℝ), (834924858653778877547059235632349741478113/8570860600137943584873531375000000000:ℝ), (1628159621595643727710645046915643608043113/17141721200275887169747062750000000000:ℝ)]]
theorem cell9_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 1 true b ν := by
 have heq : highBranch cell9 1 true b ν = Record12518109.Bernstein.bsum 1 2 (53867939897319524448786416703027870081887/1111248622441330613818750000000000000000000:ℝ) cell9_exceptional1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional1_1_g]
theorem cell9_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 1 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional1_0 hb hν) (cell9_exceptional1_1 hb hν)
def cell9_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(3307311216934518398116940693550213713/76219980614660366787375000000000:ℝ), (1758294534269510984612200996440331/30487992245864146714950000000:ℝ), (1556100066694733459697802007197/97561575186765269487840000:ℝ)],
  ![(3274812723513431960191573323587213713/76219980614660366787375000000000:ℝ), (1736494113264507846290387540440331/30487992245864146714950000000:ℝ), (1527229167586973231183408007197/97561575186765269487840000:ℝ)]]
theorem cell9_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 2 false b ν := by
 have heq : highBranch cell9 2 false b ν = Record12518109.Bernstein.bsum 1 2 (4581687502760919693550224021591/18973911329468068000000000000000:ℝ) cell9_exceptional2_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional2_0_g]
def cell9_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(371622631776901654706784356103984371513137/8570860600137943584873531375000000000:ℝ), (197507300207588665267679838855960530249/3428344240055177433949412550000000:ℝ), (174666123682903687341556384900124873/10970701568176567788638120160000:ℝ)],
  ![(367975861185397038469995082032689984513137/8570860600137943584873531375000000000:ℝ), (195061783815098591909646047055186530249/3428344240055177433949412550000000:ℝ), (171428766032400026187817021954124873/10970701568176567788638120160000:ℝ)]]
theorem cell9_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 2 true b ν := by
 have heq : highBranch cell9 2 true b ν = Record12518109.Bernstein.bsum 1 2 (171428766032400026187817021954124873/711199118362451592844000000000000000:ℝ) cell9_exceptional2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional2_1_g]
theorem cell9_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 2 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional2_0 hb hν) (cell9_exceptional2_1 hb hν)
def cell9_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(181486144663653414909283070061959200391/8689077790071281813760750000000000:ℝ), (262776932370388088924819295378927779609/4344538895035640906880375000000000:ℝ), (350611796417633923082554933881725924609/8689077790071281813760750000000000:ℝ)],
  ![(178191984594331715909168774236177200391/8689077790071281813760750000000000:ℝ), (259064503141581369011904127898927779609/4344538895035640906880375000000000:ℝ), (346457490905140125401194843256725924609/8689077790071281813760750000000000:ℝ)]]
theorem cell9_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 3 false b ν := by
 have heq : highBranch cell9 3 false b ν = Record12518109.Bernstein.bsum 1 2 (178191984594331715909168774236177200391/563287992593583268750000000000000000000:ℝ) cell9_exceptional3_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional3_0_g]
def cell9_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(6792605336059354493779970864922824815680853/325692702805241856225194192250000000000:ℝ), (9840283618272304622894446828234398369334147/162846351402620928112597096125000000000:ℝ), (13133253513956634567618983395990421537194147/325692702805241856225194192250000000000:ℝ)],
  ![(741046792110965365530548938267187567742317/36188078089471317358354910250000000000:ℝ), (1077934643674584972910738728605292596592683/18094039044735658679177455125000000000:ℝ), (1441978800530972815678701254767338504132683/36188078089471317358354910250000000000:ℝ)]]
theorem cell9_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 3 true b ν := by
 have heq : highBranch cell9 3 true b ν = Record12518109.Bernstein.bsum 1 2 (6669421128998688289774940444404688109680853/21113723826385281662556250000000000000000000:ℝ) cell9_exceptional3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional3_1_g]
theorem cell9_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 3 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional3_0 hb hν) (cell9_exceptional3_1 hb hν)
def cell9_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(181914768877989229500486929327622389/457319883687962200724250000000000:ℝ), (20087099942094714752344990206004422611/228659941843981100362125000000000:ℝ), (40336710185864659230042094176672252611/457319883687962200724250000000000:ℝ)],
  ![(100810715363161098266283859549622389/457319883687962200724250000000000:ℝ), (19906657379330561084873108036004422611/228659941843981100362125000000000:ℝ), (40055686633630019139193372301672252611/457319883687962200724250000000000:ℝ)]]
theorem cell9_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 4 false b ν := by
 have heq : highBranch cell9 4 false b ν = Record12518109.Bernstein.bsum 1 2 (100810715363161098266283859549622389/29646736452293856250000000000000000000:ℝ) cell9_exceptional4_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional4_0_g]
def cell9_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(6290299472992277801751675245166644081887/17141721200275887169747062750000000000:ℝ), (752430865141801871258223329973034741478113/8570860600137943584873531375000000000:ℝ), (1511481515730157770799435016513768608043113/17141721200275887169747062750000000000:ℝ)],
  ![(1088527075167413400553588069342623360629/5713907066758629056582354250000000000:ℝ), (248560711478155636899388098125783247159371/2856953533379314528291177125000000000:ℝ), (500320733558949371248923566470214536014371/5713907066758629056582354250000000000:ℝ)]]
theorem cell9_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 4 true b ν := by
 have heq : highBranch cell9 4 true b ν = Record12518109.Bernstein.bsum 1 2 (3265581225502240201660764208027870081887/1111248622441330613818750000000000000000000:ℝ) cell9_exceptional4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional4_1_g]
theorem cell9_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 4 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional4_0 hb hν) (cell9_exceptional4_1 hb hν)
def cell9_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(10357968248038779342794898231390122389/457319883687962200724250000000000:ℝ), (110080470187299300587702717239339443925181/2142772315019946891493473375000000000:ℝ), (130252756031913997592840248505005710467681/4285544630039893782986946750000000000:ℝ)],
  ![(377539432715954370212979450430078607/16937773469924525952750000000000:ℝ), (12053049037764641027572885256954938213909/238085812779994099054830375000000000:ℝ), (14284026741704860601495834541875634496409/476171625559988198109660750000000000:ℝ)]]
theorem cell9_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 5 false b ν := by
 have heq : highBranch cell9 5 false b ν = Record12518109.Bernstein.bsum 1 2 (10193564683330767995750445161612122389/29646736452293856250000000000000000000:ℝ) cell9_exceptional5_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional5_0_g]
def cell9_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(5619120464237335849541537595367758428723/248430742032983872025319750000000000:ℝ), (59732143601499729772525938087633155431939267/1164022241795545932374635688625000000000:ℝ), (70695059280448635094561296673924925033561767/2328044483591091864749271377250000000000:ℝ)],
  ![(381572278206832049540059582293236557581887/17141721200275887169747062750000000000:ℝ), (4061570249081305993337904527907609564803809423/80317534683892669333849862515125000000000:ℝ), (4814502523906687879961020053975122952315761923/160635069367785338667699725030250000000000:ℝ)]]
theorem cell9_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 5 true b ν := by
 have heq : highBranch cell9 5 true b ν = Record12518109.Bernstein.bsum 1 2 (381572278206832049540059582293236557581887/1111248622441330613818750000000000000000000:ℝ) cell9_exceptional5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional5_1_g]
theorem cell9_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 5 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional5_0 hb hν) (cell9_exceptional5_1 hb hν)
def cell9_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(3307311216934518398116940693550213713/76219980614660366787375000000000:ℝ), (1758294534269510984612200996440331/30487992245864146714950000000:ℝ), (1556100066694733459697802007197/97561575186765269487840000:ℝ)],
  ![(3274812723513431960191573323587213713/76219980614660366787375000000000:ℝ), (1736494113264507846290387540440331/30487992245864146714950000000:ℝ), (1527229167586973231183408007197/97561575186765269487840000:ℝ)]]
theorem cell9_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 6 false b ν := by
 have heq : highBranch cell9 6 false b ν = Record12518109.Bernstein.bsum 1 2 (4581687502760919693550224021591/18973911329468068000000000000000:ℝ) cell9_exceptional6_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional6_0_g]
def cell9_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(371622631776901654706784356103984371513137/8570860600137943584873531375000000000:ℝ), (197507300207588665267679838855960530249/3428344240055177433949412550000000:ℝ), (174666123682903687341556384900124873/10970701568176567788638120160000:ℝ)],
  ![(367975861185397038469995082032689984513137/8570860600137943584873531375000000000:ℝ), (195061783815098591909646047055186530249/3428344240055177433949412550000000:ℝ), (171428766032400026187817021954124873/10970701568176567788638120160000:ℝ)]]
theorem cell9_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 6 true b ν := by
 have heq : highBranch cell9 6 true b ν = Record12518109.Bernstein.bsum 1 2 (171428766032400026187817021954124873/711199118362451592844000000000000000:ℝ) cell9_exceptional6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional6_1_g]
theorem cell9_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 6 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional6_0 hb hν) (cell9_exceptional6_1 hb hν)
def cell9_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(8640696241886110455803133231390122389/457319883687962200724250000000000:ℝ), (91985902910651033704649773489339443925181/2142772315019946891493473375000000000:ℝ), (110156177448274123966734190820005710467681/4285544630039893782986946750000000000:ℝ)],
  ![(2825430892392699702919560053870707463/152439961229320733574750000000000:ℝ), (30127624687744500788367674520864814641727/714257438339982297164491125000000000:ℝ), (36153220697234623929118817730626903489227/1428514876679964594328982250000000000:ℝ)]]
theorem cell9_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 7 false b ν := by
 have heq : highBranch cell9 7 false b ν = Record12518109.Bernstein.bsum 1 2 (8476292677178099108758680161612122389/29646736452293856250000000000000000000:ℝ) cell9_exceptional7_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional7_0_g]
def cell9_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(35927867269528409525250418509486147953543/1904635688919543018860784750000000000:ℝ), (382586582585874929636312915273937524978201047/8924170520432518814872206946125000000000:ℝ), (458297670588931382044155123365996091923973547/17848341040865037629744413892250000000000:ℝ)],
  ![(317203771600211561648947254798236557581887/17141721200275887169747062750000000000:ℝ), (3383331583850699005760431037326359564803809423/80317534683892669333849862515125000000000:ℝ), (4061222468856114496833686693768267952315761923/160635069367785338667699725030250000000000:ℝ)]]
theorem cell9_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highBranch cell9 7 true b ν := by
 have heq : highBranch cell9 7 true b ν = Record12518109.Bernstein.bsum 1 2 (317203771600211561648947254798236557581887/1111248622441330613818750000000000000000000:ℝ) cell9_exceptional7_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_exceptional7_1_g]
theorem cell9_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
 (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell9 7 b ν :=
 highExceptional_pos_of_branches (cell9_exceptional7_0 hb hν) (cell9_exceptional7_1 hb hν)
def cell9_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(72243685214902033883629632059/17779977959061289821100000000000:ℝ)],
  ![(268231183747804515506371632059/17779977959061289821100000000000:ℝ)]]
theorem cell9_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 0 false b := by
 have heq : domainBranch cell9 0 false b = Record12518109.Bernstein.bsum 1 0 (72243685214902033883629632059/17779977959061289821100000000000000:ℝ) cell9_domain0_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain0_0_g]
def cell9_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(72243685214902033883629632059/17779977959061289821100000000000:ℝ)],
  ![(268231183747804515506371632059/17779977959061289821100000000000:ℝ)]]
theorem cell9_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 0 true b := by
 have heq : domainBranch cell9 0 true b = Record12518109.Bernstein.bsum 1 0 (72243685214902033883629632059/17779977959061289821100000000000000:ℝ) cell9_domain0_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain0_1_g]
def cell9_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(642790559384403309507928451685649/94869556647340340000000000000000:ℝ)],
  ![(603184060271503895984339359685649/94869556647340340000000000000000:ℝ)]]
theorem cell9_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 1 false b := by
 have heq : domainBranch cell9 1 false b = Record12518109.Bernstein.bsum 1 0 (603184060271503895984339359685649/94869556647340340000000000000000000:ℝ) cell9_domain1_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain1_0_g]
def cell9_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(1161347081721359443486714899724443/94869556647340340000000000000000:ℝ)],
  ![(1121740582608460029963125807724443/94869556647340340000000000000000:ℝ)]]
theorem cell9_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 1 true b := by
 have heq : domainBranch cell9 1 true b = Record12518109.Bernstein.bsum 1 0 (1121740582608460029963125807724443/94869556647340340000000000000000000:ℝ) cell9_domain1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain1_1_g]
def cell9_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(104610889774399894499623595246493/9486955664734034000000000000000:ℝ)],
  ![(106733172524982041863995351246493/9486955664734034000000000000000:ℝ)]]
theorem cell9_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 2 false b := by
 have heq : domainBranch cell9 2 false b = Record12518109.Bernstein.bsum 1 0 (104610889774399894499623595246493/9486955664734034000000000000000000:ℝ) cell9_domain2_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain2_0_g]
def cell9_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(55240011723669487381839108678751/9486955664734034000000000000000:ℝ)],
  ![(57362294474251634746210864678751/9486955664734034000000000000000:ℝ)]]
theorem cell9_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 2 true b := by
 have heq : domainBranch cell9 2 true b = Record12518109.Bernstein.bsum 1 0 (55240011723669487381839108678751/9486955664734034000000000000000000:ℝ) cell9_domain2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain2_1_g]
def cell9_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(777277742396750861266423285081/94869556647340340000000000000:ℝ)],
  ![(1245745071871518588306259285081/94869556647340340000000000000:ℝ)]]
theorem cell9_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 3 false b := by
 have heq : domainBranch cell9 3 false b = Record12518109.Bernstein.bsum 1 0 (777277742396750861266423285081/94869556647340340000000000000000:ℝ) cell9_domain3_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain3_0_g]
def cell9_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(777277742396750861266423285081/94869556647340340000000000000:ℝ)],
  ![(1245745071871518588306259285081/94869556647340340000000000000:ℝ)]]
theorem cell9_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 3 true b := by
 have heq : domainBranch cell9 3 true b = Record12518109.Bernstein.bsum 1 0 (777277742396750861266423285081/94869556647340340000000000000000:ℝ) cell9_domain3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain3_1_g]
def cell9_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(2786262380921529653504721/296467364522938562500000:ℝ)],
  ![(2140738238643067535504721/296467364522938562500000:ℝ)]]
theorem cell9_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 4 false b := by
 have heq : domainBranch cell9 4 false b = Record12518109.Bernstein.bsum 1 0 (2140738238643067535504721/296467364522938562500000000:ℝ) cell9_domain4_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain4_0_g]
def cell9_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(2786262380921529653504721/296467364522938562500000:ℝ)],
  ![(2140738238643067535504721/296467364522938562500000:ℝ)]]
theorem cell9_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 4 true b := by
 have heq : domainBranch cell9 4 true b = Record12518109.Bernstein.bsum 1 0 (2140738238643067535504721/296467364522938562500000000:ℝ) cell9_domain4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain4_1_g]
def cell9_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(28290982314169970601413447820311/4743477832367017000000000000000:ℝ)],
  ![(26347186730555153134490859820311/4743477832367017000000000000000:ℝ)]]
theorem cell9_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 5 false b := by
 have heq : domainBranch cell9 5 false b = Record12518109.Bernstein.bsum 1 0 (26347186730555153134490859820311/4743477832367017000000000000000000:ℝ) cell9_domain5_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain5_0_g]
def cell9_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(54169434594016952343185746121277/4743477832367017000000000000000:ℝ)],
  ![(52225639010402134876263158121277/4743477832367017000000000000000:ℝ)]]
theorem cell9_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 5 true b := by
 have heq : domainBranch cell9 5 true b = Record12518109.Bernstein.bsum 1 0 (52225639010402134876263158121277/4743477832367017000000000000000000:ℝ) cell9_domain5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain5_1_g]
def cell9_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(726242605271739970181738043328609887/9649139915300494678247000000000000:ℝ)],
  ![(702691857617783934919759235572609887/9649139915300494678247000000000000:ℝ)]]
theorem cell9_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 6 false b := by
 have heq : domainBranch cell9 6 false b = Record12518109.Bernstein.bsum 1 0 (702691857617783934919759235572609887/9649139915300494678247000000000000000:ℝ) cell9_domain6_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain6_0_g]
def cell9_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(705782835095415764126722172642560869/9649139915300494678247000000000000:ℝ)],
  ![(682232087441459728864743364886560869/9649139915300494678247000000000000:ℝ)]]
theorem cell9_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 6 true b := by
 have heq : domainBranch cell9 6 true b = Record12518109.Bernstein.bsum 1 0 (682232087441459728864743364886560869/9649139915300494678247000000000000000:ℝ) cell9_domain6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain6_1_g]
def cell9_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(57122964985458090840039041829/2371738916183508500000000000:ℝ)],
  ![(69948462442528429649041041829/2371738916183508500000000000:ℝ)]]
theorem cell9_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 7 false b := by
 have heq : domainBranch cell9 7 false b = Record12518109.Bernstein.bsum 1 0 (57122964985458090840039041829/2371738916183508500000000000000:ℝ) cell9_domain7_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain7_0_g]
def cell9_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(57122964985458090840039041829/2371738916183508500000000000:ℝ)],
  ![(69948462442528429649041041829/2371738916183508500000000000:ℝ)]]
theorem cell9_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 7 true b := by
 have heq : domainBranch cell9 7 true b = Record12518109.Bernstein.bsum 1 0 (57122964985458090840039041829/2371738916183508500000000000000:ℝ) cell9_domain7_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain7_1_g]
def cell9_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(18366415185577268988239348425473/474347783236701700000000000000:ℝ)],
  ![(17629288155063495796205264425473/474347783236701700000000000000:ℝ)]]
theorem cell9_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 8 false b := by
 have heq : domainBranch cell9 8 false b = Record12518109.Bernstein.bsum 1 0 (17629288155063495796205264425473/474347783236701700000000000000000:ℝ) cell9_domain8_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain8_0_g]
def cell9_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(19362730967393804016825590325611/474347783236701700000000000000:ℝ)],
  ![(18625603936880030824791506325611/474347783236701700000000000000:ℝ)]]
theorem cell9_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell9 8 true b := by
 have heq : domainBranch cell9 8 true b = Record12518109.Bernstein.bsum 1 0 (18625603936880030824791506325611/474347783236701700000000000000000:ℝ) cell9_domain8_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_domain8_1_g]
def cell9_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(342007353158714405833549/94869556647340340000000:ℝ)],
  ![(413732257856321307833549/94869556647340340000000:ℝ)]]
theorem cell9_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 0 b := by
 have heq : ordinary cell9 0 b = Record12518109.Bernstein.bsum 1 0 (342007353158714405833549/94869556647340340000000000:ℝ) cell9_ordinary0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary0_g]
def cell9_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(978956430517073935499353/284608669942021020000000:ℝ)],
  ![(763781716424253229499353/284608669942021020000000:ℝ)]]
theorem cell9_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 1 b := by
 have heq : ordinary cell9 1 b = Record12518109.Bernstein.bsum 1 0 (763781716424253229499353/284608669942021020000000000:ℝ) cell9_ordinary1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary1_g]
def cell9_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(45339389372203224012131689/94869556647340340000000:ℝ)],
  ![(44909039944017582600131689/94869556647340340000000:ℝ)]]
theorem cell9_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 2 b := by
 have heq : ordinary cell9 2 b = Record12518109.Bernstein.bsum 1 0 (44909039944017582600131689/94869556647340340000000000:ℝ) cell9_ordinary2_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary2_g]
def cell9_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(389999989/20000000:ℝ)],
  ![(409999989/20000000:ℝ)]]
theorem cell9_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 3 b := by
 have heq : ordinary cell9 3 b = Record12518109.Bernstein.bsum 1 0 (389999989/20000000000:ℝ) cell9_ordinary3_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary3_g]
def cell9_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(41992865865824805830706063/94869556647340340000000:ℝ)],
  ![(41372777324344483738706063/94869556647340340000000:ℝ)]]
theorem cell9_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 4 b := by
 have heq : ordinary cell9 4 b = Record12518109.Bernstein.bsum 1 0 (41372777324344483738706063/94869556647340340000000000:ℝ) cell9_ordinary4_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary4_g]
def cell9_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(7537383773115622339/1524951625060000000000000:ℝ)],
  ![(7537383773115622339/1524951625060000000000000:ℝ)]]
theorem cell9_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < ordinary cell9 5 b := by
 have heq : ordinary cell9 5 b = Record12518109.Bernstein.bsum 1 0 (7537383773115622339/1524951625060000000000000000:ℝ) cell9_ordinary5_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_ordinary5_g]
def cell9_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(342002609680882038816549/94869556647340340000000:ℝ)],
  ![(413727514378488940816549/94869556647340340000000:ℝ)]]
theorem cell9_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 0 false b := by
 have heq : complementBranch cell9 0 false b = Record12518109.Bernstein.bsum 1 0 (342002609680882038816549/94869556647340340000000000:ℝ) cell9_complement0_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement0_0_g]
def cell9_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(61873564270342785327918609212353/17779977959061289821100000000000:ℝ)],
  ![(75381216450422417026789523212353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 0 true b := by
 have heq : complementBranch cell9 0 true b = Record12518109.Bernstein.bsum 1 0 (61873564270342785327918609212353/17779977959061289821100000000000000:ℝ) cell9_complement0_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement0_1_g]
def cell9_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(108108996596896444140373183171/2371738916183508500000000000:ℝ)],
  ![(105372869616519543274031183171/2371738916183508500000000000:ℝ)]]
theorem cell9_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 1 false b := by
 have heq : complementBranch cell9 1 false b = Record12518109.Bernstein.bsum 1 0 (105372869616519543274031183171/2371738916183508500000000000000:ℝ) cell9_complement1_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement1_0_g]
def cell9_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(2020485961205513360213915565842679/44449944897653224552750000000000:ℝ)],
  ![(1969370160318223758028719257842679/44449944897653224552750000000000:ℝ)]]
theorem cell9_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 1 true b := by
 have heq : complementBranch cell9 1 true b = Record12518109.Bernstein.bsum 1 0 (1969370160318223758028719257842679/44449944897653224552750000000000000:ℝ) cell9_complement1_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement1_1_g]
def cell9_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(77494506515905348657018283171/2371738916183508500000000000:ℝ)],
  ![(67585889065767757590676283171/2371738916183508500000000000:ℝ)]]
theorem cell9_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 2 false b := by
 have heq : complementBranch cell9 2 false b = Record12518109.Bernstein.bsum 1 0 (67585889065767757590676283171/2371738916183508500000000000000:ℝ) cell9_complement2_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement2_0_g]
def cell9_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(1446724495352618744212619707492679/44449944897653224552750000000000:ℝ)],
  ![(1261185464326309166644123399492679/44449944897653224552750000000000:ℝ)]]
theorem cell9_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 2 true b := by
 have heq : complementBranch cell9 2 true b = Record12518109.Bernstein.bsum 1 0 (1261185464326309166644123399492679/44449944897653224552750000000000000:ℝ) cell9_complement2_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement2_1_g]
def cell9_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(92045229955309133011211908171/2371738916183508500000000000:ℝ)],
  ![(91102225592372404694869908171/2371738916183508500000000000:ℝ)]]
theorem cell9_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 3 false b := by
 have heq : complementBranch cell9 3 false b = Record12518109.Bernstein.bsum 1 0 (91102225592372404694869908171/2371738916183508500000000000000:ℝ) cell9_complement3_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement3_0_g]
def cell9_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1719426878692204768686739530430179/44449944897653224552750000000000:ℝ)],
  ![(1701916885339670160347368222430179/44449944897653224552750000000000:ℝ)]]
theorem cell9_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 3 true b := by
 have heq : complementBranch cell9 3 true b = Record12518109.Bernstein.bsum 1 0 (1701916885339670160347368222430179/44449944897653224552750000000000000:ℝ) cell9_complement3_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement3_1_g]
def cell9_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(88218418695185246075792545671/2371738916183508500000000000:ℝ)],
  ![(86378853023528431484450545671/2371738916183508500000000000:ℝ)]]
theorem cell9_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 4 false b := by
 have heq : complementBranch cell9 4 false b = Record12518109.Bernstein.bsum 1 0 (86378853023528431484450545671/2371738916183508500000000000000:ℝ) cell9_complement4_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement4_0_g]
def cell9_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(1647706695460592941686577548136429/44449944897653224552750000000000:ℝ)],
  ![(1613393798340680836424293740136429/44449944897653224552750000000000:ℝ)]]
theorem cell9_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 4 true b := by
 have heq : complementBranch cell9 4 true b = Record12518109.Bernstein.bsum 1 0 (1613393798340680836424293740136429/44449944897653224552750000000000000:ℝ) cell9_complement4_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement4_1_g]
def cell9_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(3953871/100000:ℝ)],
  ![(140163/4000:ℝ)]]
theorem cell9_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 5 false b := by
 have heq : complementBranch cell9 5 false b = Record12518109.Bernstein.bsum 1 0 (140163/4000000:ℝ) cell9_complement5_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement5_0_g]
def cell9_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(700741872923627671405269402377353/17779977959061289821100000000000:ℝ)],
  ![(620833572429065986402095360377353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 5 true b := by
 have heq : complementBranch cell9 5 true b = Record12518109.Bernstein.bsum 1 0 (620833572429065986402095360377353/17779977959061289821100000000000000:ℝ) cell9_complement5_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement5_1_g]
def cell9_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(9715675531770333449148157/94869556647340340000000:ℝ)],
  ![(9213601198887085135148157/94869556647340340000000:ℝ)]]
theorem cell9_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 6 false b := by
 have heq : complementBranch cell9 6 false b = Record12518109.Bernstein.bsum 1 0 (9213601198887085135148157/94869556647340340000000000:ℝ) cell9_complement6_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement6_0_g]
def cell9_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(1818607810380648504314946465532353/17779977959061289821100000000000:ℝ)],
  ![(1724576878449512155707177379532353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 6 true b := by
 have heq : complementBranch cell9 6 true b = Record12518109.Bernstein.bsum 1 0 (1724576878449512155707177379532353/17779977959061289821100000000000000:ℝ) cell9_complement6_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement6_1_g]
def cell9_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(4423543258065791290595661057/4743477832367017000000000000:ℝ)],
  ![(16578397526699573655444983171/14230433497101051000000000000:ℝ)]]
theorem cell9_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 7 false b := by
 have heq : complementBranch cell9 7 false b = Record12518109.Bernstein.bsum 1 0 (4423543258065791290595661057/4743477832367017000000000000000:ℝ) cell9_complement7_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement7_0_g]
def cell9_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(143579123712082835176547947173061/177799779590612898211000000000000:ℝ)],
  ![(556682304788617484836724075519183/533399338771838694633000000000000:ℝ)]]
theorem cell9_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 7 true b := by
 have heq : complementBranch cell9 7 true b = Record12518109.Bernstein.bsum 1 0 (143579123712082835176547947173061/177799779590612898211000000000000000:ℝ) cell9_complement7_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement7_1_g]
def cell9_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(72825013889808672457305461057/4743477832367017000000000000:ℝ)],
  ![(264817752240492358355574383171/14230433497101051000000000000:ℝ)]]
theorem cell9_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 8 false b := by
 have heq : complementBranch cell9 8 false b = Record12518109.Bernstein.bsum 1 0 (72825013889808672457305461057/4743477832367017000000000000000:ℝ) cell9_complement8_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement8_0_g]
def cell9_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(2707471447401701249948331380573061/177799779590612898211000000000000:ℝ)],
  ![(9861438037525712433751674375719183/533399338771838694633000000000000:ℝ)]]
theorem cell9_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 8 true b := by
 have heq : complementBranch cell9 8 true b = Record12518109.Bernstein.bsum 1 0 (2707471447401701249948331380573061/177799779590612898211000000000000000:ℝ) cell9_complement8_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement8_1_g]
def cell9_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(89925381547744392748982911057/4743477832367017000000000000:ℝ)],
  ![(326877590918940554530606733171/14230433497101051000000000000:ℝ)]]
theorem cell9_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 9 false b := by
 have heq : complementBranch cell9 9 false b = Record12518109.Bernstein.bsum 1 0 (89925381547744392748982911057/4743477832367017000000000000000:ℝ) cell9_complement9_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement9_0_g]
def cell9_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(3348444528324105853641277238923061/177799779590612898211000000000000:ℝ)],
  ![(12187626970709986170980411950769183/533399338771838694633000000000000:ℝ)]]
theorem cell9_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 9 true b := by
 have heq : complementBranch cell9 9 true b = Record12518109.Bernstein.bsum 1 0 (3348444528324105853641277238923061/177799779590612898211000000000000000:ℝ) cell9_complement9_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement9_1_g]
def cell9_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(342002609680882038816549/94869556647340340000000:ℝ)],
  ![(413727514378488940816549/94869556647340340000000:ℝ)]]
theorem cell9_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 10 false b := by
 have heq : complementBranch cell9 10 false b = Record12518109.Bernstein.bsum 1 0 (342002609680882038816549/94869556647340340000000000:ℝ) cell9_complement10_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement10_0_g]
def cell9_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(61873564270342785327918609212353/17779977959061289821100000000000:ℝ)],
  ![(75381216450422417026789523212353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 10 true b := by
 have heq : complementBranch cell9 10 true b = Record12518109.Bernstein.bsum 1 0 (61873564270342785327918609212353/17779977959061289821100000000000000:ℝ) cell9_complement10_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement10_1_g]
def cell9_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(1026019687737227033992147/47434778323670170000000:ℝ)],
  ![(1241194401830047739992147/47434778323670170000000:ℝ)]]
theorem cell9_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 11 false b := by
 have heq : complementBranch cell9 11 false b = Record12518109.Bernstein.bsum 1 0 (1026019687737227033992147/47434778323670170000000000:ℝ) cell9_complement11_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement11_0_g]
def cell9_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(382360104731545087174391538387353/17779977959061289821100000000000:ℝ)],
  ![(463079371981134706564912452387353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 11 true b := by
 have heq : complementBranch cell9 11 true b = Record12518109.Bernstein.bsum 1 0 (382360104731545087174391538387353/17779977959061289821100000000000000:ℝ) cell9_complement11_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement11_1_g]
def cell9_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(2394046728633168473817843/94869556647340340000000:ℝ)],
  ![(2896121061516416787817843/94869556647340340000000:ℝ)]]
theorem cell9_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 12 false b := by
 have heq : complementBranch cell9 12 false b = Record12518109.Bernstein.bsum 1 0 (2394046728633168473817843/94869556647340340000000000:ℝ) cell9_complement12_0_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement12_0_g]
def cell9_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(446457412823785547543686124222353/17779977959061289821100000000000:ℝ)],
  ![(540619003087277164472537038222353/17779977959061289821100000000000:ℝ)]]
theorem cell9_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ))
    (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell9 12 true b := by
 have heq : complementBranch cell9 12 true b = Record12518109.Bernstein.bsum 1 0 (446457412823785547543686124222353/17779977959061289821100000000000000:ℝ) cell9_complement12_1_g (39/1000:ℝ) (1/25:ℝ) (3129/5000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell9, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell9_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell9_complement12_1_g]
theorem cell9_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 0 b := complementReserve_pos_of_branches (cell9_complement0_0 hb hν) (cell9_complement0_1 hb hν)
theorem cell9_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 1 b := complementReserve_pos_of_branches (cell9_complement1_0 hb hν) (cell9_complement1_1 hb hν)
theorem cell9_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 2 b := complementReserve_pos_of_branches (cell9_complement2_0 hb hν) (cell9_complement2_1 hb hν)
theorem cell9_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 3 b := complementReserve_pos_of_branches (cell9_complement3_0 hb hν) (cell9_complement3_1 hb hν)
theorem cell9_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 4 b := complementReserve_pos_of_branches (cell9_complement4_0 hb hν) (cell9_complement4_1 hb hν)
theorem cell9_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 5 b := complementReserve_pos_of_branches (cell9_complement5_0 hb hν) (cell9_complement5_1 hb hν)
theorem cell9_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 6 b := complementReserve_pos_of_branches (cell9_complement6_0 hb hν) (cell9_complement6_1 hb hν)
theorem cell9_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 7 b := complementReserve_pos_of_branches (cell9_complement7_0 hb hν) (cell9_complement7_1 hb hν)
theorem cell9_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 8 b := complementReserve_pos_of_branches (cell9_complement8_0 hb hν) (cell9_complement8_1 hb hν)
theorem cell9_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 9 b := complementReserve_pos_of_branches (cell9_complement9_0 hb hν) (cell9_complement9_1 hb hν)
theorem cell9_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 10 b := complementReserve_pos_of_branches (cell9_complement10_0 hb hν) (cell9_complement10_1 hb hν)
theorem cell9_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 11 b := complementReserve_pos_of_branches (cell9_complement11_0 hb hν) (cell9_complement11_1 hb hν)
theorem cell9_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (hν : ν ∈ Set.Icc (3129/5000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell9 12 b := complementReserve_pos_of_branches (cell9_complement12_0 hb hν) (cell9_complement12_1 hb hν)
theorem cell9_all_domains {b : ℝ} (hb : b ∈ Set.Icc (39/1000:ℝ) (1/25:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell9 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell9_domain0_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain0_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain1_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain1_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain2_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain2_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain3_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain3_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain4_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain4_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain5_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain5_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain6_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain6_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain7_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain7_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell9_domain8_0 (ν := (3129/5000:ℝ)) hb (by norm_num)
   | true => exact cell9_domain8_1 (ν := (3129/5000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
