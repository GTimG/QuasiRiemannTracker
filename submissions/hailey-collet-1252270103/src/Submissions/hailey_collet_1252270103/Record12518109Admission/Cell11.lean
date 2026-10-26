/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Formulas
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
def cell11 : Cell := ⟨(9763743/10000000:ℝ), (906637/250000:ℝ), (6217/10000:ℝ), (81/2000:ℝ), (41/1000:ℝ), (2/5:ℝ), (11/25:ℝ), (991173/1000000:ℝ), (2034191/500000:ℝ), (49/2000:ℝ), (7/200:ℝ), (1/4:ℝ), (12/25:ℝ), (143/25000:ℝ), (1/50:ℝ)⟩
def cell11_regular2_g : Fin 2 → Fin 5 → ℝ := ![![(276619288269606922085439714751530215207035251673/2521040237945408572944815283843750000000:ℝ), (4448713348080582606143352479124995860412184945827/630260059486352143236203820960937500000:ℝ), (8500107398230583468589775595631011200180439748327/420173372990901428824135880640625000000:ℝ), (12250646323363979640305657030524648439933589748327/630260059486352143236203820960937500000:ℝ), (15576422596272472586335522335696776269167964748327/2521040237945408572944815283843750000000:ℝ)],
  ![(328739728110088661189409236750969252880362251673/2521040237945408572944815283843750000000:ℝ), (4469302580590610684083494176012150656563434945827/630260059486352143236203820960937500000:ℝ), (8491913718951006065863028339418942462680439748327/420173372990901428824135880640625000000:ℝ), (12216908693333645156817806333970515627433589748327/630260059486352143236203820960937500000:ℝ), (15520659232455973910661691737142088769167964748327/2521040237945408572944815283843750000000:ℝ)]]
theorem cell11_regular2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell11 2 b ν := by
 have heq : highRegular cell11 2 b ν = Record12518109.Bernstein.bsum 1 4 (276619288269606922085439714751530215207035251673/18608147830484326875000000000000000000000000000:ℝ) cell11_regular2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_regular2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_regular2_g]
def cell11_regular3_g : Fin 2 → Fin 5 → ℝ := ![![(13161747195808963899445614111969604740949326673/2521040237945408572944815283843750000000:ℝ), (4132576277125700044521222220659288214036958370827/630260059486352143236203820960937500000:ℝ), (8185695117114868867259771380837325544396525673327/420173372990901428824135880640625000000:ℝ), (11996347456278945171943200306627126628524675673327/630260059486352143236203820960937500000:ℝ), (15433100776200213051217202999877352504634050673327/2521040237945408572944815283843750000000:ℝ)],
  ![(41613450397359223787673293975448103564276326673/2521040237945408572944815283843750000000:ℝ), (4133929313041492345913465938283780447688208370827/630260059486352143236203820960937500000:ℝ), (8162520220319908493869292372196506806896525673327/420173372990901428824135880640625000000:ℝ), (11951519602700481358772335347963618816024675673327/630260059486352143236203820960937500000:ℝ), (15369678016030199433737968104447665004634050673327/2521040237945408572944815283843750000000:ℝ)]]
theorem cell11_regular3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell11 3 b ν := by
 have heq : highRegular cell11 3 b ν = Record12518109.Bernstein.bsum 1 4 (13161747195808963899445614111969604740949326673/18608147830484326875000000000000000000000000000:ℝ) cell11_regular3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_regular3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_regular3_g]
def cell11_regular4_g : Fin 2 → Fin 5 → ℝ := ![![(1743774034773335521504825012388681262394746426673/2521040237945408572944815283843750000000:ℝ), (4608164082507634873089813222737767549353084270827/630260059486352143236203820960937500000:ℝ), (7616416727058067651761769611867648007969401573327/420173372990901428824135880640625000000:ℝ), (10683102805564750399843285832101047003347551573327/630260059486352143236203820960937500000:ℝ), (13738380291318476820399202927364018191956926573327/2521040237945408572944815283843750000000:ℝ)],
  ![(1719112347392540834432882602531553917418073426673/2521040237945408572944815283843750000000:ℝ), (4566571935288851834208617408456699283004334270827/630260059486352143236203820960937500000:ℝ), (7560097195235358144414034058865579270469401573327/420173372990901428824135880640625000000:ℝ), (10614063281011398819476792901562539190847551573327/630260059486352143236203820960937500000:ℝ), (13658446393995162305189038344434330691956926573327/2521040237945408572944815283843750000000:ℝ)]]
theorem cell11_regular4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highRegular cell11 4 b ν := by
 have heq : highRegular cell11 4 b ν = Record12518109.Bernstein.bsum 1 4 (1719112347392540834432882602531553917418073426673/18608147830484326875000000000000000000000000000:ℝ) cell11_regular4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_regular4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_regular4_g]
def cell11_exceptional0_0_g : Fin 2 → Fin 3 → ℝ := ![![(5278814145495856475615395943807959022641/116396536325709637537099125000000000:ℝ), (7549180825930474294140621505071654747359/58198268162854818768549562500000000:ℝ), (3328008597071805901888768258417606492453/38798845441903212512366375000000000:ℝ)],
  ![(1747183211828593578619381043232606007547/38798845441903212512366375000000000:ℝ), (7507028728791538602443389768686654747359/58198268162854818768549562500000000:ℝ), (9936643295237428056815001331502819477359/116396536325709637537099125000000000:ℝ)]]
theorem cell11_exceptional0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 0 false b ν := by
 have heq : highBranch cell11 0 false b ν = Record12518109.Bernstein.bsum 1 2 (1747183211828593578619381043232606007547/4714064117056029475000000000000000000000:ℝ) cell11_exceptional0_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional0_0_g]
def cell11_exceptional0_1_g : Fin 2 → Fin 3 → ℝ := ![![(197605916628660727731612671264026089296827603/4362891371096574343803086502375000000000:ℝ), (282723750303349397451653202330958363832757397/2181445685548287171901543251187500000000:ℝ), (374006723529082821374129889701244129093672397/4362891371096574343803086502375000000000:ℝ)],
  ![(65403743228160618177850276491038083064609201/1454297123698858114601028834125000000000:ℝ), (281145790253977363577703146952697446332757397/2181445685548287171901543251187500000000:ℝ), (372232640763184424926851780872100379093672397/4362891371096574343803086502375000000000:ℝ)]]
theorem cell11_exceptional0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 0 true b ν := by
 have heq : highBranch cell11 0 true b ν = Record12518109.Bernstein.bsum 1 2 (65403743228160618177850276491038083064609201/176697265299611152811425000000000000000000000:ℝ) cell11_exceptional0_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional0_1_g]
theorem cell11_exceptional0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 0 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional0_0 hb hν) (cell11_exceptional0_1 hb hν)
def cell11_exceptional1_0_g : Fin 2 → Fin 3 → ℝ := ![![(20586611745730680655488096026798830139/6126133490826823028268375000000000:ℝ), (187051000160334127732209767675325083287/1021022248471137171378062500000000:ℝ), (1110376141050501748527268284178702669861/6126133490826823028268375000000000:ℝ)],
  ![(19786201258167565142464582784159830139/6126133490826823028268375000000000:ℝ), (559143105423672161191083219860975249861/3063066745413411514134187500000000:ℝ), (1107138718701815261860036852928702669861/6126133490826823028268375000000000:ℝ)]]
theorem cell11_exceptional1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 1 false b ν := by
 have heq : highBranch cell11 1 false b ν = Record12518109.Bernstein.bsum 1 2 (19786201258167565142464582784159830139/744325913219373075000000000000000000000:ℝ) cell11_exceptional1_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional1_0_g]
def cell11_exceptional1_1_g : Fin 2 → Fin 3 → ℝ := ![![(757970389804146232279175308755256405425137/229625861636661807568583500125000000000:ℝ), (21020950833081908618010850189341447603039863/114812930818330903784291750062500000000:ℝ), (41608412305362026488081270138525190944074863/229625861636661807568583500125000000000:ℝ)],
  ![(728079060579280907991844721901343768425137/229625861636661807568583500125000000000:ℝ), (20945720621263088993836823290733965103039863/114812930818330903784291750062500000000:ℝ), (13829055638538642049455272838097980314691621/76541953878887269189527833375000000000:ℝ)]]
theorem cell11_exceptional1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 1 true b ν := by
 have heq : highBranch cell11 1 true b ν = Record12518109.Bernstein.bsum 1 2 (728079060579280907991844721901343768425137/27899568205201760970225000000000000000000000:ℝ) cell11_exceptional1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional1_1_g]
theorem cell11_exceptional1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 1 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional1_0 hb hν) (cell11_exceptional1_1 hb hν)
def cell11_exceptional2_0_g : Fin 2 → Fin 3 → ℝ := ![![(84325377166024278698256374129339564213/1021022248471137171378062500000000:ℝ), (16686239647173408132058115238989879/153153337270670575706709375000:ℝ), (29091809919226809174308130807029/980181358532291684522940000:ℝ)],
  ![(83948527605391819530188130159733064213/1021022248471137171378062500000000:ℝ), (16593308500245727498040193893239879/153153337270670575706709375000:ℝ), (28851716807605968787251101807029/980181358532291684522940000:ℝ)]]
theorem cell11_exceptional2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 2 false b ν := by
 have heq : highBranch cell11 2 false b ν = Record12518109.Bernstein.bsum 1 2 (28851716807605968787251101807029/119092146115099692000000000000000:ℝ) cell11_exceptional2_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional2_0_g]
def cell11_exceptional2_1_g : Fin 2 → Fin 3 → ℝ := ![![(9475002186887626023897685419520308105262637/114812930818330903784291750062500000000:ℝ), (2499066521620862823355134899759524209293/22962586163666180756858350012500000:ℝ), (1088409381365237710021242362619472777/36740137861865889210973360020000:ℝ)],
  ![(9432681059184298090151244333391989286762637/114812930818330903784291750062500000000:ℝ), (2485154505822719627987531303881777709293/22962586163666180756858350012500000:ℝ), (359808812402102729399455067580824259/12246712620621963070324453340000:ℝ)]]
theorem cell11_exceptional2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 2 true b ν := by
 have heq : highBranch cell11 2 true b ν = Record12518109.Bernstein.bsum 1 2 (359808812402102729399455067580824259/1487976970944093918412000000000000000:ℝ) cell11_exceptional2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional2_1_g]
theorem cell11_exceptional2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 2 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional2_0 hb hν) (cell11_exceptional2_1 hb hν)
def cell11_exceptional3_0_g : Fin 2 → Fin 3 → ℝ := ![![(1620846296375487755393237642102653007547/38798845441903212512366375000000000:ℝ), (370882048539983885085487080135350249861/3063066745413411514134187500000000:ℝ), (9400113101696278345570737792752819477359/116396536325709637537099125000000000:ℝ)],
  ![(4825274379116387526422460112197818022641/116396536325709637537099125000000000:ℝ), (7004606825120758124927022786186654747359/58198268162854818768549562500000000:ℝ), (9352730605718288696719434349002819477359/116396536325709637537099125000000000:ℝ)]]
theorem cell11_exceptional3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 3 false b ν := by
 have heq : highBranch cell11 3 false b ν = Record12518109.Bernstein.bsum 1 2 (4825274379116387526422460112197818022641/14142192351168088425000000000000000000000:ℝ) cell11_exceptional3_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional3_0_g]
def cell11_exceptional3_1_g : Fin 2 → Fin 3 → ℝ := ![![(60667557064722254020778321573024529765609201/1454297123698858114601028834125000000000:ℝ), (13889024741476712253310906248732150728039863/114812930818330903784291750062500000000:ℝ), (352119924187836920739667752496196629093672397/4362891371096574343803086502375000000000:ℝ)],
  ![(180607984249987888864273122928161749193827603/4362891371096574343803086502375000000000:ℝ), (262313510038685498938957163347649946332757397/2181445685548287171901543251187500000000:ℝ), (116781947140646174764129881222350959697890799/1454297123698858114601028834125000000000:ℝ)]]
theorem cell11_exceptional3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 3 true b ν := by
 have heq : highBranch cell11 3 true b ν = Record12518109.Bernstein.bsum 1 2 (180607984249987888864273122928161749193827603/530091795898833458434275000000000000000000000:ℝ) cell11_exceptional3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional3_1_g]
theorem cell11_exceptional3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 3 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional3_0 hb hν) (cell11_exceptional3_1 hb hν)
def cell11_exceptional4_0_g : Fin 2 → Fin 3 → ℝ := ![![(4066937403353559375397213526798830139/6126133490826823028268375000000000:ℝ), (177085813760803641245354645175325083287/1021022248471137171378062500000000:ℝ), (1067349742335329023807359166678702669861/6126133490826823028268375000000000:ℝ)],
  ![(3266526915790443862373700284159830139/6126133490826823028268375000000000:ℝ), (529247546225080701730517852360975249861/3063066745413411514134187500000000:ℝ), (1064112319986642537140127735428702669861/6126133490826823028268375000000000:ℝ)]]
theorem cell11_exceptional4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 4 false b ν := by
 have heq : highBranch cell11 4 false b ν = Record12518109.Bernstein.bsum 1 2 (3266526915790443862373700284159830139/744325913219373075000000000000000000000:ℝ) cell11_exceptional4_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional4_0_g]
def cell11_exceptional4_1_g : Fin 2 → Fin 3 → ℝ := ![![(138763436428824595337528760007756405425137/229625861636661807568583500125000000000:ℝ), (19900375587641104943050478519338947603039863/114812930818330903784291750062500000000:ℝ), (39995653802321207247404916687272690944074863/229625861636661807568583500125000000000:ℝ)],
  ![(108872107203959271050198173153843768425137/229625861636661807568583500125000000000:ℝ), (19825145375822285318876451620731465103039863/114812930818330903784291750062500000000:ℝ), (13291469470858368969229821687680480314691621/76541953878887269189527833375000000000:ℝ)]]
theorem cell11_exceptional4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 4 true b ν := by
 have heq : highBranch cell11 4 true b ν = Record12518109.Bernstein.bsum 1 2 (108872107203959271050198173153843768425137/27899568205201760970225000000000000000000000:ℝ) cell11_exceptional4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional4_1_g]
theorem cell11_exceptional4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 4 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional4_0 hb hν) (cell11_exceptional4_1 hb hν)
def cell11_exceptional5_0_g : Fin 2 → Fin 3 → ℝ := ![![(250837240530175037443960165398173830139/6126133490826823028268375000000000:ℝ), (1795329667823646587499519436021319187642221/19177860893033369489994147937500000000:ℝ), (2147431520970371063050613890217370353499721/38355721786066738979988295875000000000:ℝ)],
  ![(248997771952835418469819902155534830139/6126133490826823028268375000000000:ℝ), (5350156828081889457656986927550875062926663/57533582679100108469982443812500000000:ℝ), (6404346357224391742099289082545861060499163/115067165358200216939964887625000000000:ℝ)]]
theorem cell11_exceptional5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 5 false b ν := by
 have heq : highBranch cell11 5 false b ν = Record12518109.Bernstein.bsum 1 2 (248997771952835418469819902155534830139/744325913219373075000000000000000000000:ℝ) cell11_exceptional5_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional5_0_g]
def cell11_exceptional5_1_g : Fin 2 → Fin 3 → ℝ := ![![(9388454708531474057781473885002505530425137/229625861636661807568583500125000000000:ℝ), (67214532446438424302492117204768922303955869743/718843759853569788593450647141312500000000:ℝ), (80418192032834379370464987367079888937165217243/1437687519707139577186901294282625000000000:ℝ)],
  ![(9319616364927516054261104157898592893425137/229625861636661807568583500125000000000:ℝ), (200302503766332718657101624399936364951867609229/2156531279560709365780351941423937500000000:ℝ), (239834096503655859465052404241601785561495651729/4313062559121418731560703882847875000000000:ℝ)]]
theorem cell11_exceptional5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 5 true b ν := by
 have heq : highBranch cell11 5 true b ν = Record12518109.Bernstein.bsum 1 2 (9319616364927516054261104157898592893425137/27899568205201760970225000000000000000000000:ℝ) cell11_exceptional5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional5_1_g]
theorem cell11_exceptional5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 5 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional5_0 hb hν) (cell11_exceptional5_1 hb hν)
def cell11_exceptional6_0_g : Fin 2 → Fin 3 → ℝ := ![![(84325377166024278698256374129339564213/1021022248471137171378062500000000:ℝ), (16686239647173408132058115238989879/153153337270670575706709375000:ℝ), (29091809919226809174308130807029/980181358532291684522940000:ℝ)],
  ![(83948527605391819530188130159733064213/1021022248471137171378062500000000:ℝ), (16593308500245727498040193893239879/153153337270670575706709375000:ℝ), (28851716807605968787251101807029/980181358532291684522940000:ℝ)]]
theorem cell11_exceptional6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 6 false b ν := by
 have heq : highBranch cell11 6 false b ν = Record12518109.Bernstein.bsum 1 2 (28851716807605968787251101807029/119092146115099692000000000000000:ℝ) cell11_exceptional6_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional6_0_g]
def cell11_exceptional6_1_g : Fin 2 → Fin 3 → ℝ := ![![(9475002186887626023897685419520308105262637/114812930818330903784291750062500000000:ℝ), (2499066521620862823355134899759524209293/22962586163666180756858350012500000:ℝ), (1088409381365237710021242362619472777/36740137861865889210973360020000:ℝ)],
  ![(9432681059184298090151244333391989286762637/114812930818330903784291750062500000000:ℝ), (2485154505822719627987531303881777709293/22962586163666180756858350012500000:ℝ), (359808812402102729399455067580824259/12246712620621963070324453340000:ℝ)]]
theorem cell11_exceptional6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 6 true b ν := by
 have heq : highBranch cell11 6 true b ν = Record12518109.Bernstein.bsum 1 2 (359808812402102729399455067580824259/1487976970944093918412000000000000000:ℝ) cell11_exceptional6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional6_1_g]
theorem cell11_exceptional6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 6 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional6_0 hb hν) (cell11_exceptional6_1 hb hν)
def cell11_exceptional7_0_g : Fin 2 → Fin 3 → ℝ := ![![(229493589944223159264794282898173830139/6126133490826823028268375000000000:ℝ), (4932894272661743923094405364313957562926663/57533582679100108469982443812500000000:ℝ), (5937002890248655638182808554149611060499163/115067165358200216939964887625000000000:ℝ)],
  ![(227654121366883540290654019655534830139/6126133490826823028268375000000000:ℝ), (544118010808077068694759331533430562547407/6392620297677789829998049312500000000:ℝ), (218483506835627192264083554297902261499969/4261746865118526553332032875000000000:ℝ)]]
theorem cell11_exceptional7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 7 false b ν := by
 have heq : highBranch cell11 7 false b ν = Record12518109.Bernstein.bsum 1 2 (227654121366883540290654019655534830139/744325913219373075000000000000000000000:ℝ) cell11_exceptional7_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional7_0_g]
def cell11_exceptional7_1_g : Fin 2 → Fin 3 → ℝ := ![![(8588430653618239807991799111255005530425137/229625861636661807568583500125000000000:ℝ), (184660247544394185259090486823725516911867609229/2156531279560709365780351941423937500000000:ℝ), (222314728332096241728422693795376459311495651729/4313062559121418731560703882847875000000000:ℝ)],
  ![(8519592310014281804471429384151092893425137/229625861636661807568583500125000000000:ℝ), (6789598295237467815137620726272411664883985527/79871528872618865399272294126812500000000:ℝ), (24543805415249884786897792881748730895721739081/479229173235713192395633764760875000000000:ℝ)]]
theorem cell11_exceptional7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highBranch cell11 7 true b ν := by
 have heq : highBranch cell11 7 true b ν = Record12518109.Bernstein.bsum 1 2 (8519592310014281804471429384151092893425137/27899568205201760970225000000000000000000000:ℝ) cell11_exceptional7_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_exceptional7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_exceptional7_1_g]
theorem cell11_exceptional7 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
 (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < highExceptional cell11 7 b ν :=
 highExceptional_pos_of_branches (cell11_exceptional7_0 hb hν) (cell11_exceptional7_1 hb hν)
def cell11_domain0_0_g : Fin 2 → Fin 1 → ℝ := ![![(1199526494782637110046532911633/111598272820807043880900000000000:ℝ)],
  ![(1905209807115711617823309911633/111598272820807043880900000000000:ℝ)]]
theorem cell11_domain0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 0 false b := by
 have heq : domainBranch cell11 0 false b = Record12518109.Bernstein.bsum 1 0 (1199526494782637110046532911633/223196545641614087761800000000000000:ℝ) cell11_domain0_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain0_0_g]
def cell11_domain0_1_g : Fin 2 → Fin 1 → ℝ := ![![(1199526494782637110046532911633/111598272820807043880900000000000:ℝ)],
  ![(1905209807115711617823309911633/111598272820807043880900000000000:ℝ)]]
theorem cell11_domain0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 0 true b := by
 have heq : domainBranch cell11 0 true b = Record12518109.Bernstein.bsum 1 0 (1199526494782637110046532911633/223196545641614087761800000000000000:ℝ) cell11_domain0_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain0_1_g]
def cell11_domain1_0_g : Fin 2 → Fin 1 → ℝ := ![![(1450956894995810340919299361894177/99243455095916410000000000000000:ℝ)],
  ![(1429726111273733838868140303894177/99243455095916410000000000000000:ℝ)]]
theorem cell11_domain1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 1 false b := by
 have heq : domainBranch cell11 1 false b = Record12518109.Bernstein.bsum 1 0 (1429726111273733838868140303894177/198486910191832820000000000000000000:ℝ) cell11_domain1_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain1_0_g]
def cell11_domain1_1_g : Fin 2 → Fin 1 → ℝ := ![![(2589634102232606510613270996231939/99243455095916410000000000000000:ℝ)],
  ![(2568403318510530008562111938231939/99243455095916410000000000000000:ℝ)]]
theorem cell11_domain1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 1 true b := by
 have heq : domainBranch cell11 1 true b = Record12518109.Bernstein.bsum 1 0 (2568403318510530008562111938231939/198486910191832820000000000000000000:ℝ) cell11_domain1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain1_1_g]
def cell11_domain2_0_g : Fin 2 → Fin 1 → ℝ := ![![(200565238850339730855350678876589/9924345509591641000000000000000:ℝ)],
  ![(200861994333745790260959372876589/9924345509591641000000000000000:ℝ)]]
theorem cell11_domain2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 2 false b := by
 have heq : domainBranch cell11 2 false b = Record12518109.Bernstein.bsum 1 0 (200565238850339730855350678876589/19848691019183282000000000000000000:ℝ) cell11_domain2_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain2_0_g]
def cell11_domain2_1_g : Fin 2 → Fin 1 → ℝ := ![![(92153732840770696527612456962023/9924345509591641000000000000000:ℝ)],
  ![(92450488324176755933221150962023/9924345509591641000000000000000:ℝ)]]
theorem cell11_domain2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 2 true b := by
 have heq : domainBranch cell11 2 true b = Record12518109.Bernstein.bsum 1 0 (92153732840770696527612456962023/19848691019183282000000000000000000:ℝ) cell11_domain2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain2_1_g]
def cell11_domain3_0_g : Fin 2 → Fin 1 → ℝ := ![![(1971224027458222049595741380113/99243455095916410000000000000:ℝ)],
  ![(2438829298249036932917355380113/99243455095916410000000000000:ℝ)]]
theorem cell11_domain3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 3 false b := by
 have heq : domainBranch cell11 3 false b = Record12518109.Bernstein.bsum 1 0 (1971224027458222049595741380113/198486910191832820000000000000000:ℝ) cell11_domain3_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain3_0_g]
def cell11_domain3_1_g : Fin 2 → Fin 1 → ℝ := ![![(1971224027458222049595741380113/99243455095916410000000000000:ℝ)],
  ![(2438829298249036932917355380113/99243455095916410000000000000:ℝ)]]
theorem cell11_domain3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 3 true b := by
 have heq : domainBranch cell11 3 true b = Record12518109.Bernstein.bsum 1 0 (1971224027458222049595741380113/198486910191832820000000000000000:ℝ) cell11_domain3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain3_1_g]
def cell11_domain4_0_g : Fin 2 → Fin 1 → ℝ := ![![(4796824804791666749386833/310135797174738781250000:ℝ)],
  ![(4155529887478595642386833/310135797174738781250000:ℝ)]]
theorem cell11_domain4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 4 false b := by
 have heq : domainBranch cell11 4 false b = Record12518109.Bernstein.bsum 1 0 (4155529887478595642386833/620271594349477562500000000:ℝ) cell11_domain4_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain4_0_g]
def cell11_domain4_1_g : Fin 2 → Fin 1 → ℝ := ![![(4796824804791666749386833/310135797174738781250000:ℝ)],
  ![(4155529887478595642386833/310135797174738781250000:ℝ)]]
theorem cell11_domain4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 4 true b := by
 have heq : domainBranch cell11 4 true b = Record12518109.Bernstein.bsum 1 0 (4155529887478595642386833/620271594349477562500000000:ℝ) cell11_domain4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain4_1_g]
def cell11_domain5_0_g : Fin 2 → Fin 1 → ℝ := ![![(64554318596801645190932911712903/4962172754795820500000000000000:ℝ)],
  ![(63529069456385174275327649712903/4962172754795820500000000000000:ℝ)]]
theorem cell11_domain5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 5 false b := by
 have heq : domainBranch cell11 5 false b = Record12518109.Bernstein.bsum 1 0 (63529069456385174275327649712903/9924345509591641000000000000000000:ℝ) cell11_domain5_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain5_0_g]
def cell11_domain5_1_g : Fin 2 → Fin 1 → ℝ := ![![(121379760955193544012444912009621/4962172754795820500000000000000:ℝ)],
  ![(120354511814777073096839650009621/4962172754795820500000000000000:ℝ)]]
theorem cell11_domain5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 5 true b := by
 have heq : domainBranch cell11 5 true b = Record12518109.Bernstein.bsum 1 0 (120354511814777073096839650009621/9924345509591641000000000000000000:ℝ) cell11_domain5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain5_1_g]
def cell11_domain6_0_g : Fin 2 → Fin 1 → ℝ := ![![(1459708998076028727497575189492355151/10094007158250864898715500000000000:ℝ)],
  ![(1434275394005059174326895066798355151/10094007158250864898715500000000000:ℝ)]]
theorem cell11_domain6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 6 false b := by
 have heq : domainBranch cell11 6 false b = Record12518109.Bernstein.bsum 1 0 (1434275394005059174326895066798355151/20188014316501729797431000000000000000:ℝ) cell11_domain6_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain6_0_g]
def cell11_domain6_1_g : Fin 2 → Fin 1 → ℝ := ![![(1414782219679545294343127724392514237/10094007158250864898715500000000000:ℝ)],
  ![(1389348615608575741172447601698514237/10094007158250864898715500000000000:ℝ)]]
theorem cell11_domain6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 6 true b := by
 have heq : domainBranch cell11 6 true b = Record12518109.Bernstein.bsum 1 0 (1389348615608575741172447601698514237/20188014316501729797431000000000000000:ℝ) cell11_domain6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain6_1_g]
def cell11_domain7_0_g : Fin 2 → Fin 1 → ℝ := ![![(132716105926351909607047171317/2481086377397910250000000000:ℝ)],
  ![(145566402990537495823820171317/2481086377397910250000000000:ℝ)]]
theorem cell11_domain7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 7 false b := by
 have heq : domainBranch cell11 7 false b = Record12518109.Bernstein.bsum 1 0 (132716105926351909607047171317/4962172754795820500000000000000:ℝ) cell11_domain7_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain7_0_g]
def cell11_domain7_1_g : Fin 2 → Fin 1 → ℝ := ![![(132716105926351909607047171317/2481086377397910250000000000:ℝ)],
  ![(145566402990537495823820171317/2481086377397910250000000000:ℝ)]]
theorem cell11_domain7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 7 true b := by
 have heq : domainBranch cell11 7 true b = Record12518109.Bernstein.bsum 1 0 (132716105926351909607047171317/4962172754795820500000000000000:ℝ) cell11_domain7_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain7_1_g]
def cell11_domain8_0_g : Fin 2 → Fin 1 → ℝ := ![![(37247222540618153361715285978129/496217275479582050000000000000:ℝ)],
  ![(36514924881828743336966819978129/496217275479582050000000000000:ℝ)]]
theorem cell11_domain8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 8 false b := by
 have heq : domainBranch cell11 8 false b = Record12518109.Bernstein.bsum 1 0 (36514924881828743336966819978129/992434550959164100000000000000000:ℝ) cell11_domain8_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain8_0_g]
def cell11_domain8_1_g : Fin 2 → Fin 1 → ℝ := ![![(39434991902484582548187476734803/496217275479582050000000000000:ℝ)],
  ![(38702694243695172523439010734803/496217275479582050000000000000:ℝ)]]
theorem cell11_domain8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < domainBranch cell11 8 true b := by
 have heq : domainBranch cell11 8 true b = Record12518109.Bernstein.bsum 1 0 (38702694243695172523439010734803/992434550959164100000000000000000:ℝ) cell11_domain8_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_domain8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_domain8_1_g]
def cell11_ordinary0_g : Fin 2 → Fin 1 → ℝ := ![![(786415842209663027170877/99243455095916410000000:ℝ)],
  ![(2573012499066679450512631/297730365287749230000000:ℝ)]]
theorem cell11_ordinary0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 0 b := by
 have heq : ordinary cell11 0 b = Record12518109.Bernstein.bsum 1 0 (786415842209663027170877/198486910191832820000000000:ℝ) cell11_ordinary0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary0_g]
def cell11_ordinary1_g : Fin 2 → Fin 1 → ℝ := ![![(572457721142170834329123/99243455095916410000000:ℝ)],
  ![(1503608190988822133987369/297730365287749230000000:ℝ)]]
theorem cell11_ordinary1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 1 b := by
 have heq : ordinary cell11 1 b = Record12518109.Bernstein.bsum 1 0 (1503608190988822133987369/595460730575498460000000000:ℝ) cell11_ordinary1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary1_g]
def cell11_ordinary2_g : Fin 2 → Fin 1 → ℝ := ![![(94171052442023134831183097/99243455095916410000000:ℝ)],
  ![(93743522497147754093183097/99243455095916410000000:ℝ)]]
theorem cell11_ordinary2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 2 b := by
 have heq : ordinary cell11 2 b = Record12518109.Bernstein.bsum 1 0 (93743522497147754093183097/198486910191832820000000000:ℝ) cell11_ordinary2_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary2_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary2_g]
def cell11_ordinary3_g : Fin 2 → Fin 1 → ℝ := ![![(404999989/10000000:ℝ)],
  ![(414999989/10000000:ℝ)]]
theorem cell11_ordinary3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 3 b := by
 have heq : ordinary cell11 3 b = Record12518109.Bernstein.bsum 1 0 (404999989/20000000000:ℝ) cell11_ordinary3_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary3_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary3_g]
def cell11_ordinary4_g : Fin 2 → Fin 1 → ℝ := ![![(86799248815834065107399199/99243455095916410000000:ℝ)],
  ![(86173231960766851549399199/99243455095916410000000:ℝ)]]
theorem cell11_ordinary4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 4 b := by
 have heq : ordinary cell11 4 b = Record12518109.Bernstein.bsum 1 0 (86173231960766851549399199/198486910191832820000000000:ℝ) cell11_ordinary4_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary4_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary4_g]
def cell11_ordinary5_g : Fin 2 → Fin 1 → ℝ := ![![(45224740028538591641/4574854875180000000000000:ℝ)],
  ![(45224740028538591641/4574854875180000000000000:ℝ)]]
theorem cell11_ordinary5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < ordinary cell11 5 b := by
 have heq : ordinary cell11 5 b = Record12518109.Bernstein.bsum 1 0 (45224740028538591641/9149709750360000000000000000:ℝ) cell11_ordinary5_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_ordinary5_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_ordinary5_g]
def cell11_complement0_0_g : Fin 2 → Fin 1 → ℝ := ![![(786405917864153435529877/99243455095916410000000:ℝ)],
  ![(2572982726030150675589631/297730365287749230000000:ℝ)]]
theorem cell11_complement0_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 0 false b := by
 have heq : complementBranch cell11 0 false b = Record12518109.Bernstein.bsum 1 0 (786405917864153435529877/198486910191832820000000000:ℝ) cell11_complement0_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement0_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement0_0_g]
def cell11_complement0_1_g : Fin 2 → Fin 1 → ℝ := ![![(855295635362439624479583168367211/111598272820807043880900000000000:ℝ)],
  ![(311885462584012265664815142455737/37199424273602347960300000000000:ℝ)]]
theorem cell11_complement0_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 0 true b := by
 have heq : complementBranch cell11 0 true b = Record12518109.Bernstein.bsum 1 0 (855295635362439624479583168367211/223196545641614087761800000000000000:ℝ) cell11_complement0_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement0_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement0_1_g]
def cell11_complement1_0_g : Fin 2 → Fin 1 → ℝ := ![![(676308901394758863299751261049/7443259132193730750000000000:ℝ)],
  ![(669138357227192746288702261049/7443259132193730750000000000:ℝ)]]
theorem cell11_complement1_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 1 false b := by
 have heq : complementBranch cell11 1 false b = Record12518109.Bernstein.bsum 1 0 (669138357227192746288702261049/14886518264387461500000000000000:ℝ) cell11_complement1_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement1_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement1_0_g]
def cell11_complement1_1_g : Fin 2 → Fin 1 → ℝ := ![![(16851511752149812452058543763828463/185997121368011739801500000000000:ℝ)],
  ![(50018164381237564285838293252485389/557991364104035219404500000000000:ℝ)]]
theorem cell11_complement1_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 1 true b := by
 have heq : complementBranch cell11 1 true b = Record12518109.Bernstein.bsum 1 0 (50018164381237564285838293252485389/1115982728208070438809000000000000000:ℝ) cell11_complement1_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement1_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement1_1_g]
def cell11_complement2_0_g : Fin 2 → Fin 1 → ℝ := ![![(150357465784581491199496053683/2481086377397910250000000000:ℝ)],
  ![(140841785314136439895813053683/2481086377397910250000000000:ℝ)]]
theorem cell11_complement2_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 2 false b := by
 have heq : complementBranch cell11 2 false b = Record12518109.Bernstein.bsum 1 0 (140841785314136439895813053683/4962172754795820500000000000000:ℝ) cell11_complement2_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement2_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement2_0_g]
def cell11_complement2_1_g : Fin 2 → Fin 1 → ℝ := ![![(33669455494510752617830741736885389/557991364104035219404500000000000:ℝ)],
  ![(31530574126922489927248003697885389/557991364104035219404500000000000:ℝ)]]
theorem cell11_complement2_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 2 true b := by
 have heq : complementBranch cell11 2 true b = Record12518109.Bernstein.bsum 1 0 (31530574126922489927248003697885389/1115982728208070438809000000000000000:ℝ) cell11_complement2_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement2_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement2_1_g]
def cell11_complement3_0_g : Fin 2 → Fin 1 → ℝ := ![![(583752844761137845725067036049/7443259132193730750000000000:ℝ)],
  ![(581926424904513987939018036049/7443259132193730750000000000:ℝ)]]
theorem cell11_complement3_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 3 false b := by
 have heq : complementBranch cell11 3 false b = Record12518109.Bernstein.bsum 1 0 (581926424904513987939018036049/14886518264387461500000000000000:ℝ) cell11_complement3_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement3_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement3_0_g]
def cell11_complement3_1_g : Fin 2 → Fin 1 → ℝ := ![![(43615977914853404152671853680135389/557991364104035219404500000000000:ℝ)],
  ![(14493411554245209495798621880378463/185997121368011739801500000000000:ℝ)]]
theorem cell11_complement3_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 3 true b := by
 have heq : complementBranch cell11 3 true b = Record12518109.Bernstein.bsum 1 0 (14493411554245209495798621880378463/371994242736023479603000000000000000:ℝ) cell11_complement3_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement3_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement3_1_g]
def cell11_complement4_0_g : Fin 2 → Fin 1 → ℝ := ![![(185199427252003682337469716183/2481086377397910250000000000:ℝ)],
  ![(183699933247972019871286716183/2481086377397910250000000000:ℝ)]]
theorem cell11_complement4_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 4 false b := by
 have heq : complementBranch cell11 4 false b = Record12518109.Bernstein.bsum 1 0 (183699933247972019871286716183/4962172754795820500000000000000:ℝ) cell11_complement4_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement4_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement4_0_g]
def cell11_complement4_1_g : Fin 2 → Fin 1 → ℝ := ![![(41505342944611068560378742485810389/557991364104035219404500000000000:ℝ)],
  ![(41169285880946244192572079446810389/557991364104035219404500000000000:ℝ)]]
theorem cell11_complement4_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 4 true b := by
 have heq : complementBranch cell11 4 true b = Record12518109.Bernstein.bsum 1 0 (41169285880946244192572079446810389/1115982728208070438809000000000000000:ℝ) cell11_complement4_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement4_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement4_1_g]
def cell11_complement5_0_g : Fin 2 → Fin 1 → ℝ := ![![(140163/2000:ℝ)],
  ![(3279177/50000:ℝ)]]
theorem cell11_complement5_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 5 false b := by
 have heq : complementBranch cell11 5 false b = Record12518109.Bernstein.bsum 1 0 (3279177/100000000:ℝ) cell11_complement5_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement5_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement5_0_g]
def cell11_complement5_1_g : Fin 2 → Fin 1 → ℝ := ![![(7791846787589377727748589001137211/111598272820807043880900000000000:ℝ)],
  ![(7290117448143078168156648296137211/111598272820807043880900000000000:ℝ)]]
theorem cell11_complement5_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 5 true b := by
 have heq : complementBranch cell11 5 true b = Record12518109.Bernstein.bsum 1 0 (7290117448143078168156648296137211/223196545641614087761800000000000000:ℝ) cell11_complement5_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement5_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement5_1_g]
def cell11_complement6_0_g : Fin 2 → Fin 1 → ℝ := ![![(58666006266029771445988583/297730365287749230000000:ℝ)],
  ![(57169651458965938862988583/297730365287749230000000:ℝ)]]
theorem cell11_complement6_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 6 false b := by
 have heq : complementBranch cell11 6 false b = Record12518109.Bernstein.bsum 1 0 (57169651458965938862988583/595460730575498460000000000:ℝ) cell11_complement6_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement6_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement6_0_g]
def cell11_complement6_1_g : Fin 2 → Fin 1 → ℝ := ![![(21960651559593928113109196217027211/111598272820807043880900000000000:ℝ)],
  ![(7133336038344323145841966158675737/37199424273602347960300000000000:ℝ)]]
theorem cell11_complement6_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 6 true b := by
 have heq : complementBranch cell11 6 true b = Record12518109.Bernstein.bsum 1 0 (7133336038344323145841966158675737/74398848547204695920600000000000000:ℝ) cell11_complement6_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement6_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement6_1_g]
def cell11_complement7_0_g : Fin 2 → Fin 1 → ℝ := ![![(9943047890971798935430884561/4962172754795820500000000000:ℝ)],
  ![(33006158125346696527609653683/14886518264387461500000000000:ℝ)]]
theorem cell11_complement7_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 7 false b := by
 have heq : complementBranch cell11 7 false b = Record12518109.Bernstein.bsum 1 0 (9943047890971798935430884561/9924345509591641000000000000000:ℝ) cell11_complement7_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement7_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement7_0_g]
def cell11_complement7_1_g : Fin 2 → Fin 1 → ℝ := ![![(121629502026097057161653305148243/69748920513004402425562500000000:ℝ)],
  ![(45554007824297805094179701966081/23249640171001467475187500000000:ℝ)]]
theorem cell11_complement7_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 7 true b := by
 have heq : complementBranch cell11 7 true b = Record12518109.Bernstein.bsum 1 0 (121629502026097057161653305148243/139497841026008804851125000000000000:ℝ) cell11_complement7_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement7_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement7_1_g]
def cell11_complement8_0_g : Fin 2 → Fin 1 → ℝ := ![![(167226216332904404369606284561/4962172754795820500000000000:ℝ)],
  ![(547608657938682586630135853683/14886518264387461500000000000:ℝ)]]
theorem cell11_complement8_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 8 false b := by
 have heq : complementBranch cell11 8 false b = Record12518109.Bernstein.bsum 1 0 (167226216332904404369606284561/9924345509591641000000000000000:ℝ) cell11_complement8_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement8_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement8_0_g]
def cell11_complement8_1_g : Fin 2 → Fin 1 → ℝ := ![![(2332421378041957000720101999473243/69748920513004402425562500000000:ℝ)],
  ![(2547767711035802061371662800223243/69748920513004402425562500000000:ℝ)]]
theorem cell11_complement8_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 8 true b := by
 have heq : complementBranch cell11 8 true b = Record12518109.Bernstein.bsum 1 0 (2332421378041957000720101999473243/139497841026008804851125000000000000:ℝ) cell11_complement8_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement8_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement8_1_g]
def cell11_complement9_0_g : Fin 2 → Fin 1 → ℝ := ![![(206547008443387555728150134561/4962172754795820500000000000:ℝ)],
  ![(225419760964005519718589134561/4962172754795820500000000000:ℝ)]]
theorem cell11_complement9_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 9 false b := by
 have heq : complementBranch cell11 9 false b = Record12518109.Bernstein.bsum 1 0 (206547008443387555728150134561/9924345509591641000000000000000:ℝ) cell11_complement9_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement9_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement9_0_g]
def cell11_complement9_1_g : Fin 2 → Fin 1 → ℝ := ![![(2885119347045921986609714173054493/69748920513004402425562500000000:ℝ)],
  ![(3150544132926529222893943723804493/69748920513004402425562500000000:ℝ)]]
theorem cell11_complement9_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 9 true b := by
 have heq : complementBranch cell11 9 true b = Record12518109.Bernstein.bsum 1 0 (2885119347045921986609714173054493/139497841026008804851125000000000000:ℝ) cell11_complement9_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement9_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement9_1_g]
def cell11_complement10_0_g : Fin 2 → Fin 1 → ℝ := ![![(786405917864153435529877/99243455095916410000000:ℝ)],
  ![(2572982726030150675589631/297730365287749230000000:ℝ)]]
theorem cell11_complement10_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 10 false b := by
 have heq : complementBranch cell11 10 false b = Record12518109.Bernstein.bsum 1 0 (786405917864153435529877/198486910191832820000000000:ℝ) cell11_complement10_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement10_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement10_0_g]
def cell11_complement10_1_g : Fin 2 → Fin 1 → ℝ := ![![(855295635362439624479583168367211/111598272820807043880900000000000:ℝ)],
  ![(311885462584012265664815142455737/37199424273602347960300000000000:ℝ)]]
theorem cell11_complement10_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 10 true b := by
 have heq : complementBranch cell11 10 true b = Record12518109.Bernstein.bsum 1 0 (855295635362439624479583168367211/223196545641614087761800000000000000:ℝ) cell11_complement10_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement10_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement10_1_g]
def cell11_complement11_0_g : Fin 2 → Fin 1 → ℝ := ![![(2359242564456234285692131/49621727547958205000000:ℝ)],
  ![(2573007536893924654692131/49621727547958205000000:ℝ)]]
theorem cell11_complement11_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 11 false b := by
 have heq : complementBranch cell11 11 false b = Record12518109.Bernstein.bsum 1 0 (2359242564456234285692131/99243455095916410000000000:ℝ) cell11_complement11_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement11_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement11_0_g]
def cell11_complement11_1_g : Fin 2 → Fin 1 → ℝ := ![![(5276879387394159511596480557017211/111598272820807043880900000000000:ℝ)],
  ![(5757867762877854089172692816017211/111598272820807043880900000000000:ℝ)]]
theorem cell11_complement11_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 11 true b := by
 have heq : complementBranch cell11 11 true b = Record12518109.Bernstein.bsum 1 0 (5276879387394159511596480557017211/223196545641614087761800000000000000:ℝ) cell11_complement11_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement11_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement11_1_g]
def cell11_complement12_0_g : Fin 2 → Fin 1 → ℝ := ![![(5504900971122131598555139/99243455095916410000000:ℝ)],
  ![(18011057720430227378665417/297730365287749230000000:ℝ)]]
theorem cell11_complement12_0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 12 false b := by
 have heq : complementBranch cell11 12 false b = Record12518109.Bernstein.bsum 1 0 (5504900971122131598555139/198486910191832820000000000:ℝ) cell11_complement12_0_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement12_0_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement12_0_g]
def cell11_complement12_1_g : Fin 2 → Fin 1 → ℝ := ![![(6161196137800503489019860034747211/111598272820807043880900000000000:ℝ)],
  ![(2240770012634339182536114097915737/37199424273602347960300000000000:ℝ)]]
theorem cell11_complement12_1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ))
    (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementBranch cell11 12 true b := by
 have heq : complementBranch cell11 12 true b = Record12518109.Bernstein.bsum 1 0 (6161196137800503489019860034747211/223196545641614087761800000000000000:ℝ) cell11_complement12_1_g (81/2000:ℝ) (41/1000:ℝ) (6217/10000:ℝ) (3/4:ℝ) b ν := by
  norm_num [highBranch, highRegular, regular, exceptional, complementBranch, complementary, ordinary, domainBranch, bufferedDelta, naturalDelta, radiusHi, radiusLo, nominalRadius, highRadius, totalCap, retainedWidth, amplifier, plainCap, scheduleDenominator, Pmix, Qmix, gamma, rho, rr, d, aa, cc, w, K, incumbent, mesh, pad, lowFee, highFee, omega, cell11, Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm, cell11_complement12_1_g, Fin.sum_univ_succ]
  ring
 rw [heq]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hb hν
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [cell11_complement12_1_g]
theorem cell11_complement0 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 0 b := complementReserve_pos_of_branches (cell11_complement0_0 hb hν) (cell11_complement0_1 hb hν)
theorem cell11_complement1 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 1 b := complementReserve_pos_of_branches (cell11_complement1_0 hb hν) (cell11_complement1_1 hb hν)
theorem cell11_complement2 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 2 b := complementReserve_pos_of_branches (cell11_complement2_0 hb hν) (cell11_complement2_1 hb hν)
theorem cell11_complement3 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 3 b := complementReserve_pos_of_branches (cell11_complement3_0 hb hν) (cell11_complement3_1 hb hν)
theorem cell11_complement4 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 4 b := complementReserve_pos_of_branches (cell11_complement4_0 hb hν) (cell11_complement4_1 hb hν)
theorem cell11_complement5 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 5 b := complementReserve_pos_of_branches (cell11_complement5_0 hb hν) (cell11_complement5_1 hb hν)
theorem cell11_complement6 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 6 b := complementReserve_pos_of_branches (cell11_complement6_0 hb hν) (cell11_complement6_1 hb hν)
theorem cell11_complement7 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 7 b := complementReserve_pos_of_branches (cell11_complement7_0 hb hν) (cell11_complement7_1 hb hν)
theorem cell11_complement8 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 8 b := complementReserve_pos_of_branches (cell11_complement8_0 hb hν) (cell11_complement8_1 hb hν)
theorem cell11_complement9 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 9 b := complementReserve_pos_of_branches (cell11_complement9_0 hb hν) (cell11_complement9_1 hb hν)
theorem cell11_complement10 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 10 b := complementReserve_pos_of_branches (cell11_complement10_0 hb hν) (cell11_complement10_1 hb hν)
theorem cell11_complement11 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 11 b := complementReserve_pos_of_branches (cell11_complement11_0 hb hν) (cell11_complement11_1 hb hν)
theorem cell11_complement12 {b ν : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (hν : ν ∈ Set.Icc (6217/10000:ℝ) (3/4:ℝ)) : 0 < complementReserve cell11 12 b := complementReserve_pos_of_branches (cell11_complement12_0 hb hν) (cell11_complement12_1 hb hν)
theorem cell11_all_domains {b : ℝ} (hb : b ∈ Set.Icc (81/2000:ℝ) (41/1000:ℝ)) (j : Fin 9) (upper : Bool) : 0 < domainBranch cell11 j upper b := by
 fin_cases j
 · cases upper with
   | false => exact cell11_domain0_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain0_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain1_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain1_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain2_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain2_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain3_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain3_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain4_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain4_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain5_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain5_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain6_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain6_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain7_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain7_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
 · cases upper with
   | false => exact cell11_domain8_0 (ν := (6217/10000:ℝ)) hb (by norm_num)
   | true => exact cell11_domain8_1 (ν := (6217/10000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
