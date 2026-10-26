/- Adapted from PR56 detector-affine-c0125154, Apache-2.0; exact PR50+PR56 arithmetic. -/
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
import Candidate.Affine.Arith

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle63.Arithmetic.Bernstein
noncomputable section
noncomputable def regionRowPower (δ p : ℝ) : ℝ :=
  (-2117218811024239/13985750400000000)*δ^2*p^3 +
  (783970346203/1448400000000)*δ^2*p^2 +
  (-603567464203/724200000000)*δ^2*p^1 +
  (1/2)*δ^2 +
  (197084861177461/5594300160000000)*δ^1*p^2 +
  (33410358121/193120000000)*δ^1*p^1 +
  (-844457/3000000)*δ^1 +
  (-49970437/1158720000)*p^1 +
  (77957/1200000)

noncomputable def regionRowMinimum : ℝ := 1630674172681813/4475440128000000000000

theorem regionRowMinimum_pos : 0 < regionRowMinimum := by
  norm_num [regionRowMinimum]

noncomputable def regionRowCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(2052067269504513266658973/11934507008000000000000000000 : ℝ), (78383952923143177478699/537052815360000000000000000 : ℝ), (322561417888954748069/2685264076800000000000000 : ℝ), (140910465373037171/1491813376000000000000 : ℝ)],
  ![(1088102135476729375079601/11934507008000000000000000000 : ℝ), (11438148362225448206221/179017605120000000000000000 : ℝ), (98776165373321007353/2685264076800000000000000 : ℝ), (44055809975957581/4475440128000000000000 : ℝ)],
  ![(1082222908243604952876437/11934507008000000000000000000 : ℝ), (33285894230892643202131/537052815360000000000000000 : ℝ), (89831859246694197661/2685264076800000000000000 : ℝ), (22843242074319697/4475440128000000000000 : ℝ)]]

theorem regionRowCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionRowMinimum ≤ regionRowCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionRowMinimum, regionRowCoefficients0]

theorem regionRowIdentity0 (δ p : ℝ) :
    regionRowPower δ p = tensor regionRowCoefficients0
      ((δ-(89/200))/((93/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionRowPower, tensor, basis2, basis3,
    regionRowCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionRowBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (93/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionRowPower δ p := by
  rw [regionRowIdentity0]
  exact tensor_pos regionRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionRowCoefficients0_lower

noncomputable def regionRowCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(1082222908243604952876437/11934507008000000000000000000 : ℝ), (33285894230892643202131/537052815360000000000000000 : ℝ), (89831859246694197661/2685264076800000000000000 : ℝ), (22843242074319697/4475440128000000000000 : ℝ)],
  ![(15159770155077190572863/168091648000000000000000000 : ℝ), (32257343375108941785599/537052815360000000000000000 : ℝ), (26962517706689129323/895088025600000000000000 : ℝ), (1630674172681813/4475440128000000000000 : ℝ)],
  ![(2028550360572015577846317/11934507008000000000000000000 : ℝ), (24756583166669457270857/179017605120000000000000000 : ℝ), (286784193382447509301/2685264076800000000000000 : ℝ), (112627041504186659/1491813376000000000000 : ℝ)]]

theorem regionRowCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    regionRowMinimum ≤ regionRowCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionRowMinimum, regionRowCoefficients1]

theorem regionRowIdentity1 (δ p : ℝ) :
    regionRowPower δ p = tensor regionRowCoefficients1
      ((δ-(93/200))/((97/200)-(93/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionRowPower, tensor, basis2, basis3,
    regionRowCoefficients1, Fin.sum_univ_succ]
  ring

theorem regionRowBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (93/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionRowPower δ p := by
  rw [regionRowIdentity1]
  exact tensor_pos regionRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionRowCoefficients1_lower

noncomputable def regionCrossLoPower (δ p : ℝ) : ℝ :=
  (-322189035/431227304)*δ^1*p^3 +
  (266284901807/93238336000)*δ^1*p^2 +
  (-13736139499/3572720000)*δ^1*p^1 +
  (69/37)*δ^1 +
  (1806902401141/4139782118400)*p^2 +
  (-3780380501/4287264000)*p^1 +
  (25/74)

noncomputable def regionCrossLoMinimum : ℝ := 10624724382815417/41397821184000000

theorem regionCrossLoMinimum_pos : 0 < regionCrossLoMinimum := by
  norm_num [regionCrossLoMinimum]

noncomputable def regionCrossLoCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(28646582235909192491/110394189824000000000 : ℝ), (256874783250922215293/993547708416000000000 : ℝ), (1066386805525864253/4139782118400000000 : ℝ), (10624724382815417/41397821184000000 : ℝ)],
  ![(29898410279387935367/110394189824000000000 : ℝ), (268115439535815869441/993547708416000000000 : ℝ), (1113115689883072961/4139782118400000000 : ℝ), (11090944384558829/41397821184000000 : ℝ)],
  ![(31150238322866678243/110394189824000000000 : ℝ), (279356095820709523589/993547708416000000000 : ℝ), (1159844574240281669/4139782118400000000 : ℝ), (11557164386302241/41397821184000000 : ℝ)]]

theorem regionCrossLoCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCrossLoMinimum ≤ regionCrossLoCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCrossLoMinimum, regionCrossLoCoefficients0]

theorem regionCrossLoIdentity0 (δ p : ℝ) :
    regionCrossLoPower δ p = tensor regionCrossLoCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionCrossLoPower, tensor, basis2, basis3,
    regionCrossLoCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionCrossLoBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionCrossLoPower δ p := by
  rw [regionCrossLoIdentity0]
  exact tensor_pos regionCrossLoMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCrossLoCoefficients0_lower

noncomputable def regionCrossHiPower (δ p : ℝ) : ℝ :=
  (-91086437807/93238336000)*δ^1*p^2 +
  (334400527/96560000)*δ^1*p^1 +
  (-3)*δ^1 +
  (91086437807/111886003200)*p^2 +
  (-334400527/115872000)*p^1 +
  (5/2)

noncomputable def regionCrossHiMinimum : ℝ := 589539019807507/1118860032000000

theorem regionCrossHiMinimum_pos : 0 < regionCrossHiMinimum := by
  norm_num [regionCrossHiMinimum]

noncomputable def regionCrossHiCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(1759841408351088157/2983626752000000000 : ℝ), (15816925470608591911/26852640768000000000 : ℝ), (65813747871655831/111886003200000000 : ℝ), (657237280455259/1118860032000000 : ℝ)],
  ![(98188576431605777/175507456000000000 : ℝ), (882489403939535171/1579567104000000000 : ℝ), (3672011683826291/6581529600000000 : ℝ), (36669891184199/65815296000000 : ℝ)],
  ![(1578570190323508261/2983626752000000000 : ℝ), (14187714263335603903/26852640768000000000 : ℝ), (59034649378438063/111886003200000000 : ℝ), (589539019807507/1118860032000000 : ℝ)]]

theorem regionCrossHiCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCrossHiMinimum ≤ regionCrossHiCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCrossHiMinimum, regionCrossHiCoefficients0]

theorem regionCrossHiIdentity0 (δ p : ℝ) :
    regionCrossHiPower δ p = tensor regionCrossHiCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionCrossHiPower, tensor, basis2, basis3,
    regionCrossHiCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionCrossHiBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionCrossHiPower δ p := by
  rw [regionCrossHiIdentity0]
  exact tensor_pos regionCrossHiMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCrossHiCoefficients0_lower

noncomputable def regionPlainPower (δ p : ℝ) : ℝ :=
  (-74264746599/466191680000)*δ^1*p^3 +
  (3251473805713/2311163600000)*δ^1*p^2 +
  (-1492095492873/577790900000)*δ^1*p^1 +
  (148661249/119675000)*δ^1 +
  (-296954214022319/535598297318400)*p^2 +
  (686229331867/554679264000)*p^1 +
  (-28986249/47870000)

noncomputable def regionPlainMinimum : ℝ := 971142839874013471237/28565242523648000000000000

theorem regionPlainMinimum_pos : 0 < regionPlainMinimum := by
  norm_num [regionPlainMinimum]

noncomputable def regionPlainCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(971142839874013471237/28565242523648000000000000 : ℝ), (789517361876455900711/6427179567820800000000000 : ℝ), (2266783072042888027/10711965946368000000000 : ℝ), (16084645533541757/53559829731840000000 : ℝ)],
  ![(164391245027375431290169/28565242523648000000000000 : ℝ), (37419690880981988389507/6427179567820800000000000 : ℝ), (21028448318341693133/3570655315456000000000 : ℝ), (319021424735911409/53559829731840000000 : ℝ)],
  ![(327811347214876849109101/28565242523648000000000000 : ℝ), (74049864400087520878303/6427179567820800000000000 : ℝ), (123903906838007270771/10711965946368000000000 : ℝ), (621958203938281061/53559829731840000000 : ℝ)]]

theorem regionPlainCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionPlainMinimum ≤ regionPlainCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionPlainMinimum, regionPlainCoefficients0]

theorem regionPlainIdentity0 (δ p : ℝ) :
    regionPlainPower δ p = tensor regionPlainCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionPlainPower, tensor, basis2, basis3,
    regionPlainCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionPlainBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionPlainPower δ p := by
  rw [regionPlainIdentity0]
  exact tensor_pos regionPlainMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionPlainCoefficients0_lower

noncomputable def regionTailPower (δ p : ℝ) : ℝ :=
  (4787/71000)*δ^1*p^3 +
  (-205743427/289680000)*δ^1*p^2 +
  (456403327/289680000)*δ^1*p^1 +
  (-847/1000)*δ^1 +
  (102871327/347616000)*p^2 +
  (-4005917/4896000)*p^1 +
  (541/1200)

noncomputable def regionTailMinimum : ℝ := 3448640797/695232000000

theorem regionTailMinimum_pos : 0 < regionTailMinimum := by
  norm_num [regionTailMinimum]

noncomputable def regionTailCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(166644849843773/11587200000000000 : ℝ), (1191859460565971/83427840000000000 : ℝ), (49328345311/3476160000000 : ℝ), (9799211989/695232000000 : ℝ)],
  ![(6658348501453/681600000000000 : ℝ), (47545653748831/4907520000000000 : ℝ), (1964638571/204480000000 : ℝ), (389642729/40896000000 : ℝ)],
  ![(59738999205629/11587200000000000 : ℝ), (424692766894283/83427840000000000 : ℝ), (17469366103/3476160000000 : ℝ), (3448640797/695232000000 : ℝ)]]

theorem regionTailCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionTailMinimum ≤ regionTailCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionTailMinimum, regionTailCoefficients0]

theorem regionTailIdentity0 (δ p : ℝ) :
    regionTailPower δ p = tensor regionTailCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionTailPower, tensor, basis2, basis3,
    regionTailCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionTailBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionTailPower δ p := by
  rw [regionTailIdentity0]
  exact tensor_pos regionTailMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionTailCoefficients0_lower

noncomputable def regionCutoffPower (δ p : ℝ) : ℝ :=
  (1509473/289680000)*δ^1*p^2 +
  (286940527/289680000)*δ^1*p^1 +
  (-3/2)*δ^1 +
  (-16025/19312)*p^1 +
  (5/4)

noncomputable def regionCutoffMinimum : ℝ := 80749121119/231744000000

theorem regionCutoffMinimum_pos : 0 < regionCutoffMinimum := by
  norm_num [regionCutoffMinimum]

noncomputable def regionCutoffCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(1203662263487699/3089920000000000 : ℝ), (10823998922703097/27809280000000000 : ℝ), (90125313403/231744000000 : ℝ), (90050636903/231744000000 : ℝ)],
  ![(1141498320273663/3089920000000000 : ℝ), (1140553882411221/3089920000000000 : ℝ), (85470709511/231744000000 : ℝ), (28466626337/77248000000 : ℝ)],
  ![(1079334377059627/3089920000000000 : ℝ), (9705970960698881/27809280000000000 : ℝ), (26938701873/77248000000 : ℝ), (80749121119/231744000000 : ℝ)]]

theorem regionCutoffCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCutoffMinimum ≤ regionCutoffCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCutoffMinimum, regionCutoffCoefficients0]

theorem regionCutoffIdentity0 (δ p : ℝ) :
    regionCutoffPower δ p = tensor regionCutoffCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionCutoffPower, tensor, basis2, basis3,
    regionCutoffCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionCutoffBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionCutoffPower δ p := by
  rw [regionCutoffIdentity0]
  exact tensor_pos regionCutoffMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCutoffCoefficients0_lower

noncomputable def regionComparePower (δ p : ℝ) : ℝ :=
  (1509473/72420000)*δ^1*p^4 +
  (-496480569449/1810500000000)*δ^1*p^3 +
  (13876931/30175000)*δ^1*p^2 +
  (-124624038517/603500000000)*δ^1*p^1 +
  (336135290551/2172600000000)*p^3 +
  (-156283944301/543150000000)*p^2 +
  (96333495551/724200000000)*p^1

noncomputable def regionCompareMinimum : ℝ := 31342991723977/8690400000000000

theorem regionCompareMinimum_pos : 0 < regionCompareMinimum := by
  norm_num [regionCompareMinimum]

noncomputable def regionCompareCoefficients0 : Fin 3 → Fin 5 → ℝ :=
  ![
  ![(208048203176399998847/46348800000000000000000 : ℝ), (73298855406312223399/16358400000000000000000 : ℝ), (9328994381833889051/2085696000000000000000 : ℝ), (31041135040701817/6952320000000000000 : ℝ), (38731845303649/8690400000000000 : ℝ)],
  ![(188210337185973055739/46348800000000000000000 : ℝ), (1127254026922968205571/278092800000000000000000 : ℝ), (8439304170459056087/2085696000000000000000 : ℝ), (28080541525799629/6952320000000000000 : ℝ), (35037418513813/8690400000000000 : ℝ)],
  ![(2371443256275297361/652800000000000000000 : ℝ), (1008427511938628613359/278092800000000000000000 : ℝ), (7549613959084223123/2085696000000000000000 : ℝ), (25119948010897441/6952320000000000000 : ℝ), (31342991723977/8690400000000000 : ℝ)]]

theorem regionCompareCoefficients0_lower (i : Fin 3) (j : Fin 5) :
    regionCompareMinimum ≤ regionCompareCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCompareMinimum, regionCompareCoefficients0]

theorem regionCompareIdentity0 (δ p : ℝ) :
    regionComparePower δ p = tensor24 regionCompareCoefficients0
      ((δ-(89/200))/((97/200)-(89/200))) ((p-(199/400))/((1/2)-(199/400))) := by
  norm_num [regionComparePower, tensor24, basis2, basis4,
    regionCompareCoefficients0, Fin.sum_univ_succ]
  ring

theorem regionCompareBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (97/200)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < regionComparePower δ p := by
  rw [regionCompareIdentity0]
  exact tensor24_pos regionCompareMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCompareCoefficients0_lower

end
end Cycle63.Arithmetic.Bernstein
