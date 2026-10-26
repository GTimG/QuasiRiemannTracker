import Candidate.Cycle63.Arithmetic.Bernstein.Basis
import Candidate.Affine.Arith

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle63.Arithmetic.Bernstein
noncomputable section
noncomputable def newRowPower (δ p : ℝ) : ℝ :=
  (-442285107797/3257509536000)*δ^2*p^3 +
  (4560386915055229/9048637600000000)*δ^2*p^2 +
  (-21880491190354313/27145912800000000)*δ^2*p^1 +
  (1/2)*δ^2 +
  (4142840306422061/97725286080000000)*δ^1*p^2 +
  (5160340594843099/32575095360000000)*δ^1*p^1 +
  (-844457/3000000)*δ^1 +
  (-4140530141/101206800000)*p^1 +
  (77957/1200000)

noncomputable def newRowMinimum : ℝ := 62475432889282541/39090114432000000000000

theorem newRowMinimum_pos : 0 < newRowMinimum := by
  norm_num [newRowMinimum]

noncomputable def newRowCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(77957/1200000 : ℝ), (35308362397/607240800000 : ℝ), (486997379/9488137500 : ℝ), (1801820141/40482720000 : ℝ)],
  ![(2800327/1200000000 : ℝ), (325898091548363753/234540686592000000000 : ℝ), (192551374898275267/156360457728000000000 : ℝ), (11629664714193167/6254418309120000000 : ℝ)],
  ![(7743109/200000000 : ℝ), (999350169048293257043/58635171648000000000000 : ℝ), (123377617029867016643/23454068659200000000000 : ℝ), (69189564247540543/13030038144000000000000 : ℝ)]]

theorem newRowCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients0]

theorem newRowIdentity0 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients0
      ((δ-(0))/((89/200)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients0, Fin.sum_univ_succ]
  ring

theorem newRowBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (89/200)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity0]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients0_lower

noncomputable def newRowCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(27633671/600000000 : ℝ), (1198666495559917005347/58635171648000000000000 : ℝ), (50207420155420944049/7818022886400000000000 : ℝ), (62475432889282541/39090114432000000000000 : ℝ)],
  ![(29208707/400000000 : ℝ), (2465671318507093303/73293964560000000000 : ℝ), (1374228864918011869/117270343296000000000 : ℝ), (2934874372696043/2714591280000000000 : ℝ)],
  ![(1621199/12000000 : ℝ), (1700829752303393957/23454068659200000000 : ℝ), (19982268188944253/551860439040000000 : ℝ), (15293561674908923/919767398400000000 : ℝ)]]

theorem newRowCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients1]

theorem newRowIdentity1 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients1
      ((δ-(97/200))/((3/4)-(97/200))) ((p-(0))/((1/2)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients1, Fin.sum_univ_succ]
  ring

theorem newRowBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (97/200) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity1]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients1_lower

noncomputable def newRowCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(7743109/200000000 : ℝ), (201140776267131226311557/11727034329600000000000000 : ℝ), (54966030457111768625977/10219637760000000000000000 : ℝ), (264644054548231978590161/3127209154560000000000000000 : ℝ)],
  ![(24210413/600000000 : ℝ), (209445967945063983863009/11727034329600000000000000 : ℝ), (26103356759536955090467991/4690813731840000000000000000 : ℝ), (611593221212052256191/115822561280000000000000000 : ℝ)],
  ![(25311499/600000000 : ℝ), (219469559133365948221133/11727034329600000000000000 : ℝ), (27491879822307353944357867/4690813731840000000000000000 : ℝ), (27339938640024940979209/3127209154560000000000000000 : ℝ)]]

theorem newRowCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients2]

theorem newRowIdentity2 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients2
      ((δ-(89/200))/((93/200)-(89/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients2, Fin.sum_univ_succ]
  ring

theorem newRowBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (93/200)) (hp : p ∈ Set.Icc (0) (199/400)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity2]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients2_lower

noncomputable def newRowCoefficients3 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(25311499/600000000 : ℝ), (219469559133365948221133/11727034329600000000000000 : ℝ), (27491879822307353944357867/4690813731840000000000000000 : ℝ), (27339938640024940979209/3127209154560000000000000000 : ℝ)],
  ![(1760839/40000000 : ℝ), (229493150321667912579257/11727034329600000000000000 : ℝ), (9626800961692584266082581/1563604577280000000000000000 : ℝ), (38166860307324471041261/3127209154560000000000000000 : ℝ)],
  ![(27633671/600000000 : ℝ), (241235141020339083744053/11727034329600000000000000 : ℝ), (30783500230895897214882947/4690813731840000000000000000 : ℝ), (34216860135270010982041/347467683840000000000000000 : ℝ)]]

theorem newRowCoefficients3_lower (i : Fin 3) (j : Fin 4) :
    newRowMinimum ≤ newRowCoefficients3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [newRowMinimum, newRowCoefficients3]

theorem newRowIdentity3 (δ p : ℝ) :
    newRowPower δ p = tensor newRowCoefficients3
      ((δ-(93/200))/((97/200)-(93/200))) ((p-(0))/((199/400)-(0))) := by
  norm_num [newRowPower, tensor, basis2, basis3,
    newRowCoefficients3, Fin.sum_univ_succ]
  ring

theorem newRowBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (93/200) (97/200)) (hp : p ∈ Set.Icc (0) (199/400)) :
    0 < newRowPower δ p := by
  rw [newRowIdentity3]
  exact tensor_pos newRowMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    newRowCoefficients3_lower
noncomputable def oldJunctionPower (δ p : ℝ) : ℝ :=
  (-323002549/2371022307)*δ^2*p^3 +
  (531227837/1054237500)*δ^2*p^2 +
  (-3392201527/4216950000)*δ^2*p^1 +
  (1/2)*δ^2 +
  (1554544950581/35565334605000)*δ^1*p^2 +
  (6616969133/42169500000)*δ^1*p^1 +
  (-211967/750000)*δ^1 +
  (-2101097167/50603400000)*p^1 +
  (39559/600000)

noncomputable def oldJunctionMinimum : ℝ := 2000899954949/809308947456000000

theorem oldJunctionMinimum_pos : 0 < oldJunctionMinimum := by
  norm_num [oldJunctionMinimum]

noncomputable def oldJunctionCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(39559/600000 : ℝ), (17917101839/303620400000 : ℝ), (247125073/4744068750 : ℝ), (914327167/20241360000 : ℝ)],
  ![(155279/12000000 : ℝ), (132661742489/12144816000000 : ℝ), (90949477835273/9484089228000000 : ℝ), (339113842237061/37936356912000000 : ℝ)],
  ![(45391/1500000 : ℝ), (347196366691/24289632000000 : ℝ), (318570831152711/56904535368000000 : ℝ), (4999116320757/2810100512000000 : ℝ)]]

theorem oldJunctionCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients0]

theorem oldJunctionIdentity0 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients0
      ((δ-(0))/((3/8)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients0, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/8)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity0]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients0_lower

noncomputable def oldJunctionCoefficients1 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(45391/1500000 : ℝ), (347196366691/24289632000000 : ℝ), (318570831152711/56904535368000000 : ℝ), (4999116320757/2810100512000000 : ℝ)],
  ![(3112873/96000000 : ℝ), (2859443815241/194317056000000 : ℝ), (773813537787587/151745427648000000 : ℝ), (536557581469829/606981710592000000 : ℝ)],
  ![(13704763/384000000 : ℝ), (24780451119487/1554536448000000 : ℝ), (18945929312786347/3641890263552000000 : ℝ), (2152233025744163/4855853684736000000 : ℝ)]]

theorem oldJunctionCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients1]

theorem oldJunctionIdentity1 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients1
      ((δ-(3/8))/((27/64)-(3/8))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients1, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (27/64)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity1]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients1_lower

noncomputable def oldJunctionCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(13704763/384000000 : ℝ), (24780451119487/1554536448000000 : ℝ), (18945929312786347/3641890263552000000 : ℝ), (2152233025744163/4855853684736000000 : ℝ)],
  ![(7479017/192000000 : ℝ), (13342675858523/777268224000000 : ℝ), (9660166859335303/1820945131776000000 : ℝ), (2000899954949/809308947456000000 : ℝ)],
  ![(831659/19200000 : ℝ), (1492008492923/77726822400000 : ℝ), (364769180288509/60698171059200000 : ℝ), (3878124910511/242792684236800000 : ℝ)]]

theorem oldJunctionCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients2]

theorem oldJunctionIdentity2 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients2
      ((δ-(27/64))/((15/32)-(27/64))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients2, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64) (15/32)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity2]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients2_lower

noncomputable def oldJunctionCoefficients3 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(831659/19200000 : ℝ), (1492008492923/77726822400000 : ℝ), (364769180288509/60698171059200000 : ℝ), (3878124910511/242792684236800000 : ℝ)],
  ![(1248967/24000000 : ℝ), (4518725767661/194317056000000 : ℝ), (3377223126823801/455236282944000000 : ℝ), (8694862298803/202327236864000000 : ℝ)],
  ![(1563829/24000000 : ℝ), (2966194537471/97158528000000 : ℝ), (2557191873930811/227618141472000000 : ℝ), (572683111882019/303490855296000000 : ℝ)]]

theorem oldJunctionCoefficients3_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients3]

theorem oldJunctionIdentity3 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients3
      ((δ-(15/32))/((9/16)-(15/32))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients3, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity3]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients3_lower

noncomputable def oldJunctionCoefficients4 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(1563829/24000000 : ℝ), (2966194537471/97158528000000 : ℝ), (2557191873930811/227618141472000000 : ℝ), (572683111882019/303490855296000000 : ℝ)],
  ![(2193553/24000000 : ℝ), (273741115297/6072408000000 : ℝ), (536794061871079/28452267684000000 : ℝ), (35249265598951/6322726152000000 : ℝ)],
  ![(101411/750000 : ℝ), (440214918493/6072408000000 : ℝ), (57103651449737/1580681538000000 : ℝ), (313564444382017/18968178456000000 : ℝ)]]

theorem oldJunctionCoefficients4_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients4 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients4]

theorem oldJunctionIdentity4 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients4
      ((δ-(9/16))/((3/4)-(9/16))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients4, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity4]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients4_lower
noncomputable def oldHalfPower (δ p : ℝ) : ℝ :=
  (-253861924/2371022307)*δ^2*p^3 +
  (46381178/263559375)*δ^2*p^2 +
  (-312409663/1054237500)*δ^2*p^1 +
  (1/2)*δ^2 +
  (1095065989057/4445666825625)*δ^1*p^2 +
  (1340594447/10542375000)*δ^1*p^1 +
  (-158453/187500)*δ^1 +
  (-4383469003/12650850000)*p^1 +
  (82531/150000)

noncomputable def oldHalfMinimum : ℝ := 247260208014103/4742044614000000

theorem oldHalfMinimum_pos : 0 < oldHalfMinimum := by
  norm_num [oldHalfMinimum]

noncomputable def oldHalfCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![
  ![(82531/150000 : ℝ), (37380023051/75905100000 : ℝ), (1031142314/2372034375 : ℝ), (1907539003/5060340000 : ℝ)],
  ![(349951/1500000 : ℝ), (278570178631/1518102000000 : ℝ), (1005751188690037/7113066921000000 : ℝ), (169114467746083/1580681538000000 : ℝ)],
  ![(296467/1500000 : ℝ), (194330779237/1518102000000 : ℝ), (194465574375673/2371022307000000 : ℝ), (247260208014103/4742044614000000 : ℝ)]]

theorem oldHalfCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    oldHalfMinimum ≤ oldHalfCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldHalfMinimum, oldHalfCoefficients0]

theorem oldHalfIdentity0 (δ p : ℝ) :
    oldHalfPower δ p = tensor oldHalfCoefficients0
      ((δ-(0))/((3/4)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldHalfPower, tensor, basis2, basis3,
    oldHalfCoefficients0, Fin.sum_univ_succ]
  ring

theorem oldHalfBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldHalfPower δ p := by
  rw [oldHalfIdentity0]
  exact tensor_pos oldHalfMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldHalfCoefficients0_lower

theorem newRowPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) (hreg : ¬ DetectorAffine.InRegion δ p) :
    0 < newRowPower δ p := by
  rcases le_or_gt δ (89/200) with h1 | h1
  · exact newRowBox0_pos ⟨hδ.1,h1⟩ hp
  rcases le_or_gt (97/200) δ with h2 | h2
  · exact newRowBox1_pos ⟨h2,hδ.2⟩ hp
  have h3 : p ≤ 199/400 := by
    by_contra hc
    exact hreg ⟨h1.le,h2.le,(lt_of_not_ge hc).le,hp.2⟩
  rcases le_total δ (93/200) with h4 | h4
  · exact newRowBox2_pos ⟨h1.le,h4⟩ ⟨hp.1,h3⟩
  · exact newRowBox3_pos ⟨h4,h2.le⟩ ⟨hp.1,h3⟩

theorem oldJunctionPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldJunctionPower δ p := by
  rcases le_total δ (3/8) with h1 | h1
  · exact oldJunctionBox0_pos ⟨hδ.1,h1⟩ hp
  rcases le_total δ (27/64) with h2 | h2
  · exact oldJunctionBox1_pos ⟨h1,h2⟩ hp
  rcases le_total δ (15/32) with h3 | h3
  · exact oldJunctionBox2_pos ⟨h2,h3⟩ hp
  rcases le_total δ (9/16) with h4 | h4
  · exact oldJunctionBox3_pos ⟨h3,h4⟩ hp
  · exact oldJunctionBox4_pos ⟨h4,hδ.2⟩ hp

theorem oldHalfPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldHalfPower δ p := oldHalfBox0_pos hδ hp

end
end Cycle63.Arithmetic.Bernstein
