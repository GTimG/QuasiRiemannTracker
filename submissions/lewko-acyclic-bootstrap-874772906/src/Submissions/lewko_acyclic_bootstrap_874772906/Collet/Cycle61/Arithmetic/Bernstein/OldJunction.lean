import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.Bernstein.Basis

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data from input/packet/references/37-endpoint-receipt.json.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldJunctionPower (δ p : ℝ) : ℝ :=
  (408757013/6000000000) +
  (-868438200950579/20242494000000000)*p^1 +
  (-17163958247/60000000000)*δ^1 +
  (2640821256499421/16868745000000000)*δ^1*p^1 +
  (25663691667794939/569109115750050000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-27011048373269789/33737490000000000)*δ^2*p^1 +
  (423273524161/843437250000)*δ^2*p^2 +
  (-516895955419/3794060771667)*δ^2*p^3

noncomputable def oldJunctionMinimum : ℝ := 8604603547887123299947/38851182301870080000000000

theorem oldJunctionMinimum_pos : 0 < oldJunctionMinimum := by
  norm_num [oldJunctionMinimum]

noncomputable def oldJunctionCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(408757013/6000000000 : ℝ), (7405823182159843/121454964000000000 : ℝ), (408586561325579/7590935250000000 : ℝ), (377929785350579/8096997600000000 : ℝ)],
    ![(13909247339/960000000000 : ℝ), (118838654443054991/9716397120000000000 : ℝ), (38889793160822061518389/3642298340800320000000000 : ℝ), (3977553182805064439503/404699815644480000000000 : ℝ)],
    ![(14958686299/480000000000 : ℝ), (116856840235001173/7773117696000000000 : ℝ), (15038245312962418556011/2428198893866880000000000 : ℝ), (10918392631405858550789/4856397787733760000000000 : ℝ)]]

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
  ![![(14958686299/480000000000 : ℝ), (1795488671796564689/77731176960000000000 : ℝ), (49115675540638521038953/2913838672640256000000000 : ℝ), (39293138677755580351759/3237598525155840000000000 : ℝ)],
    ![(45925497857/960000000000 : ℝ), (1276253507106231241/38865588480000000000 : ℝ), (155199239433446784282263/7284596681600640000000000 : ℝ), (61398779641673510755517/4856397787733760000000000 : ℝ)],
    ![(32358405779/240000000000 : ℝ), (2011425107637518993/19432794240000000000 : ℝ), (95637481291570211971867/1214099446933440000000000 : ℝ), (144298542058845795632477/2428198893866880000000000 : ℝ)]]

theorem oldJunctionCoefficients1_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients1]

theorem oldJunctionIdentity1 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients1
      ((δ-(3/8))/((3/4)-(3/8))) ((p-(0))/((1/4)-(0))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients1, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc (0) (1/4)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity1]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients1_lower

noncomputable def oldJunctionCoefficients2 : Fin 3 → Fin 4 → ℝ :=
  ![![(39293138677755580351759/3237598525155840000000000 : ℝ), (569757988893015459107963/58276773452805120000000000 : ℝ), (1775121834879341371169/227643646300020000000000 : ℝ), (7980343197688096351457/1295039410062336000000000 : ℝ)],
    ![(240676975316613762566311/19425591150935040000000000 : ℝ), (117126562745483501730913/12950394100623360000000000 : ℝ), (45514064548767732453973/7284596681600640000000000 : ℝ), (51086421297411940855991/12950394100623360000000000 : ℝ)],
    ![(940668702835343966607253/38851182301870080000000000 : ℝ), (887593620729290225498567/46621418762244096000000000 : ℝ), (106757848392634055129911/7284596681600640000000000 : ℝ), (284359495384251617042941/25900788201246720000000000 : ℝ)]]

theorem oldJunctionCoefficients2_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients2 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients2]

theorem oldJunctionIdentity2 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients2
      ((δ-(3/8))/((9/16)-(3/8))) ((p-(1/4))/((3/8)-(1/4))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients2, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity2]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients2_lower

noncomputable def oldJunctionCoefficients3 : Fin 3 → Fin 4 → ℝ :=
  ![![(7980343197688096351457/1295039410062336000000000 : ℝ), (131899849031408640305933/29138386726402560000000000 : ℝ), (62831668520142412764389/19425591150935040000000000 : ℝ), (10918392631405858550789/4856397787733760000000000 : ℝ)],
    ![(130889853274292904370561/25900788201246720000000000 : ℝ), (359464973349382888684001/116553546905610240000000000 : ℝ), (71468022283180197185191/46621418762244096000000000 : ℝ), (6861324963368519479909/19425591150935040000000000 : ℝ)],
    ![(129662408905532261499209/20720630560997376000000000 : ℝ), (352274076289603332964033/93242837524488192000000000 : ℝ), (337057153328849054988251/186485675048976384000000000 : ℝ), (1488483564974944150651/5180157640249344000000000 : ℝ)]]

theorem oldJunctionCoefficients3_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients3]

theorem oldJunctionIdentity3 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients3
      ((δ-(3/8))/((15/32)-(3/8))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients3, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity3]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients3_lower

noncomputable def oldJunctionCoefficients4 : Fin 3 → Fin 4 → ℝ :=
  ![![(129662408905532261499209/20720630560997376000000000 : ℝ), (352274076289603332964033/93242837524488192000000000 : ℝ), (337057153328849054988251/186485675048976384000000000 : ℝ), (1488483564974944150651/5180157640249344000000000 : ℝ)],
    ![(386532337979075498754923/51801576402493440000000000 : ℝ), (1042440434749250887452163/233107093811220480000000000 : ℝ), (64707036254162886872623/31080945841496064000000000 : ℝ), (8604603547887123299947/38851182301870080000000000 : ℝ)],
    ![(284359495384251617042941/25900788201246720000000000 : ℝ), (851109884176119671307893/116553546905610240000000000 : ℝ), (1813115517454847907379/418504656752640000000000 : ℝ), (7711104829354703708657/3885118230187008000000000 : ℝ)]]

theorem oldJunctionCoefficients4_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients4 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients4]

theorem oldJunctionIdentity4 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients4
      ((δ-(15/32))/((9/16)-(15/32))) ((p-(3/8))/((1/2)-(3/8))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients4, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity4]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients4_lower

noncomputable def oldJunctionCoefficients5 : Fin 3 → Fin 4 → ℝ :=
  ![![(940668702835343966607253/38851182301870080000000000 : ℝ), (403990498785104806917769/29138386726402560000000000 : ℝ), (778572198341709173150393/116553546905610240000000000 : ℝ), (7711104829354703708657/3885118230187008000000000 : ℝ)],
    ![(38888429306596122446719/1079199508385280000000000 : ℝ), (80240866023806812486987/3642298340800320000000000 : ℝ), (118061556041667246346793/9712795575467520000000000 : ℝ), (26765492223108358082477/4856397787733760000000000 : ℝ)],
    ![(144298542058845795632477/2428198893866880000000000 : ℝ), (4866106076727558366061/121409944693344000000000 : ℝ), (190287780982572467499889/7284596681600640000000000 : ℝ), (2206245482696271453817/134899938548160000000000 : ℝ)]]

theorem oldJunctionCoefficients5_lower (i : Fin 3) (j : Fin 4) :
    oldJunctionMinimum ≤ oldJunctionCoefficients5 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldJunctionMinimum, oldJunctionCoefficients5]

theorem oldJunctionIdentity5 (δ p : ℝ) :
    oldJunctionPower δ p = tensor oldJunctionCoefficients5
      ((δ-(9/16))/((3/4)-(9/16))) ((p-(1/4))/((1/2)-(1/4))) := by
  norm_num [oldJunctionPower, tensor, basis2, basis3,
    oldJunctionCoefficients5, Fin.sum_univ_succ]
  ring

theorem oldJunctionBox5_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < oldJunctionPower δ p := by
  rw [oldJunctionIdentity5]
  exact tensor_pos oldJunctionMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldJunctionCoefficients5_lower

end Cycle61.Arithmetic.Bernstein
