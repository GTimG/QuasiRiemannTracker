import Candidate.Target830.Count.Windows
import Candidate.Cycle63.Arithmetic.Bernstein.Basis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def w0_dn_power (δ p : ℝ) : ℝ := (3)*δ^0*p^0 +
  (-84999/44999)*δ^0*p^1
def w0_dn_minimum : ℝ := 184995/89998
def w0_dn_table : Fin 3 → Fin 4 → ℝ := ![
  ![(11924679/5759872:ℝ), (5948173/2879936:ℝ), (11868013/5759872:ℝ), (184995/89998:ℝ)],
  ![(11924679/5759872:ℝ), (5948173/2879936:ℝ), (11868013/5759872:ℝ), (184995/89998:ℝ)],
  ![(11924679/5759872:ℝ), (5948173/2879936:ℝ), (11868013/5759872:ℝ), (184995/89998:ℝ)]]
theorem w0_dn_lower (i : Fin 3) (j : Fin 4) :
    w0_dn_minimum ≤ w0_dn_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_dn_minimum,w0_dn_table]
theorem w0_dn_identity (δ p : ℝ) :
    w0_dn_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_dn_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_dn_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_dn_table,Fin.sum_univ_succ]
  ring
theorem w0_dn_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_dn_power δ p := by
  rw [w0_dn_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_dn_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_dn_lower
theorem w0_dn_binding (δ p : ℝ) :
    w0_dn_power δ p=guardD Plane.oldWeak δ p := by
  norm_num [w0_dn_power,guardD,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_aa_power (δ p : ℝ) : ℝ := (2)*δ^0*p^0 +
  (-40000/44999)*δ^0*p^1
def w0_aa_minimum : ℝ := 69998/44999
def w0_aa_table : Fin 3 → Fin 4 → ℝ := ![
  ![(140621/89998:ℝ), (210619/134997:ℝ), (420613/269994:ℝ), (69998/44999:ℝ)],
  ![(140621/89998:ℝ), (210619/134997:ℝ), (420613/269994:ℝ), (69998/44999:ℝ)],
  ![(140621/89998:ℝ), (210619/134997:ℝ), (420613/269994:ℝ), (69998/44999:ℝ)]]
theorem w0_aa_lower (i : Fin 3) (j : Fin 4) :
    w0_aa_minimum ≤ w0_aa_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_aa_minimum,w0_aa_table]
theorem w0_aa_identity (δ p : ℝ) :
    w0_aa_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_aa_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_aa_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_aa_table,Fin.sum_univ_succ]
  ring
theorem w0_aa_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_aa_power δ p := by
  rw [w0_aa_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_aa_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_aa_lower
theorem w0_aa_binding (δ p : ℝ) :
    w0_aa_power δ p=guardA Plane.oldWeak δ p := by
  norm_num [w0_aa_power,guardA,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_cc_power (δ p : ℝ) : ℝ := (1)*δ^0*p^0 +
  (-1005451199/2249950000)*δ^0*p^1
def w0_cc_minimum : ℝ := 3494448801/4499900000
def w0_cc_table : Fin 3 → Fin 4 → ℝ := ![
  ![(224650174463/287993600000:ℝ), (67294507219/86398080000:ℝ), (671939620991/863980800000:ℝ), (3494448801/4499900000:ℝ)],
  ![(224650174463/287993600000:ℝ), (67294507219/86398080000:ℝ), (671939620991/863980800000:ℝ), (3494448801/4499900000:ℝ)],
  ![(224650174463/287993600000:ℝ), (67294507219/86398080000:ℝ), (671939620991/863980800000:ℝ), (3494448801/4499900000:ℝ)]]
theorem w0_cc_lower (i : Fin 3) (j : Fin 4) :
    w0_cc_minimum ≤ w0_cc_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_cc_minimum,w0_cc_table]
theorem w0_cc_identity (δ p : ℝ) :
    w0_cc_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_cc_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_cc_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_cc_table,Fin.sum_univ_succ]
  ring
theorem w0_cc_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_cc_power δ p := by
  rw [w0_cc_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_cc_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_cc_lower
theorem w0_cc_binding (δ p : ℝ) :
    w0_cc_power δ p=guardC Plane.oldWeak δ p := by
  norm_num [w0_cc_power,guardC,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_j_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-141665/89998)*δ^0*p^1 +
  (-1)*δ^1*p^0 +
  (-1)*δ^1*p^1 +
  (40000/44999)*δ^1*p^2
def w0_j_minimum : ℝ := 13177971/11519744
def w0_j_table : Fin 3 → Fin 4 → ℝ := ![
  ![(3455164817/2949054464:ℝ), (10327979683/8847163392:ℝ), (5145267145/4423581696:ℝ), (26700933/23039488:ℝ)],
  ![(6866202655/5898108928:ℝ), (20523544685/17694326784:ℝ), (10224311015/8847163392:ℝ), (53056875/46078976:ℝ)],
  ![(1705518919/1474527232:ℝ), (5097782501/4423581696:ℝ), (2539521935/2211790848:ℝ), (13177971/11519744:ℝ)]]
theorem w0_j_lower (i : Fin 3) (j : Fin 4) :
    w0_j_minimum ≤ w0_j_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_j_minimum,w0_j_table]
theorem w0_j_identity (δ p : ℝ) :
    w0_j_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_j_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_j_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_j_table,Fin.sum_univ_succ]
  ring
theorem w0_j_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_j_power δ p := by
  rw [w0_j_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_j_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_j_lower
theorem w0_j_binding (δ p : ℝ) :
    w0_j_power δ p=guardJ Plane.oldWeak δ p := by
  norm_num [w0_j_power,guardJ,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_tlo_power (δ p : ℝ) : ℝ := (1)*δ^1*p^0 +
  (-3255401199/2249950000)*δ^1*p^1 +
  (1005451199/2249950000)*δ^1*p^2
def w0_tlo_minimum : ℝ := 387883816911/2303948800000
def w0_tlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(324170201750109/1887394856960000:ℝ), (1610120842161819/9436974284800000:ℝ), (780970643197/4607897600000:ℝ), (387883816911/2303948800000:ℝ)],
  ![(26284070412171/150991588556800:ℝ), (130550338553661/754957942784000:ℝ), (63321944043/368631808000:ℝ), (31450039209/184315904000:ℝ)],
  ![(166465779277083/943697428480000:ℝ), (826818810839853/4718487142400000:ℝ), (401038978939/2303948800000:ℝ), (199183581657/1151974400000:ℝ)]]
theorem w0_tlo_lower (i : Fin 3) (j : Fin 4) :
    w0_tlo_minimum ≤ w0_tlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_tlo_minimum,w0_tlo_table]
theorem w0_tlo_identity (δ p : ℝ) :
    w0_tlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_tlo_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_tlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_tlo_table,Fin.sum_univ_succ]
  ring
theorem w0_tlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_tlo_power δ p := by
  rw [w0_tlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_tlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_tlo_lower
theorem w0_tlo_binding (δ p : ℝ) :
    w0_tlo_power δ p=guardTLo Plane.oldWeak δ p := by
  norm_num [w0_tlo_power,guardTLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_thi_power (δ p : ℝ) : ℝ := (2499/4000)*δ^0*p^0 +
  (-4164951/10588000)*δ^0*p^1 +
  (-12499/10000)*δ^1*p^0 +
  (1346569347/1124975000)*δ^1*p^1 +
  (-505651199/2249950000)*δ^1*p^2
def w0_thi_minimum : ℝ := 106308094552101/943697428480000
def w0_thi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(228435038421603/1887394856960000:ℝ), (1142905422138661/9436974284800000:ℝ), (8934507367773/73726361600000:ℝ), (279372498759/2303948800000:ℝ)],
  ![(88210245505161/754957942784000:ℝ), (88279904295683/754957942784000:ℝ), (690219110411/5898108928000:ℝ), (21585613041/184315904000:ℝ)],
  ![(106308094552101/943697428480000:ℝ), (532046092626707/4718487142400000:ℝ), (4160485196251/36863180800000:ℝ), (130133913633/1151974400000:ℝ)]]
theorem w0_thi_lower (i : Fin 3) (j : Fin 4) :
    w0_thi_minimum ≤ w0_thi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_thi_minimum,w0_thi_table]
theorem w0_thi_identity (δ p : ℝ) :
    w0_thi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_thi_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_thi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_thi_table,Fin.sum_univ_succ]
  ring
theorem w0_thi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_thi_power δ p := by
  rw [w0_thi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_thi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_thi_lower
theorem w0_thi_binding (δ p : ℝ) :
    w0_thi_power δ p=guardTHi Plane.oldWeak δ p := by
  norm_num [w0_thi_power,guardTHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_rlo_power (δ p : ℝ) : ℝ := (25/74)*δ^0*p^0 +
  (-29380855637/33299260000)*δ^0*p^1 +
  (37162238853713/88143141220000)*δ^0*p^2 +
  (69/37)*δ^1*p^0 +
  (-303851833089/83248150000)*δ^1*p^1 +
  (9619431819860637/3746083501850000)*δ^1*p^2 +
  (-47599440000/74921670037)*δ^1*p^3
def w0_rlo_minimum : ℝ := 201996230051315853/767197901178880000
def w0_rlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(4277468716321317073219/15712213016143462400000:ℝ), (12690740279576912387731/47136639048430387200000:ℝ), (16341349503370459289/61375832094310400000:ℝ), (201996230051315853/767197901178880000:ℝ)],
  ![(1733624645375884006057/6284885206457384960000:ℝ), (5143751892913126896793/18854655619372154880000:ℝ), (6623784265899356267/24550332837724160000:ℝ), (81881749607644359/306879160471552000:ℝ)],
  ![(2195327255279051478533/7856106508071731200000:ℝ), (6514009592494361048117/23568319524215193600000:ℝ), (8388785913063161023/30687916047155200000:ℝ), (103706258993452971/383598950589440000:ℝ)]]
theorem w0_rlo_lower (i : Fin 3) (j : Fin 4) :
    w0_rlo_minimum ≤ w0_rlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_rlo_minimum,w0_rlo_table]
theorem w0_rlo_identity (δ p : ℝ) :
    w0_rlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_rlo_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_rlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_rlo_table,Fin.sum_univ_succ]
  ring
theorem w0_rlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_rlo_power δ p := by
  rw [w0_rlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_rlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_rlo_lower
theorem w0_rlo_binding (δ p : ℝ) :
    w0_rlo_power δ p=guardRLo Plane.oldWeak δ p := by
  norm_num [w0_rlo_power,guardRLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_rhi_power (δ p : ℝ) : ℝ := (5/2)*δ^0*p^0 +
  (-2422101199/899980000)*δ^0*p^1 +
  (28487448821267/40498200020000)*δ^0*p^2 +
  (-3)*δ^1*p^0 +
  (7266303597/2249950000)*δ^1*p^1 +
  (-85462346463801/101245500050000)*δ^1*p^2
def w0_rhi_minimum : ℝ := 6421458522347217/10367539205120000
def w0_rhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(274138844617979539913/424654405841715200000:ℝ), (819235530535915905737/1273963217525145600000:ℝ), (1062582386542553803/1658806272819200000:ℝ), (13230790378259031/20735078410240000:ℝ)],
  ![(108048209116532652539/169861762336686080000:ℝ), (322890876856175324411/509585287010058240000:ℝ), (418802829875078209/663522509127680000:ℝ), (5214741484590693/8294031364096000:ℝ)],
  ![(133051100482341861391/212327202920857600000:ℝ), (397609426872480358159/636981608762572800000:ℝ), (515715881416418621/829403136409600000:ℝ), (6421458522347217/10367539205120000:ℝ)]]
theorem w0_rhi_lower (i : Fin 3) (j : Fin 4) :
    w0_rhi_minimum ≤ w0_rhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_rhi_minimum,w0_rhi_table]
theorem w0_rhi_identity (δ p : ℝ) :
    w0_rhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_rhi_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_rhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_rhi_table,Fin.sum_univ_succ]
  ring
theorem w0_rhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_rhi_power δ p := by
  rw [w0_rhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_rhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_rhi_lower
theorem w0_rhi_binding (δ p : ℝ) :
    w0_rhi_power δ p=guardRHi Plane.oldWeak δ p := by
  norm_num [w0_rhi_power,guardRHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_mlo_power (δ p : ℝ) : ℝ := (-476425597/800000000)*δ^0*p^0 +
  (21722542459801/17999600000000)*δ^0*p^1 +
  (-848474708088201733/1619928000800000000)*δ^0*p^2 +
  (2476425597/2000000000)*δ^1*p^0 +
  (-114360945500199/44999000000000)*δ^1*p^1 +
  (121430553560199/89998000000000)*δ^1*p^2 +
  (-7648890012/50622750025)*δ^1*p^3
def w0_mlo_minimum : ℝ := 90094022300405609759/16986176233668608000000000
def w0_mlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(90094022300405609759/16986176233668608000000000:ℝ), (933764882191895332111/2997560511823872000000000:ℝ), (81877450419172999157/132704501825536000000000:ℝ), (764477604700001667/829403136409600000000:ℝ)],
  ![(11828263133006405301437/6794470493467443200000000:ℝ), (41314776794754587120477/20383411480402329600000000:ℝ), (24548326792100955187/10616360146042880000000:ℝ), (6892991661739869/2654090036510720000:ℝ)],
  ![(29525610821365810448713/8493088116834304000000000:ℝ), (95349940488255357478249/25479264350502912000000000:ℝ), (265915359691675440259/66352250912768000000000:ℝ), (1771821091943708229/414701568204800000000:ℝ)]]
theorem w0_mlo_lower (i : Fin 3) (j : Fin 4) :
    w0_mlo_minimum ≤ w0_mlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_mlo_minimum,w0_mlo_table]
theorem w0_mlo_identity (δ p : ℝ) :
    w0_mlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_mlo_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_mlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_mlo_table,Fin.sum_univ_succ]
  ring
theorem w0_mlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_mlo_power δ p := by
  rw [w0_mlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_mlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_mlo_lower
theorem w0_mlo_binding (δ p : ℝ) :
    w0_mlo_power δ p=guardMLo Plane.oldWeak δ p := by
  norm_num [w0_mlo_power,guardMLo,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_mhi_power (δ p : ℝ) : ℝ := (16912523/25000000)*δ^0*p^0 +
  (-46011360299/35155468750)*δ^0*p^1 +
  (28139797709583197/50622750025000000)*δ^0*p^2 +
  (-79412523/62500000)*δ^1*p^0 +
  (3556911695841/1406218750000)*δ^1*p^1 +
  (-3656383562091/2812437500000)*δ^1*p^2 +
  (13462506010713/101245500050000)*δ^1*p^3
def w0_mhi_minimum : ℝ := 68403813906238191/3239856001600000000
def w0_mhi_table : Fin 3 → Fin 4 → ℝ := ![
  ![(889435770039912394657241/33972352467337216000000000:ℝ), (1204549451944915308713/46836882997248000000000:ℝ), (209476902899783329999/8294031364096000000000:ℝ), (160673004036267993/6479712003200000000:ℝ)],
  ![(329917544833371927579563/13588940986934886400000000:ℝ), (7591461052775520414091/318490804381286400000000:ℝ), (15522788774582391209/663522509127680000000:ℝ), (475969010957991/20735078410240000:ℝ)],
  ![(380075977063473621620287/16986176233668608000000000:ℝ), (8739982290407020911167/398113505476608000000000:ℝ), (89296408232388225113/4147015682048000000000:ℝ), (68403813906238191/3239856001600000000:ℝ)]]
theorem w0_mhi_lower (i : Fin 3) (j : Fin 4) :
    w0_mhi_minimum ≤ w0_mhi_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_mhi_minimum,w0_mhi_table]
theorem w0_mhi_identity (δ p : ℝ) :
    w0_mhi_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_mhi_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_mhi_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_mhi_table,Fin.sum_univ_succ]
  ring
theorem w0_mhi_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_mhi_power δ p := by
  rw [w0_mhi_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_mhi_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_mhi_lower
theorem w0_mhi_binding (δ p : ℝ) :
    w0_mhi_power δ p=guardMHi Plane.oldWeak δ p := by
  norm_num [w0_mhi_power,guardMHi,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_widthlo_power (δ p : ℝ) : ℝ := (696461/1000000)*δ^0*p^0 +
  (-15006399769/11249750000)*δ^0*p^1 +
  (1141615040028479/2024910001000000)*δ^0*p^2 +
  (-3196461/2500000)*δ^1*p^0 +
  (142110140487/56248750000)*δ^1*p^1 +
  (-144891410337/112497500000)*δ^1*p^2 +
  (13010082853401/101245500050000)*δ^1*p^3
def w0_widthlo_minimum : ℝ := 7094300298558849/259188480128000000
def w0_widthlo_table : Fin 3 → Fin 4 → ℝ := ![
  ![(44349589239799044007937/1358894098693488640000000:ℝ), (30101720412764780533/936737659944960000000:ℝ), (10495106845036105843/331761254563840000000:ℝ), (16140293509761927/518376960256000000:ℝ)],
  ![(16683158778664094758691/543557639477395456000000:ℝ), (192440176462119401231/6369816087625728000000:ℝ), (789104606002652453/26540900365107200000:ℝ), (242631152855037/8294031364096000:ℝ)],
  ![(19533102326760714892759/679447049346744320000000:ℝ), (225235817646797868547/7962270109532160000000:ℝ), (4616254152515102741/165880627281920000000:ℝ), (7094300298558849/259188480128000000:ℝ)]]
theorem w0_widthlo_lower (i : Fin 3) (j : Fin 4) :
    w0_widthlo_minimum ≤ w0_widthlo_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_widthlo_minimum,w0_widthlo_table]
theorem w0_widthlo_identity (δ p : ℝ) :
    w0_widthlo_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_widthlo_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_widthlo_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_widthlo_table,Fin.sum_univ_succ]
  ring
theorem w0_widthlo_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_widthlo_power δ p := by
  rw [w0_widthlo_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_widthlo_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_widthlo_lower
theorem w0_widthlo_binding (δ p : ℝ) :
    w0_widthlo_power δ p=guardWidth Plane.oldWeak δ p := by
  norm_num [w0_widthlo_power,guardWidth,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_tail_power (δ p : ℝ) : ℝ := (16912523/37500000)*δ^1*p^0 +
  (-223588898089/281243750000)*δ^1*p^1 +
  (716454599/2699940000)*δ^1*p^2 +
  (-26470841/31250000)*δ^2*p^0 +
  (269257531277/175777343750)*δ^2*p^1 +
  (-58572559/89998000)*δ^2*p^2 +
  (160/2647)*δ^2*p^3
def w0_tail_minimum : ℝ := 599495552116029/92157952000000000
def w0_tail_table : Fin 3 → Fin 4 → ℝ := ![
  ![(12032216086614196213/1509915885568000000000:ℝ), (11813407774480000179/1509915885568000000000:ℝ), (54351050256338579/7077730713600000000:ℝ), (2777508083287341/368631808000000000:ℝ)],
  ![(5630206708843975011/754957942784000000000:ℝ), (5523994775643907893/754957942784000000000:ℝ), (1693096414393627/235924357120000000:ℝ), (1296863320706667/184315904000000000:ℝ)],
  ![(2609525657682179717/377478971392000000000:ℝ), (2558142036499674531/377478971392000000000:ℝ), (11750675118351619/1769432678400000000:ℝ), (599495552116029/92157952000000000:ℝ)]]
theorem w0_tail_lower (i : Fin 3) (j : Fin 4) :
    w0_tail_minimum ≤ w0_tail_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_tail_minimum,w0_tail_table]
theorem w0_tail_identity (δ p : ℝ) :
    w0_tail_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_tail_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_tail_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_tail_table,Fin.sum_univ_succ]
  ring
theorem w0_tail_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_tail_power δ p := by
  rw [w0_tail_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_tail_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_tail_lower
theorem w0_tail_binding (δ p : ℝ) :
    w0_tail_power δ p=guardTail Plane.oldWeak δ p := by
  norm_num [w0_tail_power,guardTail,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

def w0_monotone_power (δ p : ℝ) : ℝ := (1838751199/899980000)*δ^0*p^0 +
  (-1005451199/449990000)*δ^0*p^1 +
  (28487448821267/40498200020000)*δ^0*p^2 +
  (-5505351199/2249950000)*δ^1*p^0 +
  (176791247/66175000)*δ^1*p^1 +
  (-84971749456199/101245500050000)*δ^1*p^2
def w0_monotone_minimum : ℝ := 26621203257002097/51837696025600000
def w0_monotone_table : Fin 3 → Fin 4 → ℝ := ![
  ![(227106453504064354103/424654405841715200000:ℝ), (678858392784666887351/1273963217525145600000:ℝ), (1761474544688012201/3317612545638400000:ℝ), (54847237763572791/103675392051200000:ℝ)],
  ![(89513605272237525509/169861762336686080000:ℝ), (267570778078493401733/509585287010058240000:ℝ), (694281795308455579/1327045018255360000:ℝ), (21617928855515397/41470156820480000:ℝ)],
  ![(110230786428561636721/212327202920857600000:ℝ), (329497748803900060657/636981608762572800000:ℝ), (854967215927132847/1658806272819200000:ℝ), (26621203257002097/51837696025600000:ℝ)]]
theorem w0_monotone_lower (i : Fin 3) (j : Fin 4) :
    w0_monotone_minimum ≤ w0_monotone_table i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w0_monotone_minimum,w0_monotone_table]
theorem w0_monotone_identity (δ p : ℝ) :
    w0_monotone_power δ p = Cycle63.Arithmetic.Bernstein.tensor w0_monotone_table
      ((δ-(111/256))/((57/128)-(111/256)))
      ((p-(63/128))/((1/2)-(63/128))) := by
  norm_num [w0_monotone_power,Cycle63.Arithmetic.Bernstein.tensor,
    Cycle63.Arithmetic.Bernstein.basis2,Cycle63.Arithmetic.Bernstein.basis3,
    w0_monotone_table,Fin.sum_univ_succ]
  ring
theorem w0_monotone_positive {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2)) :
    0 < w0_monotone_power δ p := by
  rw [w0_monotone_identity]
  exact Cycle63.Arithmetic.Bernstein.tensor_pos
    (by norm_num [w0_monotone_minimum])
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hδ)
    (Cycle63.Arithmetic.Bernstein.normalize_mem (by norm_num) hp) w0_monotone_lower
theorem w0_monotone_binding (δ p : ℝ) :
    w0_monotone_power δ p=guardMonotone Plane.oldWeak δ p := by
  norm_num [w0_monotone_power,guardMonotone,affineD,affineA,affineC,affineU,affineJ,affineN,affineTNum,affineRNum,affineMNum,affineAntitone,affineUPrime,affineJPrime,Plane.lambda,Plane.B,SourcePlane.lambda,SourcePlane.B,mHi,kappa0,widthLower,widthUpper,plainLower]
  <;> ring

theorem window0_admissible (δ p : ℝ) (ha : window0.Available δ p) :
    Admissible window0.plane δ p := by
  have hd : δ ∈ Set.Icc (111/256:ℝ) (57/128) := ha.1
  have hp : p ∈ Set.Icc (63/128:ℝ) (1/2) := ha.2
  change Admissible Plane.oldWeak δ p
  constructor
  · rw [←w0_dn_binding]
    exact w0_dn_positive hd hp
  · rw [←w0_aa_binding]
    exact w0_aa_positive hd hp
  · rw [←w0_cc_binding]
    exact w0_cc_positive hd hp
  · rw [←w0_j_binding]
    exact w0_j_positive hd hp
  · rw [←w0_tlo_binding]
    exact w0_tlo_positive hd hp
  · rw [←w0_thi_binding]
    exact w0_thi_positive hd hp
  · rw [←w0_rlo_binding]
    exact w0_rlo_positive hd hp
  · rw [←w0_rhi_binding]
    exact w0_rhi_positive hd hp
  · rw [←w0_mlo_binding]
    exact w0_mlo_positive hd hp
  · rw [←w0_mhi_binding]
    exact w0_mhi_positive hd hp
  · rw [←w0_widthlo_binding]
    exact w0_widthlo_positive hd hp
  · rw [←w0_tail_binding]
    exact w0_tail_positive hd hp
  · rw [←w0_monotone_binding]
    exact w0_monotone_positive hd hp

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.window0_admissible
