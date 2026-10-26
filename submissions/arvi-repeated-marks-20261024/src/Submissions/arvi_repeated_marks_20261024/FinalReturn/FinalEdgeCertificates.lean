/- Repeated marks: fork of Collet's final-stage module FinalEdgeCertificates (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_20261024.FinalReturn.FinalEnvelopeBounds
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_oldSmall
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_oldPeak
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_oldSwitch
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_newSwitch
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_newTop
import Submissions.arvi_repeated_marks_20261024.FinalReturn.Rows.Edge_newKink
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return.FinalEdges
open QRH.Record1252270103Return
noncomputable section

theorem window01_mem : returnWindow01∈returnWindows := by simp [returnWindows]
theorem window02_mem : returnWindow02∈returnWindows := by simp [returnWindows]
theorem window03_mem : returnWindow03∈returnWindows := by simp [returnWindows]
theorem window04_mem : returnWindow04∈returnWindows := by simp [returnWindows]
theorem window05_mem : returnWindow05∈returnWindows := by simp [returnWindows]
theorem window06_mem : returnWindow06∈returnWindows := by simp [returnWindows]
theorem window07_mem : returnWindow07∈returnWindows := by simp [returnWindows]
theorem window08_mem : returnWindow08∈returnWindows := by simp [returnWindows]
theorem window09_mem : returnWindow09∈returnWindows := by simp [returnWindows]
theorem window10_mem : returnWindow10∈returnWindows := by simp [returnWindows]
theorem window11_mem : returnWindow11∈returnWindows := by simp [returnWindows]
theorem envelope_row001 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row001_pos hδ hp) hR
theorem envelope_row002 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row002_pos hδ hp) hR
theorem envelope_row003 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row003_pos hδ hp) hR
theorem envelope_row004 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row004_pos hδ hp) hR
theorem envelope_row005 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row005_pos hδ hp) hR
theorem envelope_row006 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row006_pos hδ hp) hR
theorem envelope_row007 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row007_pos hδ hp) hR
theorem envelope_row008 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row008_pos hδ hp) hR
theorem envelope_row009 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row009_pos hδ hp) hR
theorem envelope_row010 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row010_pos hδ hp) hR
theorem envelope_row011 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row011_pos hδ hp) hR
theorem envelope_row012 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (51/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row012_pos hδ hp) hR
theorem envelope_row013 {δ p:ℝ} (hδ:δ∈Set.Icc (51/128:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow01.Available δ p := by
  change δ∈Set.Icc (51/128:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow01 window01_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row013_pos hδ hp) hR
theorem envelope_row014 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row014_pos hδ hp) hR
theorem envelope_row015 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow02.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow02 window02_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row015_pos hδ hp) hR
theorem envelope_row016 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row016_pos hδ hp) hR
theorem envelope_row017 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow03.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow03 window03_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row017_pos hδ hp) hR
theorem envelope_row018 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row018_pos hδ hp) hR
theorem envelope_row019 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow05.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow05 window05_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row019_pos hδ hp) hR
theorem envelope_row020 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row020_pos hδ hp) hR
theorem envelope_row021 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row021_pos hδ hp) hR
theorem envelope_row022 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (933/2048:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (933/2048:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row022_pos hδ hp) hR
theorem envelope_row023 {δ p:ℝ} (hδ:δ∈Set.Icc (933/2048:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (933/2048:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row023_pos hδ hp) hR
theorem envelope_row024 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row024_pos hδ hp) hR
theorem envelope_row025 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row025_pos hδ hp) hR
theorem envelope_row026 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row026_pos hδ hp) hR
theorem envelope_row027 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope finalCountScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row027_pos hδ hp) hR
theorem envelope_row028 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row028_pos hδ hp) hR
theorem envelope_row029 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row029_pos hδ hp) hR
theorem envelope_row030 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row030_pos hδ hp) hR
theorem envelope_row031 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row031_pos hδ hp) hR
theorem envelope_row032 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row032_pos hδ hp) hR
theorem envelope_row033 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row033_pos hδ hp) hR
theorem envelope_row034 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row034_pos hδ hp) hR
theorem cover_node_000 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row001 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem edge_oldSmall_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_000 (by simpa using hδ) (by simpa using hp)
theorem cover_node_001 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row002 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem edge_oldPeak_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_001 (by simpa using hδ) (by simpa using hp)
theorem cover_node_002 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row003 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_003 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row004 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_004 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hsplit | hsplit
 · exact cover_node_002 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_003 ⟨hsplit,hδ.2⟩ hp
theorem edge_oldSwitch_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_004 (by simpa using hδ) (by simpa using hp)
theorem cover_node_005 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row005 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_006 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row006 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_007 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hsplit | hsplit
 · exact cover_node_005 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_006 ⟨hsplit,hδ.2⟩ hp
theorem edge_newSwitch_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_007 (by simpa using hδ) (by simpa using hp)
theorem cover_node_008 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row007 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_009 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row008 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_010 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row009 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_011 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row010 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_012 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row011 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_013 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (51/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row012 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_014 {δ p:ℝ} (hδ:δ∈Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row013 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_015 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (51/128:ℝ) with hsplit | hsplit
 · exact cover_node_013 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_014 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_016 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hsplit | hsplit
 · exact cover_node_012 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_015 hδ ⟨hsplit,hp.2⟩
theorem cover_node_017 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row014 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_018 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row015 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_019 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row016 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_020 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row017 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_021 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row018 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_022 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row019 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_023 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row020 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_024 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row021 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_025 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (933/2048:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row022 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_026 {δ p:ℝ} (hδ:δ∈Set.Icc (933/2048:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row023 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_027 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (933/2048:ℝ) with hsplit | hsplit
 · exact cover_node_025 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_026 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_028 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hsplit | hsplit
 · exact cover_node_024 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_027 hδ ⟨hsplit,hp.2⟩
theorem cover_node_029 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hsplit | hsplit
 · exact cover_node_023 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_028 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_030 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hsplit | hsplit
 · exact cover_node_022 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_029 hδ ⟨hsplit,hp.2⟩
theorem cover_node_031 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hsplit | hsplit
 · exact cover_node_021 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_030 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_032 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hsplit | hsplit
 · exact cover_node_020 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_031 hδ ⟨hsplit,hp.2⟩
theorem cover_node_033 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row024 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_034 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hsplit | hsplit
 · exact cover_node_032 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_033 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_035 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hsplit | hsplit
 · exact cover_node_019 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_034 hδ ⟨hsplit,hp.2⟩
theorem cover_node_036 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hsplit | hsplit
 · exact cover_node_018 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_035 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_037 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hsplit | hsplit
 · exact cover_node_017 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_036 hδ ⟨hsplit,hp.2⟩
theorem cover_node_038 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hsplit | hsplit
 · exact cover_node_016 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_037 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_039 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hsplit | hsplit
 · exact cover_node_011 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_038 hδ ⟨hsplit,hp.2⟩
theorem cover_node_040 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row025 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_041 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row026 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_042 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row027 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_043 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row028 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_044 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hsplit | hsplit
 · exact cover_node_042 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_043 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_045 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hsplit | hsplit
 · exact cover_node_041 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_044 hδ ⟨hsplit,hp.2⟩
theorem cover_node_046 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row029 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_047 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hsplit | hsplit
 · exact cover_node_045 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_046 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_048 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hsplit | hsplit
 · exact cover_node_040 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_047 hδ ⟨hsplit,hp.2⟩
theorem cover_node_049 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hsplit | hsplit
 · exact cover_node_039 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_048 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_050 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hsplit | hsplit
 · exact cover_node_010 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_049 hδ ⟨hsplit,hp.2⟩
theorem cover_node_051 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row030 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_052 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hsplit | hsplit
 · exact cover_node_050 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_051 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_053 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hsplit | hsplit
 · exact cover_node_009 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_052 hδ ⟨hsplit,hp.2⟩
theorem cover_node_054 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hsplit | hsplit
 · exact cover_node_008 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_053 ⟨hsplit,hδ.2⟩ hp
theorem edge_newTop_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_054 (by simpa using hδ) (by simpa using hp)
theorem cover_node_055 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row031 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_056 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row032 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_057 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row033 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_058 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact envelope_row034 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_059 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hsplit | hsplit
 · exact cover_node_057 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_058 ⟨hsplit,hδ.2⟩ hp
theorem cover_node_060 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hsplit | hsplit
 · exact cover_node_056 hδ ⟨hp.1,hsplit⟩
 · exact cover_node_059 hδ ⟨hsplit,hp.2⟩
theorem cover_node_061 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hsplit | hsplit
 · exact cover_node_055 ⟨hδ.1,hsplit⟩ hp
 · exact cover_node_060 ⟨hsplit,hδ.2⟩ hp
theorem edge_newKink_certificate {δ p:ℝ} (hδ:δ∈Set.Icc 0 (3/4))
 (hp:p∈Set.Icc 0 (1/2)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 exact cover_node_061 (by simpa using hδ) (by simpa using hp)
theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-rowFee := by
 cases e with
 | oldSmall => exact edge_oldSmall_certificate hδ hp
 | oldPeak => exact edge_oldPeak_certificate hδ hp
 | oldSwitch => exact edge_oldSwitch_certificate hδ hp
 | newSwitch => exact edge_newSwitch_certificate hδ hp
 | newTop => exact edge_newTop_certificate hδ hp
 | newKink => exact edge_newKink_certificate hδ hp
#print axioms QRH.RepeatedMarks.Return.FinalEdges.closed_envelope_return_cover

end
end QRH.RepeatedMarks.Return.FinalEdges
