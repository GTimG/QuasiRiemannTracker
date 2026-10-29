/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.FinalEnvelopeBounds
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part00
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part01
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part02
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part03
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part04
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part05
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part06
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part07
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part08
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part09
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part10
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Rows.Part11
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section
theorem window01_mem : returnWindow01 ∈ returnWindows := by simp [returnWindows]
theorem window02_mem : returnWindow02 ∈ returnWindows := by simp [returnWindows]
theorem window03_mem : returnWindow03 ∈ returnWindows := by simp [returnWindows]
theorem window04_mem : returnWindow04 ∈ returnWindows := by simp [returnWindows]
theorem window05_mem : returnWindow05 ∈ returnWindows := by simp [returnWindows]
theorem window06_mem : returnWindow06 ∈ returnWindows := by simp [returnWindows]
theorem window07_mem : returnWindow07 ∈ returnWindows := by simp [returnWindows]
theorem window08_mem : returnWindow08 ∈ returnWindows := by simp [returnWindows]
theorem window09_mem : returnWindow09 ∈ returnWindows := by simp [returnWindows]
theorem window10_mem : returnWindow10 ∈ returnWindows := by simp [returnWindows]
theorem window11_mem : returnWindow11 ∈ returnWindows := by simp [returnWindows]
theorem window12_mem : returnWindow12 ∈ returnWindows := by simp [returnWindows]
theorem window13_mem : returnWindow13 ∈ returnWindows := by simp [returnWindows]
theorem window14_mem : returnWindow14 ∈ returnWindows := by simp [returnWindows]
theorem window15_mem : returnWindow15 ∈ returnWindows := by simp [returnWindows]
theorem window16_mem : returnWindow16 ∈ returnWindows := by simp [returnWindows]
theorem window17_mem : returnWindow17 ∈ returnWindows := by simp [returnWindows]

theorem envelope_row000 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row000_pos hδ hp) hR

theorem envelope_row001 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row001_pos hδ hp) hR

theorem envelope_row002 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row002_pos hδ hp) hR

theorem envelope_row003 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row003_pos hδ hp) hR

theorem envelope_row004 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row004_pos hδ hp) hR

theorem envelope_row005 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row005_pos hδ hp) hR

theorem envelope_row006 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row006_pos hδ hp) hR

theorem envelope_row007 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row007_pos hδ hp) hR

theorem envelope_row008 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row008_pos hδ hp) hR

theorem envelope_row009 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row009_pos hδ hp) hR

theorem envelope_row010 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row010_pos hδ hp) hR

theorem envelope_row011 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row011_pos hδ hp) hR

theorem envelope_row012 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row012_pos hδ hp) hR

theorem envelope_row013 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row013_pos hδ hp) hR

theorem envelope_row014 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row014_pos hδ hp) hR

theorem envelope_row015 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row015_pos hδ hp) hR

theorem envelope_row016 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row016_pos hδ hp) hR

theorem envelope_row017 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row017_pos hδ hp) hR

theorem envelope_row018 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row018_pos hδ hp) hR

theorem envelope_row019 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row019_pos hδ hp) hR

theorem envelope_row020 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row020_pos hδ hp) hR

theorem envelope_row021 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row021_pos hδ hp) hR

theorem envelope_row022 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row022_pos hδ hp) hR

theorem envelope_row023 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row023_pos hδ hp) hR

theorem envelope_row024 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row024_pos hδ hp) hR

theorem envelope_row025 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row025_pos hδ hp) hR

theorem envelope_row026 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row026_pos hδ hp) hR

theorem envelope_row027 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row027_pos hδ hp) hR

theorem envelope_row028 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row028_pos hδ hp) hR

theorem envelope_row029 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row029_pos hδ hp) hR

theorem envelope_row030 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row030_pos hδ hp) hR

theorem envelope_row031 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row031_pos hδ hp) hR

theorem envelope_row032 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row032_pos hδ hp) hR

theorem envelope_row033 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row033_pos hδ hp) hR

theorem envelope_row034 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row034_pos hδ hp) hR

theorem envelope_row035 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row035_pos hδ hp) hR

theorem envelope_row036 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row036_pos hδ hp) hR

theorem envelope_row037 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row037_pos hδ hp) hR

theorem envelope_row038 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row038_pos hδ hp) hR

theorem envelope_row039 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row039_pos hδ hp) hR

theorem envelope_row040 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row040_pos hδ hp) hR

theorem envelope_row041 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row041_pos hδ hp) hR

theorem envelope_row042 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row042_pos hδ hp) hR

theorem envelope_row043 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row043_pos hδ hp) hR

theorem envelope_row044 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row044_pos hδ hp) hR

theorem envelope_row045 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row045_pos hδ hp) hR

theorem envelope_row046 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row046_pos hδ hp) hR

theorem envelope_row047 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row047_pos hδ hp) hR

theorem envelope_row048 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row048_pos hδ hp) hR

theorem envelope_row049 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row049_pos hδ hp) hR

theorem envelope_row050 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row050_pos hδ hp) hR

theorem envelope_row051 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row051_pos hδ hp) hR

theorem envelope_row052 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row052_pos hδ hp) hR

theorem envelope_row053 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row053_pos hδ hp) hR

theorem envelope_row054 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row054_pos hδ hp) hR

theorem envelope_row055 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row055_pos hδ hp) hR

theorem envelope_row056 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row056_pos hδ hp) hR

theorem envelope_row057 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row057_pos hδ hp) hR

theorem envelope_row058 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row058_pos hδ hp) hR

theorem envelope_row059 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row059_pos hδ hp) hR

theorem envelope_row060 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row060_pos hδ hp) hR

theorem envelope_row061 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row061_pos hδ hp) hR

theorem envelope_row062 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row062_pos hδ hp) hR

theorem envelope_row063 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row063_pos hδ hp) hR

theorem envelope_row064 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row064_pos hδ hp) hR

theorem envelope_row065 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row065_pos hδ hp) hR

theorem envelope_row066 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row066_pos hδ hp) hR

theorem envelope_row067 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row067_pos hδ hp) hR

theorem envelope_row068 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row068_pos hδ hp) hR

theorem envelope_row069 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row069_pos hδ hp) hR

theorem envelope_row070 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row070_pos hδ hp) hR

theorem envelope_row071 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row071_pos hδ hp) hR

theorem envelope_row072 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row072_pos hδ hp) hR

theorem envelope_row073 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row073_pos hδ hp) hR

theorem envelope_row074 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row074_pos hδ hp) hR

theorem envelope_row075 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row075_pos hδ hp) hR

theorem envelope_row076 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row076_pos hδ hp) hR

theorem envelope_row077 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row077_pos hδ hp) hR

theorem envelope_row078 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row078_pos hδ hp) hR

theorem envelope_row079 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row079_pos hδ hp) hR

theorem envelope_row080 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row080_pos hδ hp) hR

theorem envelope_row081 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row081_pos hδ hp) hR

theorem envelope_row082 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row082_pos hδ hp) hR

theorem envelope_row083 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row083_pos hδ hp) hR

theorem envelope_row084 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row084_pos hδ hp) hR

theorem envelope_row085 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row085_pos hδ hp) hR

theorem envelope_row086 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row086_pos hδ hp) hR

theorem envelope_row087 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row087_pos hδ hp) hR

theorem envelope_row088 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row088_pos hδ hp) hR

theorem envelope_row089 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row089_pos hδ hp) hR

theorem envelope_row090 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row090_pos hδ hp) hR

theorem envelope_row091 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row091_pos hδ hp) hR

theorem envelope_row092 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row092_pos hδ hp) hR

theorem envelope_row093 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row093_pos hδ hp) hR

theorem envelope_row094 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row094_pos hδ hp) hR

theorem envelope_row095 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row095_pos hδ hp) hR

theorem envelope_row096 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row096_pos hδ hp) hR

theorem envelope_row097 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row097_pos hδ hp) hR

theorem envelope_row098 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row098_pos hδ hp) hR

theorem envelope_row099 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row099_pos hδ hp) hR

theorem envelope_row100 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row100_pos hδ hp) hR

theorem envelope_row101 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row101_pos hδ hp) hR

theorem envelope_row102 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row102_pos hδ hp) hR

theorem envelope_row103 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row103_pos hδ hp) hR

theorem envelope_row104 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row104_pos hδ hp) hR

theorem envelope_row105 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row105_pos hδ hp) hR

theorem envelope_row106 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row106_pos hδ hp) hR

theorem envelope_row107 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row107_pos hδ hp) hR

theorem envelope_row108 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row108_pos hδ hp) hR

theorem envelope_row109 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row109_pos hδ hp) hR

theorem envelope_row110 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row110_pos hδ hp) hR

theorem envelope_row111 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row111_pos hδ hp) hR

theorem envelope_row112 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row112_pos hδ hp) hR

theorem envelope_row113 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row113_pos hδ hp) hR

theorem envelope_row114 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row114_pos hδ hp) hR

theorem envelope_row115 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row115_pos hδ hp) hR

theorem envelope_row116 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row116_pos hδ hp) hR

theorem envelope_row117 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row117_pos hδ hp) hR

theorem envelope_row118 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row118_pos hδ hp) hR

theorem envelope_row119 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row119_pos hδ hp) hR

theorem envelope_row120 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row120_pos hδ hp) hR

theorem envelope_row121 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row121_pos hδ hp) hR

theorem envelope_row122 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row122_pos hδ hp) hR

theorem envelope_row123 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row123_pos hδ hp) hR

theorem envelope_row124 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row124_pos hδ hp) hR

theorem envelope_row125 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row125_pos hδ hp) hR

theorem envelope_row126 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row126_pos hδ hp) hR

theorem envelope_row127 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row127_pos hδ hp) hR

theorem envelope_row128 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row128_pos hδ hp) hR

theorem envelope_row129 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row129_pos hδ hp) hR

theorem envelope_row130 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row130_pos hδ hp) hR

theorem envelope_row131 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row131_pos hδ hp) hR

theorem envelope_row132 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row132_pos hδ hp) hR

theorem envelope_row133 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row133_pos hδ hp) hR

theorem envelope_row134 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row134_pos hδ hp) hR

theorem envelope_row135 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row135_pos hδ hp) hR

theorem envelope_row136 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row136_pos hδ hp) hR

theorem envelope_row137 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row137_pos hδ hp) hR

theorem envelope_row138 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row138_pos hδ hp) hR

theorem envelope_row139 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row139_pos hδ hp) hR

theorem envelope_row140 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row140_pos hδ hp) hR

theorem envelope_row141 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row141_pos hδ hp) hR

theorem envelope_row142 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row142_pos hδ hp) hR

theorem envelope_row143 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row143_pos hδ hp) hR

theorem envelope_row144 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row144_pos hδ hp) hR

theorem envelope_row145 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row145_pos hδ hp) hR

theorem envelope_row146 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row146_pos hδ hp) hR

theorem envelope_row147 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row147_pos hδ hp) hR

theorem envelope_row148 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row148_pos hδ hp) hR

theorem envelope_row149 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row149_pos hδ hp) hR

theorem envelope_row150 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row150_pos hδ hp) hR

theorem envelope_row151 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row151_pos hδ hp) hR

theorem envelope_row152 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row152_pos hδ hp) hR

theorem envelope_row153 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row153_pos hδ hp) hR

theorem envelope_row154 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row154_pos hδ hp) hR

theorem envelope_row155 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row155_pos hδ hp) hR

theorem envelope_row156 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row156_pos hδ hp) hR

theorem envelope_row157 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row157_pos hδ hp) hR

theorem envelope_row158 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row158_pos hδ hp) hR

theorem envelope_row159 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row159_pos hδ hp) hR

theorem envelope_row160 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row160_pos hδ hp) hR

theorem envelope_row161 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row161_pos hδ hp) hR

theorem envelope_row162 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row162_pos hδ hp) hR

theorem envelope_row163 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row163_pos hδ hp) hR

theorem envelope_row164 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row164_pos hδ hp) hR

theorem envelope_row165 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row165_pos hδ hp) hR

theorem envelope_row166 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row166_pos hδ hp) hR

theorem envelope_row167 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row167_pos hδ hp) hR

theorem envelope_row168 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row168_pos hδ hp) hR

theorem envelope_row169 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row169_pos hδ hp) hR

theorem envelope_row170 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row170_pos hδ hp) hR

theorem envelope_row171 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row171_pos hδ hp) hR

theorem envelope_row172 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row172_pos hδ hp) hR

theorem envelope_row173 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row173_pos hδ hp) hR

theorem envelope_row174 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row174_pos hδ hp) hR

theorem envelope_row175 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row175_pos hδ hp) hR

theorem envelope_row176 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row176_pos hδ hp) hR

theorem envelope_row177 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row177_pos hδ hp) hR

theorem envelope_row178 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row178_pos hδ hp) hR

theorem envelope_row179 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row179_pos hδ hp) hR

theorem envelope_row180 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row180_pos hδ hp) hR

theorem envelope_row181 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row181_pos hδ hp) hR

theorem envelope_row182 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row182_pos hδ hp) hR

theorem envelope_row183 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row183_pos hδ hp) hR

theorem envelope_row184 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row184_pos hδ hp) hR

theorem envelope_row185 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row185_pos hδ hp) hR

theorem envelope_row186 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row186_pos hδ hp) hR

theorem envelope_row187 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row187_pos hδ hp) hR

theorem envelope_row188 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row188_pos hδ hp) hR

theorem envelope_row189 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row189_pos hδ hp) hR

theorem envelope_row190 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row190_pos hδ hp) hR

theorem envelope_row191 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row191_pos hδ hp) hR

theorem envelope_row192 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row192_pos hδ hp) hR

theorem envelope_row193 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row193_pos hδ hp) hR

theorem envelope_row194 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row194_pos hδ hp) hR

theorem envelope_row195 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row195_pos hδ hp) hR

theorem envelope_row196 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row196_pos hδ hp) hR

theorem envelope_row197 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row197_pos hδ hp) hR

theorem envelope_row198 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row198_pos hδ hp) hR

theorem envelope_row199 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row199_pos hδ hp) hR

theorem envelope_row200 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row200_pos hδ hp) hR

theorem envelope_row201 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row201_pos hδ hp) hR

theorem envelope_row202 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row202_pos hδ hp) hR

theorem envelope_row203 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row203_pos hδ hp) hR

theorem envelope_row204 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row204_pos hδ hp) hR

theorem envelope_row205 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row205_pos hδ hp) hR

theorem envelope_row206 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row206_pos hδ hp) hR

theorem envelope_row207 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row207_pos hδ hp) hR

theorem envelope_row208 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row208_pos hδ hp) hR

theorem envelope_row209 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row209_pos hδ hp) hR

theorem envelope_row210 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row210_pos hδ hp) hR

theorem envelope_row211 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row211_pos hδ hp) hR

theorem envelope_row212 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row212_pos hδ hp) hR

theorem envelope_row213 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row213_pos hδ hp) hR

theorem envelope_row214 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row214_pos hδ hp) hR

theorem envelope_row215 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row215_pos hδ hp) hR

theorem envelope_row216 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row216_pos hδ hp) hR

theorem envelope_row217 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row217_pos hδ hp) hR

theorem envelope_row218 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row218_pos hδ hp) hR

theorem envelope_row219 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row219_pos hδ hp) hR

theorem envelope_row220 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row220_pos hδ hp) hR

theorem envelope_row221 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row221_pos hδ hp) hR

theorem envelope_row222 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row222_pos hδ hp) hR

theorem envelope_row223 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row223_pos hδ hp) hR

theorem envelope_row224 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row224_pos hδ hp) hR

theorem envelope_row225 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row225_pos hδ hp) hR

theorem envelope_row226 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row226_pos hδ hp) hR

theorem envelope_row227 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row227_pos hδ hp) hR

theorem envelope_row228 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row228_pos hδ hp) hR

theorem envelope_row229 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row229_pos hδ hp) hR

theorem envelope_row230 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row230_pos hδ hp) hR

theorem envelope_row231 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row231_pos hδ hp) hR

theorem envelope_row232 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row232_pos hδ hp) hR

theorem envelope_row233 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row233_pos hδ hp) hR

theorem envelope_row234 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row234_pos hδ hp) hR

theorem envelope_row235 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row235_pos hδ hp) hR

theorem envelope_row236 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row236_pos hδ hp) hR

theorem envelope_row237 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row237_pos hδ hp) hR

theorem envelope_row238 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row238_pos hδ hp) hR

theorem envelope_row239 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row239_pos hδ hp) hR

theorem envelope_row240 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row240_pos hδ hp) hR

theorem envelope_row241 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row241_pos hδ hp) hR

theorem envelope_row242 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row242_pos hδ hp) hR

theorem envelope_row243 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row243_pos hδ hp) hR

theorem envelope_row244 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row244_pos hδ hp) hR

theorem envelope_row245 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row245_pos hδ hp) hR

theorem envelope_row246 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row246_pos hδ hp) hR

theorem envelope_row247 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row247_pos hδ hp) hR

theorem envelope_row248 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row248_pos hδ hp) hR

theorem envelope_row249 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row249_pos hδ hp) hR

theorem envelope_row250 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row250_pos hδ hp) hR

theorem envelope_row251 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row251_pos hδ hp) hR

theorem envelope_row252 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row252_pos hδ hp) hR

theorem envelope_row253 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row253_pos hδ hp) hR

theorem envelope_row254 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row254_pos hδ hp) hR

theorem envelope_row255 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row255_pos hδ hp) hR

theorem envelope_row256 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row256_pos hδ hp) hR

theorem envelope_row257 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row257_pos hδ hp) hR

theorem envelope_row258 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row258_pos hδ hp) hR

theorem envelope_row259 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row259_pos hδ hp) hR

theorem envelope_row260 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row260_pos hδ hp) hR

theorem envelope_row261 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row261_pos hδ hp) hR

theorem envelope_row262 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row262_pos hδ hp) hR

theorem envelope_row263 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row263_pos hδ hp) hR

theorem envelope_row264 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row264_pos hδ hp) hR

theorem envelope_row265 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row265_pos hδ hp) hR

theorem envelope_row266 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row266_pos hδ hp) hR

theorem envelope_row267 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row267_pos hδ hp) hR

theorem envelope_row268 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row268_pos hδ hp) hR

theorem envelope_row269 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row269_pos hδ hp) hR

theorem envelope_row270 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row270_pos hδ hp) hR

theorem envelope_row271 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row271_pos hδ hp) hR

theorem envelope_row272 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row272_pos hδ hp) hR

theorem envelope_row273 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row273_pos hδ hp) hR

theorem envelope_row274 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row274_pos hδ hp) hR

theorem envelope_row275 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row275_pos hδ hp) hR

theorem envelope_row276 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row276_pos hδ hp) hR

theorem envelope_row277 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row277_pos hδ hp) hR

theorem envelope_row278 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row278_pos hδ hp) hR

theorem envelope_row279 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row279_pos hδ hp) hR

theorem envelope_row280 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row280_pos hδ hp) hR

theorem envelope_row281 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row281_pos hδ hp) hR

theorem envelope_row282 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row282_pos hδ hp) hR

theorem envelope_row283 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row283_pos hδ hp) hR

theorem envelope_row284 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row284_pos hδ hp) hR

theorem envelope_row285 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row285_pos hδ hp) hR

theorem envelope_row286 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row286_pos hδ hp) hR

theorem envelope_row287 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row287_pos hδ hp) hR

theorem envelope_row288 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row288_pos hδ hp) hR

theorem envelope_row289 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row289_pos hδ hp) hR

theorem envelope_row290 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row290_pos hδ hp) hR

theorem envelope_row291 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row291_pos hδ hp) hR

theorem envelope_row292 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row292_pos hδ hp) hR

theorem envelope_row293 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow17.Available δ p := by
    change δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow17 window17_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .Cphys hd0 hp0) (row293_pos hδ hp) hR

theorem envelope_row294 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row294_pos hδ hp) hR

theorem envelope_row295 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow01.Available δ p := by
    change δ ∈ Set.Icc (9/32:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow01 window01_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row295_pos hδ hp) hR

theorem envelope_row296 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row296_pos hδ hp) hR

theorem envelope_row297 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row297_pos hδ hp) hR

theorem envelope_row298 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row298_pos hδ hp) hR

theorem envelope_row299 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row299_pos hδ hp) hR

theorem envelope_row300 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow03.Available δ p := by
    change δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow03 window03_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row300_pos hδ hp) hR

theorem envelope_row301 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row301_pos hδ hp) hR

theorem envelope_row302 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row302_pos hδ hp) hR

theorem envelope_row303 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row303_pos hδ hp) hR

theorem envelope_row304 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row304_pos hδ hp) hR

theorem envelope_row305 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row305_pos hδ hp) hR

theorem envelope_row306 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row306_pos hδ hp) hR

theorem envelope_row307 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row307_pos hδ hp) hR

theorem envelope_row308 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row308_pos hδ hp) hR

theorem envelope_row309 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row309_pos hδ hp) hR

theorem envelope_row310 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row310_pos hδ hp) hR

theorem envelope_row311 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row311_pos hδ hp) hR

theorem envelope_row312 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row312_pos hδ hp) hR

theorem envelope_row313 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row313_pos hδ hp) hR

theorem envelope_row314 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row314_pos hδ hp) hR

theorem envelope_row315 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row315_pos hδ hp) hR

theorem envelope_row316 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row316_pos hδ hp) hR

theorem envelope_row317 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row317_pos hδ hp) hR

theorem envelope_row318 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row318_pos hδ hp) hR

theorem envelope_row319 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row319_pos hδ hp) hR

theorem envelope_row320 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row320_pos hδ hp) hR

theorem envelope_row321 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row321_pos hδ hp) hR

theorem envelope_row322 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row322_pos hδ hp) hR

theorem envelope_row323 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row323_pos hδ hp) hR

theorem envelope_row324 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row324_pos hδ hp) hR

theorem envelope_row325 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row325_pos hδ hp) hR

theorem envelope_row326 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row326_pos hδ hp) hR

theorem envelope_row327 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row327_pos hδ hp) hR

theorem envelope_row328 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row328_pos hδ hp) hR

theorem envelope_row329 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row329_pos hδ hp) hR

theorem envelope_row330 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row330_pos hδ hp) hR

theorem envelope_row331 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row331_pos hδ hp) hR

theorem envelope_row332 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row332_pos hδ hp) hR

theorem envelope_row333 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row333_pos hδ hp) hR

theorem envelope_row334 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row334_pos hδ hp) hR

theorem envelope_row335 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row335_pos hδ hp) hR

theorem envelope_row336 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (255/512:ℝ) (511/1024:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row336_pos hδ hp) hR

theorem envelope_row337 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (511/1024:ℝ) (1023/2048:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row337_pos hδ hp) hR

theorem envelope_row338 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (1023/2048:ℝ) (2047/4096:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row338_pos hδ hp) hR

theorem envelope_row339 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (2047/4096:ℝ) (4095/8192:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row339_pos hδ hp) hR

theorem envelope_row340 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (909/2048:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row340_pos hδ hp) hR

theorem envelope_row341 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (8191/16384:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row341_pos hδ hp) hR

theorem envelope_row342 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (8191/16384:ℝ) (16383/32768:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row342_pos hδ hp) hR

theorem envelope_row343 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (16383/32768:ℝ) (32767/65536:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row343_pos hδ hp) hR

theorem envelope_row344 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (1821/4096:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (65535/131072:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row344_pos hδ hp) hR

theorem envelope_row345 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (3639/8192:ℝ))
    (hp : p ∈ Set.Icc (65535/131072:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row345_pos hδ hp) hR

theorem envelope_row346 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3639/8192:ℝ) (1821/4096:ℝ))
    (hp : p ∈ Set.Icc (65535/131072:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row346_pos hδ hp) hR

theorem envelope_row347 {δ p : ℝ} (hδ : δ ∈ Set.Icc (1821/4096:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row347_pos hδ hp) hR

theorem envelope_row348 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row348_pos hδ hp) hR

theorem envelope_row349 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row349_pos hδ hp) hR

theorem envelope_row350 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row350_pos hδ hp) hR

theorem envelope_row351 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row351_pos hδ hp) hR

theorem envelope_row352 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row352_pos hδ hp) hR

theorem envelope_row353 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row353_pos hδ hp) hR

theorem envelope_row354 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow04.Available δ p := by
    change δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ) ∧ p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow04 window04_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row354_pos hδ hp) hR

theorem envelope_row355 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row355_pos hδ hp) hR

theorem envelope_row356 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row356_pos hδ hp) hR

theorem envelope_row357 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row357_pos hδ hp) hR

theorem envelope_row358 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row358_pos hδ hp) hR

theorem envelope_row359 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row359_pos hδ hp) hR

theorem envelope_row360 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row360_pos hδ hp) hR

theorem envelope_row361 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow15.Available δ p := by
    change δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ) ∧ p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow15 window15_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row361_pos hδ hp) hR

theorem envelope_row362 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row362_pos hδ hp) hR

theorem envelope_row363 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row363_pos hδ hp) hR

theorem envelope_row364 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row364_pos hδ hp) hR

theorem envelope_row365 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row365_pos hδ hp) hR

theorem envelope_row366 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row366_pos hδ hp) hR

theorem envelope_row367 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row367_pos hδ hp) hR

theorem envelope_row368 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have ha : returnWindow16.Available δ p := by
    change δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ) ∧ p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)
    constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
  have hR := finiteEnvelope_le_window returnWindow16 window16_mem (κ := kappa) ha
  exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row368_pos hδ hp) hR

theorem envelope_row369 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row369_pos hδ hp) hR

theorem envelope_row370 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row370_pos hδ hp) hR

theorem envelope_row371 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row371_pos hδ hp) hR

theorem envelope_row372 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row372_pos hδ hp) hR

theorem envelope_row373 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row373_pos hδ hp) hR

theorem envelope_row374 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row374_pos hδ hp) hR

theorem envelope_row375 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  have hd0 : δ ∈ Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
  have hp0 : p ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
  have hR := finiteEnvelope_le_old hd0 hp0
  exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row375_pos hδ hp) hR

theorem cover_node_000 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row001 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row002 hδ ⟨hsplit,hp.2⟩

theorem cover_node_001 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row000 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_000 hδ ⟨hsplit,hp.2⟩

theorem cover_node_002 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row008 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row009 hδ ⟨hsplit,hp.2⟩

theorem cover_node_003 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row007 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_002 hδ ⟨hsplit,hp.2⟩

theorem cover_node_004 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row015 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row016 hδ ⟨hsplit,hp.2⟩

theorem cover_node_005 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row014 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_004 hδ ⟨hsplit,hp.2⟩

theorem cover_node_006 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact cover_node_003 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_005 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_007 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact cover_node_001 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_006 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_008 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row010 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row017 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_009 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row003 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_008 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_010 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row011 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row018 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_011 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row004 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_010 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_012 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_009 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_011 hδ ⟨hsplit,hp.2⟩

theorem cover_node_013 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row012 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row019 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_014 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row005 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_013 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_015 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row013 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row020 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_016 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row006 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_015 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_017 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_014 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_016 hδ ⟨hsplit,hp.2⟩

theorem cover_node_018 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_012 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_017 hδ ⟨hsplit,hp.2⟩

theorem cover_node_019 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_007 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_018 hδ ⟨hsplit,hp.2⟩

theorem cover_node_020 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row022 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row023 hδ ⟨hsplit,hp.2⟩

theorem cover_node_021 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row021 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_020 hδ ⟨hsplit,hp.2⟩

theorem cover_node_022 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row029 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row030 hδ ⟨hsplit,hp.2⟩

theorem cover_node_023 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row028 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_022 hδ ⟨hsplit,hp.2⟩

theorem cover_node_024 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row036 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row037 hδ ⟨hsplit,hp.2⟩

theorem cover_node_025 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row035 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_024 hδ ⟨hsplit,hp.2⟩

theorem cover_node_026 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact cover_node_023 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_025 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_027 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact cover_node_021 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_026 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_028 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row031 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row038 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_029 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row024 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_028 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_030 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row032 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row039 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_031 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row025 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_030 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_032 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_029 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_031 hδ ⟨hsplit,hp.2⟩

theorem cover_node_033 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row033 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row040 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_034 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row026 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_033 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_035 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row034 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row041 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_036 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row027 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_035 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_037 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_034 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_036 hδ ⟨hsplit,hp.2⟩

theorem cover_node_038 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_032 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_037 hδ ⟨hsplit,hp.2⟩

theorem cover_node_039 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_027 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_038 hδ ⟨hsplit,hp.2⟩

theorem cover_node_040 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_019 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_039 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_041 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row043 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row044 hδ ⟨hsplit,hp.2⟩

theorem cover_node_042 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row042 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_041 hδ ⟨hsplit,hp.2⟩

theorem cover_node_043 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row050 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row051 hδ ⟨hsplit,hp.2⟩

theorem cover_node_044 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row049 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_043 hδ ⟨hsplit,hp.2⟩

theorem cover_node_045 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row057 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row058 hδ ⟨hsplit,hp.2⟩

theorem cover_node_046 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row056 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_045 hδ ⟨hsplit,hp.2⟩

theorem cover_node_047 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact cover_node_044 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_046 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_048 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact cover_node_042 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_047 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_049 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row052 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row059 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_050 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row045 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_049 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_051 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row053 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row060 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_052 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row046 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_051 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_053 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_050 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_052 hδ ⟨hsplit,hp.2⟩

theorem cover_node_054 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row054 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row061 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_055 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row047 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_054 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_056 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row055 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row062 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_057 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row048 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_056 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_058 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_055 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_057 hδ ⟨hsplit,hp.2⟩

theorem cover_node_059 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_053 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_058 hδ ⟨hsplit,hp.2⟩

theorem cover_node_060 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_048 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_059 hδ ⟨hsplit,hp.2⟩

theorem cover_node_061 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row064 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row065 hδ ⟨hsplit,hp.2⟩

theorem cover_node_062 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row063 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_061 hδ ⟨hsplit,hp.2⟩

theorem cover_node_063 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row066 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row067 hδ ⟨hsplit,hp.2⟩

theorem cover_node_064 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row068 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row069 hδ ⟨hsplit,hp.2⟩

theorem cover_node_065 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_063 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_064 hδ ⟨hsplit,hp.2⟩

theorem cover_node_066 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_062 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_065 hδ ⟨hsplit,hp.2⟩

theorem cover_node_067 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row071 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row072 hδ ⟨hsplit,hp.2⟩

theorem cover_node_068 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row070 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_067 hδ ⟨hsplit,hp.2⟩

theorem cover_node_069 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row073 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row074 hδ ⟨hsplit,hp.2⟩

theorem cover_node_070 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row075 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row076 hδ ⟨hsplit,hp.2⟩

theorem cover_node_071 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_069 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_070 hδ ⟨hsplit,hp.2⟩

theorem cover_node_072 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_068 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_071 hδ ⟨hsplit,hp.2⟩

theorem cover_node_073 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_066 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_072 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_074 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row078 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row079 hδ ⟨hsplit,hp.2⟩

theorem cover_node_075 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row077 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_074 hδ ⟨hsplit,hp.2⟩

theorem cover_node_076 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row080 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row081 hδ ⟨hsplit,hp.2⟩

theorem cover_node_077 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row082 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row083 hδ ⟨hsplit,hp.2⟩

theorem cover_node_078 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_076 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_077 hδ ⟨hsplit,hp.2⟩

theorem cover_node_079 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_075 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_078 hδ ⟨hsplit,hp.2⟩

theorem cover_node_080 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row085 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row086 hδ ⟨hsplit,hp.2⟩

theorem cover_node_081 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row084 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_080 hδ ⟨hsplit,hp.2⟩

theorem cover_node_082 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row087 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row088 hδ ⟨hsplit,hp.2⟩

theorem cover_node_083 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row089 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row090 hδ ⟨hsplit,hp.2⟩

theorem cover_node_084 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_082 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_083 hδ ⟨hsplit,hp.2⟩

theorem cover_node_085 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_081 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_084 hδ ⟨hsplit,hp.2⟩

theorem cover_node_086 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact cover_node_079 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_085 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_087 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_073 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_086 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_088 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_060 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_087 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_089 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_040 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_088 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_090 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row092 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row093 hδ ⟨hsplit,hp.2⟩

theorem cover_node_091 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row091 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_090 hδ ⟨hsplit,hp.2⟩

theorem cover_node_092 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row099 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row100 hδ ⟨hsplit,hp.2⟩

theorem cover_node_093 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row098 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_092 hδ ⟨hsplit,hp.2⟩

theorem cover_node_094 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row106 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row107 hδ ⟨hsplit,hp.2⟩

theorem cover_node_095 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row105 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_094 hδ ⟨hsplit,hp.2⟩

theorem cover_node_096 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact cover_node_093 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_095 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_097 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact cover_node_091 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_096 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_098 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row101 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row108 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_099 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row094 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_098 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_100 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row102 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row109 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_101 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row095 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_100 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_102 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_099 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_101 hδ ⟨hsplit,hp.2⟩

theorem cover_node_103 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row103 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row110 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_104 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row096 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_103 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_105 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row104 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row111 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_106 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row097 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_105 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_107 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_104 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_106 hδ ⟨hsplit,hp.2⟩

theorem cover_node_108 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_102 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_107 hδ ⟨hsplit,hp.2⟩

theorem cover_node_109 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_097 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_108 hδ ⟨hsplit,hp.2⟩

theorem cover_node_110 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row113 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row114 hδ ⟨hsplit,hp.2⟩

theorem cover_node_111 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row112 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_110 hδ ⟨hsplit,hp.2⟩

theorem cover_node_112 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row120 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row121 hδ ⟨hsplit,hp.2⟩

theorem cover_node_113 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row119 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_112 hδ ⟨hsplit,hp.2⟩

theorem cover_node_114 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row127 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row128 hδ ⟨hsplit,hp.2⟩

theorem cover_node_115 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row126 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_114 hδ ⟨hsplit,hp.2⟩

theorem cover_node_116 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact cover_node_113 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_115 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_117 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact cover_node_111 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_116 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_118 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row122 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row129 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_119 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row115 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_118 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_120 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row123 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row130 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_121 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row116 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_120 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_122 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_119 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_121 hδ ⟨hsplit,hp.2⟩

theorem cover_node_123 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row124 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row131 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_124 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row117 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_123 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_125 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row125 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row132 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_126 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row118 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_125 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_127 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_124 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_126 hδ ⟨hsplit,hp.2⟩

theorem cover_node_128 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_122 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_127 hδ ⟨hsplit,hp.2⟩

theorem cover_node_129 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_117 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_128 hδ ⟨hsplit,hp.2⟩

theorem cover_node_130 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_109 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_129 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_131 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row134 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row135 hδ ⟨hsplit,hp.2⟩

theorem cover_node_132 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row133 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_131 hδ ⟨hsplit,hp.2⟩

theorem cover_node_133 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row141 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row142 hδ ⟨hsplit,hp.2⟩

theorem cover_node_134 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row140 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_133 hδ ⟨hsplit,hp.2⟩

theorem cover_node_135 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row148 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row149 hδ ⟨hsplit,hp.2⟩

theorem cover_node_136 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row147 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_135 hδ ⟨hsplit,hp.2⟩

theorem cover_node_137 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact cover_node_134 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_136 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_138 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact cover_node_132 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_137 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_139 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row143 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row150 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_140 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row136 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_139 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_141 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row144 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row151 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_142 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row137 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_141 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_143 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_140 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_142 hδ ⟨hsplit,hp.2⟩

theorem cover_node_144 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row145 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row152 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_145 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row138 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_144 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_146 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row146 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row153 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_147 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row139 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_146 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_148 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_145 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_147 hδ ⟨hsplit,hp.2⟩

theorem cover_node_149 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_143 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_148 hδ ⟨hsplit,hp.2⟩

theorem cover_node_150 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_138 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_149 hδ ⟨hsplit,hp.2⟩

theorem cover_node_151 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row155 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row156 hδ ⟨hsplit,hp.2⟩

theorem cover_node_152 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row154 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_151 hδ ⟨hsplit,hp.2⟩

theorem cover_node_153 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row157 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row158 hδ ⟨hsplit,hp.2⟩

theorem cover_node_154 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row159 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row160 hδ ⟨hsplit,hp.2⟩

theorem cover_node_155 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_153 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_154 hδ ⟨hsplit,hp.2⟩

theorem cover_node_156 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_152 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_155 hδ ⟨hsplit,hp.2⟩

theorem cover_node_157 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row162 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row163 hδ ⟨hsplit,hp.2⟩

theorem cover_node_158 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row161 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_157 hδ ⟨hsplit,hp.2⟩

theorem cover_node_159 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row164 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row165 hδ ⟨hsplit,hp.2⟩

theorem cover_node_160 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row166 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row167 hδ ⟨hsplit,hp.2⟩

theorem cover_node_161 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_159 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_160 hδ ⟨hsplit,hp.2⟩

theorem cover_node_162 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_158 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_161 hδ ⟨hsplit,hp.2⟩

theorem cover_node_163 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_156 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_162 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_164 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row169 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row170 hδ ⟨hsplit,hp.2⟩

theorem cover_node_165 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row168 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_164 hδ ⟨hsplit,hp.2⟩

theorem cover_node_166 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row171 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row172 hδ ⟨hsplit,hp.2⟩

theorem cover_node_167 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row173 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row174 hδ ⟨hsplit,hp.2⟩

theorem cover_node_168 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_166 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_167 hδ ⟨hsplit,hp.2⟩

theorem cover_node_169 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_165 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_168 hδ ⟨hsplit,hp.2⟩

theorem cover_node_170 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row176 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row177 hδ ⟨hsplit,hp.2⟩

theorem cover_node_171 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row175 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_170 hδ ⟨hsplit,hp.2⟩

theorem cover_node_172 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row178 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row179 hδ ⟨hsplit,hp.2⟩

theorem cover_node_173 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row180 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row181 hδ ⟨hsplit,hp.2⟩

theorem cover_node_174 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_172 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_173 hδ ⟨hsplit,hp.2⟩

theorem cover_node_175 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_171 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_174 hδ ⟨hsplit,hp.2⟩

theorem cover_node_176 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact cover_node_169 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_175 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_177 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_163 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_176 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_178 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_150 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_177 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_179 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_130 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_178 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_180 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row183 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row184 hδ ⟨hsplit,hp.2⟩

theorem cover_node_181 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row182 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_180 hδ ⟨hsplit,hp.2⟩

theorem cover_node_182 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row190 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row191 hδ ⟨hsplit,hp.2⟩

theorem cover_node_183 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row189 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_182 hδ ⟨hsplit,hp.2⟩

theorem cover_node_184 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row197 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row198 hδ ⟨hsplit,hp.2⟩

theorem cover_node_185 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row196 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_184 hδ ⟨hsplit,hp.2⟩

theorem cover_node_186 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact cover_node_183 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_185 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_187 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact cover_node_181 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_186 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_188 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row192 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row199 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_189 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row185 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_188 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_190 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row193 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row200 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_191 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row186 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_190 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_192 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_189 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_191 hδ ⟨hsplit,hp.2⟩

theorem cover_node_193 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row194 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row201 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_194 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row187 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_193 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_195 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row195 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row202 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_196 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row188 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_195 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_197 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_194 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_196 hδ ⟨hsplit,hp.2⟩

theorem cover_node_198 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_192 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_197 hδ ⟨hsplit,hp.2⟩

theorem cover_node_199 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_187 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_198 hδ ⟨hsplit,hp.2⟩

theorem cover_node_200 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row204 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row205 hδ ⟨hsplit,hp.2⟩

theorem cover_node_201 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row203 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_200 hδ ⟨hsplit,hp.2⟩

theorem cover_node_202 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row211 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row212 hδ ⟨hsplit,hp.2⟩

theorem cover_node_203 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row210 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_202 hδ ⟨hsplit,hp.2⟩

theorem cover_node_204 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row218 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row219 hδ ⟨hsplit,hp.2⟩

theorem cover_node_205 {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row217 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_204 hδ ⟨hsplit,hp.2⟩

theorem cover_node_206 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact cover_node_203 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_205 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_207 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact cover_node_201 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_206 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_208 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row213 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row220 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_209 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row206 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_208 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_210 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row214 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row221 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_211 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row207 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_210 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_212 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_209 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_211 hδ ⟨hsplit,hp.2⟩

theorem cover_node_213 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row215 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row222 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_214 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row208 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_213 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_215 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row216 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row223 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_216 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row209 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_215 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_217 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_214 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_216 hδ ⟨hsplit,hp.2⟩

theorem cover_node_218 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_212 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_217 hδ ⟨hsplit,hp.2⟩

theorem cover_node_219 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_207 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_218 hδ ⟨hsplit,hp.2⟩

theorem cover_node_220 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_199 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_219 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_221 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row225 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row226 hδ ⟨hsplit,hp.2⟩

theorem cover_node_222 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row224 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_221 hδ ⟨hsplit,hp.2⟩

theorem cover_node_223 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row232 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row233 hδ ⟨hsplit,hp.2⟩

theorem cover_node_224 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row231 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_223 hδ ⟨hsplit,hp.2⟩

theorem cover_node_225 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row239 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row240 hδ ⟨hsplit,hp.2⟩

theorem cover_node_226 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row238 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_225 hδ ⟨hsplit,hp.2⟩

theorem cover_node_227 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact cover_node_224 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_226 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_228 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact cover_node_222 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_227 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_229 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row234 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row241 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_230 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row227 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_229 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_231 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row235 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row242 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_232 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row228 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_231 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_233 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_230 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_232 hδ ⟨hsplit,hp.2⟩

theorem cover_node_234 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row236 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row243 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_235 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row229 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_234 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_236 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row237 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row244 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_237 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row230 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_236 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_238 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_235 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_237 hδ ⟨hsplit,hp.2⟩

theorem cover_node_239 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_233 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_238 hδ ⟨hsplit,hp.2⟩

theorem cover_node_240 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_228 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_239 hδ ⟨hsplit,hp.2⟩

theorem cover_node_241 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row246 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row247 hδ ⟨hsplit,hp.2⟩

theorem cover_node_242 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row245 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_241 hδ ⟨hsplit,hp.2⟩

theorem cover_node_243 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row248 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row249 hδ ⟨hsplit,hp.2⟩

theorem cover_node_244 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row250 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row251 hδ ⟨hsplit,hp.2⟩

theorem cover_node_245 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_243 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_244 hδ ⟨hsplit,hp.2⟩

theorem cover_node_246 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_242 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_245 hδ ⟨hsplit,hp.2⟩

theorem cover_node_247 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row253 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row254 hδ ⟨hsplit,hp.2⟩

theorem cover_node_248 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row252 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_247 hδ ⟨hsplit,hp.2⟩

theorem cover_node_249 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row255 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row256 hδ ⟨hsplit,hp.2⟩

theorem cover_node_250 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row257 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row258 hδ ⟨hsplit,hp.2⟩

theorem cover_node_251 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_249 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_250 hδ ⟨hsplit,hp.2⟩

theorem cover_node_252 {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_248 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_251 hδ ⟨hsplit,hp.2⟩

theorem cover_node_253 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_246 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_252 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_254 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row260 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row261 hδ ⟨hsplit,hp.2⟩

theorem cover_node_255 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row259 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_254 hδ ⟨hsplit,hp.2⟩

theorem cover_node_256 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row262 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row263 hδ ⟨hsplit,hp.2⟩

theorem cover_node_257 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row264 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row265 hδ ⟨hsplit,hp.2⟩

theorem cover_node_258 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_256 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_257 hδ ⟨hsplit,hp.2⟩

theorem cover_node_259 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_255 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_258 hδ ⟨hsplit,hp.2⟩

theorem cover_node_260 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact envelope_row267 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row268 hδ ⟨hsplit,hp.2⟩

theorem cover_node_261 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row266 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_260 hδ ⟨hsplit,hp.2⟩

theorem cover_node_262 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact envelope_row269 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row270 hδ ⟨hsplit,hp.2⟩

theorem cover_node_263 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact envelope_row271 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row272 hδ ⟨hsplit,hp.2⟩

theorem cover_node_264 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_262 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_263 hδ ⟨hsplit,hp.2⟩

theorem cover_node_265 {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_261 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_264 hδ ⟨hsplit,hp.2⟩

theorem cover_node_266 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact cover_node_259 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_265 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_267 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_253 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_266 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_268 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_240 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_267 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_269 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_220 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_268 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_270 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row280 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row287 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_271 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row273 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_270 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_272 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row301 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row308 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_273 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row294 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_272 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_274 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_271 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_273 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_275 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row322 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row329 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_276 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row315 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_275 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_277 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row348 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row355 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_278 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row362 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row369 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_279 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_277 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_278 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_280 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_276 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_279 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_281 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_274 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_280 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_282 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row281 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row288 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_283 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row274 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_282 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_284 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row302 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row309 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_285 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row295 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_284 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_286 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_283 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_285 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_287 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row323 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row330 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_288 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row316 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_287 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_289 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row349 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row356 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_290 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row363 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row370 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_291 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_289 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_290 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_292 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_288 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_291 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_293 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_286 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_292 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_294 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (3/8:ℝ) with hsplit | hsplit
  · exact cover_node_281 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_293 hδ ⟨hsplit,hp.2⟩

theorem cover_node_295 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row282 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row289 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_296 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row275 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_295 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_297 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row303 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row310 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_298 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row296 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_297 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_299 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_296 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_298 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_300 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row324 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row331 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_301 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row317 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_300 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_302 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row350 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row357 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_303 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row364 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row371 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_304 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_302 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_303 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_305 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_301 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_304 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_306 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_299 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_305 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_307 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row283 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row290 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_308 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row276 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_307 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_309 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row304 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row311 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_310 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row297 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_309 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_311 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_308 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_310 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_312 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row325 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row332 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_313 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row318 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_312 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_314 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row351 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row358 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_315 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row365 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row372 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_316 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_314 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_315 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_317 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_313 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_316 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_318 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_311 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_317 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_319 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (15/32:ℝ) with hsplit | hsplit
  · exact cover_node_306 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_318 hδ ⟨hsplit,hp.2⟩

theorem cover_node_320 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (7/16:ℝ) with hsplit | hsplit
  · exact cover_node_294 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_319 hδ ⟨hsplit,hp.2⟩

theorem cover_node_321 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row284 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row291 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_322 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row277 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_321 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_323 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row305 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row312 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_324 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row298 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_323 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_325 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_322 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_324 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_326 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row326 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row333 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_327 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row319 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_326 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_328 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row352 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row359 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_329 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row366 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row373 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_330 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_328 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_329 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_331 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_327 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_330 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_332 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_325 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_331 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_333 {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact envelope_row285 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row292 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_334 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (45/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row278 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_333 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_335 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row306 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row313 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_336 {δ p : ℝ} (hδ : δ ∈ Set.Icc (45/128:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact envelope_row299 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_335 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_337 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact cover_node_334 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_336 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_338 {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact envelope_row327 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row334 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_339 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row320 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_338 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_340 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row353 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row360 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_341 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row367 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row374 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_342 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_340 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_341 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_343 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_339 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_342 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_344 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_337 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_343 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_345 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (63/128:ℝ) with hsplit | hsplit
  · exact cover_node_332 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_344 hδ ⟨hsplit,hp.2⟩

theorem cover_node_346 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (9/32:ℝ) with hsplit | hsplit
  · exact envelope_row279 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row286 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_347 {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (45/128:ℝ) with hsplit | hsplit
  · exact envelope_row293 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row300 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_348 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (21/64:ℝ) with hsplit | hsplit
  · exact cover_node_346 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_347 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_349 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (27/64:ℝ) with hsplit | hsplit
  · exact envelope_row307 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row314 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_350 {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (225/512:ℝ) with hsplit | hsplit
  · exact envelope_row321 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row328 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_351 {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (111/256:ℝ) with hsplit | hsplit
  · exact cover_node_349 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_350 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_352 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3/8:ℝ) with hsplit | hsplit
  · exact cover_node_348 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_351 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_353 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (511/1024:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (255/512:ℝ) with hsplit | hsplit
  · exact envelope_row335 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row336 hδ ⟨hsplit,hp.2⟩

theorem cover_node_354 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (1023/2048:ℝ) (4095/8192:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (2047/4096:ℝ) with hsplit | hsplit
  · exact envelope_row338 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row339 hδ ⟨hsplit,hp.2⟩

theorem cover_node_355 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (511/1024:ℝ) (4095/8192:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (1023/2048:ℝ) with hsplit | hsplit
  · exact envelope_row337 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_354 hδ ⟨hsplit,hp.2⟩

theorem cover_node_356 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (4095/8192:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (511/1024:ℝ) with hsplit | hsplit
  · exact cover_node_353 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_355 hδ ⟨hsplit,hp.2⟩

theorem cover_node_357 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (8191/16384:ℝ) (32767/65536:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (16383/32768:ℝ) with hsplit | hsplit
  · exact envelope_row342 hδ ⟨hp.1,hsplit⟩
  · exact envelope_row343 hδ ⟨hsplit,hp.2⟩

theorem cover_node_358 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (32767/65536:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (8191/16384:ℝ) with hsplit | hsplit
  · exact envelope_row341 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_357 hδ ⟨hsplit,hp.2⟩

theorem cover_node_359 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (1821/4096:ℝ))
    (hp : p ∈ Set.Icc (65535/131072:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (3639/8192:ℝ) with hsplit | hsplit
  · exact envelope_row345 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row346 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_360 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (1821/4096:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (65535/131072:ℝ) with hsplit | hsplit
  · exact envelope_row344 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_359 hδ ⟨hsplit,hp.2⟩

theorem cover_node_361 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (32767/65536:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (1821/4096:ℝ) with hsplit | hsplit
  · exact cover_node_360 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row347 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_362 {δ p : ℝ} (hδ : δ ∈ Set.Icc (909/2048:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (32767/65536:ℝ) with hsplit | hsplit
  · exact cover_node_358 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_361 hδ ⟨hsplit,hp.2⟩

theorem cover_node_363 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (909/2048:ℝ) with hsplit | hsplit
  · exact envelope_row340 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_362 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_364 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (4095/8192:ℝ) with hsplit | hsplit
  · exact cover_node_356 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_363 hδ ⟨hsplit,hp.2⟩

theorem cover_node_365 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (15/32:ℝ) with hsplit | hsplit
  · exact envelope_row354 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row361 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_366 {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (69/128:ℝ) with hsplit | hsplit
  · exact envelope_row368 ⟨hδ.1,hsplit⟩ hp
  · exact envelope_row375 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_367 {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (33/64:ℝ) with hsplit | hsplit
  · exact cover_node_365 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_366 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_368 {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (57/128:ℝ) with hsplit | hsplit
  · exact cover_node_364 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_367 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_369 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total δ (453/1024:ℝ) with hsplit | hsplit
  · exact cover_node_352 ⟨hδ.1,hsplit⟩ hp
  · exact cover_node_368 ⟨hsplit,hδ.2⟩ hp

theorem cover_node_370 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (127/256:ℝ) with hsplit | hsplit
  · exact cover_node_345 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_369 hδ ⟨hsplit,hp.2⟩

theorem cover_node_371 {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  rcases le_total p (31/64:ℝ) with hsplit | hsplit
  · exact cover_node_320 hδ ⟨hp.1,hsplit⟩
  · exact cover_node_370 hδ ⟨hsplit,hp.2⟩

theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)<theta-reserve := by
  cases e with
  | oldSmall => exact cover_node_089 hδ hp
  | oldSwitch => exact cover_node_179 hδ hp
  | newSwitch => exact cover_node_269 hδ hp
  | newTop => exact cover_node_371 hδ hp

end
end Qrh.JointDetector.PointwiseReturn.FinalEdges
