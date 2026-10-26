/- The combined proof: the endpoint from the source step.
Fork of Collet's Record1252270103Graph/FinalSources.lean and Graph/Endpoint.lean (Apache-2.0). The
chain starts at Sil's fourth-power source face (`Graph/Start.lean`); the steps and the final return
use the cap `6(2β − 1) ≤ 9/2`, the baseline's `β ≤ 7/8` (`Graph/NaturalCap.lean`). The final count
face is the last face `faceC` of the face family and the final physical face is its face `faceP`
(`Faceless/Gen/Chain.lean`, generated with their exact values). -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Gen.Chain
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.EndpointFromGlobalSources
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Graph QRH.RepeatedMarks.Finite QRH.Record12518109Existence

lemma final_C_face :
    Record1252270103Source.globalFace (faceC.B:ℝ) (faceC.L:ℝ) (faceC.cap:ℝ)=
      QRH.RepeatedMarks.Return.countGlobal := by
  rw [faceC_B, faceC_L, faceC_cap]
  norm_num [Record1252270103Source.globalFace,QRH.RepeatedMarks.Return.countGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.countCB,
    QRH.RepeatedMarks.Return.countCL]

lemma final_P_face :
    Record1252270103Source.globalFace (faceP.B:ℝ) (faceP.L:ℝ) (faceP.cap:ℝ)=
      QRH.RepeatedMarks.Return.physicalGlobal := by
  rw [faceP_B, faceP_L, faceP_cap]
  norm_num [Record1252270103Source.globalFace,QRH.RepeatedMarks.Return.physicalGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.physicalB,
    QRH.RepeatedMarks.Return.physicalLambda]

theorem final_global_suppliers (step : NFStep2)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    UniformUnitFaceSource QRH.RepeatedMarks.Return.countGlobal ∧
    UniformUnitFaceSource QRH.RepeatedMarks.Return.physicalGlobal := by
  obtain ⟨hC,hP⟩ := chain_sources step hbeta QRH.RepeatedMarks.natural_cap
  change UniformUnitFaceSource _ at hC hP
  rw [final_C_face] at hC
  rw [final_P_face] at hP
  exact ⟨hC,hP⟩

theorem beta_of_step (step : NFStep2) :
    HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta := by
  by_cases hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta
  · obtain ⟨hC,hP⟩ := final_global_suppliers step hbeta
    exact QRH.RepeatedMarks.Return.beta_of_two_global_sources hC hP
  · have ht : (51/100:ℝ)≤QRH.RepeatedMarks.Return.theta := by
      norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c]
    exact (not_le.mp hbeta).le.trans ht

theorem dirichlet_of_step (step : NFStep2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : QRH.RepeatedMarks.Return.theta<s.re) (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke
    (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
    (fun χ s hs hpole=>HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
      ((beta_of_step step).trans_lt hs) hpole) χ s hs hpole

end
end QRH.RepeatedMarks.Graph
