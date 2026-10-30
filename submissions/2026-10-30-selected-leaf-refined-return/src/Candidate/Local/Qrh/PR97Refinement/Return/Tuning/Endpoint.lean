/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The return at theta = 174799/200000 from the global source G(4967/5000, 49/20, 1/10).
Adapted from PR76 `FinalReturn/EndpointFromGlobalSources.lean` and `Graph/Endpoint.lean`
(Repeated marks, Apache-2.0; forks of Collet's Record1252270103Graph, Apache-2.0).
The count face C = (4967/5000, 49/20, 9999/100000) and the physical face
P = (9933999/10^7, 2451/1000, 31/500) are literal subfaces of G. The natural cap
`2β − 1 ≤ naturalK/6 = 3/4` is the baseline's `β ≤ 7/8` (PR76 `Graph/NaturalCap.lean`).
The source G is a hypothesis here, under `51/100 ≤ β`; the complementary case is trivial. -/
/- Modified for the 46-step density-split chain (27 Oct 2026): source face G(9888151/10000000, 4683001/2000000, 1/10), count face C = (9888151/10000000, 4683001/2000000, 9999/100000), physical face P = (9888151/10000000, 4683001/2000000, 31/500), theta = 4369779/5000000 = 0.8739558. Proofs unchanged. -/
/- Modified by ArviFoxy (2026-10-28): two-source endpoint after PR 85 `Return/Endpoint.lean`: the count face and the physical face are supplied by two global sources G(96232839/100000000, 3853/2000, 1/10) and G(49283557/50000000, 4503/2000, 1/10) (theta = 43693617/50000000); proofs as in PR 86. -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
/- Modified (2026-10-30, E5 retune, design 2): the count face and the physical face are both supplied by the end face G(99999/100000, 401/200, 13399/100000) of the selected-leaf line (c(Λ) = 1/10 + (3/50)(5143/2000 - Λ) at Λ = 401/200); theta = 43670599/50000000 = 0.87341198. The sources are hypotheses (under `51/100 ≤ β`); proofs unchanged. -/
import Candidate.Local.Qrh.PR97Refinement.Return.Tuning.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PR97Refinement.Return.Tuning
open QRH.Record1252270103Return QRH.PR97Refinement.ReturnTuning Qrh.JointDetector.BoundaryPhysical.Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

/-- The global face of the count source `G(99999/100000, 200001/100000, 671447/5000000)`. -/
abbrev countSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (99999/100000) (200001/100000) (671447/5000000)
/-- The global face of the physical source `G(99999/100000, 200001/100000, 671447/5000000)`. -/
abbrev physicalSourceFace : SourceFace := QRH.Record1252270103Source.globalFace (99999/100000) (200001/100000) (671447/5000000)

theorem source_restricts_count : countSourceFace.Restricts countGlobal := by
 constructor <;> norm_num [countSourceFace,QRH.Record1252270103Source.globalFace,countGlobal,
  QRH.Record1252270103Return.globalFace,countCB,countCL,countCap]

theorem source_restricts_physical : physicalSourceFace.Restricts physicalGlobal := by
 constructor <;> norm_num [physicalSourceFace,QRH.Record1252270103Source.globalFace,physicalGlobal,
  QRH.Record1252270103Return.globalFace,physicalB,physicalLambda,physicalCap]

theorem uniform_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
 (hs : UniformUnitFaceSource strong) : UniformUnitFaceSource weak := by
 intro ε hε
 obtain ⟨mesh,hm,hsrc⟩ := hs ε hε
 exact ⟨mesh,hm,unit_source_restrict h hsrc⟩

lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [naturalK]
 linarith

theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤theta :=
 Final.beta_of_global_sources hC hP natural_cap_return

/-- **The two-source return.** The count face `C` and the physical face `P` of the return are supplied by two
(possibly different) global sources: `G(99999/100000, 200001/100000, 671447/5000000)` for the count windows and
`G(99999/100000, 200001/100000, 671447/5000000)` for the capped physical windows and the physical numerator (here the
same face). Each is given under `51/100 ≤ β`; the complementary case is trivial. -/
theorem beta_le_theta_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000))
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000)) :
    HeckeZeroSupremum.beta ≤ (1746764287/2000000000 : ℝ) := by
  rw [← theta_value]
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · exact beta_of_two_global_sources (uniform_restrict source_restricts_count (hC hbeta))
      (uniform_restrict source_restricts_physical (hP hbeta))
  · have ht : (51/100:ℝ) ≤ theta := by norm_num [theta,c]
    exact (not_le.mp hbeta).le.trans ht

/-- The Dirichlet transfer of `beta_le_theta_of_sources` (as PR76 `Graph.dirichlet_of_step`). -/
theorem dirichlet_of_sources
    (hC : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000))
    (hP : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1746764287 / 2000000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num)
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      ((beta_le_theta_of_sources hC hP).trans_lt hs) hpole) χ s hs hpole

/-- The fixed return, conditional only on the actual global source at its target face. -/
theorem beta_le_target_of_global_source
    (h : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000)) :
    HeckeZeroSupremum.beta ≤ (1746764287/2000000000 : ℝ) :=
  beta_le_theta_of_sources h h

theorem dirichlet_of_global_source
    (h : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99999/100000) (200001/100000) (671447/5000000))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1746764287/2000000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 :=
  dirichlet_of_sources h h χ hs hpole

#print axioms beta_le_target_of_global_source
#print axioms dirichlet_of_global_source

end
end QRH.PR97Refinement.Return.Tuning
