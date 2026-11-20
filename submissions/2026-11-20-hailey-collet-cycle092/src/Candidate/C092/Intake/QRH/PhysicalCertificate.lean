/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.PhysicalCertificate.Original
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group00
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group01
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group02
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group03
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group04
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group05
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group06
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group07
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group08
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group09
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group10
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group11
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group12
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group13
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group14
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group15
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group16
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group17
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group18
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group19
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group20
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group21
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group22
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group23
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group24
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group25
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group26
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group27
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group28
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group29
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group30
import Candidate.C092.Intake.QRH.PhysicalCertificate.Group31

/-! Actual finite Q geometry and stored-value checks. Physical price soundness remains conditional. -/

set_option autoImplicit false

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- The complete actual Q forest, in the supplied checker's deterministic order. -/
def qForest : List Root := group00 ++ group01 ++ group02 ++ group03 ++ group04 ++ group05 ++ group06 ++ group07 ++ group08 ++ group09 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 ++ group16 ++ group17 ++ group18 ++ group19 ++ group20 ++ group21 ++ group22 ++ group23 ++ group24 ++ group25 ++ group26 ++ group27 ++ group28 ++ group29 ++ group30 ++ group31

/-- Every actual terminal box matches its recursive midpoint position, and every stored bound passes its threshold. -/
theorem qForest_checked : checkForest qForest = true := by
  simp only [qForest, checkForest_append, group00_checked, group01_checked, group02_checked, group03_checked, group04_checked, group05_checked, group06_checked, group07_checked, group08_checked, group09_checked, group10_checked, group11_checked, group12_checked, group13_checked, group14_checked, group15_checked, group16_checked, group17_checked, group18_checked, group19_checked, group20_checked, group21_checked, group22_checked, group23_checked, group24_checked, group25_checked, group26_checked, group27_checked, group28_checked, group29_checked, group30_checked, group31_checked, Bool.and_self]

/-- The actual forest contains 2,045 explicitly specified coarse roots. -/
theorem qForest_length : qForest.length = 2045 := by
  norm_num only [qForest, List.length_append, group00_length, group01_length, group02_length, group03_length, group04_length, group05_length, group06_length, group07_length, group08_length, group09_length, group10_length, group11_length, group12_length, group13_length, group14_length, group15_length, group16_length, group17_length, group18_length, group19_length, group20_length, group21_length, group22_length, group23_length, group24_length, group25_length, group26_length, group27_length, group28_length, group29_length, group30_length, group31_length]

/-- The actual forest makes exactly 2,561 complete four-way subdivisions. -/
theorem qForest_splits : Coverage.forestSplits (qForest.map Root.erase) = 2561 := by
  norm_num only [qForest, List.map_append, splits_append, group00_splits, group01_splits, group02_splits, group03_splits, group04_splits, group05_splits, group06_splits, group07_splits, group08_splits, group09_splits, group10_splits, group11_splits, group12_splits, group13_splits, group14_splits, group15_splits, group16_splits, group17_splits, group18_splits, group19_splits, group20_splits, group21_splits, group22_splits, group23_splits, group24_splits, group25_splits, group26_splits, group27_splits, group28_splits, group29_splits, group30_splits, group31_splits]

/-- All 9,728 actual terminal rectangles, including exterior leaves, are present. -/
theorem qForest_leaves : Coverage.forestLeaves (qForest.map Root.erase) = 9728 := by
  rw [Coverage.forestLeaves_eq, List.length_map, qForest_length, qForest_splits]

/-- The actual complete forest has 12,289 nodes. -/
theorem qForest_nodes : Coverage.forestNodes (qForest.map Root.erase) = 12289 := by
  rw [Coverage.forestNodes_eq, List.length_map, qForest_length, qForest_splits]

/-- The actual Q forest has exactly 9681 terminals on route mixed. -/
theorem qForest_mixed : routeCount .mixed qForest = 9681 := by
  norm_num only [qForest, routeCount_append, group00_mixed, group01_mixed, group02_mixed, group03_mixed, group04_mixed, group05_mixed, group06_mixed, group07_mixed, group08_mixed, group09_mixed, group10_mixed, group11_mixed, group12_mixed, group13_mixed, group14_mixed, group15_mixed, group16_mixed, group17_mixed, group18_mixed, group19_mixed, group20_mixed, group21_mixed, group22_mixed, group23_mixed, group24_mixed, group25_mixed, group26_mixed, group27_mixed, group28_mixed, group29_mixed, group30_mixed, group31_mixed]

/-- The actual Q forest has exactly 47 terminals on route currentExterior. -/
theorem qForest_currentExterior : routeCount .currentExterior qForest = 47 := by
  norm_num only [qForest, routeCount_append, group00_currentExterior, group01_currentExterior, group02_currentExterior, group03_currentExterior, group04_currentExterior, group05_currentExterior, group06_currentExterior, group07_currentExterior, group08_currentExterior, group09_currentExterior, group10_currentExterior, group11_currentExterior, group12_currentExterior, group13_currentExterior, group14_currentExterior, group15_currentExterior, group16_currentExterior, group17_currentExterior, group18_currentExterior, group19_currentExterior, group20_currentExterior, group21_currentExterior, group22_currentExterior, group23_currentExterior, group24_currentExterior, group25_currentExterior, group26_currentExterior, group27_currentExterior, group28_currentExterior, group29_currentExterior, group30_currentExterior, group31_currentExterior]

/-- The actual Q forest has exactly 0 terminals on route oldExterior. -/
theorem qForest_oldExterior : routeCount .oldExterior qForest = 0 := by
  norm_num only [qForest, routeCount_append, group00_oldExterior, group01_oldExterior, group02_oldExterior, group03_oldExterior, group04_oldExterior, group05_oldExterior, group06_oldExterior, group07_oldExterior, group08_oldExterior, group09_oldExterior, group10_oldExterior, group11_oldExterior, group12_oldExterior, group13_oldExterior, group14_oldExterior, group15_oldExterior, group16_oldExterior, group17_oldExterior, group18_oldExterior, group19_oldExterior, group20_oldExterior, group21_oldExterior, group22_oldExterior, group23_oldExterior, group24_oldExterior, group25_oldExterior, group26_oldExterior, group27_oldExterior, group28_oldExterior, group29_oldExterior, group30_oldExterior, group31_oldExterior]

/-- Every real point in an actual coarse root lies in an actual recorded terminal with a positive stored value. -/
theorem qForest_covers_positive_record {p : Point}
    (hp : ∃ root ∈ qForest, root.box.Contains p) :
    ∃ record ∈ forestRecords qForest, record.box.Contains p ∧ 0 < record.normalized := by
  rcases forest_covers_record qForest_checked hp with ⟨record, hm, hb, ha⟩
  exact ⟨record, hm, hb, record.normalized_pos ha⟩

/-- Complete geometric assembly for Q, conditional on the still-required pointwise interpretation of each recorded leaf. -/
theorem qForest_pointwise_of_leaf_sound {P : Point → Prop}
    (hLeaf : ∀ record ∈ forestRecords qForest, record.accepted = true →
      ∀ p, record.box.Contains p → P p)
    {p : Point} (hp : ∃ root ∈ qForest, root.box.Contains p) : P p :=
  forest_pointwise_of_leaf_sound qForest_checked hLeaf hp

end QRH.PhysicalCertificate
