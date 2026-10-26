import Submissions.arvi_repeated_marks_20261024.Faceless.Validity
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Scalar0
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_00
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_01
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_02
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_10
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_11
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_0_12
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_00
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_01
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_02
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_10
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_11
import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.High0_1_12

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

theorem piece0_certs : piece0.Certs where
  sig0 := by norm_num [piece0]
  H0 := by norm_num [piece0]
  Dy0 := by norm_num [piece0]
  capS := by norm_num [piece0, capF]
  field i := by
    fin_cases i
    exacts [⟨_, p0_field_0⟩, ⟨_, p0_field_1⟩, ⟨_, p0_field_2⟩, ⟨_, p0_field_3⟩, ⟨_, p0_field_4⟩, ⟨_, p0_field_5⟩, ⟨_, p0_field_6⟩, ⟨_, p0_field_7⟩, ⟨_, p0_field_8⟩]
  scal e jj := by
    fin_cases e <;> fin_cases jj
    exacts [⟨_, p0_scal_0_0⟩, ⟨_, p0_scal_0_1⟩, ⟨_, p0_scal_0_2⟩, ⟨_, p0_scal_0_3⟩, ⟨_, p0_scal_0_4⟩, ⟨_, p0_scal_0_5⟩, ⟨_, p0_scal_0_6⟩, ⟨_, p0_scal_0_7⟩, ⟨_, p0_scal_0_8⟩, ⟨_, p0_scal_0_9⟩, ⟨_, p0_scal_0_10⟩, ⟨_, p0_scal_0_11⟩, ⟨_, p0_scal_0_12⟩, ⟨_, p0_scal_0_13⟩, ⟨_, p0_scal_0_14⟩, ⟨_, p0_scal_0_15⟩, ⟨_, p0_scal_1_0⟩, ⟨_, p0_scal_1_1⟩, ⟨_, p0_scal_1_2⟩, ⟨_, p0_scal_1_3⟩, ⟨_, p0_scal_1_4⟩, ⟨_, p0_scal_1_5⟩, ⟨_, p0_scal_1_6⟩, ⟨_, p0_scal_1_7⟩, ⟨_, p0_scal_1_8⟩, ⟨_, p0_scal_1_9⟩, ⟨_, p0_scal_1_10⟩, ⟨_, p0_scal_1_11⟩, ⟨_, p0_scal_1_12⟩, ⟨_, p0_scal_1_13⟩, ⟨_, p0_scal_1_14⟩, ⟨_, p0_scal_1_15⟩]
  weak e := by
    fin_cases e
    exacts [⟨_, p0_weak_0⟩, ⟨_, p0_weak_1⟩]
  sec e s i := by
    fin_cases e <;> fin_cases s <;> fin_cases i
    exacts [⟨_, p0_sec_0_0_0⟩, ⟨_, p0_sec_0_0_1⟩, ⟨_, p0_sec_0_0_2⟩, ⟨_, p0_sec_0_0_3⟩, ⟨_, p0_sec_0_1_0⟩, ⟨_, p0_sec_0_1_1⟩, ⟨_, p0_sec_0_1_2⟩, ⟨_, p0_sec_0_1_3⟩, ⟨_, p0_sec_0_2_0⟩, ⟨_, p0_sec_0_2_1⟩, ⟨_, p0_sec_0_2_2⟩, ⟨_, p0_sec_0_2_3⟩, ⟨_, p0_sec_1_0_0⟩, ⟨_, p0_sec_1_0_1⟩, ⟨_, p0_sec_1_0_2⟩, ⟨_, p0_sec_1_0_3⟩, ⟨_, p0_sec_1_1_0⟩, ⟨_, p0_sec_1_1_1⟩, ⟨_, p0_sec_1_1_2⟩, ⟨_, p0_sec_1_1_3⟩, ⟨_, p0_sec_1_2_0⟩, ⟨_, p0_sec_1_2_1⟩, ⟨_, p0_sec_1_2_2⟩, ⟨_, p0_sec_1_2_3⟩]
  cell e := by
    fin_cases e
    exacts [⟨_, p0_cell_0⟩, ⟨_, p0_cell_1⟩]
  high e k := by
    rcases k with ⟨i, jj⟩
    fin_cases e <;> fin_cases i <;> fin_cases jj
    exacts [⟨_, p0_high_0_00⟩, ⟨_, p0_high_0_01⟩, ⟨_, p0_high_0_02⟩, ⟨_, p0_high_0_10⟩, ⟨_, p0_high_0_11⟩, ⟨_, p0_high_0_12⟩, ⟨_, p0_high_1_00⟩, ⟨_, p0_high_1_01⟩, ⟨_, p0_high_1_02⟩, ⟨_, p0_high_1_10⟩, ⟨_, p0_high_1_11⟩, ⟨_, p0_high_1_12⟩]

end QRH.RepeatedMarks.Faceless
