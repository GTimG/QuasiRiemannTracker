/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source245
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source271
set_option autoImplicit false
namespace Record1252270103Finite
def source274 : Source := ⟨(484018720081/500000000000),(822371543623/250000000000),(549989/10000000),(283203366833/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source274_valid : SourceValid source274 source271 (some source245) := by decide +kernel
#print axioms source274_valid
end Record1252270103Finite
