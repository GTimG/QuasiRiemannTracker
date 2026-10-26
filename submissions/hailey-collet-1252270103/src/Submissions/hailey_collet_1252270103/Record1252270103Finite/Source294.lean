/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source289
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source292
set_option autoImplicit false
namespace Record1252270103Finite
def source294 : Source := ⟨(3869577887487/4000000000000),(818296256111/250000000000),(549989/10000000),(56391870494007/100000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source294_valid : SourceValid source294 source292 (some source289) := by decide +kernel
#print axioms source294_valid
end Record1252270103Finite
