/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source244
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source271
set_option autoImplicit false
namespace Record1252270103Finite
def source273 : Source := ⟨(968140180139/1000000000000),(1646051879881/500000000000),(549989/10000000),(566751259983/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source273_valid : SourceValid source273 source271 (some source244) := by decide +kernel
#print axioms source273_valid
end Record1252270103Finite
