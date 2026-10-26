/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source171
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source176
set_option autoImplicit false
namespace Record1252270103Finite
def source213 : Source := ⟨(967678905491/1000000000000),(656082715227/200000000000),(549989/10000000),(8829040059/15625000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source213_valid : SourceValid source213 source176 (some source171) := by decide +kernel
#print axioms source213_valid
end Record1252270103Finite
