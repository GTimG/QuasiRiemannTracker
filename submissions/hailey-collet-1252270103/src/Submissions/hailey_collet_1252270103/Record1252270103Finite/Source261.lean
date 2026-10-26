/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source255
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source256
set_option autoImplicit false
namespace Record1252270103Finite
def source261 : Source := ⟨(192636373127/200000000000),(3169988015303/1000000000000),(549989/10000000),(137147969797/250000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source261_valid : SourceValid source261 source256 (some source255) := by decide +kernel
#print axioms source261_valid
end Record1252270103Finite
