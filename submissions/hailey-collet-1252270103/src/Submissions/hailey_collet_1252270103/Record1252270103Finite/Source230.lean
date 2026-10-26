/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source213
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source218
set_option autoImplicit false
namespace Record1252270103Finite
def source230 : Source := ⟨(193263142881/200000000000),(3246229223437/1000000000000),(549989/10000000),(279957404577/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source230_valid : SourceValid source230 source218 (some source213) := by decide +kernel
#print axioms source230_valid
end Record1252270103Finite
