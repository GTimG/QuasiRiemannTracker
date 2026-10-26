/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source209
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source213
set_option autoImplicit false
namespace Record1252270103Finite
def source226 : Source := ⟨(967619540989/1000000000000),(3278909582251/1000000000000),(549989/10000000),(564799197707/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source226_valid : SourceValid source226 source213 (some source209) := by decide +kernel
#print axioms source226_valid
end Record1252270103Finite
