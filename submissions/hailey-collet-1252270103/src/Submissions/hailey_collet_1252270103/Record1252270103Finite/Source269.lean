/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source255
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source265
set_option autoImplicit false
namespace Record1252270103Finite
def source269 : Source := ⟨(962939824583/1000000000000),(3164216356823/1000000000000),(549989/10000000),(13692486369/25000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source269_valid : SourceValid source269 source265 (some source255) := by decide +kernel
#print axioms source269_valid
end Record1252270103Finite
