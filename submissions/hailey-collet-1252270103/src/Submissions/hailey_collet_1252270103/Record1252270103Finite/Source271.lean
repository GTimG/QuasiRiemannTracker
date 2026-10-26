/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source244
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source268
set_option autoImplicit false
namespace Record1252270103Finite
def source271 : Source := ⟨(193632973709/200000000000),(3292733759277/1000000000000),(549989/10000000),(141714928021/250000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source271_valid : SourceValid source271 source268 (some source244) := by decide +kernel
#print axioms source271_valid
end Record1252270103Finite
