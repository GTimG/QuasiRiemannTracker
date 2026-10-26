/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source277
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source283
set_option autoImplicit false
namespace Record1252270103Finite
def source285 : Source := ⟨(15119900567/15625000000),(3280245219427/1000000000000),(549989/10000000),(282514040849/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source285_valid : SourceValid source285 source283 (some source277) := by decide +kernel
#print axioms source285_valid
end Record1252270103Finite
