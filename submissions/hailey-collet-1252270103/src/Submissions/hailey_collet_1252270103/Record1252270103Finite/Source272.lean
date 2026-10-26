/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source255
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source269
set_option autoImplicit false
namespace Record1252270103Finite
def source272 : Source := ⟨(962798689407/1000000000000),(790214720491/250000000000),(549989/10000000),(547230515727/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source272_valid : SourceValid source272 source269 (some source255) := by decide +kernel
#print axioms source272_valid
end Record1252270103Finite
