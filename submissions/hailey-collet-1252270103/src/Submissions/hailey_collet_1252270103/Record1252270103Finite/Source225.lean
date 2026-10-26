/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source206
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source212
set_option autoImplicit false
namespace Record1252270103Finite
def source225 : Source := ⟨(483987561633/500000000000),(164396177829/50000000000),(549989/10000000),(566138467121/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source225_valid : SourceValid source225 source212 (some source206) := by decide +kernel
#print axioms source225_valid
end Record1252270103Finite
