/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source193
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source201
set_option autoImplicit false
namespace Record1252270103Finite
def source203 : Source := ⟨(30167755571/31250000000),(805709389091/250000000000),(549989/10000000),(111294589421/200000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source203_valid : SourceValid source203 source201 (some source193) := by decide +kernel
#print axioms source203_valid
end Record1252270103Finite
