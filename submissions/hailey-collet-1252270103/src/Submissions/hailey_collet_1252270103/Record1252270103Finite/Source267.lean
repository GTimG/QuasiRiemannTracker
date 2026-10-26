/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source244
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source263
set_option autoImplicit false
namespace Record1252270103Finite
def source267 : Source := ⟨(484162161/500000000),(3296805827059/1000000000000),(549989/10000000),(567454883433/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source267_valid : SourceValid source267 source263 (some source244) := by decide +kernel
#print axioms source267_valid
end Record1252270103Finite
