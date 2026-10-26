/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source180
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source182
set_option autoImplicit false
namespace Record1252270103Finite
def source185 : Source := ⟨(60393484997/62500000000),(1622895772401/500000000000),(549989/10000000),(559897033079/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source185_valid : SourceValid source185 source182 (some source180) := by decide +kernel
#print axioms source185_valid
end Record1252270103Finite
