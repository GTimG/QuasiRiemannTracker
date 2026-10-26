/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source292
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source298
set_option autoImplicit false
namespace Record1252270103Finite
def source301 : Source := ⟨(48369515545621/50000000000000),(163653997694883/50000000000000),(549989/10000000),(56390239081147/100000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source301_valid : SourceValid source301 source298 (some source292) := by decide +kernel
#print axioms source301_valid
end Record1252270103Finite
