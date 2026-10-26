/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source254
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source282
set_option autoImplicit false
namespace Record1252270103Finite
def source284 : Source := ⟨(962512109261/1000000000000),(630811771219/200000000000),(549989/10000000),(273078127583/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source284_valid : SourceValid source284 source282 (some source254) := by decide +kernel
#print axioms source284_valid
end Record1252270103Finite
