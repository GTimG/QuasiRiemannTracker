/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source101
set_option autoImplicit false
namespace Record1252270103Finite
def source103 : Source := ⟨(490185053009/500000000000),(3635423616051/1000000000000),(24333623369/500000000000),(618171022473/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source103_valid : SourceValid source103 source101 (some source101) := by decide +kernel
#print axioms source103_valid
end Record1252270103Finite
