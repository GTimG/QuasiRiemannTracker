/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source007
set_option autoImplicit false
namespace Record1252270103Finite
def source008 : Source := ⟨(62362914321/62500000000),(543950579517/125000000000),(6435356391/200000000000),(727033114831/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source008_valid : SourceValid source008 source007 none := by decide +kernel
#print axioms source008_valid
end Record1252270103Finite
