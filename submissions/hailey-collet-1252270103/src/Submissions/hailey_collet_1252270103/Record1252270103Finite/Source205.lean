/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source200
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source202
set_option autoImplicit false
namespace Record1252270103Finite
def source205 : Source := ⟨(964422199241/1000000000000),(399977935829/125000000000),(549989/10000000),(276521239619/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source205_valid : SourceValid source205 source202 (some source200) := by decide +kernel
#print axioms source205_valid
end Record1252270103Finite
