/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Source009
set_option autoImplicit false
namespace Record1252270103Finite
def source010 : Source := ⟨(49872291451/50000000000),(866012706781/200000000000),(8181368711/250000000000),(723566154511/1000000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source010_valid : SourceValid source010 source009 none := by decide +kernel
#print axioms source010_valid
end Record1252270103Finite
