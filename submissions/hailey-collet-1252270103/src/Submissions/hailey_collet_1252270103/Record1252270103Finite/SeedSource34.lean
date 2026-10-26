/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource32
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource34 : Source := ⟨(982201211907/1000000000000),(1849815024469/500000000000),(47234056529/1000000000000),(78520517663/125000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource34_valid : SeedSourceValid seedSource34 seedSource32 := by decide +kernel
#print axioms seedSource34_valid
end Record1252270103Finite
