/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source193
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source198
set_option autoImplicit false
namespace Record1252270103Finite
def source201 : Source := ⟨(60344280461/62500000000),(3226284864241/1000000000000),(549989/10000000),(278535888897/500000000000),(1/1000000000000),(1/100000000),(1/10000000)⟩
theorem source201_valid : SourceValid source201 source198 (some source193) := by decide +kernel
#print axioms source201_valid
end Record1252270103Finite
