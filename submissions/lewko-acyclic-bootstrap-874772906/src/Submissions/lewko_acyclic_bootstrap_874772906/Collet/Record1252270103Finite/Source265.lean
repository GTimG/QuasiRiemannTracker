/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source255
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source261
set_option autoImplicit false
namespace Record1252270103Finite
def source265 : Source := ⟨(120376502483/125000000000),(633187326663/200000000000),(549989/10000000),(548001273281/1000000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source265_valid : SourceValid source265 source261 (some source255) := by decide +kernel
#print axioms source265_valid
end Record1252270103Finite
