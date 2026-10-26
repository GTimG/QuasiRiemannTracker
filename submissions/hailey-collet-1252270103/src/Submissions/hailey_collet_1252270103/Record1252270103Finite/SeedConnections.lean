/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceAll
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceGraph
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedCommonWidth
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceDenominators
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFaces
set_option autoImplicit false
namespace Record1252270103Finite

theorem seed_natural_cost : seedNatural.L=6*(2*(87481891/100000000)-1) := by
 norm_num [seedNatural]
theorem new_natural_cost : natural.L=6*(2*(8747759/10000000)-1) := by
 norm_num [natural]
theorem seed_C_parameters : seedSource64.B=482045093689/500000000000 ∧
 seedSource64.L=3198839752287/1000000000000 ∧ seedSource64.cap=54998999999/1000000000000 := by
 norm_num [seedSource64]
theorem seed_P_parameters : seedSource63.B=96934050457/100000000000 ∧
 seedSource63.L=3328741896069/1000000000000 ∧ seedSource63.cap=54998999999/1000000000000 := by
 norm_num [seedSource63]
#print axioms seed_natural_cost
#print axioms new_natural_cost
#print axioms seed_C_parameters
#print axioms seed_P_parameters
end Record1252270103Finite
