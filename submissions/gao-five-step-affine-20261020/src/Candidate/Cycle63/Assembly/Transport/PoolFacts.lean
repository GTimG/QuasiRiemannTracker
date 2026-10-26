import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RaySlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.RayQuotient

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
namespace SevenEighths
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance poolFactsFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

omit [NeZero M] in
/-- A prime in a ray pool lies outside the excluded set. -/
theorem poolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

end SevenEighths
end
end OAI
