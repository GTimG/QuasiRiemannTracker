import Candidate.Target836.Detector836.Rows.OldLower
import Candidate.Target836.Detector836.Rows.OldHalf
import Candidate.Target836.Detector836.Rows.OldJunction
import Candidate.Target836.Detector836.Rows.NewJunction
import Candidate.Target836.Detector836.Rows.Top

set_option autoImplicit false
namespace Target836.EndpointCertificates
noncomputable section
open Target836.Arithmetic Target836.EndpointArithmetic

/-- All five scalar ends for the three-branch detector schedule. -/
theorem endpoint_pack {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent d0 δ p ≤ theta-reserve ∧
    oldExponent y δ p ≤ theta-reserve ∧
    oldExponent dMinus δ p ≤ theta-reserve ∧
    newExponent dMinus δ p ≤ theta-reserve ∧
    newExponent dPlus δ p ≤ theta-reserve :=
  ⟨old_lower_bound hδ hp,old_half_bound hδ hp,old_junction_bound hδ hp,
    new_junction_bound hδ hp,top_bound hδ hp⟩

end
end Target836.EndpointCertificates
#print axioms Target836.EndpointCertificates.endpoint_pack
