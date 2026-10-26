import Candidate.Target830.Marked.VariableSupply
import Candidate.Target830.Parameters

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830

theorem marked_density_eq (delta : ℝ) :
    Marked830.VariableSupply.density delta=rho delta := rfl

theorem marked_phi_eq (delta : ℝ) :
    Marked830.VariableSupply.phi delta=phi delta := rfl

theorem marked_capI_eq (delta : ℝ) :
    Marked830.VariableSupply.cap delta=capI delta := rfl

theorem marked_capP_eq (delta : ℝ) :
    Marked830.VariableSupply.plainCap delta=capP delta := rfl

theorem marked_physicalGain_eq (delta S D : ℝ) :
    Marked830.VariableSupply.physicalGain delta S D=
      phi delta*(2*min S (capI delta*D)+min S (capP delta*D))/3 := rfl

end OAI.SevenEighths.Target830
#print axioms OAI.SevenEighths.Target830.marked_physicalGain_eq
