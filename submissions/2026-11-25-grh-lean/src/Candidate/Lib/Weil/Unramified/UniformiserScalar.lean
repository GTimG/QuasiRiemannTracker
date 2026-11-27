import Candidate.Lib.ClassField.HeckeL.AutCharLFunction

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Scalar by which a uniformiser acts in the Weil representation. -/

/-- The complex number χ(ϖ_w)·q_w^{k/2}, where χ = `AutChar.spaceChar` a k is the Hecke character x
↦ a(x/x̄)υ(x)^{−k} and ϖ_w the chosen uniformiser at w. -/
noncomputable def AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E) n
    [Fintype n] w := (a.spaceChar (Fintype.card n)).atUnif w * √w.q ^ Fintype.card n
