/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedMiddleReturnOriginalProduct
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

/-- The complete error-label prime mass and complementary main front use
ALL original prime slots exactly once, including empty/full error masks. -/
theorem original_prime_front (D : BaselineData) (J : Finset (Fin D.N))
    {Z : ℝ} (hZ : 0<Z) :
    mainFront D J Z*(∏k : J,(Z^(D.length k.val))^(-(4/25:ℝ)))=Z^(-4*Geometry.ell/25) := by
  have hs : (∑k : {i : Fin D.N // i∉J},D.length k.val)+(∑k : J,D.length k.val)=Geometry.ell := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun i : Fin D.N=>i∉J) D.length
    let e : {i : Fin D.N // ¬i∉J}≃J := Equiv.subtypeEquivRight (fun i=>not_not)
    have he := Fintype.sum_equiv e (fun k=>D.length k.val) (fun k=>D.length k.val) (fun _=>rfl)
    rw [he,D.slots_sum] at hh
    exact hh
  unfold mainFront
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,←Real.rpow_add hZ]
  congr 1
  nlinarith only [hs]

#print axioms original_prime_front
end
end QRH.Cycle092.MixedMiddleReturn
