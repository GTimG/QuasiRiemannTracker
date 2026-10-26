/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal normalized frozen-squarefree centered rows on one common maximal pool.
Frozen ordinary ideals stay in the squarefree projector after cofactor extraction. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

/-- The marked product is the literal original finite marked family. -/
theorem normalized_centered_newton_marked {κ:Type*} (P:Finset (Ideal O))
    (slots:Finset κ)(marked:κ→Ideal O)(D A₁ A₂:Ideal O)(depth:ℕ)
    (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hT:0<T)
    (hp:∀p∈P,Prime p)(hN:∀p∈P,16≤p.absNorm)(havoid:∀p∈P,∀i∈slots,¬p∣marked i)
    (hsupport:∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→
      IsCoprime D ((∏i∈slots,marked i)*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*((∏i∈slots,marked i)*n.1*n.2))).card<P.card) :
    correctedCenteredRow P D (∏i∈slots,marked i) A₁ A₂ ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
            (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
          frozenCenteredRow ψ W₁ W₂ (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
            (X₁/(newtonDivisorPair S A).1.absNorm) (X₂/(newtonDivisorPair S A).2.absNorm)
            (Y₁/(newtonDivisorPair S A).1.absNorm) (Y₂/(newtonDivisorPair S A).2.absNorm)
            (T/pairNorm (newtonDivisorPair S A)) := by
  exact normalized_centered_newton P D (∏i∈slots,marked i) A₁ A₂ depth ψ W₁ W₂
    b X₁ X₂ Y₁ Y₂ T hT hp hN (pool_avoids_marked_product P slots marked hp havoid) hsupport

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.normalized_centered_newton_marked
