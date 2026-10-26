/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal normalized frozen-squarefree centered rows on one common maximal pool.
Frozen ordinary ideals stay in the squarefree projector after cofactor extraction. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CorrectedCenteredPools
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SourceModifier
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

def centeredProfile (W₁ W₂:ℝ→ℂ)(X₁ X₂ Y₁ Y₂:ℝ)(n:IdealPair):ℂ :=
  pairProfile W₁ W₂ X₁ X₂ n-pairProfile W₁ W₂ Y₁ Y₂ n

def commonPool (b X₁ X₂ Y₁ Y₂:ℝ):Finset IdealPair :=
  holePairPool b (max X₁ Y₁) (max X₂ Y₂)

def frozenProfile (W₁ W₂:ℝ→ℂ)(A₁ A₂:Ideal O)(X₁ X₂ Y₁ Y₂:ℝ)(n:IdealPair):ℂ :=
  ordinaryHoleIndicator (A₁*n.1) (A₂*n.2)*centeredProfile W₁ W₂ X₁ X₂ Y₁ Y₂ n

def frozenCenteredRow (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)
    (A₁ A₂:Ideal O)(b X₁ X₂ Y₁ Y₂ T:ℝ):ℂ :=
  (Real.sqrt T:ℂ)⁻¹*∑n∈commonPool b X₁ X₂ Y₁ Y₂,
    (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n

def correctedCenteredRow (P:Finset (Ideal O))(D M A₁ A₂:Ideal O)
    (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂ Y₁ Y₂ T:ℝ):ℂ :=
  (Real.sqrt T:ℂ)⁻¹*∑n∈commonPool b X₁ X₂ Y₁ Y₂,
    (((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*(M*n.1*n.2))).card)):ℂ)*
      (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*
        frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n

end
end QRH.Record1252270103Source.High.CorrectedCentered
