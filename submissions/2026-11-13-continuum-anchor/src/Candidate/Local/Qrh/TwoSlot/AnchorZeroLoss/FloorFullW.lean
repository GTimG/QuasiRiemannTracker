/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Inclusive averaged floor through the physical scalar and complete FullW
integral. Uses Hailey Collet's scalar and FullW reconstruction theorems. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorIntegrated
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.FullWBound
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.SourceScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily
open HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Weighted.FullWContour

/-- The complete physical FullW floor bound, before the signal normalizer
and row partition. Prime caps remain explicit source obligations; the actual
scalar and both remaining contour integrations are discharged here. -/
theorem physical_floor_fullW {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (kap : ℝ)
    (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (he : D.e < 1/1000)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (Z d : ℝ), 1 ≤ Z → U=Z^d → ∀ (η : Character) (rows : Finset FreeRow),
    (∀u∈rows,u.val ≠ 1) →
    (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
    (∀u∈rows,Z^(d-2*D.t) ≤ rowNorm u) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue ≠ 1) →
    (∀J:Finset (Fin D.N),∀P:∀i:J,sourcePrimePool F Z i.val,
      Function.Injective (fun i => (P i).val)) →
    (∀P:∀i,sourcePrimePool F Z i,Function.Injective (fun i => (P i).val)) →
    (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus) →
    (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm) →
    (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell i)) →
    (∀i,sourcePrimePool F Z i) →
    ∀ {ι : Type} [Fintype ι] (ψ : FreeRow → ι → Character)
      (B H : ℝ) (i : ℕ), 2 < B → 0 ≤ H → H ≤ (3*i+2:ℕ)*B →
    (∀u∈rows,detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (ψ u)) (3*(i+1:ℕ)*B) < 51/100+2*D.e) →
    (∀z:ℂ,z.re=17/50 → |z.im| ≤ H → ∀u∈rows,∀j,
      ‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z‖
        ≤ Z^(D.ell j*(1/100+D.t))) →
    ∀ (X v : ℝ), 0 < X → 0 < v → v ≤ 99 →
    ‖finiteCentralFullWRows F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
      (fun j => Z^(D.ell j)) F.W F.W X (U^v) Z D.e (fun _ => 51/100) (fun _ => H)‖ ≤
      C*X^(4/25:ℝ)*Z^(-3/20+16*D.e)*
      (η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*(U^v)^(-(1/2:ℝ))*
      Z^((17/25)*D.t+(-3/20+D.t)*∑j,D.ell j)*
      U^(33/50+2*eps+(38/25)*D.t) := by
  obtain ⟨Cm,hCm,hm⟩ := physical_floor_integrated F kap hkaplo hkaphi hkapbeta hbeta he.le
  obtain ⟨Cs,hCs,hs⟩ := source_frequency_scalar_bound D.e eps D.e_pos he heps
    F.S F.exclusions F.maximal
  obtain ⟨Cw,hCw,hw⟩ := finiteFullW_uniform_norm_bound F.W 1 2 (by norm_num) F.complex_support
  refine ⟨Cw*Cm*Cs,by positivity,?_⟩
  filter_upwards [hm] with U hm
  refine ⟨hm.1,?_⟩
  intro Z d hZ hUZ η rows hone hrows hfreq hrow hdis hdisAll hη hQ hS Pbase
    ι _ ψ B H i hB hH hHi hnext hmain X v hX hv hvhi
  have hZp := zero_lt_one.trans_le hZ
  have hUp := zero_lt_one.trans hm.1
  let A : ℝ := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*
    U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  let raw : ℝ := Cm*A*(U^v)^(-(1/2:ℝ))*Z^((-3/20+D.t)*∑j,D.ell j)*
    U^(1+(38/25:ℝ)*D.t)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hraw : 0 ≤ raw := by dsimp only [raw]; positivity
  have hr (q : ℝ×ℝ) (hq:q∈szRectangle H) :
      ‖integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
        (fun j => Z^(D.ell j)) F.W (U^v)
        ((((51/100+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤ raw := by
    apply hm.2 Z hZ η _ _ (by simp) (by norm_num) rows hrows hrow hdis hdisAll hη hQ hS
      Pbase (hmain _ (by norm_num) (by simpa using hq.2)) v A hv hvhi hA
    intro u hu
    exact hs η u (ψ u) B (51/100) H i hB le_rfl (by norm_num) hHi (hnext u hu)
      _ _ (by simp) (by norm_num) (by simpa using hq.1) Z d D.t U hZp hUZ
      (hfreq u hu) (hrows u hu).2
  have hh := hw D.e (51/100) B H i D.e_pos he le_rfl (by norm_num) hB hHi
    F.S F.exclusions F.maximal F.first η rows hone (sourcePrimePool F Z)
    (fun j => source_prime_pool_outside F Z j) ψ hnext (fun _ => F.W)
    (fun j => Z^(D.ell j)) F.W 1 2 (by norm_num) F.complex_support X (U^v) Z raw
    hX (Real.rpow_pos_of_pos hUp _) hZp hraw hr
  apply hh.trans_eq
  dsimp only [raw,A]
  rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
    show (51/100+16*D.e+17/50-1:ℝ)=-3/20+16*D.e by ring]
  have hU : U^(2*eps)*U^(-(17/50:ℝ))*U^(1+(38/25)*D.t) =
      U^(33/50+2*eps+(38/25)*D.t) := by
    rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
    congr 1
    ring
  rw [Real.rpow_add hZp ((17/25)*D.t) ((-3/20+D.t)*∑j,D.ell j)]
  calc
    _ = Cw*Cm*Cs*X^(4/25:ℝ)*Z^(-3/20+16*D.e)*(η.modulus.absNorm:ℝ)^(2*eps)*
        (3+H)^(2*eps)*(U^v)^(-(1/2:ℝ))*
        (Z^((17/25)*D.t)*Z^((-3/20+D.t)*∑j,D.ell j))*
        (U^(2*eps)*U^(-(17/50:ℝ))*U^(1+(38/25)*D.t)) := by ring
    _ = _ := by rw [hU]

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.physical_floor_fullW
