/- Copyright (c) 2026 Sil, Hailey Collet and OpenAI. Apache-2.0.
Literal finite cells and partitions with no old Bounds or PhysicalSchedule
in scope. The numerical cell admission is still supplied by ReturnFiniteNumerator.

-/
import Candidate.Feedback.FourthPower.ReturnCarrierInterfaces
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Imported.FullWFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReturnNumeratorCarrier
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Assembly
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem fullW_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),
      finiteCentralFullWRows S hS hmax η (cubeBinRows R idx grid i j) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralFullWRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i j u).mp hu with ⟨_,hi,hj⟩
  simp only [hi,hj]

theorem fullW_dyadic_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e U : ℝ) (a H : FreeRow→ℝ)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤ U) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H =
      ∑k∈smallDyadicIndices U,
        finiteCentralFullWRows S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralFullWRows
  exact retained_dyadic_sum R U hR _

theorem fullW_cells_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B U : ℝ) (idx grid : FreeRow→ℕ)
    (n m : ℕ) (N : ℂ) (A : ℝ) (hA : 0≤ A)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤ U)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m)
    (hcell : ∀k∈smallDyadicIndices U,∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
      (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty →
      ‖finiteCentralFullWRows S hS hmax η (cubeBinRows (R∩dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 X Y Z e (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B)/N‖≤ A) :
    ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)/N‖ ≤
      ((smallDyadicIndices U).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*A := by
  rw [fullW_dyadic_partition S hS hmax η R T hT W Yp W0 W1 X Y Z e U _ _ hR,
    Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices U,(n+1:ℕ)*(m+1:ℕ)*A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [fullW_bin_partition S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e B
        idx grid n m (fun u hu=>hlabel u (Finset.mem_inter.mp hu).1),Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),A := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro j hj
          by_cases hn : (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty
          · exact hcell k hk i hi j hj hn
          · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hn
            simpa only [hempty,finiteCentralFullWRows,Finset.sum_empty,zero_div,norm_zero] using hA
        _ = _ := by simp;ring
    _ = _ := by simp;ring

section Geometry
variable [Geometry.Parameters]
def primePool (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))

theorem poolOutside (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) :
    ∀j P,P∈primePool D F Z j→P.val∉F.S :=
  fun j P hP=>(mem_pool _ F.S 1 2 (Z^(D.length j)) P).mp hP |>.2.2.2

abbrev normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  ReturnCarrierInterfaces.normalizer D F Z

def fullW (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (R : Finset FreeRow) (a H : FreeRow→ℝ) : ℂ :=
  Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η R
    (primePool D F Z) (poolOutside D F Z) (fun _ y=>(F.w y:ℂ)) (fun j=>Z^(D.length j))
    F.W F.W (Z^Geometry.x) (Z^Geometry.y) Z D.e a H

def selectedRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (grid : FreeRow→ℕ) :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(Geometry.h+ReturnCarrierInterfaces.rowPadding))) grid

def cellRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (idx grid : FreeRow→ℕ) (k i j : ℕ) :=
  cubeBinRows (selectedRows D F Z grid∩dyadicRows 1 k) idx grid i j

structure CellFacts (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z τ : ℝ) (R : Finset FreeRow) (d a : ℝ) (i : ℕ) : Prop where
  d_lower : (1/200:ℝ)≤ d
  d_upper : d≤ Geometry.dPlus
  a_lower : (51/100:ℝ)< a
  a_upper : a≤7/8
  source_rows : ∀u∈R,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-D.t)
  moment_rows : ∀u∈R,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d
  frequency_lower : ∀u∈R,Z^(d-2*D.t)≤ rowNorm u
  natural_nonprincipal : ∀u∈R,∀θ,(rayCubeFamily F.modulus ⊤ le_top u θ).residue≠1
  next_maximum : ∀u∈R,detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    (3*(i+1:ℕ)*Z^τ)< a+2*D.e
  current_maximum : ∀u∈R,a≤ detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    ((3*i:ℕ)*Z^τ)

theorem selected_rows_facts (D : BaselineData) (F : BaselineSourceData D)
    (Z : ℝ) (grid : FreeRow→ℕ) :
    ∀u∈selectedRows D F Z grid,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤ Z^(Geometry.h+ReturnCarrierInterfaces.rowPadding) := by
  intro u hu
  rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hb,hcal,_⟩
  rcases mem_rowBand.mp hb with ⟨hne,hlo,hhi⟩
  exact ⟨hne,hlo,hcal,hhi.le⟩
end Geometry
end
end Candidate.Feedback.FourthPower.ReturnNumeratorCarrier
