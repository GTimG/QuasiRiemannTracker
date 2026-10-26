import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LocalizedFirst
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentAmplificationChildInput CenteredMomentFirstCommonSourceBudget
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- The actual normalized allocation polynomial on an annular row set is
paid by the smooth common-source energy, without counting those rows. -/
theorem actual_annular_allocated_energy {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed C L : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t H : ℝ) (hH : 0<H) (rows : Finset O)
    (hrows : ∀z∈rows,H/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤H) :
    (∑z∈rows,‖allocatedPolynomial (original s R seed) C L τ t (volume s) z‖^2)≤
      (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L
        CenteredMomentFirstAnnularMajorant.profile H).re/volume s := by
  have he (z : O) : allocatedPolynomial (original s R seed) C L τ t (volume s) z=
      (Real.sqrt (volume s):ℂ)⁻¹*commonGauss (original s R seed) C hC τ t L z :=
    (normalized_common_gauss_allocation (original s R seed) s.pools_ne s.prime
      C hC hseed τ t (volume s) L z).symm
  simp only [he,norm_mul,norm_inv,mul_pow,inv_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (volume_pos s).le]
  simp_rw [←div_eq_inv_mul]
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  rw [commonEnergy_real _ _ _ _ _ _ _ _ hH]
  calc
    _ = ∑z∈rows,‖commonGauss (original s R seed) C hC τ t L z‖^2*
        (CenteredMomentFirstAnnularMajorant.profile (‖eisEmbedding z‖^2/H)).re := by
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [CenteredMomentFirstAnnularMajorant.scaled_majorant H _ hH
        (hrows z hz).1 (hrows z hz).2,mul_one]
    _ ≤ _ := sum_le_hasSum rows
      (fun z _=>mul_nonneg (sq_nonneg _)
        (CenteredMomentFirstAnnularMajorant.profile_nonneg _))
      (common_summable (original s R seed) C hC τ t L _ H hH).hasSum

def firstSignedRow (reflected : Bool) (z : O) : O := if reflected then -z else z

theorem actual_signed_annular_allocated_energy {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed C L : Ideal O)
    (hC : Supported C) (hseed : seed∣C) (τ : Character) (t H : ℝ) (hH : 0<H)
    (rows : Finset O)
    (hrows : ∀z∈rows,H/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤H) :
    (∑z∈rows,‖allocatedPolynomial (original s R seed) C L τ t (volume s)
      (firstSignedRow reflected z)‖^2)≤
      (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L
        CenteredMomentFirstAnnularMajorant.profile H).re/volume s := by
  cases reflected
  · exact actual_annular_allocated_energy s R seed C L hC hseed τ t H hH rows hrows
  · have hh := actual_annular_allocated_energy s R seed C L hC hseed τ t H hH
      (rows.image (fun z=>-z)) (by
        intro z hz
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hrows x hx)
    rw [Finset.sum_image (fun x _ y _ h=>neg_injective h)] at hh
    exact hh

/-- Keeps all original source labels inside the sum while replacing their
annular rows by the literal live-allocation child energies. -/
theorem actual_joint_annular_live_energy {Label ι : Type*} [Fintype Label] [Fintype ι]
    (reflected : Bool) (labels : Finset Label) (N : ℕ) (a b : ℝ) (ha : 0<a) (s : Input ι)
    (hcard : Fintype.card ι≤N) (haS : a≤ s.lower) (hbS : s.upper≤b)
    (C : Label→ Ideal O) (R seed : Ideal O) (hC : ∀j,Supported (C j))
    (hseed : ∀j,seed∣C j) (τ : Label→ Character) (t : Label→ℝ)
    (L : Label→ Ideal O) (H weight : Label→ℝ) (rows : Label→Finset O)
    (hH : ∀j,0<H j) (hw : ∀j,0≤weight j)
    (hrows : ∀j,∀z∈rows j,H j/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤H j) :
    (∑j∈labels,weight j*∑z∈rows j,
      ‖allocatedPolynomial (original s R seed) (C j) (L j) (τ j) (t j) (volume s) (firstSignedRow reflected z)‖^2)≤
    ∑j∈labels,weight j*((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
      ∑B : actualAllocations s.pools (C j),
        if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R (L j) B
            (τ j) (t j) CenteredMomentFirstAnnularMajorant.profile (H j)
        else 0) := by
  refine Finset.sum_le_sum fun j hj => ?_
  apply mul_le_mul_of_nonneg_left _ (hw j)
  apply (actual_signed_annular_allocated_energy reflected s R seed (C j) (L j) (hC j) (hseed j)
    (τ j) (t j) (H j) (hH j) (rows j) (hrows j)).trans
  exact common_energy_live_allocations N a b ha s hcard haS hbS (C j) R seed
    (hC j) (hseed j) (τ j) (t j) (L j) CenteredMomentFirstAnnularMajorant.profile (H j) (hH j)
    (fun _=>CenteredMomentFirstAnnularMajorant.profile_nonneg _)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
