/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The weighted divisor fibre on the genuine colored carrier. Adapted from
Sil ConcreteLabelAssembly8, without any S0 coefficient equivalence. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerActual
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabelAssembly11
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.ColoredFrameAdmissible
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L:ℝ} {θ:GData L} {mesh Z:ℝ}

abbrev coloredCarrier (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a) (ω₁ ω₂:Character) :=
  RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)

/-- Each genuine cube-free colored column divides the square of its actual
second twist. This is independent of regular/fixed class cancellation. -/
theorem column_dvd_twist_sq (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a) (ω₁ ω₂:Character)
    (g:Lab (coloredCarrier s ha ω₁ ω₂)→Id) (hg:IsColumn (coloredCarrier s ha ω₁ ω₂) g) :
    ∀l,g l∣(Ideal.span {lA (coloredCarrier s ha ω₁ ω₂) l})^2 := by
  intro l
  have hcf:=QRH.Cycle092.ColoredGaussFrameProvider.lab_cubeFree ω₁ ω₂ s ha l
  have hc:∀P,leftExponent l.1.val.1 l.1.val.2 P≤ 2 ∧ rightExponent l.1.val.1 l.1.val.2 P≤ 2:=by
    intro P
    have h:=hcf P
    omega
  rcases hg l with h|h <;> rw [h]
  · exact left_dvd_twist_sq _ _ (lab_data _ l).1 (lab_data _ l).2.2 l.2 (fun P=>(hc P).1)
  · exact right_dvd_twist_sq _ _ (lab_data _ l).1 (lab_data _ l).2.1 (lab_data _ l).2.2 l.2 (fun P=>(hc P).2)

/-- Genuine image labels retain a two-divisor encoding (column, twist ideal)
plus the inverse-norm second divisor. The row y is the original packed row. -/
theorem image_fibre (η:Character) (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a)
    (ω₁ ω₂:Character) (rs:GSrc θ mesh Z) (j₀:DictIdx) (ξ:RayCharacter)
    (g:Lab (coloredCarrier s ha ω₁ ω₂)→Id) (hg:IsColumn (coloredCarrier s ha ω₁ ω₂) g)
    (n:Fin 4→ℤ) (χ:RayCharacter)
    (Ks:Finset (Σ _:Lab (coloredCarrier s ha ω₁ ω₂),Id))
    (hfits:∀x∈Ks.image (fun k=>(frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η),Fits η rs x)
    (Cexp ε:ℝ) (hfib:FibreAt Z Cexp θ.Bmask ε 2) :
    ∀y:O,y≠0 → ((Ideal.span {y}).absNorm:ℝ)≤ Z^Cexp →
      ∑x∈(Ks.image (fun k=>(frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)).filter
        (fun x=>x.twist∣y),gWeight x≤ Z^(ε/8) := by
  have hgdvd:=column_dvd_twist_sq s ha ω₁ ω₂ g hg
  apply hfib L θ mesh _ (fun x=>![x.G,Ideal.span {x.twist}])
  · intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    show ‖(1:ℂ)‖≤ 1
    rw [norm_one]
  · intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact hgdvd k.1
  · intro x hx
    exact ⟨(hfits x hx).D_sq.ne_zero,(hfits x hx).D_cap⟩
  · intro x hx i
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    fin_cases i
    · exact hgdvd k.1
    · exact dvd_pow_self _ two_ne_zero
  · intro x hx x' hx' h
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨k',_,rfl⟩:=Finset.mem_image.mp hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc,hD⟩:=h
    have hG:g k.1=g k'.1:=congrFun hc 0
    have hsp:Ideal.span {lA (coloredCarrier s ha ω₁ ω₂) k.1}=Ideal.span {lA (coloredCarrier s ha ω₁ ω₂) k'.1}:=congrFun hc 1
    have hA:=spanInj_holds (coloredCarrier s ha ω₁ ω₂) k.1 k'.1 hsp
    show (frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η=
      (frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k').toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η
    rw [frameData_eq j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k k' hG hA hD]

/-- The exact native dyad raising identity holds on either true class image. -/
theorem image_raised (η:Character) (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a)
    (ω₁ ω₂:Character) (rs:GSrc θ mesh Z) (j₀:DictIdx) (ξ:RayCharacter)
    (g:Lab (coloredCarrier s ha ω₁ ω₂)→Id) (n:Fin 4→ℤ) (χ:RayCharacter)
    (Ks:Finset (Σ _:Lab (coloredCarrier s ha ω₁ ω₂),Id)) :
    Ks.image (fun k=>(frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)=
      (Ks.image (fun k=>setN ((frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η) n)).image (raised rs) := by
  rw [Finset.image_image]
  rfl

/-- Source-only raised envelope, nonnegative true inverse-norm weights and the
proved original-row fibre establish every AdmissibleGroup clause. -/
theorem image_admissible (η:Character) (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a)
    (ω₁ ω₂:Character) (rs:GSrc θ mesh Z) (j₀:DictIdx) (ξ:RayCharacter)
    (g:Lab (coloredCarrier s ha ω₁ ω₂)→Id) (hg:IsColumn (coloredCarrier s ha ω₁ ω₂) g)
    (n:Fin 4→ℤ) (χ:RayCharacter)
    (Ks:Finset (Σ _:Lab (coloredCarrier s ha ω₁ ω₂),Id))
    (hfits:∀x∈Ks.image (fun k=>(frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η),Fits η rs x)
    (Mmin Mmax ε:ℝ) (hH:Mmin≤ commonH rs ∧ commonH rs≤ Mmax)
    (hlog:Real.logb Z 2≤ mesh) (hfib:FibreAt Z (Mmax+2) θ.Bmask ε 2) :
    QRH.SilDensitySplit.CubeFree.Second.AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε Z rs
      (Ks.image (fun k=>(frameData j₀ ξ s rs (coloredCarrier s ha ω₁ ω₂) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)) (commonH rs) := by
  rw [image_raised η s ha ω₁ ω₂ rs j₀ ξ g n χ Ks]
  apply raised_admissible η Mmin Mmax ε rs _ _ hlog hH
  · rw [←image_raised η s ha ω₁ ω₂ rs j₀ ξ g n χ Ks]
    exact image_fibre η s ha ω₁ ω₂ rs j₀ ξ g hg n χ Ks hfits (Mmax+2) ε hfib
  · intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact lA_ne _ k.1

end
end QRH.Cycle092.ColoredFrameAdmissible
#print axioms QRH.Cycle092.ColoredFrameAdmissible.image_admissible
