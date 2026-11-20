/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Specialize Sil's second-scale cutoff comparison to a real colored active
source, including the max-one guard and the actual normalized frame volume. -/
import Candidate.C092.transport.FirstGroupWindow
import Submissions.sil_density_split_20261026.CubeFree.FP.RepairedRemainderGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentActiveSource CenteredMomentSourceMass CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree FP MixedInnerExceptionalBlock MixedPrincipalPair
open MixedPrincipalWindow MixedOriginalNormCap ConcretePrimeRowBridge
open Packet.Grouped Second.ConcreteGroup
open QRH.Record1252270103KernelMass QRH.Cycle092
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O

theorem nonempty_sharp {ι:Type} [Fintype ι] {a b:ℝ} (s : Source ι a b) (ha : 0<a) (ω₁ ω₂:Id→ℂ)
    (h : (RootColoredSeed.active s ha ω₁ ω₂).Nonempty) :
    1  ≤  sourceNormCap s.P b s.T s.d := by
  obtain ⟨I,hI⟩:=h
  unfold RootColoredSeed.active at hI
  rw [mem_activeSource] at hI
  have hc:=TwistedRawSource.sourceColumn_cap s ha ω₁ ω₂ 1 I hI.2
  exact (show (1:ℝ) ≤ I.absNorm by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hc.1)).trans hc.2

theorem frequency_cutoff {ι:Type} [Fintype ι] {a b L mesh Z:ℝ} {θ:GData L}
    (rs:GSrc θ mesh Z) (s:Source ι a b) (ha:0<a) (ω₁ ω₂:Id→ℂ)
    (active : (RootColoredSeed.active s ha ω₁ ω₂).Nonempty)
    (K ξ:ℝ) (hK:0<K) (hk:rs.kLog=Real.logb Z K)
    (hvol:rs.vol=sourceVolume s/pairNorm s.d)
    (hpay:32*(b^2*(2:ℝ)^Fintype.card ι)^2*Z^(ξ/2)  ≤  Z^mesh) :
    32*frequencyRadius ((RawSides.residualCapQ s)^2/K) Z ξ  ≤  Z^(cutoffLog rs) := by
  have hZ:=rs.hZ
  have h0:=zero_lt_one.trans hZ
  have hpos:=rs.vol_pos h0
  have hcut:Z^(cutoffLog rs)=rs.vol^2/K*Z^mesh := by
    unfold cutoffLog GSrc.colLog
    rw [hk,Real.rpow_add h0,Real.rpow_sub h0,mul_comm (2:ℝ),Real.rpow_mul h0.le,
      Real.rpow_logb h0 hZ.ne' hpos,Real.rpow_two,Real.rpow_logb h0 hZ.ne' hK]
  rw [hcut]
  unfold frequencyRadius RawSides.residualCapQ
  rw [max_eq_right (nonempty_sharp s ha ω₁ ω₂ active),RepairedRemainderGeometry.sharp_support_factored,←hvol]
  have h':=mul_le_mul_of_nonneg_right hpay (by positivity : 0 ≤ rs.vol^2/K)
  convert h' using 1 <;> ring

theorem frequency_fee (N:ℕ) (b ξ mesh:ℝ) (hsep:ξ/2 < mesh) :
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀ j ≤ N,32*(b^2*(2:ℝ)^j)^2*Z^(ξ/2)  ≤  Z^mesh := by
  filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_rpow_atTop (sub_pos.mpr hsep)).eventually_ge_atTop
    (32*(b^2*(2:ℝ)^N)^2)] with Z hz hZ
  refine ⟨hz,?_⟩;intro j hj
  have hb:32*(b^2*(2:ℝ)^j)^2  ≤  32*(b^2*(2:ℝ)^N)^2 := by gcongr <;> norm_num
  have he:Z^mesh=Z^(mesh-ξ/2)*Z^(ξ/2):=by rw [←Real.rpow_add (zero_lt_one.trans hz)];ring_nf
  rw [he];exact mul_le_mul_of_nonneg_right (hb.trans hZ) (Real.rpow_nonneg (zero_lt_one.trans hz).le _)

#print axioms frequency_cutoff
#print axioms frequency_fee
end QRH.Cycle092.FixedFramePacking
