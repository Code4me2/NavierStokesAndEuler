import Euler.ParentPacketSourceData
import Euler.PacketSourceGeometryData
import Euler.PacketActivationSourceData

/-! Changing the source normal and reference plane leaves the older
physical frame and its scalar parameters unchanged. The source strain
and time interval are the actual fields of the same parent. -/

noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set EulerSmoothLimit EulerParentPacketFrames EulerTransversePacketProvider
  EulerTransverseFrameCoordinates

variable {A : Parent} {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖=1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖=1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')

def reframe : ParentFrame (A.transverseData m' hm' R' S hS) τ where
  B := P.B
  B₁ := P.B₁
  m := P.m
  v := P.v
  c := P.c
  G := P.G
  error := P.error
  G_lower := P.G_lower
  error_nonneg := P.error_nonneg
  B_derivative := P.B_derivative
  ray_equation := P.ray_equation
  velocity_equation := P.velocity_equation
  ray_nonzero := P.ray_nonzero
  velocity_nonzero := P.velocity_nonzero
  tangent := P.tangent
  B_bound := P.B_bound
  B₁_bound := P.B₁_bound
  remainder_bound := P.remainder_bound

@[simp] theorem reframe_v : (P.reframe m' hm' R').v=P.v := rfl
@[simp] theorem reframe_sigma : (P.reframe m' hm' R').sigma=P.sigma := rfl
@[simp] theorem reframe_shear : (P.reframe m' hm' R').shear=P.shear := rfl


@[simp] theorem reframe_terminalBound (CM CH : ℝ) :
    (P.reframe m' hm' R').terminalBound CM CH=P.terminalBound CM CH := rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerTransversePacketProvider EulerTransverseFrameCoordinates

variable (A : Parent) {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m' : Space) (hm' : ‖m'‖=1) (R' : V ≃ₗᵢ[ℝ] referencePlane m')



end EulerParentPacketFrames.Parent
