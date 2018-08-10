Require Import HoTT.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** ** Some equational theory for groupoids *)
(** [e⁻¹ = e] *)
Definition inv_e
           {G : groupoid}
           (a : G)
  : inv (e a) = e a
  := (grpd_left_identity (inv (e a)))^ @ grpd_right_inverse (e a).

(** [(g⁻¹)⁻¹ = g] *)
Definition inv_involutive
           {G : groupoid}
           {a₁ a₂ : G}
           (g : G a₁ a₂)
  : inv (inv g) = g.
Proof.
  refine ((grpd_right_identity (inv (inv g)))^ @ _).
  refine (ap (fun p => _ ● p) (grpd_left_inverse g)^ @ _).
  refine (grpd_right_assoc _ _ _ @ _).
  refine (ap (fun p => p ● _) (grpd_left_inverse _) @ _).
  apply grpd_left_identity.
Defined.

(** [(g h)⁻¹ = h⁻¹ g ⁻¹] *)
Definition inv_prod
           {G : groupoid}
           {a₁ a₂ a₃ : G}
           (g₁ : G a₁ a₂)
           (g₂ : G a₂ a₃)
  : inv (g₁ ● g₂) = inv g₂ ● inv g₁.
Proof.
  refine (_ @ (grpd_right_identity (inv g₂ ● inv g₁))).
  refine (_ @ ap (fun p => _ ● p) (grpd_right_inverse (g₁ ● g₂))).
  refine (_ @ grpd_left_assoc _ _ _).
  refine (_ @ ap (fun p => p ● _) (grpd_right_assoc (inv g₂ ● inv g₁) g₁ g₂)^).
  refine (_ @ ap (fun p => (p ● _) ● _) (grpd_right_assoc (inv g₂) (inv g₁) g₁)).
  refine (_ @ (ap (fun p => ((_ ● p) ● _) ● _) (grpd_left_inverse _))^).
  refine (_ @ (ap (fun p => (p ● _) ● _) (grpd_right_identity _))^).
  refine (_ @ (ap (fun p => p ● _) (grpd_left_inverse _))^).
  exact (grpd_left_identity _)^.
Defined.