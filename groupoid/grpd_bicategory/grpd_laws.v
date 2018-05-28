Require Import HoTT.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** ** Some equational theory for groupoids *)
(** [e⁻¹ = e] *)
Definition inv_e
           {G : groupoid}
           (a : under G)
  : inv (@e G a) = e a
  := (ce _)^ @ ic (e a).

(** [(g⁻¹)⁻¹ = g] *)
Definition inv_involutive
           {G : groupoid}
           {a₁ a₂ : under G}
           (g : hom G a₁ a₂)
  : inv (inv g) = g.
Proof.
  refine ((ce (inv (inv g)))^ @ _).
  refine (ap (fun p => _ · p) (ic g)^ @ _).
  refine (car _ _ _ @ _).
  refine (ap (fun p => p · _) (ic _) @ _).
  apply ec.
Defined.

(** [(g h)⁻¹ = h⁻¹ g ⁻¹] *)
Definition inv_prod
           {G : groupoid}
           {a₁ a₂ a₃ : under G}
           (g₁ : hom G a₁ a₂)
           (g₂ : hom G a₂ a₃)
  : inv (g₁ · g₂) = inv g₂ · inv g₁.
Proof.
  refine (_ @ (ce (inv g₂ · inv g₁))).
  refine (_ @ ap (fun p => _ · p) (ci (g₁ · g₂))).
  refine (_ @ cal _ _ _).
  refine (_ @ ap (fun p => p · _) (car (inv g₂ · inv g₁) g₁ g₂)^).
  refine (_ @ ap (fun p => (p · _) · _) (car (inv g₂) (inv g₁) g₁)).
  refine (_ @ (ap (fun p => ((_ · p) · _) · _) (ic _))^).
  refine (_ @ (ap (fun p => (p · _) · _) (ce _))^).
  refine (_ @ (ap (fun p => p · _) (ic _))^).
  exact (ec _)^.
Defined.