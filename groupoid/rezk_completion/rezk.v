(** This file defines a groupoid quotient HIT and derives some recursion/induction principles for it. *)
Require Import HoTT.
Require Import Category.
From GR Require Import
     general.
From GR.basics Require Export
     globe_over path_over square.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** * The groupoid quotient over a type. *)
(** Given a type [A] and a groupoid [G], we construct a type [gquot G] such that
    we have [A -> gquot A G] and the equality of [gquot A G] is described by [G].
    We use the standard method to define the HIT
    <<
    HIT gquot G :=
     | gcl : A -> gquot G
     | gcleq : Π(a₁ a₂ : A), hom G a₁ a₂ -> gcl a₁ = gcl a₂
     | ge : Π(a : A), gcleq (e a) = idpath
     | ginv : Π(a₁ a₂ : A) (g : hom G a₁ a₂), gcleq g⁻¹ = (gcleq g)^
     | gconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
               gcleq (g₁ × g₂) = gcleq g₁ @ gcleq g₂
     | gtrunc : Is-1-Type (gquot G)
    >>
*)
Module Export rezk.
  Local Open Scope category.
  
  Private Inductive rezk (C : PreCategory) :=
  | rcl : C -> rezk C.

  Axiom rcleq
    : forall (C : PreCategory) {x y : C} (g : x <~=~> y),
      rcl C x = rcl C y.

  Axiom re
    : forall (C : PreCategory) (x : C),
      rcleq C (isomorphic_refl C x) = idpath.

  Axiom rconcat
    : forall (C : PreCategory)
             {x y z : C}
             (g : y <~=~> z) (f : x <~=~> y),
      rcleq C (isomorphic_trans f g) = rcleq C f @ rcleq C g.
  
  Axiom rtrunc
    : forall (C : PreCategory), IsTrunc 1 (rezk C).

  Instance gquot_istrunct (C : PreCategory) : IsTrunc 1 (rezk C).
  Proof.
    apply rtrunc.
  Defined.

  Section rezk_ind.
    Variable (C : PreCategory)
             (Y : rezk C -> Type)
             (rclY : forall (x : C), Y(rcl C x))
             (rcleqY : forall (x y : C) (f : x <~=~> y),
                 path_over Y (rcleq C f) (rclY x) (rclY y))
             (reY : forall (x : C), globe_over Y
                                               (path_to_globe (re C x))
                                               (rcleqY x x (isomorphic_refl C x))
                                               (path_over_id (rclY x)))
             (rconcatY : forall (x y z : C)
                                (g : y <~=~> z) (f : x <~=~> y),
                 globe_over Y
                            (path_to_globe (rconcat C g f))
                            (rcleqY x z (isomorphic_trans f g))
                            (path_over_concat (rcleqY x y f)
                                              (rcleqY y z g)))
             (truncY : forall (x : rezk C), IsTrunc 1 (Y x)).

    Fixpoint rezk_ind (x : rezk C) : Y x
      := (match x with
         | rcl a => fun _ _ _ _ => rclY a
          end) rcleqY reY rconcatY truncY.

    Axiom rezk_ind_beta_rcleq : forall {x y : C} (f : x <~=~> y),
        apd_po rezk_ind (rcleq C f)
        =
        rcleqY x y f.
  End rezk_ind.
End rezk.

Arguments rezk_ind {C} Y rclY rcleqY reY rconcatY truncY.