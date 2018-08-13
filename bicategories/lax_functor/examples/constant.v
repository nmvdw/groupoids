Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor.

Section ConstantFunctor.
  Context `{Funext}
          {C D : BiCategory}.
  Variable (Y : D).

  Definition constant_d
    : PseudoFunctor_d C D.
  Proof.
    make_pseudo_functor.
    - exact (fun _ => Y).
    - exact (fun _ _ _ => id₁ Y).
    - exact (fun _ _ _ _ _ => id₂ (id₁ Y)).
    - exact (fun _ _ _ _ _ => left_unit (id₁ Y)).
    - exact (fun _ => id₂ (id₁ Y)).
    - exact (fun _ _ _ _ _ => left_unit_inv (id₁ Y)).
    - exact (fun _ => id₂(id₁ Y)).
  Defined.

  Definition constant_is_pseudo
    : is_pseudo_functor_p constant_d.
  Proof.
    make_is_pseudo ; intros ; cbn.
    - reflexivity.
    - rewrite vcomp_left_identity.
      reflexivity.
    - rewrite hcomp_id₂, vcomp_right_identity, vcomp_left_identity.
      reflexivity.
    - rewrite hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
      apply left_unit_is_right_unit.
    - rewrite hcomp_id₂, vcomp_right_identity, vcomp_left_identity.
      reflexivity.
    - rewrite vcomp_left_identity.
      rewrite vcomp_assoc.
      rewrite <- triangle_r.
      rewrite left_unit_is_right_unit.
      reflexivity.
    - apply left_unit_right.
    - apply left_unit_left.
    - apply vcomp_left_identity.
    - apply vcomp_right_identity.
  Qed.

  Definition lax_constant
    : LaxFunctor C D
    := Build_PseudoFunctor constant_d constant_is_pseudo.

  Global Instance lax_ap_functor_pseudo
    : is_pseudo lax_constant
    := _.
End ConstantFunctor.