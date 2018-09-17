Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor.

Section IdentityFunctor.
  Variable (C : BiCategory).

  Definition id_functor_d : PseudoFunctor_d C C.
  Proof.
    make_pseudo_functor ; simpl in *.
    - exact idmap.
    - exact (fun _ _ => idmap).
    - exact (fun _ _ _ _ => idmap).
    - intros X Y Z g f ; simpl.
      exact (id₂ (g · f)).
    - intros X ; simpl in *.
      exact (id₂ (id₁ X)).
    - intros X Y Z g f ; simpl in *.
      exact (id₂ (g · f)).
    - intros X ; simpl in *.
      exact (id₂ (id₁ X)).
  Defined.

  Definition id_functor_is_pseudo : is_pseudo_functor_p id_functor_d.
  Proof.
    make_is_pseudo.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f g h η₁ η₂ ; simpl in *.
      reflexivity.
    - intros X Y Z f₁ f₂ g₁ g₂ η₁ η₂ ; simpl in *.
      rewrite vcomp_left_identity, vcomp_right_identity.
      reflexivity.
    - intros X Y f ; simpl in *.
      rewrite hcomp_id₂, !vcomp_right_identity.
      reflexivity.
    - intros X Y f ; simpl in *.
      rewrite hcomp_id₂, !vcomp_right_identity.
      reflexivity.
    - intros W X Y Z h g f ; simpl in *.
      rewrite !hcomp_id₂, !vcomp_left_identity, !vcomp_right_identity.
      reflexivity.
    - intros X Y Z g f ; simpl in *.
      apply vcomp_left_identity.
    - intros X Y Z g f ; simpl in *.
      apply vcomp_left_identity.
    - intros X ; simpl in *.
      apply vcomp_left_identity.
    - intros X ; simpl in *.
      apply vcomp_left_identity.
  Qed.

  Definition lax_id_functor : LaxFunctor C C
    := Build_PseudoFunctor id_functor_d id_functor_is_pseudo.

  Global Instance lax_id_functor_pseudo
    : is_pseudo lax_id_functor
    := _.
End IdentityFunctor.