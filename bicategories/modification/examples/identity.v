Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     modification.modification.

Section IdModification.
  Context `{Univalence}
          {C D : BiCategory}
          {F G : LaxFunctor C D}.
  Variable (η : LaxTransformation F G).

  Local Notation id_modification_d
    := (fun A => id₂ (η A)).

  Definition id_modification_is_modification : is_modification id_modification_d.
  Proof.
    intros A B f.
    unfold bc_whisker_r, bc_whisker_l ; cbn.
    rewrite !hcomp_id₂.
    rewrite vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition id_modification : Modification η η
    := Build_Modification id_modification_d id_modification_is_modification.

  Definition id_modification_is_iso : iso_modification id_modification.
  Proof.
    intros X ; cbn.
    apply _.
  Qed.

  Definition id_iso_modification : IsoModification η η.
  Proof.
    make_iso_modification.
    - exact id_modification.
    - exact id_modification_is_iso.
  Defined.
End IdModification.