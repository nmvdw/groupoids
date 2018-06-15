Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory lax_functor full_sub lax_functor.examples.identity.

Definition lax_inclusion_d
           `{Univalence}
           (C : BiCategory)
           (P : C -> hProp)
  : LaxFunctor_d (full_sub C P) C.
Proof.
  simple refine {| Fobj_d := _ |}.
  - intros X.
    exact X.1.
  - intros X Y ; simpl.
    exact 1%functor.
  - intros X Y Z ; simpl.
    apply id_functor_c_m.
  - intros.
    unfold hcomp ; cbn.
    exact 1%morphism.
Defined.

Definition is_lax_inclusion
           `{Univalence}
           (C : BiCategory)
           (P : C -> hProp)
  : is_lax (lax_inclusion_d C P).
Proof.
  repeat split.
  - intros ; simpl.
    unfold hcomp.
    rewrite identity_of, !right_identity.
    reflexivity.
  - intros ; simpl.
    unfold hcomp.
    rewrite identity_of, !right_identity.
    reflexivity.
  - intros ; simpl.
    unfold hcomp.
    rewrite !identity_of, !right_identity, !left_identity.
    reflexivity.
Qed.

Definition lax_inclusion
           `{Univalence}
           (C : BiCategory)
           (P : C -> hProp)
  : LaxFunctor (full_sub C P) C
  := (lax_inclusion_d C P;is_lax_inclusion C P).

Global Instance lax_inclusion_pseudo
       `{Univalence}
       (C : BiCategory)
       (P : C -> hProp)    
  : is_pseudo_functor (lax_inclusion C P).
Proof.
  simple refine {| Fcomp_iso := _ |}.
Defined.