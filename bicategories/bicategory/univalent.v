Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint.

Definition locally_univalent (C : BiCategory)
  : Type
  := forall (X Y : C), IsCategory (C⟦X,Y⟧).

Definition univalent_0 `{Funext} (C : BiCategory)
  : Type
  := forall (X Y : C), IsEquiv(id_to_adjequiv X Y).

Definition univalent `{Funext} (C : BiCategory)
  := (locally_univalent C * univalent_0 C)%type.

Global Instance univalent_hprop `{Funext} (C : BiCategory)
  : IsHProp (univalent C)
  := _.

Global Instance hom_locally_univalent_cat
       `{Univalence}
       {C : BiCategory}
       (UC : locally_univalent C)
       (X Y : C)
  : IsTrunc 1 (C⟦X,Y⟧).
Proof.
  unfold locally_univalent in UC.
  apply _.
Defined.

Global Instance sigma_trunc
       {X : Type}
       (P : X -> Type)
       (n : trunc_index)       
       `{forall (x : X), IsTrunc (trunc_S n) (P x)}
       `{IsTrunc (trunc_S n) X}
  : IsTrunc (trunc_S n) {x : X & P x}
  := _.

Global Instance obj_univalent_cat
       `{Univalence}
       (C : BiCategory)
       (UC : univalent C)
  : IsTrunc 2 C.
Proof.
  intros X Y.
  destruct UC as [LC UC].
  specialize (UC X Y).
  rewrite (path_universe (id_to_adjequiv X Y)).
  apply sigma_trunc.
  - intros.
    apply sigma_trunc.
    + apply _.
    + apply sigma_trunc.
      * apply _.
      * apply sigma_trunc.
        ** apply _.
        ** apply hom_locally_univalent_cat ; assumption.
  - apply hom_locally_univalent_cat ; assumption.
Defined.