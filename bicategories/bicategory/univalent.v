Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint.

Class LocallyUnivalent (C : BiCategory)
  := locally_univalent :> forall (X Y : C), IsCategory (C⟦X,Y⟧).

Global Instance ishprop_LocallyUnivalent `{Funext} (C : BiCategory)
  : IsHProp (LocallyUnivalent C).
Proof.
  unfold LocallyUnivalent.
  apply _.
Defined.

Class Univalent_0 `{Funext} (C : BiCategory)
  := univalent_0 :> forall (X Y : C), IsEquiv(id_to_adjequiv X Y).

Global Instance ishprop_Univalent_0 `{Funext} (C : BiCategory)
  : IsHProp (Univalent_0 C).
Proof.
  unfold Univalent_0.
  apply _.
Defined.

Class Univalent `{Funext} (C : BiCategory)
  := { Univalent_Univalent_0 :> Univalent_0 C;
       Univalent_LocallyUnivalent :> LocallyUnivalent C }.

Global Instance univalent_hprop `{Funext} (C : BiCategory)
  : IsHProp (Univalent C).
Proof.
  apply hprop_allpath.
  intros x y.
  destruct x as [x1 x2], y as [y1 y2].
  assert (x1 = y1) as ->.
  { apply path_ishprop. }
  assert (x2 = y2) as ->.
  { apply path_ishprop. }
  reflexivity.
Defined.

Global Instance hom_locally_univalent_cat
       `{Univalence}
       {C : BiCategory}
       {UC : LocallyUnivalent C}
       (X Y : C)
  : IsTrunc 1 (C⟦X,Y⟧)
  := _.

Global Instance obj_univalent_cat
       `{Univalence}
       (C : BiCategory)
       `{Univalent C}
  : IsTrunc 2 C.
Proof.
  intros X Y.
  rewrite (path_universe (id_to_adjequiv X Y)).
  apply _.
Defined.
