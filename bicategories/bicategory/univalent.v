Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint.

Definition locally_univalent (C : BiCategory)
  : Type
  := forall (X Y : C), IsCategory (C⟦X,Y⟧).

Definition univalent_0 `{Univalence} (C : BiCategory)
  : Type
  := forall (X Y : C), IsEquiv(id_to_adjequiv X Y).

Definition univalent `{Univalence} (C : BiCategory)
  := (locally_univalent C * univalent_0 C)%type.

Global Instance univalent_hprop `{Univalence} (C : BiCategory)
  : IsHProp (univalent C)
  := _.