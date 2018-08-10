Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory.

Definition locally_univalent (C : BiCategory)
  : Type
  := forall (X Y : C), IsCategory (C⟦X,Y⟧).

Global Instance locally_univalent_hprop `{Univalence} (C : BiCategory)
  : IsHProp (locally_univalent C)
  := _.