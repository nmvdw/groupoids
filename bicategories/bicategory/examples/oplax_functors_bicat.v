Require Import HoTT.
From GR Require Import
     bicategories.bicategory.bicategory
     bicategories.bicategory.examples.lax_functors_bicat
     bicategories.bicategory.examples.opposite_2.

Definition OpLax `{Univalence} (C D : BiCategory) := Lax (op2 C) (op2 D).