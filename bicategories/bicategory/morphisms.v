(** Morphisms INSIDE a bicategory *)
Require Import HoTT.
From GR.bicategories Require Import bicategory.bicategory.

Class IsEquivalence `{Univalence} {B : BiCategory} {X Y : B} (f : Hom B X Y) :=
  {
    morphism_inverse : Hom B Y X;
    left_inverse : Isomorphic (morphism_inverse ⋅ f)%bicategory (id_m _);
    right_inverse : Isomorphic (f ⋅ morphism_inverse)%bicategory (id_m _);
  }.

Local Notation "m ^-1" := (morphism_inverse m) : bicategory.

Class Equivalent `{Univalence} {B : BiCategory} (X Y : B) :=
  {
    morphism_equivalent :> Hom B X Y;
    isequivalence_equivalent :> IsEquivalence morphism_equivalent
  }.

Section Equivalent.
  Context `{Univalence}.
  Local Open Scope bicategory_scope.
  Variable B : BiCategory.

  Global Instance isequivalence_identity (X : B) : IsEquivalence (id_m X).
  Proof.
    simple refine {| morphism_inverse := id_m X |}.
    - simple refine {| Category.morphism_isomorphic := (un_l X X (id_m X)) |}.
    - simple refine {| Category.morphism_isomorphic := (un_l X X (id_m X)) |}.
  Defined.

  Definition idtoequiv (X Y : B) (Heq : X = Y) : Equivalent X Y.
  Proof.
    destruct Heq.
    simple refine {| morphism_equivalent := id_m X |}.
  Defined.

End Equivalent.

