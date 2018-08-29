Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory.

Record is_equivalence
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
  := Build_IsEquivalence
       {
         equiv_inv : C⟦Y,X⟧ ;
         retr : (f · equiv_inv) ==> (id₁ Y) ;
         sect : (equiv_inv · f) ==> (id₁ X) ;
         retr_iso : IsIsomorphism retr ;
         sect_iso : IsIsomorphism sect
       }.

Arguments Build_IsEquivalence {C X Y f} equiv_inv retr sect {_ _}.
Arguments equiv_inv {C X Y} {_} _.
Arguments retr {C X Y} _ _.
Arguments sect {C X Y} _ _.

Global Instance retr_isisomorphism
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
       (H : is_equivalence f)
  : IsIsomorphism (retr f H)
  := retr_iso _ H.

Global Instance sect_isisomorphism
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
       (H : is_equivalence f)
  : IsIsomorphism (sect f H)
  := sect_iso _ H.

Record equivalence
       {C : BiCategory}
       (X Y : C)
  := Build_Equivalence
       {
         equiv_morph :> C⟦X,Y⟧ ;
         equiv_isequiv : is_equivalence equiv_morph
       }.

Arguments Build_Equivalence {C X Y} equiv_morph equiv_isequiv.
Arguments equiv_morph {C X Y} _.
Arguments equiv_isequiv {C X Y} _.

Ltac make_equivalence := simple refine (Build_Equivalence _ _).

Definition equivalence_inv
           {C : BiCategory}
           {X Y : C}
           (f : equivalence X Y)
  : equivalence Y X.
Proof.
  make_equivalence.
  - exact (equiv_inv (equiv_isequiv f)).
  - simple refine (Build_IsEquivalence _ _ _).
Defined.

Definition id_isequiv
           {C : BiCategory}
           (X : C)
  : is_equivalence (id₁ X)
  := Build_IsEquivalence
       (id₁ X)
       (left_unit (id₁ X))
       (left_unit (id₁ X)).

Definition id_equiv
           {C : BiCategory}
           (X : C)
  : equivalence X X
  := Build_Equivalence (id₁ X) (id_isequiv X).

Definition comp_sect
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : (equivalence_inv f · equivalence_inv g) · (g · f) ==> id₁ X.
Proof.
  refine (_ ∘ (assoc _ _ (g · f))).
  refine (sect f _ ∘ (_ ◅ _)).
  refine (_ ∘ assoc_inv _ g f).
  exact (left_unit f ∘ (sect g _ ▻ f)).
Defined.

Local Instance comp_sect_isiso
      {C : BiCategory}
      {X Y Z : C}
      (g : equivalence Y Z) (f : equivalence X Y)
  : IsIsomorphism (comp_sect g f)
  := _.

Definition comp_retr
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : (g · f) · (equivalence_inv f · equivalence_inv g) ==> (id₁ Z).
Proof.
  refine (_ ∘ assoc g f _).
  refine (retr g _ ∘ (g ◅ _)).
  refine (_ ∘ assoc_inv f _ _).
  refine (left_unit _ ∘ _).
  exact (retr f _ ▻ _).
Defined.

Local Instance comp_retr_isiso
      {C : BiCategory}
      {X Y Z : C}
      (g : equivalence Y Z) (f : equivalence X Y)
  : IsIsomorphism (comp_retr g f)
  := _.

Definition comp_isequiv
       {C : BiCategory}
       {X Y Z : C}
       (g : equivalence Y Z) (f : equivalence X Y)
  : is_equivalence (g · f)
  := Build_IsEquivalence
       (equivalence_inv f · equivalence_inv g)
       (comp_retr g f)
       (comp_sect g f).

Definition comp_equiv
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : equivalence X Z
  := Build_Equivalence (g · f) (comp_isequiv g f).

Definition idtoequiv
           {C : BiCategory}
           (X Y : C)
           (Heq : X = Y)
  : equivalence X Y.
Proof.
  destruct Heq.
  exact (id_equiv X).
Defined.
