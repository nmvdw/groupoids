Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory.

Record is_equivalence
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
  := Build_IsEquivalence
       {
         f_inv : C⟦Y,X⟧ ;
         retr : (f · f_inv) ==> (id₁ Y) ;
         sect : (f_inv · f) ==> (id₁ X) ;
         retr_iso : IsIsomorphism retr ;
         sect_iso : IsIsomorphism sect
       }.

Arguments Build_IsEquivalence {C X Y f} f_inv retr sect {_ _}.
Arguments f_inv {C X Y} {_} _.
Arguments retr {C X Y} f {_}.
Arguments sect {C X Y} f {_}.

Global Instance retr_isisomorphism
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
       (H : is_equivalence f)
  : IsIsomorphism (retr f)
  := retr_iso _ H.

Global Instance sect_isisomorphism
       {C : BiCategory}
       {X Y : C}
       (f : C⟦X,Y⟧)
       (H : is_equivalence f)
  : IsIsomorphism (sect f)
  := sect_iso _ H.

Record equivalence
       {C : BiCategory}
       (X Y : C)
  := Build_Equivalence
       {
         equiv :> C⟦X,Y⟧ ;
         equiv_isequiv : is_equivalence equiv
       }.

Arguments Build_Equivalence {C X Y} equiv equiv_isequiv.
Arguments equiv {C X Y} _.
Arguments equiv_isequiv {C X Y} _.

Definition e_inv
           {C : BiCategory}
           {X Y : C}
           (f : equivalence X Y)
  : C⟦Y,X⟧
  := f_inv (equiv_isequiv f).

Definition id_isequiv
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : is_equivalence (id₁ X)
  := Build_IsEquivalence
       (id₁ X)
       (left_unit (id₁ X))
       (left_unit (id₁ X)).

Definition id_equiv
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : equivalence X X
  := Build_Equivalence (id₁ X) (id_isequiv X).

Definition inv_isequiv
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : equivalence X Y)
  : is_equivalence (e_inv f)
  := Build_IsEquivalence f (sect f) (retr f).

Definition inv_equiv
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : equivalence X Y)
  : equivalence Y X
  := Build_Equivalence (e_inv f) (inv_isequiv f).

Definition comp_sect
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : (e_inv f · e_inv g) · (equiv g · equiv f) ==> id₁ X.
Proof.
  refine (_ ∘ (assoc (e_inv f) (e_inv g) (equiv g · equiv f))).
  refine (sect f ∘ ((e_inv f) ▻ _)).
  refine (_ ∘ assoc_inv (e_inv g) g f).
  exact (left_unit f ∘ (sect g ◅ f)).
Defined.

Local Instance comp_sect_isiso
      `{Univalence}
      {C : BiCategory}
      {X Y Z : C}
      (g : equivalence Y Z) (f : equivalence X Y)
  : IsIsomorphism (comp_sect g f)
  := _.

Definition comp_retr
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : (equiv g · equiv f) · (e_inv f · e_inv g) ==> (id₁ Z).
Proof.
  refine (_ ∘ assoc (equiv g) (equiv f) (e_inv f · e_inv g)).
  refine (retr g ∘ (g ▻ _))%morphism.
  refine (_ ∘ assoc_inv f (e_inv f) (e_inv g)).
  refine (left_unit (e_inv g) ∘ _).
  exact (retr f ◅ e_inv g).
Defined.

Local Instance comp_retr_isiso
      `{Univalence}
      {C : BiCategory}
      {X Y Z : C}
      (g : equivalence Y Z) (f : equivalence X Y)
  : IsIsomorphism (comp_retr g f)
  := _.

Definition comp_isequiv
       `{Univalence}
       {C : BiCategory}
       {X Y Z : C}
       (g : equivalence Y Z) (f : equivalence X Y)
  : is_equivalence (equiv g · equiv f)
  := Build_IsEquivalence
       (e_inv f · e_inv g)
       (comp_retr g f)
       (comp_sect g f).

Definition comp_equiv
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : equivalence X Z
  := Build_Equivalence (equiv g · equiv f) (comp_isequiv g f).

Definition idtoequiv
           `{Univalence}
           {C : BiCategory}
           (X Y : C)
           (Heq : X = Y)
  : equivalence X Y.
Proof.
  destruct Heq.
  exact (id_equiv X).
Defined.