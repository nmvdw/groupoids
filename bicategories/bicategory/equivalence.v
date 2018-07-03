Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory.

Local Open Scope bicategory_scope.

Record is_equivalence
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : one_cell X Y)
  := Build_IsEquivalence
       {
         f_inv : one_cell Y X ;
         retr : two_cell (f · f_inv) (id_m Y) ;
         sect : two_cell (f_inv · f) (id_m X) ;
         retr_iso : IsIsomorphism retr ;
         sect_iso : IsIsomorphism sect
       }.

Arguments Build_IsEquivalence {_ C X Y f} f_inv retr sect {_ _}.
Arguments f_inv {_ C X Y} {_} _.
Arguments retr {_ C X Y} f _.
Arguments sect {_ C X Y} f _.

Global Instance retr_isisomorphism
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : one_cell X Y)
       (H : is_equivalence f)
  : IsIsomorphism (retr f H).
Proof.
  apply retr_iso.
Defined.

Global Instance sect_isisomorphism
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : one_cell X Y)
       (H : is_equivalence f)
  : IsIsomorphism (sect f H).
Proof.
  apply sect_iso.
Defined.

Record equivalence
       `{Univalence}
       {C : BiCategory}
       (X Y : C)
  := Build_Equivalence
       {
         equiv :> one_cell X Y ;
         equiv_isequiv : is_equivalence equiv
       }.

Arguments Build_Equivalence {_ C X Y} equiv equiv_isequiv.
Arguments equiv {_ C X Y} _.
Arguments equiv_isequiv {_ C X Y} _.

Definition e_inv
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : equivalence X Y)
  : one_cell Y X
  := f_inv (equiv_isequiv f).

Definition id_isequiv
       `{Univalence}
       {C : BiCategory}
       (X : C)
  : is_equivalence (id_m X)
  := Build_IsEquivalence
       (id_m X)
       (un_l X X (id_m X))
       (un_l X X (id_m X)).

Definition id_equiv
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : equivalence X X
  := Build_Equivalence (id_m X) (id_isequiv X).

Definition inv_isequiv
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : equivalence X Y)
  : is_equivalence (e_inv f)
  := Build_IsEquivalence
       f
       (sect f _)
       (retr f _).

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
  : two_cell ((e_inv f · e_inv g) · (equiv g · equiv f))%morphism (id_m X).
Proof.
  refine (_ o assoc (e_inv f,e_inv g,equiv g · equiv f))%morphism ; cbn.
  simple refine (_ o bc_whisker_r f (e_inv f) _)%morphism.
  - apply sect.
  - refine (_ o (assoc (e_inv g, equiv g, equiv f))^-1)%morphism ; simpl.
    refine (un_l _ _ _ o _)%morphism ; cbn.
    refine (bc_whisker_l f _ _) ; cbn.
    apply sect.
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
  : two_cell ((equiv g · equiv f) · (e_inv f · e_inv g))%morphism (id_m Z).
Proof.
  refine (_ o assoc (equiv g, equiv f,e_inv f · e_inv g))%morphism ; cbn.
  simple refine (_ o bc_whisker_r (e_inv g) g _)%morphism.
  - apply retr.
  - refine (_ o (assoc (equiv f,e_inv f,e_inv g))^-1)%morphism ; simpl.
    refine (un_l _ _ _ o _)%morphism.
    refine (bc_whisker_l (e_inv g) _ _) ; cbn.
    apply retr.
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