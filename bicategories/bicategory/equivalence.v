Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory.

Local Open Scope bicategory_scope.

Record is_equivalence
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : one_cell X Y)
  := {
      f_inv : one_cell Y X ;
      retr : two_cell (f ⋅ f_inv) (id_m Y) ;
      sect : two_cell (f_inv ⋅ f) (id_m X) ;
      retr_iso : IsIsomorphism retr ;
      sect_iso : IsIsomorphism sect
    }.

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
  := {
      equiv :> one_cell X Y ;
      equiv_isequiv : is_equivalence equiv
    }.

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
  := {| f_inv := id_m X ;
        retr := un_l X X (id_m X) ;
        sect := un_l X X (id_m X)
     |}.

Definition id_equiv
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : equivalence X X
  := {| equiv := id_m X ; equiv_isequiv := id_isequiv X|}.

Definition inv_isequiv
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (f : equivalence X Y)
  : is_equivalence (e_inv f)
  := {| f_inv := f ; retr := sect f (equiv_isequiv f) ; sect := retr f _|}.

Definition inv_equiv
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (f : equivalence X Y)
  : equivalence Y X
  := {| equiv := e_inv f ; equiv_isequiv := inv_isequiv f |}.

Definition comp_sect
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : two_cell ((e_inv f ⋅ e_inv g) ⋅ (equiv g ⋅ equiv f))%morphism (id_m X).
Proof.
  refine (_ o assoc (e_inv f,e_inv g,equiv g ⋅ equiv f))%morphism ; cbn.
  simple refine (_ o bc_whisker_r f (e_inv f) _)%morphism.
  - apply sect.
  - refine (_ o (assoc (e_inv g, equiv g, equiv f))^-1)%morphism ; simpl.
    refine (un_l _ _ _ o _)%morphism ; cbn.
    refine (bc_whisker_l f _ _) ; cbn.
    apply sect.
Defined.

Global Instance pair_equiv
       {C D : PreCategory}
       {X₁ Y₁ : C} {X₂ Y₂ : D}
       (f : morphism C X₁ Y₁) (g : morphism D X₂ Y₂)
       `{IsIsomorphism _ _ _ f} `{IsIsomorphism _ _ _ g}
  : @IsIsomorphism (Category.prod C D) (X₁,X₂) (Y₁,Y₂) (f,g)%morphism.
Proof.
  apply _.
Defined.

Local Instance comp_sect_isiso
      `{Univalence}
      {C : BiCategory}
      {X Y Z : C}
      (g : equivalence Y Z) (f : equivalence X Y)
  : IsIsomorphism (comp_sect g f).
Proof.
  unfold comp_sect.
  repeat (apply Category.isisomorphism_compose).
  - apply _.
  - unfold bc_whisker_r.
    apply Morphisms.iso_functor.
    apply iso_pair.
    + apply _.
    + repeat (apply Category.isisomorphism_compose)
      ; unfold bc_whisker_l ; apply _.
  - apply _.
Defined.

Definition comp_retr
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : two_cell ((equiv g ⋅ equiv f) ⋅ (e_inv f ⋅ e_inv g))%morphism (id_m Z).
Proof.
  refine (_ o assoc (equiv g, equiv f,e_inv f ⋅ e_inv g))%morphism ; cbn.
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
  : IsIsomorphism (comp_retr g f).
Proof.
  unfold comp_sect.
  repeat (apply Category.isisomorphism_compose).
  - apply _.
  - unfold bc_whisker_r.
    apply Morphisms.iso_functor.
    apply iso_pair.
    + apply _.
    + repeat (apply Category.isisomorphism_compose)
      ; unfold bc_whisker_l ; apply _.
  - apply _.
Defined.

Definition comp_isequiv
       `{Univalence}
       {C : BiCategory}
       {X Y Z : C}
       (g : equivalence Y Z) (f : equivalence X Y)
  : is_equivalence (equiv g ⋅ equiv f)
  := {| f_inv := e_inv f ⋅ e_inv g ; sect := comp_sect g f ; retr := comp_retr g f|}.

Definition comp_equiv
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (g : equivalence Y Z) (f : equivalence X Y)
  : equivalence X Z
  := {| equiv := equiv g ⋅ equiv f ; equiv_isequiv := comp_isequiv g f |}.

Definition idtoequiv `{Univalence} {C : BiCategory} (X Y : C) (Heq : X = Y)
  : equivalence X Y.
Proof.
  destruct Heq.
  exact (id_equiv X).
Defined.