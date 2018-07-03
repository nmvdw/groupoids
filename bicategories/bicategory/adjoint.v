Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.bicategory_laws
     equivalence.

Local Open Scope bicategory_scope.

Record adjunction_d
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (l : one_cell X Y)
       (r : one_cell Y X)
  := Build_Adjunction_d
       {
         unit_d : two_cell (id_m X) (c_m (r,l)) ;
         counit_d : two_cell (c_m (l,r)) (id_m Y)
       }.

Arguments unit_d {_ C X Y l r}.
Arguments counit_d {_ C X Y l r}.

Definition is_adjunction
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction_d l r)
  : Type
  := ((((un_r _ _ r)
          o (((bc_whisker_r (id_m Y) r (counit_d A))
                o (assoc (r,l,r)))
               o (bc_whisker_l r (r · l) (unit_d A)))
          o ((un_l Y X r)^-1))
       = 1)
      *
      (((un_l _ _ l)
                         o (((bc_whisker_l l _ (counit_d A))
                         o ((assoc (l,r,l))^-1))
                         o (bc_whisker_r _ l (unit_d A)))
                         o (un_r X Y l)^-1)
                      = 1                         
      ))%morphism.

Definition is_hprop_is_adjunction
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction_d l r)
  : IsHProp (is_adjunction A)
  := _.

Definition adjunction
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           (l : one_cell X Y) (r : one_cell Y X)
  := {A : adjunction_d l r & is_adjunction A}.

Definition Build_Adjunction
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction_d l r)
           (pA : is_adjunction A)
  := (A;pA).

Definition unit
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction l r)
  : two_cell (id_m X) (c_m (r,l))
  := unit_d A.1.

Definition counit
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction l r)
  : two_cell (c_m (l,r)) (id_m Y)
  := counit_d A.1.

Definition unit_counit_l
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction l r)
  : (((un_r _ _ r)
        o (((bc_whisker_r (id_m Y) r (counit A))
              o (assoc (r,l,r)))
             o (bc_whisker_l r (r · l) (unit A)))
        o ((un_l Y X r)^-1))
     = 1)%morphism
  := Datatypes.fst A.2.

Definition unit_counit_r
           `{Univalence}
           {C : BiCategory}
           {X Y : C}
           {l : one_cell X Y} {r : one_cell Y X}
           (A : adjunction l r)
  : (((un_l _ _ l)
        o (((bc_whisker_l l _ (counit A))
              o ((assoc (l,r,l))^-1))
             o (bc_whisker_r _ l (unit A)))
        o (un_r X Y l)^-1)
     = 1                         
    )%morphism
  := Datatypes.snd A.2.

Definition id_adjunction
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : adjunction (id_m X) (id_m X).
Proof.
  simple refine (Build_Adjunction _ _).
  - simple refine {|unit_d := _|}.
    + exact (@morphism_inverse (_ -> _) _ _ (un_l X X) _ (id_m X)).
    + exact (un_l X X (id_m X)).
  - split ; simpl.
    + unfold bc_whisker_r, bc_whisker_l.
      rewrite <- triangle_r.
      rewrite <- composition_of ; simpl.
      rewrite left_identity.
      rewrite !un_l_is_un_r.
      pose (@right_inverse (_ -> _) _ _ (un_l X X) _) as p.
      pose (equiv_path_natural_transformation _ _ p (id_m X)) as q.
      cbn in q.
      rewrite q.
      rewrite identity_of, right_identity.
      rewrite q.
      reflexivity.
    + unfold bc_whisker_r, bc_whisker_l.
      rewrite <- !un_l_is_un_r.
      rewrite triangle_l.
      rewrite <- composition_of ; simpl.
      rewrite left_identity.
      rewrite !un_l_is_un_r, inv_un_l_is_inv_un_r.
      pose (@right_inverse (_ -> _) _ _ (un_l X X) _) as p.
      pose (equiv_path_natural_transformation _ _ p (id_m X)) as q.
      cbn in q.
      rewrite q.
      rewrite identity_of, right_identity.
      rewrite q.
      reflexivity.
Defined.

(*
Definition comp_adjunction
           `{Univalence}
           {C : BiCategory}
           {X Y Z : C}
           (l₁ : one_cell X Y) (r₁ : one_cell Y X)
           (l₂ : one_cell Y Z) (r₂ : one_cell Z Y)
           (A₁ : adjunction l₁ r₁)
           (A₂ : adjunction l₂ r₂)
  : adjunction (c_m (l₂,l₁)) (c_m (r₁,r₂)).
Proof.
  simple refine (_;_).
  - simple refine {|unit_d := _|}.
    + pose (unit A₁).
      pose (unit A₂).
      refine (_ o t)%morphism.
      refine (_ o bc_whisker_l _ _ _)%morphism.
      cbn.
*)