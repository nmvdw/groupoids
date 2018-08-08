Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.bicategory_laws
     equivalence.

Record adjunction_d
       {C : BiCategory}
       {X Y : C}
       (l : C⟦X,Y⟧)
       (r : C⟦Y,X⟧)
  := Build_Adjunction_d
       {
         unit_d : id₁ X ==> r · l ;
         counit_d : l · r ==> id₁ Y
       }.

Arguments Build_Adjunction_d {C X Y l r} _ _.
Arguments unit_d {C X Y l r}.
Arguments counit_d {C X Y l r}.

Definition is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction_d l r)
  : Type
  := Datatypes.prod
       (((right_unit r)
          ∘ (r ▻ counit_d A)
          ∘ (assoc r l r)
          ∘ (unit_d A ◅ r)
          ∘ (left_unit_inv r))
        = id₂ r)
       (((left_unit l)
           ∘ (counit_d A ◅ l)
           ∘ assoc_inv l r l
           ∘ (l ▻ unit_d A)
          ∘ right_unit_inv l)
        = id₂ l).

Definition is_hprop_is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction_d l r)
  : IsHProp (is_adjunction A)
  := _.

Definition adjunction
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧) (r : C⟦Y,X⟧)
  := {A : adjunction_d l r & is_adjunction A}.

Definition Build_Adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction_d l r)
           (pA : is_adjunction A)
  := (A;pA).

Definition unit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction l r)
  : id₁ X ==> r · l
  := unit_d A.1.

Definition counit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction l r)
  : l · r ==> id₁ Y
  := counit_d A.1.

Definition unit_counit_l
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction l r)
  : ((right_unit r)
       ∘ (r ▻ counit A)
       ∘ (assoc r l r)
       ∘ (unit A ◅ r)
       ∘ (left_unit_inv r))
    = id₂ r
  := Datatypes.fst A.2.

Definition unit_counit_r
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧} {r : C⟦Y,X⟧}
           (A : adjunction l r)
  : ((left_unit l)
       ∘ (counit A ◅ l)
       ∘ assoc_inv l r l
       ∘ (l ▻ unit A)
       ∘ right_unit_inv l)
    = id₂ l
  := Datatypes.snd A.2.

Definition id_adjunction_d
           {C : BiCategory}
           (X : C)
  : adjunction_d (id₁ X) (id₁ X).
Proof.
  simple refine (Build_Adjunction_d _ _).
  - exact (left_unit_inv (id₁ X)).
  - exact (left_unit (id₁ X)).
Defined.

Definition id_is_adjunction
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : is_adjunction (id_adjunction_d X).
Proof.
  split ; simpl.
  - unfold bc_whisker_r, bc_whisker_l.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_right.
    rewrite vcomp_left_identity.
    rewrite left_unit_is_right_unit.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite left_unit_left, vcomp_left_identity, hcomp_id₂.
    rewrite vcomp_left_identity.
    apply left_unit_left.
  - unfold bc_whisker_r, bc_whisker_l.
    rewrite <- !left_unit_is_right_unit.
    rewrite triangle_r.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite left_unit_left, vcomp_left_identity, hcomp_id₂.
    rewrite vcomp_left_identity.
    apply right_unit_left.
Qed.    

Definition id_adjunction
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : adjunction (id₁ X) (id₁ X)
  := Build_Adjunction (id_adjunction_d X) (id_is_adjunction X).