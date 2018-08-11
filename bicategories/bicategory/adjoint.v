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
  := Build_Adjunction_d
       {
         right_d : C⟦Y,X⟧ ;
         unit_d : id₁ X ==> right_d · l ;
         counit_d : l · right_d ==> id₁ Y
       }.

Arguments Build_Adjunction_d {C X Y l} _ _ _.
Ltac make_adjunction := simple refine (Build_Adjunction_d _ _ _).
Arguments right_d {C X Y l}.
Arguments unit_d {C X Y l}.
Arguments counit_d {C X Y l}.

Definition is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
  : Type
  := Datatypes.prod
       (((right_unit (right_d A))
          ∘ ((right_d A) ▻ counit_d A)
          ∘ (assoc (right_d A) l (right_d A))
          ∘ (unit_d A ◅ (right_d A))
          ∘ (left_unit_inv (right_d A)))
        = id₂ (right_d A))
       (((left_unit l)
           ∘ (counit_d A ◅ l)
           ∘ assoc_inv l (right_d A) l
           ∘ (l ▻ unit_d A)
          ∘ right_unit_inv l)
        = id₂ l).

Ltac make_is_adjunction := split.

Definition is_hprop_is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
  : IsHProp (is_adjunction A)
  := _.

Definition adjunction
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
  := {A : adjunction_d l & is_adjunction A}.

Definition Build_Adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
           (pA : is_adjunction A)
  := (A;pA).

Definition right_adjoint
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : C⟦Y,X⟧
  := right_d A.1.

Definition unit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : id₁ X ==> right_adjoint A · l
  := unit_d A.1.

Definition counit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : l · right_adjoint A ==> id₁ Y
  := counit_d A.1.

Definition unit_counit_l
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : ((right_unit (right_adjoint A))
       ∘ ((right_adjoint A) ▻ counit A)
       ∘ (assoc (right_adjoint A) l (right_adjoint A))
       ∘ (unit A ◅ (right_adjoint A))
       ∘ (left_unit_inv (right_adjoint A)))
    = id₂ (right_adjoint A)
  := Datatypes.fst A.2.

Definition unit_counit_r
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : ((left_unit l)
       ∘ (counit A ◅ l)
       ∘ assoc_inv l (right_adjoint A) l
       ∘ (l ▻ unit A)
       ∘ right_unit_inv l)
    = id₂ l
  := Datatypes.snd A.2.

Definition is_adjoint_equivalence
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction l)
  : Type
  := Datatypes.prod (IsIsomorphism (unit A))
                    (IsIsomorphism (counit A)).

Global Instance is_adjoint_equivalence_is_hprop
       {C : BiCategory}
       {X Y : C}
       {l : C⟦X,Y⟧}
       (A : adjunction l)
  : IsHProp (is_adjoint_equivalence A)
  := _.

Definition id_adjunction_d
           {C : BiCategory}
           (X : C)
  : adjunction_d (id₁ X).
Proof.
  make_adjunction.
  - exact (id₁ X).
  - exact (left_unit_inv (id₁ X)).
  - exact (left_unit (id₁ X)).
Defined.

Definition id_is_adjunction
           `{Univalence}
           {C : BiCategory}
           (X : C)
  : is_adjunction (id_adjunction_d X).
Proof.
  make_is_adjunction ; simpl.
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
  : adjunction (id₁ X)
  := Build_Adjunction (id_adjunction_d X) (id_is_adjunction X).