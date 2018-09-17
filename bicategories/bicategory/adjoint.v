Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory_laws
     equivalence.

Definition is_left_adjoint_d
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
  := { right_d : C⟦Y,X⟧
     & (id₁ X ==> right_d · l)
        * (l · right_d ==> id₁ Y) }%type. 

Definition right_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint_d l)
  : C⟦Y,X⟧
  := A.1.

Definition unit_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}           
           (A : is_left_adjoint_d l)
  : id₁ X ==> right_d A · l
  := fst A.2.

Definition counit_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}           
           (A : is_left_adjoint_d l)
  : l · right_d A ==> id₁ Y
  := snd A.2.

Ltac make_is_left_adjoint := simple refine ((_;(_,_))).

Definition is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint_d l)
  : Type
  := (right_unit (right_d A)
      ∘ (right_d A) ◅ counit_d A
      ∘ assoc (right_d A) l (right_d A)
      ∘ unit_d A ▻ (right_d A)
      ∘ left_unit_inv (right_d A)
     = id₂ (right_d A))
   * (left_unit l
      ∘ counit_d A ▻ l
      ∘ assoc_inv l (right_d A) l
      ∘ l ◅ unit_d A
      ∘ right_unit_inv l
     = id₂ l).

Ltac make_is_adjunction := split.

Definition is_hprop_is_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint_d l)
  : IsHProp (is_adjunction A)
  := _.

Definition is_left_adjoint
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)           
  := { ld : is_left_adjoint_d l & is_adjunction ld }.

Definition Build_is_left_adjoint
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (ld : is_left_adjoint_d l)
           (Hl : is_adjunction ld)
  := (ld;Hl).

Definition right_adjoint
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : C⟦Y,X⟧
  := right_d A.1.

Definition unit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : id₁ X ==> right_adjoint A · l
  := unit_d A.1.

Definition counit
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : l · right_adjoint A ==> id₁ Y
  := counit_d A.1.

Definition unit_counit_l
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : ((right_unit (right_adjoint A))
       ∘ ((right_adjoint A) ◅ counit A)
       ∘ (assoc (right_adjoint A) l (right_adjoint A))
       ∘ (unit A ▻ (right_adjoint A))
       ∘ (left_unit_inv (right_adjoint A)))
    = id₂ (right_adjoint A)
  := fst A.2.

Definition unit_counit_r
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : ((left_unit l)
       ∘ (counit A ▻ l)
       ∘ assoc_inv l (right_adjoint A) l
       ∘ (l ◅ unit A)
       ∘ right_unit_inv l)
    = id₂ l
  := snd A.2.

Definition adjunction_is_equivalence
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
  : Type
  := IsIsomorphism (unit A)
     * IsIsomorphism (counit A).

Definition is_adjoint_equivalence
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
  : Type
  := { A : is_left_adjoint l
     & adjunction_is_equivalence A }.

Coercion is_adjoint_equivalence_to_left_adjoint
         {C : BiCategory}
         {X Y : C}
         {l : C⟦X,Y⟧}
         (A : is_adjoint_equivalence l)
  : is_left_adjoint l
  := A.1.

Global Instance ishprop_adjunction_is_equivalence
       {C : BiCategory}
       {X Y : C}
       {l : C⟦X,Y⟧}
       (A : is_left_adjoint l)
  : IsHProp (adjunction_is_equivalence A)
  := _.

Definition adjoint_equivalence
           {C : BiCategory}
           (X Y : C)
  : Type
  := {l : C⟦X,Y⟧ & is_adjoint_equivalence l}.

Definition Build_adjoint_equivalence
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : is_left_adjoint l)
           (unit_iso : IsIsomorphism (unit A))
           (counit_iso : IsIsomorphism (counit A))
  : adjoint_equivalence X Y
  := (l;(A;(unit_iso,counit_iso))).

Notation "X '≃' Y" := (adjoint_equivalence X Y) (at level 30) : bicategory_scope.

Coercion adjoint_equivalence_map
         {C : BiCategory}
         {X Y : C}
         (A : X ≃ Y)
  := A.1.

Coercion adjoint_equivalence_adjunction 
         {C : BiCategory}
         {X Y : C}
         (l : X ≃ Y)
  : is_left_adjoint l
  := l.2.1.

Global Instance unit_isomorphism
       {C : BiCategory}
       {X Y : C}
       (l : X ≃ Y)
  : IsIsomorphism (unit l).
Proof.
  apply l.2.
Defined.

Global Instance counit_isomorphism
       {C : BiCategory}
       {X Y : C}
       (l : X ≃ Y)
  : IsIsomorphism (counit l).
Proof.
  apply l.2.
Defined.

Definition unit_inv
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : right_adjoint l · l ==> id₁ X
  := (unit l)^-1%bicategory.

Definition counit_inv
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : id₁ Y ==> l · right_adjoint l
  := (counit l)^-1%bicategory.

Definition adjoint_equivalence_is_equivalence 
      {C : BiCategory}
      {X Y : C}
      (l : X ≃ Y)
  : is_equivalence l
  := Build_IsEquivalence (right_adjoint l) (counit l) (unit_inv l).

Coercion adjoint_equivalent_equivalence
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : equivalence X Y
  := Build_Equivalence l (adjoint_equivalence_is_equivalence l).

(* * Examples of adjunctinos and adjoint equivalences *)

Definition id_adjunction_d
           {C : BiCategory}
           (X : C)
  : is_left_adjoint_d (id₁ X).
Proof.
  make_is_left_adjoint.
  - exact (id₁ X).
  - exact (left_unit_inv (id₁ X)).
  - exact (left_unit (id₁ X)).
Defined.

Definition id_is_adjunction
           `{Funext}
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
    rewrite right_unit_id_is_left_unit_id.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite left_unit_left, vcomp_left_identity, hcomp_id₂.
    rewrite vcomp_left_identity.
    apply left_unit_left.
  - unfold bc_whisker_r, bc_whisker_l, counit_d ; cbn.
    rewrite <- !right_unit_id_is_left_unit_id.
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
           `{Funext}
           {C : BiCategory}
           (X : C)
  : is_left_adjoint (id₁ X)
  := Build_is_left_adjoint (id_adjunction_d X) (id_is_adjunction X).

Definition id_adjoint_equivalence
           `{Funext}
           {C : BiCategory}
           (X : C)
  : X ≃ X
  := Build_adjoint_equivalence (id_adjunction X) _ _.

Definition inv_adjunction_d
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : is_left_adjoint_d (right_adjoint l).
Proof.
  make_is_left_adjoint.
  - exact l.
  - exact (counit_inv l).
  - exact (unit_inv l).
Defined.

Definition inv_adjunction_p
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : is_adjunction (inv_adjunction_d l).
Proof.
  make_is_adjunction.
  - cbn ; unfold bc_whisker_l, bc_whisker_r.        
    rewrite !vcomp_assoc.
    pose (unit_counit_r l) as p.
    rewrite !vcomp_assoc in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    refine (vcomp_move_R_pM _ _ _ _) ; simpl.
    rewrite vcomp_left_identity.
    rewrite <- (vcomp_left_identity (right_unit l)).
    refine (vcomp_move_R_pM _ _ _ _) ; simpl.
    rewrite !vcomp_assoc.
    rewrite p.
    reflexivity.
  - cbn ; unfold bc_whisker_l, bc_whisker_r.        
    rewrite !vcomp_assoc.
    pose (unit_counit_l l) as p.
    rewrite !vcomp_assoc in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    refine (vcomp_move_R_pM _ _ _ _) ; simpl.
    rewrite vcomp_left_identity.
    rewrite <- (vcomp_left_identity (left_unit (right_adjoint l))).
    refine (vcomp_move_R_pM _ _ _ _) ; simpl.
    rewrite !vcomp_assoc.
    rewrite p.
    reflexivity.
Qed.

Definition inv_adjunction
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : is_left_adjoint (right_adjoint l)
  := Build_is_left_adjoint (inv_adjunction_d l) (inv_adjunction_p l).

Definition inv_equivalence
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : Y ≃ X
  := Build_adjoint_equivalence (inv_adjunction l) _ _.

Definition id_to_adjequiv
           `{Funext}
           {C : BiCategory}
           (X Y : C)
  : X = Y -> X ≃ Y
  := fun p =>
       match p with
       | idpath => id_adjoint_equivalence X
       end.

Definition transport_one_cell_FlFr
           `{Funext}
           {C : BiCategory}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : transport (fun (z : A) => C⟦f z,g z⟧)
              p
              h
      ==>
      id_to_adjequiv _ _ (ap g p) · h · id_to_adjequiv _ _ (ap f p^)
  := match p with
     | idpath => right_unit_inv _ ∘ left_unit_inv _
     end.

Definition transport_vcomp₁_l
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           {f₁ f₂ : C⟦X,Y⟧}
           (q : f₁ = f₂)
  : g ◅ idtoiso (C⟦X,Y⟧) q = idtoiso _ (ap (hcomp1 g) q).
Proof.
  induction q ; cbn.
  apply hcomp_id₂.
Defined.

Definition transport_vcomp₁_r
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦X,Y⟧)
           {f₁ f₂ : C⟦Y,Z⟧}
           (q : f₁ = f₂)
  : idtoiso (C⟦Y,Z⟧) q ▻ g = idtoiso _ (ap (fun (f : C⟦Y,Z⟧) => f · g) q).
Proof.
  induction q ; cbn.
  apply hcomp_id₂.
Defined.

Definition transport_two_cell_FlFr
           `{Funext}
           {C : BiCategory}
           {A : Type}
           {X Y : C}
           (F G : A -> C⟦X,Y⟧)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (α : F a₁ ==> G a₁)
  : transport (fun (z : A) => F z ==> G z)
              p
              α
    =
    idtoiso (C⟦X,Y⟧) (ap G p) ∘ α ∘ (idtoiso (C⟦X,Y⟧) (ap F p))^-1.
Proof.
  induction p ; cbn.
  rewrite vcomp_left_identity, vcomp_right_identity.
  reflexivity.
Qed.