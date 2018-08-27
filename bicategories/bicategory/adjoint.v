Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.bicategory_laws
     equivalence.

Definition adjunction_d
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
  := {right_d : C⟦Y,X⟧
                & Datatypes.prod (id₁ X ==> right_d · l) (l · right_d ==> id₁ Y)}.

Definition right_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
  : C⟦Y,X⟧
  := A.1.

Definition unit_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
  : id₁ X ==> right_d A · l
  := Datatypes.fst A.2.

Definition counit_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjunction_d l)
  : l · right_d A ==> id₁ Y
  := Datatypes.snd A.2.

Definition Build_Adjunction_d
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (right_d : C⟦Y,X⟧)
           (unit_d : id₁ X ==> right_d · l)
           (counit_d : l · right_d ==> id₁ Y)
  : adjunction_d l
  := (right_d;(unit_d,counit_d)).

Ltac make_adjunction := simple refine (Build_Adjunction_d _ _ _).

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

Definition adjoint_equivalence
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
  : Type
  := {A : adjunction l & is_adjoint_equivalence A}.

Coercion adjoint_equivalence_to_adjoint
         {C : BiCategory}
         {X Y : C}
         {l : C⟦X,Y⟧}
         (A : adjoint_equivalence l)
  := A.1.

Global Instance unit_isomorphism
       {C : BiCategory}
       {X Y : C}
       {l : C⟦X,Y⟧}
       (A : adjoint_equivalence l)
  : IsIsomorphism (unit A).
Proof.
  apply A.
Defined.

Global Instance counit_isomorphism
       {C : BiCategory}
       {X Y : C}
       {l : C⟦X,Y⟧}
       (A : adjoint_equivalence l)
  : IsIsomorphism (counit A).
Proof.
  apply A.
Defined.

Definition unit_inv
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjoint_equivalence l)
  : right_adjoint A · l ==> id₁ X
  := ((unit A)^-1)%morphism.

Definition counit_inv
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A : adjoint_equivalence l)
  : id₁ Y ==> l · right_adjoint A
  := ((counit A)^-1)%morphism.

Definition adjoint_equivalent
           {C : BiCategory}
           (X Y : C)
  : Type
  := {l : C⟦X,Y⟧ & adjoint_equivalence l}.

Coercion adjoint_equivalent_map
         {C : BiCategory}
         {X Y : C}
         (A : adjoint_equivalent X Y)
  := A.1.

Notation "X '≃' Y" := (adjoint_equivalent X Y) (at level 30) : bicategory_scope.

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
    rewrite left_unit_is_right_unit.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite left_unit_left, vcomp_left_identity, hcomp_id₂.
    rewrite vcomp_left_identity.
    apply left_unit_left.
  - unfold bc_whisker_r, bc_whisker_l, counit_d ; cbn.
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
           `{Funext}
           {C : BiCategory}
           (X : C)
  : adjunction (id₁ X)
  := Build_Adjunction (id_adjunction_d X) (id_is_adjunction X).

Definition id_adjoint_equivalence
           `{Funext}
           {C : BiCategory}
           (X : C)
  : adjoint_equivalence (id₁ X).
Proof.
  simple refine (id_adjunction X;_).
  split ; apply _.
Defined.

Definition inv_adjunction_d
           {C : BiCategory}
           {X Y : C}
           {l : C ⟦ X, Y ⟧}
           (A : adjoint_equivalence l)
  : adjunction_d (right_adjoint A).
Proof.
  make_adjunction.
  - exact l.
  - exact (counit_inv A).
  - exact (unit_inv A).
Defined.

Definition inv_adjunction_p
           {C : BiCategory}
           {X Y : C}
           {l : C ⟦ X, Y ⟧}
           (A : adjoint_equivalence l)
  : is_adjunction (inv_adjunction_d A).
Proof.
  make_is_adjunction.
  - cbn ; unfold bc_whisker_l, bc_whisker_r.        
    rewrite !vcomp_assoc.
    pose (unit_counit_r A).
    rewrite !vcomp_assoc in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    unfold vcomp, id₂ in *.
    refine ((left_identity _ _ _ _)^ @ _).
    refine (Morphisms.iso_moveR_pM _ _ _) ; simpl.
    refine (p^ @ _).
    rewrite left_identity.
    rewrite !associativity.
    reflexivity.
  - cbn ; unfold bc_whisker_l, bc_whisker_r.        
    rewrite !vcomp_assoc.
    pose (unit_counit_l A).
    rewrite !vcomp_assoc in p.
    unfold bc_whisker_l, bc_whisker_r in p.
    unfold vcomp, id₂ in *.
    refine ((left_identity _ _ _ _)^ @ _).
    refine (Morphisms.iso_moveR_pM _ _ _) ; simpl.
    refine (p^ @ _).
    rewrite left_identity.
    rewrite !associativity.
    reflexivity.
Qed.

Definition inv_adjunction
           {C : BiCategory}
           {X Y : C}
           {l : C ⟦ X, Y ⟧}
           (A : adjoint_equivalence l)
  : adjunction (right_adjoint A)
  := Build_Adjunction (inv_adjunction_d A) (inv_adjunction_p A).

Definition inv_equivalence
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           {l : C ⟦ X, Y ⟧}
           (A : adjoint_equivalence l)
  : adjoint_equivalence (right_adjoint A).
Proof.
  simple refine (_;_).
  - exact (inv_adjunction A).
  - split.
    + apply _.
    + apply _.
Defined.        

Definition inv_adjunction_equivalence
           `{Funext}
           {C : BiCategory}
           {X Y : C}
  : X ≃ Y -> Y ≃ X.
Proof.
  intros A.
  simple refine (right_adjoint A.2;_) ; cbn.
  apply inv_equivalence.
Defined.

Definition comp_adjunction_d
           {C : BiCategory}
           {X Y Z : C}
           {l₁ : C ⟦ X, Y ⟧} {l₂ : C⟦Y,Z⟧}
           (A₂ : adjunction l₂) (A₁ : adjunction l₁)
  : adjunction_d (l₂ · l₁).
Proof.
  make_adjunction.
  - exact (right_adjoint A₁ · right_adjoint A₂).
  - refine (_ ∘ unit A₁).
    refine (_ ∘ (right_unit_inv _ ◅ l₁)).
    refine (_ ∘ ((_ ▻ unit A₂) ◅ l₁)).
    exact (assoc_inv _ _ _ ∘ (_ ▻ assoc _ _ _) ∘ assoc _ _ _).
  - refine (counit A₂ ∘ _).
    refine ((l₂ ▻ left_unit _) ∘ _).
    refine ((l₂ ▻ (counit A₁ ◅ _)) ∘ _).
    exact (assoc _ _ _ ∘ (assoc _ _ _ ◅ _) ∘ assoc_inv _ _ _).
Defined.

Definition id_to_adjequiv
           `{Funext}
           {C : BiCategory}
           (X Y : C)
  : X = Y -> X ≃ Y
  := fun p =>
       match p with
       | idpath => (id₁ X;id_adjoint_equivalence X)
       end.

Definition transport_hom₁
           `{Funext}
           {C : BiCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           (f : C⟦X₁,Y₁⟧)
           (p : X₁ = X₂) (q : Y₁ = Y₂)
  : (transport (fun (z : C * C) => C⟦Datatypes.fst z,Datatypes.snd z⟧)
               (path_prod' p q)
               f)
      ==>
      id_to_adjequiv _ _ q · f · id_to_adjequiv _ _ p^
  := match p, q with
     | idpath, idpath => right_unit_inv _ ∘ left_unit_inv _
     end.

Definition transport_hom₂
           `{Funext}
           {C : BiCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           (f : C⟦X₁,Y₁⟧)
           (p : X₁ = X₂) (q : Y₁ = Y₂)
  : (id_to_adjequiv _ _ q · f · id_to_adjequiv _ _ p^)
      ==>
      transport(fun (z : C * C) => C⟦Datatypes.fst z,Datatypes.snd z⟧)
      (path_prod' p q)
      f
  := match p, q with
     | idpath, idpath => left_unit _ ∘ right_unit _
     end.
