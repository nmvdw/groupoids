Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
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
  := (unit l)^-1.

Definition counit_inv
           {C : BiCategory}
           {X Y : C}
           (l : X ≃ Y)
  : id₁ Y ==> l · right_adjoint l
  := (counit l)^-1.

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
    unfold vcomp, id₂ in *.
    refine ((left_identity _ _ _ _)^ @ _).
    refine (Morphisms.iso_moveR_pM _ _ _) ; simpl.
    refine (p^ @ _).
    rewrite left_identity.
    rewrite !associativity.
    reflexivity.
  - cbn ; unfold bc_whisker_l, bc_whisker_r.        
    rewrite !vcomp_assoc.
    pose (unit_counit_l l) as p.
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

Definition transport_two_cell_FlFr
           `{Funext}
           {C : BiCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : (transport (fun (z : A) => C⟦f z,g z⟧)
               p
               h)
      ==>
      id_to_adjequiv _ _ (ap g p) · h · id_to_adjequiv _ _ (ap f p^)
  := match p with
     | idpath => right_unit_inv _ ∘ left_unit_inv _
     end.

(* Separate file *)
(*
Definition right_adjoint_unique_fun
      {C : BiCategory}
      {X Y : C}
      (l : C⟦X,Y⟧)
      (L1 L2 : is_left_adjoint l)
  : right_adjoint L1 ==> right_adjoint L2.
Proof.
  refine (_ ∘ left_unit_inv _).
  refine (_ ∘ unit L2 ▻ _).
  refine (_ ∘ assoc _ _ _).
  refine (_ ∘ _ ◅ counit L1).
  apply right_unit.
Defined.

Definition right_adjoint_unique
      {C : BiCategory}
      {X Y : C}
      (l : C⟦X,Y⟧)
      (L1 L2 : is_left_adjoint l)
  : IsIsomorphism (right_adjoint_unique_fun l L1 L2).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (right_adjoint_unique_fun l L2 L1).
  - unfold right_adjoint_unique_fun.
    pose @unit_counit_l.
    admit.
  - admit.
Admitted.

Global Instance ishprop_is_adjoint_equivalence
       {C : BiCategory}
       {X Y : C}
       (l : C⟦X,Y⟧)
  : IsHProp (is_adjoint_equivalence l).
Proof.
  apply hprop_allpath.
  unfold is_adjoint_equivalence.
  intros [[L1 ?] ?] [[L2 ?] ?].
  apply path_sigma_hprop. simpl.
  apply path_sigma_hprop. simpl.
  admit.
Admitted.



Definition unique_right
           {C : BiCategory}
           {X Y : C}
           {l : C⟦X,Y⟧}
           (A₁ : adjoint_equivalence l)
           (A₂ : adjoint_equivalence l)
  : right_adjoint A₁ ==> right_adjoint A₂.
Proof.
  refine (_ ∘ left_unit_inv (right_adjoint A₁)).
  refine (_ ∘ (unit A₂) ▻ right_adjoint A₁).
  refine (_ ∘ assoc _ _ _).
  refine (_ ∘ right_adjoint A₂ ◅ (counit A₁)).
  apply right_unit.
Defined.

Global Instance unique_right_iso
       {C : BiCategory}
       {X Y : C}
       {l : C⟦X,Y⟧}
       (A₁ : adjoint_equivalence l)
       (A₂ : adjoint_equivalence l)
  : IsIsomorphism (unique_right A₁ A₂).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - refine (_ ∘ left_unit_inv (right_adjoint A₂)).
    refine (_ ∘ (unit A₁) ▻ right_adjoint A₂).
    refine (_ ∘ assoc _ _ _).
    refine (_ ∘ right_adjoint A₁ ◅ (counit A₂)).
    apply right_unit.
  - admit.
  - unfold unique_right, vcomp, bc_whisker_l, bc_whisker_r ; cbn.
    rewrite !associativity.
    pose (unit_counit_l A₁).

  - unfold unique_right, vcomp, bc_whisker_l, bc_whisker_r ; cbn.
    rewrite !associativity.
    pose (unit_counit_l A₁).
    pose @triangle_r.
    pose @left_unit_inv_natural.

           
Definition new_right
           {C : BiCategory}
           {X Y : C}
           (h : C⟦X,Y⟧)
           (Hh : is_equivalence h)
  : C⟦Y,X⟧
  := f_inv Hh.

Definition new_counit
           {C : BiCategory}
           {X Y : C}
           (h : C⟦X,Y⟧)
           (Hh : is_equivalence h)
  : h · new_right h Hh ==> id₁ Y
  := @retr _ _ _ h Hh.

Definition new_unit
           {C : BiCategory}
           {X Y : C}
           (h : C⟦X,Y⟧)
           (Hh : is_equivalence h)
  : id₁ X ==> new_right h Hh · h.
Proof.
  refine (_ ∘ (@sect _ _ _ h Hh)^-1) ; unfold new_right ; cbn.
  refine (right_unit _ ∘ _ ◅ @sect _ _ _ h Hh ∘ _).
  refine (_ ∘ (right_unit_inv _) ▻ h).
  refine (_ ∘ ((f_inv Hh ◅ (@retr _ _ _ h Hh)^-1) ▻ h)).
  refine (assoc_inv _ _ _ ∘ _ ∘ assoc _ _ _).
  refine (_ ◅ _).
  apply assoc.
Defined.

Definition new_adj
           {C : BiCategory}
           {X Y : C}
           (h : C⟦X,Y⟧)
           (Hh : is_equivalence h)
  : adjunction_d h.
Proof.
  make_adjunction.
  - exact (new_right h Hh).
  - exact (new_unit h Hh).
  - exact (new_counit h Hh).
Defined.

Definition test
           {C : BiCategory}
           {X Y : C}
           (h : C⟦X,Y⟧)
           (Hh : is_equivalence h)
  : is_adjunction (new_adj h Hh).
Proof.
  split.
  - cbn ; unfold new_right, new_counit, new_unit, bc_whisker_l, bc_whisker_r.
    rewrite <- !vcomp_assoc.
    refine (vcomp_move_R_pM _ _ _ _).
    rewrite vcomp_left_identity ; simpl.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- inverse_pentagon_5.
    rewrite !vcomp_assoc.
    rewrite triangle_r_inv.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => (_ ∘ (_ ∘ (_ ∘ (_ ∘ z)))) * id₂ _) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_inv_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z)) * id₂ _) (vcomp_assoc _ _ _)^).
    rewrite <- inverse_pentagon_2.
    rewrite !vcomp_assoc.
    rewrite right_unit_assoc.
    rewrite !(ap (fun z => (_ ∘ z) * id₂ _) (vcomp_assoc _ _ _)^).
    rewrite <- hcomp_id₂.
    rewrite <- assoc_inv_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => (_ ∘ z) * id₂ _) (vcomp_assoc _ _ _)^).
    rewrite assoc_left, vcomp_left_identity.
    unfold bc_whisker_l.
    rewrite <- (vcomp_left_identity (id₂ (f_inv Hh))), !interchange.
    rewrite !vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (f_inv Hh))), !interchange.
    rewrite !vcomp_left_identity.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite <- (vcomp_left_identity (id₂ (f_inv Hh))), !interchange.
    rewrite !vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ z)))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (f_inv Hh))), !interchange.
    rewrite !vcomp_left_identity.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (f_inv Hh))), !interchange.
    rewrite !vcomp_left_identity.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z)))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- !interchange.
    rewrite !vcomp_assoc, !vcomp_left_identity.
    pose @left_unit_inv_natural.

    pose @triangle_r_inv.

    pose @right_unit_natural.
    rewrite !vcomp_assoc, !vcomp_left_identity.
    !vcomp_assoc.
    pose @right_unit_natural.

    pose @assoc_inv_natural.
    pose @inverse_pentagon_2.
        
    pose @assoc_inv_natural.
    pose @triangle_r_inv.
    pose @right_unit_natural.
    pose @triangle_l_inv.
    pose @left_unit_inv_natural.
    cbn.
    admit.
  - cbn ; unfold new_right, new_counit, new_unit, bc_whisker_l, bc_whisker_r.
    rewrite <- !vcomp_assoc.
    
    rewrite right_unit_natural.
    pose 
*)