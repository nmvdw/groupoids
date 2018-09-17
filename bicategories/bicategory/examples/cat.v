Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.univalent
     adjoint
     adjoint_unique.
From GR.bicategories.bicategory.examples Require Import
     precat full_sub.

Definition Cat `{Funext} : BiCategory
  := full_sub PreCat (fun C => BuildhProp (IsCategory C)).

Definition path_functor_natural
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (p : Core.object_of F = Core.object_of G)
           (q : forall (X Y : C)
                       (f : morphism C X Y),
               ((@morphism_isomorphic _ _ _
                                      (Category.Morphisms.idtoiso
                                         _
                                         (ap (fun H => H Y) p)))
                  o F _1 f
                = G _1 f
                    o @morphism_isomorphic _ _ _
                    (Category.Morphisms.idtoiso _ (ap (fun H => H X) p)))%morphism)
  : F = G.
Proof.
  simple refine (path_functor _ _ _ _).
  - exact p.
  - funext X Y f.
    destruct F, G.
    cbn in *.
    induction p.
    specialize (q X Y f).
    simpl in *.
    rewrite left_identity, right_identity in q.
    exact q.
Defined.

Definition isotoid_functor
           `{Funext}
           {C D : PreCategory}
           `{IsCategory D}
           {F G : Functor C D}
           (η : @Isomorphic (C -> D) F G)
  : F = G.
Proof.
  simple refine (path_functor_natural _ _).
  - funext X.
    simple refine (isotoid _ _ _ _).
    simple refine (Build_Isomorphic _).
  - intros X Y f.
    pose (commutes (@morphism_isomorphic _ _ _ η) X Y f).
    rewrite !ap_apply_l, !ap10_path_forall.
    rewrite !eisretr.
    apply p.
Defined.

Definition components_idtoiso
           `{Funext}
           {C D : PreCategory}
           `{IsCategory D}
           {F G : Functor C D}
           (p : F = G)
           (X : C)
  : Core.components_of
      (@morphism_isomorphic (C -> D) _ _ (Category.Morphisms.idtoiso (C -> D) p))
      X
    =
    @morphism_isomorphic
      D (F X) (G X)
      (Category.Morphisms.idtoiso D (ap (fun (H : Functor C D) => H X) p)).
Proof.
  induction p ; cbn.
  reflexivity.
Defined.

Definition components_isotoid_functor
           `{Funext}
           {C D : PreCategory}
           `{IsCategory D}
           {F G : Functor C D}
           (e : @Isomorphic (C -> D) F G)
           (X : C)
  : ap (fun H : Functor C D => Core.object_of H X) (isotoid_functor e)
    =
    isotoid D (F X) (G X) (Build_Isomorphic _).
Proof.
  rewrite (ap_compose object_of (fun f => f X)).
  unfold isotoid_functor, path_functor_natural, path_functor.
  rewrite path_functor_uncurried_fst.
  rewrite ap_apply_l.
  rewrite ap10_path_forall.
  reflexivity.
Defined.

Global Instance is_category_functor_category
       `{Funext}
       (C D : PreCategory)
       `{IsCategory D}
  : IsCategory (C -> D).
Proof.
  intros F G ; cbn in *.
  simple refine (isequiv_adjointify _ _ _ _).
  - exact isotoid_functor.
  - intros e.
    apply path_isomorphic ; cbn.
    apply path_natural_transformation.
    intros X ; simpl.
    rewrite components_idtoiso.
    rewrite components_isotoid_functor.
    rewrite eisretr.
    reflexivity.
  - intros p.
    induction p ; simpl.
    rewrite <- path_functor_uncurried_idpath.
    unfold isotoid_functor, path_functor_natural, path_functor.
    f_ap.
    apply path_sigma_hprop.
    rewrite <- path_forall_1 ; cbn.
    f_ap.
    funext X ; simpl.
    rewrite <- (eisretr ((@Category.Morphisms.idtoiso D (F X) (F X))^-1%function)) ; cbn.
    f_ap.
    apply path_isomorphic.
    reflexivity.
Defined.

Global Instance locally_univalent_cat `{Univalence}
  : LocallyUnivalent Cat.
Proof.
  intros [X CX] [Y CY].
  apply is_category_functor_category.
  apply CY.
Defined.








(** Fully faithful functors. *)
Class fullyfaithful
      {C D : PreCategory}
      (F : Functor C D)
  := fullyfaithful_comp :> forall (X Y : C), IsEquiv (@morphism_of C D F X Y).

Definition inverse_image_arrow
           {C D : PreCategory}
           (F : Functor C D)
           `{fullyfaithful C D F}
           {X Y : C}
  : morphism D (F X) (F Y) -> morphism C X Y
  := (@morphism_of C D F X Y)^-1%function.

Definition inverse_image_faithful
           {C D : PreCategory}
           (F : Functor C D)
           `{fullyfaithful C D F}
           {X Y : C}
           (f : morphism D (F X) (F Y))
  : morphism_of F (inverse_image_arrow F f) = f
  := eisretr _ _.

Definition inverse_image_id
           {C D : PreCategory}
           (F : Functor C D)
           `{fullyfaithful C D F}
           (X : C)
  : inverse_image_arrow F 1%morphism = (1%morphism : morphism C X X).
Proof.
  rewrite <- (eissect (@morphism_of C D F X X) 1%morphism).
  f_ap.
  rewrite identity_of.
  reflexivity.
Qed.

Definition inverse_image_compose
           {C D : PreCategory}
           (F : Functor C D)
           `{fullyfaithful C D F}
           (X Y Z : C)
           (f : morphism D (F X) (F Y)) (g : morphism D (F Y) (F Z))
  : inverse_image_arrow F (g o f)%morphism
    =
    (inverse_image_arrow F g o inverse_image_arrow F f)%morphism.
Proof.
  refine (_ @ eissect (@morphism_of C D F X Z) _).
  f_ap.
  rewrite composition_of.
  rewrite !eisretr.
  reflexivity.
Qed.

(** Isomorphisms *)
Definition is_isomorphism
           `{Funext}
           {C D : PreCategory}
           (F : Functor C D)
  : Type
  := fullyfaithful F * IsEquiv (object_of F).

Global Instance ishprop_is_isomorphism
       `{Univalence}
       {C D : PreCategory}
       (F : Functor C D)
  : IsHProp (is_isomorphism F).
Proof.
  unfold is_isomorphism, fullyfaithful.
  apply _.
Defined.

Definition isomorphic
           `{Funext}
           (C D : PreCategory)
  : Type
  := {F : Functor C D & is_isomorphism F}.

Definition identity_iso
           `{Funext}
           (C : PreCategory)
  : isomorphic C C.
Proof.
  exists 1%functor.
  split ; try intro ; apply _.
Defined.

Definition id_to_iso
           `{Funext}
           {C D : Cat}
  : C = D -> isomorphic C.1 D.1.
Proof.
  intros p.
  induction p.
  exact (identity_iso C.1).
Defined.

Definition inv_iso_map
           `{Univalence}
           {C D : PreCategory}
           (F : isomorphic C D)
  : Functor D C.
Proof.
  destruct F as [F [HF1 HF2]].
  simple refine (Build_Functor _ _ _ _ _ _).
  - exact (object_of F)^-1%function.
  - intros X Y f ; cbn.
    simple refine (inverse_image_arrow F _).
    refine (Category.Morphisms.idtoiso _ _^ o f o Category.Morphisms.idtoiso _ _)%morphism
    ; apply eisretr.
  - intros X Y Z f g ; cbn.
    rewrite <- inverse_image_compose.
    f_ap.
    rewrite !associativity.
    rewrite !(ap (fun z => _ o (_ o z))%morphism (associativity _ _ _ _ _ _ _ _)^).
    rewrite idtoiso_comp, concat_Vp ; simpl.
    rewrite left_identity.
    reflexivity.
  - intros X ; cbn.
    rewrite right_identity, idtoiso_comp, concat_pV.
    rewrite <- (inverse_image_id F _).
    reflexivity.
Defined.

Global Instance counit_X
       `{Univalence}
       {C D : Cat}
       (F : Functor C.1 D.1)
       (HF : @is_adjoint_equivalence Cat C D F)
       (X : D.1)
  : IsIsomorphism (counit HF X).
Proof.
  destruct HF as [R [Hu Hc]].
  apply _.
Defined.

Global Instance unit_X
       `{Univalence}
       {C D : Cat}
       (F : Functor C.1 D.1)
       (HF : @is_adjoint_equivalence Cat C D F)
       (X : C.1)
  : IsIsomorphism (unit HF X).
Proof.
  destruct HF as [R [Hu Hc]].
  apply _.
Defined.

(** Adjoint equivalences are isomorphisms. Isomorphisms are adjoint equivalences *)
Definition adj_triangle
           `{Univalence}
           {C D : Cat}
           (F : Functor C.1 D.1)
           (HF : @is_adjoint_equivalence Cat C D F)
           (X : C.1)
  : (F _1 (((unit HF)^-1) X) = counit HF (F X))%morphism.
Proof.
  refine ((left_identity _ _ _ _)^ @ _).
  simple refine (iso_moveR_pM _ _ _) ; simpl.
  pose (equiv_path_natural_transformation _ _ (unit_counit_r HF) X).
  cbn in p.
  rewrite !identity_of, !left_identity, !right_identity in p.
  symmetry.
  apply p.
Qed.

Definition is_adjequiv_to_is_iso
           `{Univalence}
           {C D : Cat}
           (F : Functor C.1 D.1)
           (HF : @is_adjoint_equivalence Cat C D F)
  : is_isomorphism F.
Proof.
  split.
  - intros X Y.
    simple refine (isequiv_adjointify _ _ _ _).
    + intros f.
      simple refine (_ o morphism_of (right_adjoint HF) f o _)%morphism.
      * exact ((unit HF)^-1 Y).
      * exact (unit HF X).
    + intros f.
      rewrite !composition_of.
      rewrite (adj_triangle F HF Y).
      rewrite (commutes (counit HF)) ; simpl.
      rewrite associativity.
      rewrite <- (adj_triangle F HF X).
      rewrite <- composition_of.
      rewrite left_inverse.
      rewrite identity_of, right_identity.
      reflexivity.
    + intros f.
      rewrite !associativity.
      rewrite <- (commutes (unit HF) X Y f).
      rewrite <- !associativity.
      rewrite left_inverse, left_identity.
      reflexivity.
  - simple refine (isequiv_adjointify _ _ _ _).
    + exact (right_adjoint HF).
    + intros X.
      destruct D as [D HD].
      simpl in *.
      refine ((@Category.Morphisms.idtoiso D (F (right_adjoint HF X)) X)^-1%function _).
      apply (@Build_Isomorphic _ _ _ (counit HF X) _).
    + intros X.
      destruct C as [C HC].
      simpl in *.
      refine ((@Category.Morphisms.idtoiso C (right_adjoint HF (F X)) X)^-1%function _).
      apply (@Build_Isomorphic _ _ _ (unit HF X)^-1 _).
Qed.

Definition is_iso_to_is_adjequiv_is_left_adjoint_d
           `{Univalence}
           {C D : Cat}
           (F : Cat⟦C,D⟧)
           (HF : is_isomorphism F)
  : is_left_adjoint_d F.
Proof.
  make_is_left_adjoint.
  - exact (inv_iso_map (F;HF)).
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros X ; cbn.
      refine (Category.Morphisms.idtoiso _ _^).
      apply eissect.
    + intros X Y f ; simpl.
      destruct HF.
      refine ((eissect (@morphism_of _ _ F _ _) _)^ @ _).
      rewrite <- (eissect (@morphism_of _ _ F _ _)
                          (Category.Morphisms.idtoiso C.1 (eissect _ X)^)).
      unfold inverse_image_arrow.
      rewrite <- inverse_image_compose.
      f_ap.
      rewrite !composition_of.
      rewrite !idtoiso_functor.
      rewrite !ap_V, <- !eisadj.
      rewrite !associativity.
      f_ap.
      rewrite idtoiso_comp.
      rewrite concat_Vp, right_identity.
      reflexivity.
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros X ; cbn.
      refine (Category.Morphisms.idtoiso _ _).
      apply eisretr.
    + intros X Y f ; cbn.
      destruct HF.
      unfold inverse_image_arrow.
      rewrite (eisretr (@morphism_of _ _ F _ _)).
      rewrite <- !associativity.
      rewrite !idtoiso_comp, concat_Vp ; simpl.
      rewrite left_identity.
      reflexivity.
Defined.

Definition is_iso_to_is_adjequiv_is_adjunction
           `{Univalence}
           {C D : Cat}
           (F : Cat⟦C,D⟧)
           (HF : is_isomorphism F)
  : is_adjunction (is_iso_to_is_adjequiv_is_left_adjoint_d F HF).
Proof.
  make_is_adjunction.
  - apply path_natural_transformation.
    intros X ; cbn.
    rewrite !left_identity, !right_identity.
    rewrite idtoiso_comp, concat_pV ; simpl.
    rewrite left_identity.
    unfold inverse_image_arrow.
    rewrite eisadj.
    rewrite <- idtoiso_functor.
    rewrite (eissect (@morphism_of _ _ F _ _)).
    rewrite idtoiso_comp.
    rewrite concat_Vp ; simpl.
    reflexivity.
  - apply path_natural_transformation.
    intros X ; cbn.
    rewrite !left_identity, !right_identity.
    rewrite idtoiso_comp, concat_pV ; simpl.
    rewrite inverse_image_id, identity_of, right_identity.
    rewrite idtoiso_functor.
    rewrite eisadj.
    rewrite idtoiso_comp.
    rewrite <- ap_pp, concat_Vp.
    reflexivity.
Qed.

Definition is_iso_to_is_adjequiv
           `{Univalence}
           {C D : Cat}
           (F : Functor C.1 D.1)
           (HF : is_isomorphism F)
  : @is_adjoint_equivalence Cat C D F.
Proof.
  simple refine (_;_).
  - simple refine (Build_is_left_adjoint _ _).
    + exact (is_iso_to_is_adjequiv_is_left_adjoint_d F HF).
    + exact (is_iso_to_is_adjequiv_is_adjunction F HF).
  - split ; apply isisomorphism_natural_transformation ; intros X ; apply _.
Defined.

Definition iso_to_adjequiv
           `{Univalence}
           {C D : Cat}
  : isomorphic C.1 D.1 -> C ≃ D.
Proof.
  intros L.
  simple refine (_;_).
  - apply L.
  - cbn.
    apply is_iso_to_is_adjequiv.
    apply L.
Defined.

Definition adjequiv_to_iso
           `{Univalence}
           {C D : Cat}
  : C ≃ D -> isomorphic C.1 D.1.
Proof.
  intros L.
  simple refine (_;_).
  - apply L.
  - cbn.
    apply is_adjequiv_to_is_iso.
    apply L.
Defined.

Global Instance is_equiv_adjequiv_to_iso
       `{Univalence}
       (C D : Cat)
  : IsEquiv (@iso_to_adjequiv _ C D).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - exact adjequiv_to_iso.
  - intros L.
    apply path_sigma_hprop.
    reflexivity.
  - intros L.
    apply path_sigma_hprop.
    reflexivity.
Defined.

Definition iso_to_adjequiv_equiv
           `{Univalence}
           {C D : Cat}
  : isomorphic C.1 D.1 <~> C ≃ D
  := BuildEquiv _ _ (@iso_to_adjequiv _ C D) _.

Definition factor_id_to_adjequiv
           `{Univalence}
           (C D : Cat)
  : id_to_adjequiv C D = @iso_to_adjequiv _ C D o @id_to_iso _ C D.
Proof.
  funext p.
  induction p ; cbn.
  apply path_adjoint_equivalence.
  reflexivity.
Defined.

(** Simplify data in isomorphism *)
Definition isomorphic_data
           (C D : PreCategory)
  := {F : (object C <~> object D)
          & {HF : (forall (X Y : C), morphism C X Y <~> morphism D (F X) (F Y))
                  & (forall (X Y Z : C) (f : morphism C X Y) (g : morphism C Y Z),
                        HF X Z (g o f) = HF _ _ g o HF _ _ f)
                    *
                    (forall (X : C),
                        HF X X 1 = 1)
     }}%type%morphism.

Definition id_isomorphic_data
           (C : PreCategory)
  : isomorphic_data C C
  := (equiv_idmap;(fun _ _ => equiv_idmap;(fun _ _ _ _ _ => idpath,fun _ => idpath))).

Definition id_to_isomorphic_data
           `{Funext}
           (C D : Cat)
  : C = D -> isomorphic_data C.1 D.1.
Proof.
  intros p.
  induction p.
  exact (id_isomorphic_data C.1).
Defined.

Section Isomorphic_IsomorphicData_Equivalent.
  Context `{Funext}.
  Variable (C D : PreCategory).

  Definition isomorphic_to_isomorphic_data
    : isomorphic C D -> isomorphic_data C D.
  Proof.
    intros [F [HF1 HF2]].
    simple refine (_;(_;(_,_))).
    - exact (BuildEquiv _ _ (object_of F) _).
    - exact (fun X Y => BuildEquiv _ _ (@morphism_of _ _ F X Y) _).
    - exact (composition_of F).
    - exact (identity_of F).
  Defined.

  Definition isomorphic_data_to_isomorphic
    : isomorphic_data C D -> isomorphic C D.
  Proof.
    intros [F [HF [Fcomp Fid]]].
    simple refine (_;_).
    - simple refine (Build_Functor _ _ _ _ _ _).
      + exact F.
      + exact HF.
      + exact Fcomp.
      + exact Fid.
    - split ; simpl.
      + unfold fullyfaithful.
        apply _.
      + apply _.
  Defined.

  Global Instance isequiv_isomorphic_data_to_isomorphic
    : IsEquiv isomorphic_data_to_isomorphic.
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - exact isomorphic_to_isomorphic_data.
    - intros [F [HF1 HF2]].
      reflexivity.
    - intros [F [HF [Fcomp Fid]]].
      reflexivity.
  Defined.
End Isomorphic_IsomorphicData_Equivalent.

Definition factor_id_to_iso
           `{Univalence}
           (C D : Cat)
  : @id_to_iso _ C D = isomorphic_data_to_isomorphic C.1 D.1 o id_to_isomorphic_data C D.
Proof.
  funext p.
  induction p ; cbn.
  reflexivity.
Defined.

(** Useful lemmata *)
Definition transport_morphism
           {C : PreCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           (p : X₁ = X₂) (q : Y₁ = Y₂)
  : morphism C X₁ Y₁ -> morphism C X₂ Y₂
  := fun f => (Category.Morphisms.idtoiso _ q o f o Category.Morphisms.idtoiso _ p^)%morphism.

Definition transport_morphism_11
           `{Funext}
           {C : PreCategory}
           {X Y : C}
  : transport_morphism (idpath : X = X) (idpath : Y = Y) = idmap.
Proof.
  funext f.
  unfold transport_morphism ; cbn.
  rewrite left_identity, right_identity.
  reflexivity.
Qed.

Definition transport_morphism_id
           {C : PreCategory}
           {X₁ X₂ : C}
           (p : X₁ = X₂)
  : (transport_morphism p p 1
    =
    1)%morphism.
Proof.
  unfold transport_morphism.
  induction p ; cbn.
  rewrite !right_identity.
  reflexivity.
Qed.

Definition transport_morphism_compose
           {C : PreCategory}
           {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
           (p : X₁ = X₂)
           (q : Y₁ = Y₂)
           (r : Z₁ = Z₂)
           (f : morphism C X₁ Y₁)
           (g : morphism C Y₁ Z₁)
  : (transport_morphism q r g o transport_morphism p q f
     =
     transport_morphism p r (g o f))%morphism.
Proof.
  unfold transport_morphism.
  induction p, q, r ; cbn.
  rewrite !left_identity, !right_identity.
  reflexivity.
Defined.

Global Instance transport_morphism_isequiv
       {C : PreCategory}
       {X₁ X₂ Y₁ Y₂ : C}
       (p : X₁ = X₂) (q : Y₁ = Y₂)
  : IsEquiv (transport_morphism p q).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - exact (transport_morphism p^ q^).
  - intros f.
    unfold transport_morphism.
    induction p, q ; simpl.
    rewrite !left_identity, !right_identity.
    reflexivity.
  - intros f.
    unfold transport_morphism.
    induction p, q ; simpl.
    rewrite !left_identity, !right_identity.
    reflexivity.
Defined.

Definition transport_morphism_equiv
           {C : PreCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           (p : X₁ = X₂) (q : Y₁ = Y₂)
  : morphism C X₁ Y₁ <~> morphism C X₂ Y₂
  := BuildEquiv _ _ (transport_morphism p q) _.

Definition transport_morphism_inj
           {C : PreCategory}
           {X₁ X₂ Y₁ Y₂ : C}
           (p : X₁ = X₂) (q : Y₁ = Y₂)
           (f g : morphism C X₁ Y₁)
  : transport_morphism p q f = transport_morphism p q g -> f = g.
Proof.
  intros Hfg.
  rewrite <- (eissect (transport_morphism p q) f).
  rewrite <- (eissect (transport_morphism p q) g) ; simpl.
  rewrite Hfg.
  reflexivity.
Defined.

Definition equiv_compose_left
           {A B : Type}
           (f : A <~> B)
           (C : Type)
  : C <~> A -> C <~> B
  := fun (h : C <~> A) => equiv_compose f h.

Global Instance isequiv_equiv_compose
       `{Funext}
       {A B C : Type}
       (f : A <~> B)
  : IsEquiv (equiv_compose_left f C).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - intros e.
    exact (equiv_compose (symmetric_equiv _ _ f) e).
  - intros h.
    apply path_equiv.
    funext x ; simpl.
    rewrite eisretr.
    reflexivity.
  - intros h.
    apply path_equiv.
    funext x ; simpl.
    rewrite eissect.
    reflexivity.
Defined.

Definition equiv_compose_left_equiv
           `{Funext}
           {A B : Type}
           (f : A <~> B)
           (C : Type)
  : (C <~> A) <~> (C <~> B)
  := BuildEquiv _ _ (equiv_compose_left f C) _.

Definition path_universe_equiv
           `{Univalence}
           {A B : Type}
  : (A <~> B) <~> A = B
  := BuildEquiv (A <~> B) (A = B) (fun (f : A <~> B) => path_universe f) _.

Definition transport_idmap_equiv
           `{Univalence}
           {A B : Type}
  : A = B <~> (A <~> B)
  := BuildEquiv (A = B) (A <~> B) (fun (p : A = B) => BuildEquiv _ _ (transport idmap p) _) _.

Definition functor_forall_equiv
           `{Funext}
           {A B : Type}
           {P : A -> Type} {Q : B -> Type}
           (f : B <~> A)
           (g : forall (b : B), P (f b) <~> Q b)
  : (forall (a : A), P a) <~> (forall (b : B), Q b)
  := BuildEquiv _ _ (functor_forall f g) _.

Definition functor_sigma_equiv
           {A B : Type}
           {P : A -> Type} {Q : B -> Type}
           (f : A <~> B)
           (g : forall (a : A), P a <~> Q (f a))
  : {x : A & P x} <~> {y : B & Q y}
  := BuildEquiv _ _ (functor_sigma f g) _.

Definition functor_prod_equiv
           {A A' B B'  : Type}
           (f : A <~> A')
           (g : B <~> B')
  : A * B <~> A' * B'
  := BuildEquiv _ _ (functor_prod f g) _.

(** Simplify data in isomorphism via univalence *)
Definition isomorphic_path_data
           (C D : PreCategory)
  := {F : (object C = object D)
          & {HF : (forall (X Y : C),
                      morphism C X Y
                      =
                      morphism D (transport idmap F X) (transport idmap F Y))
                  & (forall (X Y Z : C) (f : morphism C X Y) (g : morphism C Y Z),
                        transport idmap (HF X Z) (g o f)
                        =
                        transport idmap (HF Y Z) g o transport idmap (HF X Y) f)
                    *
                    (forall (X : C),
                        transport idmap (HF X X) 1 = 1)
     }}%type%morphism.

Definition id_isomorphic_path_data
           (C : PreCategory)
  : isomorphic_path_data C C
  := (idpath;(fun _ _ => idpath;(fun _ _ _ _ _ => idpath,fun _ => idpath))).

Definition id_to_isomorphic_path_data
           `{Funext}
           (C D : Cat)
  : C = D -> isomorphic_path_data C.1 D.1.
Proof.
  intros p.
  induction p.
  exact (id_isomorphic_path_data C.1).
Defined.

Definition isomorphic_path_data_to_isomorphic_data
           `{Univalence}
           (C D : PreCategory)
  : isomorphic_path_data C D <~> isomorphic_data C D.
Proof.
  simple refine (functor_sigma_equiv _ _).
  - exact transport_idmap_equiv.
  - intros F ; simpl.
    simple refine (functor_sigma_equiv _ _).
    + refine (functor_forall_equiv equiv_idmap _).
      intros X.
      refine (functor_forall_equiv equiv_idmap _).
      intros Y ; simpl.
      apply transport_idmap_equiv.
    + intros HF. simpl.
      simple refine (functor_prod_equiv _ _).
      * exact equiv_idmap.
      * exact equiv_idmap.
Defined.

Definition factor_id_to_isomorphic_data
           `{Univalence}
           (C D : Cat)
  : id_to_isomorphic_data C D
    =
    ((isomorphic_path_data_to_isomorphic_data C.1 D.1))
      o id_to_isomorphic_path_data C D.
Proof.
  funext p.
  induction p.
  simple refine (path_sigma' _ _ _).
  - reflexivity.
  - simpl.
    apply path_sigma_hprop.
    reflexivity.
Defined.

Definition eq_cat
       `{Univalence}
       (C D : Cat)
  : C = D <~> C.1 = D.1
  := BuildEquiv _ _ (fun z => z..1) _.

Definition ap10_equiv
           `{Funext}
           {A B : Type}
           (f g : A -> B)
  : f = g <~> f == g
  := BuildEquiv _ _ ap10 _.

Definition postconcat_equiv
           {A : Type}
           {x y z : A}
           (p : y = z)
  : (x = y) <~> (x = z)
  := BuildEquiv _ _ (fun q => q @ p) _.

Definition preconcat_equiv
           {A : Type}
           {x y z : A}
           (p : x = y)
  : (y = z) <~> (x = z)
  := BuildEquiv _ _ (fun q => p @ q) _.

Definition id_precat_to_isomorphic_path_data
       `{Univalence}
       (C D : Cat)
  : C.1 = D.1 <~> isomorphic_path_data C.1 D.1.
Proof.
  refine (equiv_compose' _ (equiv_path_precategory_uncurried' C.1 D.1)^-1%equiv).
  simple refine (functor_sigma_equiv equiv_idmap _).
  intros p ; simpl.
  simple refine (functor_sigma_equiv _ _).
  - refine (equiv_compose' _ (ap10_equiv _ _)).
    refine (functor_forall_equiv (transport_idmap_equiv p) _).
    intros X.
    refine (equiv_compose' _ (ap10_equiv _ _)).
    refine (functor_forall_equiv (transport_idmap_equiv p) _).
    intros Y ; simpl.
    refine (equiv_compose' _ (equiv_compose' _ (equiv_compose' _ _))).
    + exact (preconcat_equiv
               (path_universe
                  (transport_morphism (transport_Vp idmap p X)^
                   (transport_Vp idmap p Y)^))).
    + exact (preconcat_equiv
               (transport_const
                  p
                  (morphism
                     C.1
                     (transport idmap p^ (transport idmap p X))
                     (transport idmap p^ (transport idmap p Y))))^).
    + exact (preconcat_equiv
               (transport_arrow
                  p
                  (Core.morphism C.1 (transport idmap p^ (transport idmap p X)))
                  (transport idmap p Y))^).
    + cbn.
      exact (preconcat_equiv
               (ap10 (@transport_arrow
                        _
                        _
                        (fun x : Type => x -> Type)
                        _ _ p
                        (Core.morphism C.1)
                        (transport idmap p X))
                     (transport idmap p Y))^).
  -intros q ; cbn.
   destruct C as [C HC], D as [D HD].
   destruct C, D.
   cbn in *.
   induction p ; simpl.
   induction q ; simpl.
   clear HC. clear HD.
   simple refine (functor_prod_equiv _ _).
   + simple refine (equiv_iff_hprop _ _).
     * intros r X Y Z f g ; simpl in *.
       induction r.
       rewrite !concat_p1.
       rewrite !transport_path_universe.
       rewrite !transport_morphism_11.
       reflexivity.
     * intros r.
       funext X Y Z f g ; simpl in *.
       specialize (r X Y Z g f).
       rewrite !concat_p1 in r.
       rewrite !transport_path_universe in r.
       rewrite !transport_morphism_11 in r.
       exact r.
   + simple refine (equiv_iff_hprop _ _).
     * intros r X ; simpl in *.
       induction r.
       rewrite !concat_p1.
       rewrite transport_path_universe.
       rewrite transport_morphism_id.
       reflexivity.
     * intros r.
       funext X.
       specialize (r X).
       rewrite concat_p1 in r.
       rewrite transport_path_universe in r.
       rewrite transport_morphism_id in r.
       exact r.
Defined.

Definition path_universe_eq
           `{Univalence}
           {A B : Type}
           (f g : A -> B)
           `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : f == g -> path_universe f = path_universe g
  := @path2_universe _ _ A B (BuildEquiv _ _ f _) (BuildEquiv _ _ g _).

Definition factor_id_to_isomorphic_path_data
           `{Univalence}
           (C D : Cat)
  : id_to_isomorphic_path_data C D
    =
    id_precat_to_isomorphic_path_data C D o eq_cat C D.
Proof.
  funext p.
  induction p.
  simple refine (path_sigma' _ idpath _).
  apply path_sigma_hprop.
  funext X Y ; cbn.
  unfold functor_forall ; cbn.
  rewrite concat_p1.
  rewrite <- path_universe_1.
  simple refine (path_universe_eq _ _ _).
  intros f ; cbn.
  rewrite transport_morphism_11.
  reflexivity.
Qed.

Global Instance univalent_0_cat `{Univalence}
  : Univalent_0 Cat.
Proof.
  intros C D.
  rewrite factor_id_to_adjequiv.
  rewrite factor_id_to_iso.
  rewrite factor_id_to_isomorphic_data.
  rewrite factor_id_to_isomorphic_path_data.
  apply isequiv_compose'.
  - apply isequiv_compose'.
    + apply isequiv_compose'.
      * apply isequiv_compose'.
        ** apply _.
        ** apply _.
      * apply _.
    +  apply _.
  - apply _.
Defined.

Global Instance univalent_cat `{Univalence}
  : Univalent Cat.
Proof.
  split ; apply _.
Defined.