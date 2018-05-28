Require Import HoTT.
From HoTT.Categories Require Import GroupoidCategory.
From GR.bicategories.bicategory Require Import
     bicategory examples.cat examples.full_sub.

(** The definition of groupoids. *)
Definition groupoid := {C : PreCategory & IsGroupoid C}.

(** The structure of groupoids *)

(** The underlying type of objects. *)
Definition under (G : groupoid) : Type
  := object G.1.

Coercion grpd_to_type := under.

(** The homsets. *)
Definition hom (G : groupoid) : G -> G -> hSet
  := fun x y => BuildhSet (morphism G.1 x y)%morphism.

(** The unit element. *)
Definition e {G : groupoid} (x : G) : hom G x x
  := 1%morphism.

(** Composition. *)
Definition comp {G : groupoid} {x y z : G}
  : hom G x y -> hom G y z -> hom G x z
  := fun g h => (h o g)%morphism.

Notation "p · q" := (comp p q) (at level 40).

(** Inverses. *)
Definition inv {G : groupoid} {x y : G}
  : hom G x y -> hom G y x
  := fun g => @morphism_inverse _ _ _ g (G.2 _ _ g).

(** Left associativity. *)
Definition cal
           {G : groupoid}
           {v x y z : G}
           (p : hom G v x) (q : hom G x y) (r : hom G y z)
  : (p · q) · r = p · (q · r)
  := (associativity G.1 v x y z p q r)^.

(** Right associativity. *)
Definition car
           {G : groupoid}
           {v x y z : G}
           (p : hom G v x) (q : hom G x y) (r : hom G y z)
  : p · (q · r) = (p · q) · r
  := associativity G.1 v x y z p q r.

(** Right neutrality. *)
Definition ce
           {G : groupoid}
           {x y : G}
           (p : hom G x y)
  : p · e y = p
  := left_identity G.1 x y p.

(** Left neutrality. *)
Definition ec
           {G : groupoid}
           {x y : G}
           (p : hom G x y)
  : e x · p = p
  := right_identity G.1 x y p.

(** Right inverse. *)
Definition ci
           {G : groupoid}
           {x y : G}
           (p : hom G x y)
  : p · inv p = e x
  := @left_inverse G.1 x y p (G.2 x y p).

(** Left inverse. *)
Definition ic
           {G : groupoid}
           {x y : G}
           (p : hom G x y)
  : inv p · p = e y
  := @right_inverse G.1 x y p (G.2 x y p).

(** A function for building groupoids. *)
Definition Build_grpd
           (obj : Type)
           (hom : obj -> obj -> hSet)
           (e : forall (x : obj), hom x x)
           (inv : forall {x y : obj}, hom x y -> hom y x)
           (comp : forall {x y z : obj}, hom x y -> hom y z -> hom x z)
           (assoc : forall (x y z v : obj) (p : hom v x) (q : hom x y) (r : hom y z),
               comp p (comp q r) = comp (comp p q) r)
           (ec : forall (x y : obj) (p : hom x y),
               comp (e x) p = p)
           (ce : forall (x y : obj) (p : hom x y),
               comp p (e y) = p)
           (ic : forall (x y : obj) (p : hom x y),
               comp (inv p) p = e y)
           (ci : forall (x y : obj) (p : hom x y),
               comp p (inv p) = e x)
  : groupoid.
Proof.
  simple refine (_;_).
  - simple refine (@Build_PreCategory
                     obj
                     hom
                     e
                     (fun _ _ _ p q => comp _ _ _ q p)
                     _ _ _ _).
    + cbn ; intros.
      apply assoc.
    + cbn ; intros.
      apply ce.
    + cbn ; intros.
      apply ec.
  - intros x y p ; cbn in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _) ; cbn.
    + exact (inv _ _ p).
    + apply ci.
    + apply ic.
Defined.

(** Groupoid functors *)
Definition grpd_functor `{Univalence} (G₁ G₂ : groupoid) : PreCategory
  := functor_category G₁.1 G₂.1.

(** The object part of a functor. *)
Definition grpd_object_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : under G₁ -> under G₂
  := object_of F.

(** The morphism part of a functor. *)
Definition grpd_morphism_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁},
    hom G₁ x y -> hom G₂ (grpd_object_of F x) (grpd_object_of F y)
  := morphism_of F.

(** Functors preserve the unit. *)
Definition grpd_identity_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall (x : under G₁), grpd_morphism_of F (e x) = e (grpd_object_of F x)
  := identity_of F.

(** Functors preserve the multiplication. *)
Definition grpd_composition_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y z : under G₁} (p : hom G₁ x y) (q : hom G₁ y z),
    grpd_morphism_of F (p · q) = grpd_morphism_of F p · grpd_morphism_of F q
  := composition_of F.

(** Functors preserve inverses. *)
Definition grpd_inverse_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁} (p : hom G₁ x y),
    grpd_morphism_of F (inv p) = inv (grpd_morphism_of F p).
Proof.
  intros x y p.
  apply iso_moveL_1V.
  refine (((grpd_composition_of F p (inv p))^ @ _ @ grpd_identity_of F x)).
  apply (ap (grpd_morphism_of F)).
  apply ci.
Defined.

(** We have a bicategory of groupoids. *)
Definition grpd `{Univalence} : BiCategory
  := full_sub Cat (fun C => BuildhProp (IsGroupoid C)).

(** Note: it has the expected objects and morphisms. *)
Definition grpd_obj `{Univalence} : Obj grpd = groupoid
  := idpath.

Definition grpd_hom `{Univalence} : Hom grpd = grpd_functor
  := idpath.